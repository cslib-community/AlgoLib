/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Frontend.Statements

/-!
# Method declaration assembly

Collects lexically scoped resources and temporary arguments, then emits method declarations from
the elaborated body. This is the sole entry point used by the public frontend dispatcher.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
open Lean Elab Command Term Meta Parser

/-- Reserve local and guard registers before elaborating paths. Names are lexical;
slots are method scratch and never specialize executable code. -/
partial def collect (rs : Array Resource) (body : Syntax) : TermElabM (Array Resource) := do
  let mut rs := rs
  for raw in items body do
    let stx : TSyntax `doElem := ⟨raw⟩
    match stx with
    | `(doElem| let mut $x:ident := $_:term)
    | `(doElem| let mut $x:ident : Nat := $_:term) =>
      rs := rs.push ⟨x, ← `(Nat), true, true⟩
    | `(doElem| let $x:ident := $_:term)
    | `(doElem| let $x:ident : Nat := $_:term) =>
      rs := rs.push ⟨x, ← `(Nat), true, false⟩
    | `(doElem| if $q:term then $yes:doSeq else $no:doSeq) =>
      rs ← guards rs q
      rs ← collect (← collect rs yes) no
    | `(doElem| if $q:term then $yes:doSeq) =>
      rs ← collect (← guards rs q) yes
    | `(doElem| while $q:term
        $[invariant $[$_:str]? $_:term]* $_:loopCost
        $[done_with $_]? $[decreasing $_]? do $body:doSeq)
    | `(doElem| while $q:term
        $[invariant $[$_:str]? $_:term
        ]* $[done_with $_]? $[decreasing $_]? do $body:doSeq) =>
      rs ← collect (← guards rs q) body
    | _ => pure ()
  return rs
where
  guards (rs : Array Resource) (q : Term) : TermElabM (Array Resource) := do
    if q.raw.isIdent then return rs
    let key := "_guard" ++ toString (q.raw.getPos?.getD 0)
    return rs ++ #[⟨mkIdent (Name.mkSimple (key ++ "a")), ← `(Nat), true, true⟩,
      ⟨mkIdent (Name.mkSimple (key ++ "b")), ← `(Nat), true, true⟩]

partial def collectArguments (known rs : Array Resource) (body : Syntax) :
    TermElabM (Array Resource) := do
  let mut rs := rs
  for raw in items body do
    let stx : TSyntax `doElem := ⟨raw⟩
    match stx with
    | `(doElem| $f:ident($args:term,*)) =>
      if args.getElems.any (fun a => mentions known a.raw) then
        let key := "_argument" ++ toString (f.raw.getPos?.getD 0)
        rs := rs.push ⟨mkIdent (Name.mkSimple key), ← `(Nat), true, true⟩
    | `(doElem| if $_:term then $yes:doSeq else $no:doSeq) =>
      rs ← collectArguments known (← collectArguments known rs yes) no
    | `(doElem| if $_:term then $yes:doSeq) => rs ← collectArguments known rs yes
    | `(doElem| while $_:term
        $[invariant $[$_:str]? $_:term]* $_:loopCost
        $[done_with $_]? $[decreasing $_]? do $body:doSeq)
    | `(doElem| while $_:term
        $[invariant $[$_:str]? $_:term
        ]* $[done_with $_]? $[decreasing $_]? do $body:doSeq) =>
      rs ← collectArguments known rs body
    | `(doElem| $e:term) =>
      let (f, args) ← receiverApplication e
      if args.any (fun a => mentions known a.raw) then
        let key := "_argument" ++ toString (f.raw.getPos?.getD 0)
        rs := rs.push ⟨mkIdent (Name.mkSimple key), ← `(Nat), true, true⟩
    | _ => pure ()
  return rs

/-- Existing `ram method` dispatches resource parameters here. Immutable parameters
specialize the method before execution and must not be confused with RAM inputs. -/
def declareMethod (name : Ident) (binders : Array (TSyntax `leafny_binder))
    (ret : Ident) (retTy : Term) (pre post : Array Term) (credits : Option Term)
    (body : TSyntax ``Parser.Term.doSeq) : CommandElabM Unit := do
  let mut rs : Array Resource := #[]
  let mut params : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  let mut args : Array Term := #[]
  for b in binders do
    match b with
    | `(leafny_binder| (mut $x:ident : $ty:term)) => rs := rs.push ⟨x, ty, false, true⟩
    | `(leafny_binder| ($x:ident : $ty:term)) =>
      params := params.push (← `(bracketedBinder| ($x : $ty)))
      args := args.push (← `($x))
    | _ => throwErrorAt b "Use typed mutable resources and explicit immutable configuration \
        parameters"
  if rs.isEmpty then throwErrorAt name "Declare at least one mutable resource"
  let inputs := rs
  rs ← Command.runTermElabM fun _ => do
    let rs ← collect rs body
    collectArguments rs rs body
  let names := rs.map (·.name.getId)
  unless names.toList.Nodup do throwErrorAt name "Mutable resource names must be distinct"
  for r in rs do
    if r.name.getId == ret.getId || ret.getId == `remaining ||
        ret.getId == r.name.getId.appendAfter "Old" || r.name.getId == `remaining ||
        names.contains (r.name.getId.appendAfter "Old") then
      throwErrorAt r.name "Reserve distinct output, Old, and remaining-credit names"
  let input := mkIdent (← liftCoreM <| mkFreshUserName `input)
  let output := mkIdent (← liftCoreM <| mkFreshUserName `output)
  let (fragment, state, pre, post, budget, uniformBudget) ← Command.runTermElabM fun _ => do
    let mut fragment ← statements rs body credits.isNone (inputs.map (·.name.getId))
    let mut p ← `(True)
    for fact in pre.reverse do p ← `($fact ∧ $p)
    let mut q ← `(True)
    for fact in post.reverse do q ← `($fact ∧ $q)
    let state ← stateType inputs
    let result ← if retTy.raw.isIdent && retTy.raw.getId == `Unit then `(()) else do
      let mut values : Array Term := #[]
      for i in [:inputs.size] do values := values.push (← project inputs i (← `($output)))
      let mut value := values.back!
      for v in values.toList.dropLast.reverse do value ← `(($v, $value))
      pure value
    q ← `(let $ret : $retTy := $result; $q)
    p ← bindOld inputs (← `($input)) (← bindViews inputs (← `($input)) p)
    q ← bindOld inputs (← `($input)) (← bindViews inputs (← `($output)) q)
    if rs.size > inputs.size then
      let scratch ← stateType (rs.extract inputs.size rs.size)
      let enter ← operation (← `(enterLocals $state $scratch)) #[]
        (← `(Locals.credits (L := $scratch)))
      let initializeCost := fun t => do
        let mut result := t
        for r in rs.extract inputs.size rs.size do
          result ← substitute r.name.getId (⟨Syntax.mkNumLit "0"⟩) result
        return result
      let enter : Fragment := { enter with transfer := initializeCost }
      let leave ← operation (← `(leaveLocals $state $scratch)) #[] (← `(0))
      fragment ← seq enter (← seq fragment leave)
    let budget ← match credits, fragment.estimate with
      | some c, _ => bindViews inputs (← `($input)) c
      | none, some c => bindViews inputs (← `($input)) c
      | none, none => throwErrorAt body "Loops need a logical credits clause and a resource \
        invariant; RAM time is inferred"
    let plan ← bindOld inputs (← `($input)) fragment.plan
    return ({ fragment with plan }, state, p, q, budget, fragment.estimate.getD budget)
  if rs.size > inputs.size then
    let scratchType ← Command.runTermElabM fun _ => stateType (rs.extract inputs.size rs.size)
    let scratchName := mkIdent (name.getId.appendAfter "Locals")
    elabCommand (← `(command| abbrev $scratchName : Type := $scratchType))
  let obligations := mkIdent (name.getId.appendAfter "Obligations")
  let certificate := mkIdent (name.getId.appendAfter "Certificate")
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    @[reducible] def $name $params* : Algorithm $state $state where
      body := $(fragment.program)
      annotations := fun $input => $(fragment.plan)
      «requires» := fun $input => $pre
      «ensures» := fun $input $output => $post
      «credits» := fun $input => $budget))
  let obligationType ← if params.isEmpty then `(($name).Obligations)
    else `(∀ $params*, ($name $args*).Obligations)
  elabCommand (← `(command| def $obligations : Prop := $obligationType))
  elabCommand (← `(command|
    @[reducible] def $certificate (proof : $obligations) $params* : Procedure $state $state :=
      ($name $args*).certify (proof $args*)))
  if credits.isNone && !(← Command.runTermElabM fun _ => do
      let fragment ← statements rs body true (inputs.map (·.name.getId))
      return fragment.estimate.any (fun c => mentions inputs c)) then
    let uniform := mkIdent (name.getId.appendAfter "UniformCredits")
    elabCommand (← `(command|
      instance $uniform:ident (proof : $obligations) $params* :
          UniformCredits ($certificate proof $args*) where
        amount := $uniformBudget
        bound _ := Nat.le_refl _))


end AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
