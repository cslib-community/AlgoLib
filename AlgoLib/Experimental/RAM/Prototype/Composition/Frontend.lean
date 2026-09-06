/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Velvet.Syntax
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts

/-!
# Owned procedures in the existing mutable `ram method` frontend

This elaborator is called by LogicalFrontend's existing declaration handler. It
reuses Velvet binders, Lean mutable assignment/conditionals and annotated loops.
Mutable parameters denote separately owned mathematical values. Assignment of a
verified procedure updates one parameter; all other parameters are framed by typed
composition. Receiver calls are shorthand for the same assignment.

A procedure expression describes fixed code, not a runtime Lean callback. Runtime
parameters may occur in invariants and postconditions, but not specialize that
code. Every call body and every guard still needs a supported RAM implementation.
The first adapter supports resource procedures and single-resource queries. Scalar
array expressions continue through the existing array frontend.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
open Lean Elab Command Term Meta Parser

syntax (name := receiverCall) ident noWs "(" term,* ")" : doElem

private structure Resource where
  name : Ident
  type : Term
  deriving Inhabited

private structure Fragment where
  program : Term
  plan : Term
  estimate : Option Term
  writes : Array Nat := #[]

private def stateType (rs : Array Resource) : TermElabM Term := do
  let mut t := rs.back!.type
  for r in rs.toList.dropLast.reverse do t ← `($(r.type) × $t)
  return t

private partial def project (rs : Array Resource) (i : Nat) (s : Term) : TermElabM Term := do
  if rs.size == 1 then return s
  if i == 0 then `(($s).1)
  else project (rs.extract 1 rs.size) (i - 1) (← `(($s).2))

private def bindViews (rs : Array Resource) (s : Term) (t : Term) : TermElabM Term := do
  let mut result := t
  for i in (List.range rs.size).reverse do
    result ← `(let $(rs[i]!.name) : $(rs[i]!.type) := $(← project rs i s); $result)
  return result

private def bindOld (rs : Array Resource) (s : Term) (t : Term) : TermElabM Term := do
  let mut result := t
  for i in (List.range rs.size).reverse do
    let old := mkIdent (rs[i]!.name.getId.appendAfter "Old")
    result ← `(let $old : $(rs[i]!.type) := $(← project rs i s); $result)
  return result

private def skip : TermElabM Fragment :=
  return ⟨← `(Program.identity), ← `(Plan.identity), some (← `(0)), #[]⟩

private def seq (p q : Fragment) : TermElabM Fragment := do
  let estimate ← match p.estimate, q.estimate with
    | some x, some y => pure (some (← `($x + $y)))
    | _, _ => pure none
  return ⟨← `(Program.seq $(p.program) $(q.program)), ← `(Plan.seq $(p.plan) $(q.plan)),
    estimate, p.writes ++ q.writes⟩

/-- Focus a call on one typed component; the remaining components become automatic frames. -/
private partial def focus (rs : Array Resource) (i : Nat) (p : Fragment) : TermElabM Fragment := do
  if rs.size == 1 then return p
  if i == 0 then
    let rest ← stateType (rs.extract 1 rs.size)
    return { p with
      program := ← `(Program.frame $(p.program) $rest)
      plan := ← `(Plan.frame $(p.plan) $rest) }
  let inner ← focus (rs.extract 1 rs.size) (i - 1) p
  let framed : Fragment := { inner with
    program := ← `(Program.frame $(inner.program) $(rs[0]!.type))
    plan := ← `(Plan.frame $(inner.plan) $(rs[0]!.type)) }
  let swap : Fragment := ⟨← `(Program.swap), ← `(Plan.swap), some (← `(0)), #[]⟩
  seq swap (← seq framed swap)

private partial def liftQuery (rs : Array Resource) (i : Nat) (q : Term) : TermElabM Term := do
  if rs.size == 1 then return q
  if i == 0 then `(testLeft $q)
  else `(testRight $(← liftQuery (rs.extract 1 rs.size) (i - 1) q))

private def query (rs : Array Resource) (q : Term) : TermElabM Term := do
  -- Receiver query syntax such as `left.nonempty` is ordinary Lean identifier syntax.
  let id := q.raw.getId
  let .str receiver field := id
    | throwErrorAt q "Use a certified resource query such as left.nonempty"
  let some i := rs.findIdx? (fun r => r.name.getId == receiver)
    | throwErrorAt q "A query must name one declared mutable resource"
  liftQuery rs i (mkIdent (Name.mkSimple field))

private partial def checkStatic (rs : Array Resource) (term : Syntax) : TermElabM Unit := do
  if term.isIdent then
    for r in rs do
      let n := term.getId
      if r.name.getId.isPrefixOf n || (r.name.getId.appendAfter "Old").isPrefixOf n then
        throwErrorAt term
          "Procedure arguments describe fixed code. Runtime input '{r.name}' must pass through a \
        certified typed operation"
  for child in term.getArgs do checkStatic rs child

private def items (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Parser.Term.doSeqBracketed then stx[1].getArgs.map (·[0])
  else if stx.getKind == ``Parser.Term.doSeqIndent then stx[0].getArgs.map (·[0])
  else #[]

private partial def statements (rs : Array Resource) (body : TSyntax ``Parser.Term.doSeq)
    (inferBudget : Bool) (nested := false) : TermElabM Fragment := do
  let mut result ← skip
  let all := items body.raw
  for i in [:all.size] do
    let stx : TSyntax `doElem := ⟨all[i]!⟩
    if stx.raw.getKind == ``Parser.Term.doReturn && (nested || i + 1 < all.size) then
      throwErrorAt stx "Return is supported only at method exit"
    result ← seq result (← statement stx)
  return result
where
  call (target : Ident) (proc : Term) : TermElabM Fragment := do
    let some i := rs.findIdx? (fun r => r.name.getId == target.getId)
      | throwErrorAt target "Assignment requires a declared mutable resource"
    checkStatic rs proc.raw
    let amount ← `(UniformCredits.amount (proc := $proc))
    let proc ← if inferBudget then `(Procedure.uniform $proc) else pure proc
    let part : Fragment := ⟨← `(Program.call ($proc).body), ← `(Plan.call $proc),
      some (← `(UniformCredits.amount (proc := $proc))), #[i]⟩
    let part := { part with estimate := some amount }
    focus rs i part
  statement (stx : TSyntax `doElem) : TermElabM Fragment := withRef stx do
    match stx with
    | `(doElem| $target:ident := $proc:term) => call target proc
    | `(doElem| $f:ident($args:term,*)) =>
      let .str receiver field := f.getId
        | throwErrorAt f "Use a receiver such as left.append(...)"
      call (mkIdent receiver) (← `($(mkIdent (Name.mkSimple field)) $args*))
    | `(doElem| if $q:term then $yes:doSeq else $no:doSeq) =>
      let test ← query rs q
      let yes ← statements rs yes inferBudget true
      let no ← statements rs no inferBudget true
      let estimate ← match yes.estimate, no.estimate with
        | some x, some y => pure (some (← `(1 + max $x $y)))
        | _, _ => pure none
      return ⟨← `(Program.branch $test $(yes.program) $(no.program)),
        ← `(Plan.branch $test $(yes.plan) $(no.plan)), estimate, yes.writes ++ no.writes⟩
    | `(doElem| if $q:term then $yes:doSeq) =>
      statement (← `(doElem| if $q then $yes else pure ()))
    | `(doElem| while $q:term
        $[invariant $[$label:str]? $inv:term
        ]*
        $[done_with $done]?
        $[decreasing $measure]?
        do $body:doSeq) =>
      if measure.isSome || done.isSome then
        throwErrorAt stx "Owned loops use invariant clauses (including remaining credits); use \
        assert after the loop for its exit fact"
      let test ← query rs q
      let body ← statements rs body inferBudget true
      let s := mkIdent (← mkFreshUserName `state)
      let entry := mkIdent (← mkFreshUserName `entry)
      let remaining := mkIdent `remaining
      let mut invTerm ← `(True)
      for fact in inv.reverse do invTerm ← `($fact ∧ $invTerm)
      invTerm ← bindViews rs (← `($s)) invTerm
      for i in [:rs.size] do
        unless body.writes.contains i do
          invTerm ← `($(← project rs i (← `($s))) = $(← project rs i (← `($entry))) ∧ $invTerm)
      let loopInv ← `(fun ($s : $(← stateType rs)) ($remaining : Nat) => $invTerm)
      return ⟨← `(Program.loop $test $(body.program)),
        ← `(Plan.atEntry (fun ($entry : $(← stateType rs)) =>
          Plan.loop $test $loopInv $(body.plan))),
        none, body.writes⟩
    | `(doElem| assert $fact:term) =>
      let s := mkIdent (← mkFreshUserName `state)
      let predicate ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) fact))
      return ⟨← `(Program.identity), ← `(Plan.assert $predicate), some (← `(0)), #[]⟩
    | `(doElem| return) | `(doElem| return ()) | `(doElem| pure ()) => skip
    | `(doElem| $e:term) =>
      let (head, args) ← match e with
        | `($f:ident $args:term*) => pure (f, args)
        | `($f:ident) => pure (f, #[])
        | _ => throwErrorAt e "Use a receiver call or assign a verified procedure"
      let .str receiver field := head.getId
        | throwErrorAt e "A receiver call must name a declared mutable resource"
      let mut actual : Array Term := #[]
      for arg in args do
        match arg with
        | `(()) => pure ()
        | `(($a:term, $b:term)) => actual := actual ++ #[a, b]
        | `(($a:term)) => actual := actual.push a
        | _ => actual := actual.push arg
      call (mkIdent receiver) (← `($(mkIdent (Name.mkSimple field)) $actual*))
    | _ => throwErrorAt stx "Owned statements are procedure assignments, receiver calls, \
        conditionals, annotated loops, and assertions"

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
    | `(leafny_binder| (mut $x:ident : $ty:term)) => rs := rs.push ⟨x, ty⟩
    | `(leafny_binder| ($x:ident : $ty:term)) =>
      params := params.push (← `(bracketedBinder| ($x : $ty)))
      args := args.push (← `($x))
    | _ => throwErrorAt b "Use typed mutable resources and explicit immutable configuration \
        parameters"
  if rs.isEmpty then throwErrorAt name "Declare at least one mutable resource"
  let names := rs.map (·.name.getId)
  unless names.toList.Nodup do throwErrorAt name "Mutable resource names must be distinct"
  for r in rs do
    if r.name.getId == ret.getId || ret.getId == `remaining ||
        ret.getId == r.name.getId.appendAfter "Old" || r.name.getId == `remaining ||
        names.contains (r.name.getId.appendAfter "Old") then
      throwErrorAt r.name "Reserve distinct output, Old, and remaining-credit names"
  let input := mkIdent (← liftCoreM <| mkFreshUserName `input)
  let output := mkIdent (← liftCoreM <| mkFreshUserName `output)
  let (fragment, state, pre, post, budget) ← Command.runTermElabM fun _ => do
    let fragment ← statements rs body credits.isNone
    let mut p ← `(True)
    for fact in pre.reverse do p ← `($fact ∧ $p)
    let mut q ← `(True)
    for fact in post.reverse do q ← `($fact ∧ $q)
    let state ← stateType rs
    let result ← if retTy.raw.isIdent && retTy.raw.getId == `Unit then `(()) else `($output)
    q ← `(let $ret : $retTy := $result; $q)
    p ← bindOld rs (← `($input)) (← bindViews rs (← `($input)) p)
    q ← bindOld rs (← `($input)) (← bindViews rs (← `($output)) q)
    let budget ← match credits, fragment.estimate with
      | some c, _ => bindViews rs (← `($input)) c
      | none, some c => pure c
      | none, none => throwErrorAt body "Loops need a logical credits clause and a resource \
        invariant; RAM time is inferred"
    let plan ← bindOld rs (← `($input)) fragment.plan
    return ({ fragment with plan }, state, p, q, budget)
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

end AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
