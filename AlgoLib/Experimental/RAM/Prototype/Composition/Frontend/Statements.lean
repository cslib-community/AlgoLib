/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Frontend.Expressions

/-!
# Structured statements and loop annotations

Recursively elaborates assignments, calls, branches, and annotated loops into the exact Program
and Plan. Supplied counting arguments remain verification obligations.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
open Lean Elab Command Term Meta Parser

/-- Attach lexical identities to unscoped primitive/call diagnostics, including loop guards. -/
private def scopePlan (scope : String) (plan : Term) : TermElabM Term := do
  return ⟨← plan.raw.replaceM fun node => do
    let tag (site : Term) : TermElabM Term := do
      if scope.isEmpty then return site
      match site with
      | `($s:str) =>
        if s.getString.contains "\n" then return site
        return quote (scope ++ "\n" ++ s.getString)
      | _ => return site
    match node with
    | `(Plan.invokeAt $site $op) => return some (← `(Plan.invokeAt $(← tag site) $op)).raw
    | `(Plan.callAt $site $proc) => return some (← `(Plan.callAt $(← tag site) $proc)).raw
    | _ => return none⟩

partial def statements (rs : Array Resource) (body : TSyntax ``Parser.Term.doSeq)
    (inferBudget : Bool) (active : Array Name) (nested := false) (scope : String := "") :
    TermElabM Fragment := do
  let mut active := active
  let mut result ← skip
  let all := items body.raw
  for i in [:all.size] do
    let stx : TSyntax `doElem := ⟨all[i]!⟩
    if stx.raw.getKind == ``Parser.Term.doReturn && (nested || i + 1 < all.size) then
      throwErrorAt stx "Return is supported only at method exit"
    let (part, next) ← statement active stx
    let part ← do
      let site ← sourceSite stx
      -- Only the current primitive is labelled; its continuation keeps its own source.
      let plan ← match part.plan with
        | `(Plan.invoke $op) => `(Plan.invokeAt $site $op)
        | _ => pure part.plan
      pure { part with plan }
    let part := { part with plan := ← scopePlan scope part.plan }
    result ← seq result part
    active := next
  return result
where
  call (active : Array Name) (target : Ident) (proc : Term) : TermElabM Fragment := do
    let i ← resource rs active target
    checkStatic rs proc.raw
    let proc ← if inferBudget then `(contract% ($proc)) else pure proc
    let amount ← `(($proc).credits $(rs[i]!.name))
    focus rs i ⟨← `(Program.call ($proc).body),
      ← `(Plan.callAt $(← sourceSite target) $proc), some amount, #[i], pure, some amount⟩
  receiver (active : Array Name) (f : Ident) (args : Array Term) : TermElabM Fragment := do
    let .str target field := f.getId
      | throwErrorAt f "Use a receiver such as buffer.append(...)"
    unless args.any (fun a => mentions rs a.raw) do
      return ← call active (mkIdent target) (← `($(mkIdent (Name.mkSimple field)) $args*))
    if args.isEmpty then throwErrorAt f "Missing runtime argument"
    for arg in args.pop do checkStatic rs arg
    let i ← resource rs active (mkIdent target)
    let key := Name.mkSimple ("_argument" ++ toString (f.raw.getPos?.getD 0))
    let some j := rs.findIdx? (fun r => r.name.getId == key)
      | throwErrorAt f "Missing runtime argument slot"
    let prepare ← assignment rs active j args.back!
    let config := args.pop
    let proc ← `($(mkIdent (Name.mkSimple (field ++ "From"))) $config*)
    let proc ← if inferBudget then `(contract% ($proc)) else pure proc
    let amount ← `(($proc).credits ($(rs[i]!.name), $(rs[j]!.name)))
    let part : Fragment := ⟨← `(Program.call ($proc).body),
      ← `(Plan.callAt $(← sourceSite f) $proc),
      some amount, #[i,j], pure, some amount⟩
    seq prepare (← focusPair rs i j part)
  declare (active : Array Name) (x : Ident) (e : Term) :
      TermElabM (Fragment × Array Name) := do
    let some i := rs.findIdx? (fun r => r.name.getId == x.getId)
      | throwErrorAt x "Missing local slot"
    return (← assignment rs active i e, active.push x.getId)
  loop (active : Array Name) (q : Term) (label : Array (Option (TSyntax `str)))
      (inv : Array Term) (cost done measure : Option Term)
      (body : TSyntax ``Parser.Term.doSeq) (amortized := false)
      (initialBound : Option Term := none) (loopName : Option Ident := none) :
      TermElabM Fragment := do
    let (before, test, guardFact) ← condition rs active q
    let loopScope := loopName.map (fun n =>
      if scope.isEmpty then n.getId.toString else scope ++ "." ++ n.getId.toString)
    let mut body ← statements rs body inferBudget active true (loopScope.getD scope)
    let s := mkIdent (← mkFreshUserName `state)
    let entry := mkIdent (← mkFreshUserName `entry)
    let remaining := mkIdent `remaining
    if let some measure := measure then
      let predicate ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) measure))
      let program ← `(Program.seq $(body.program) Program.identity)
      let plan ← `(Plan.atEntry (fun $entry => Plan.seq $(body.plan)
        (Plan.assert (fun $s => $predicate $s < $predicate $entry))))
      body := {body with program, plan}
    body ← seq body before
    let site ← sourceSite q
    let site ← if let some key := loopScope then
      `( $(quote key) ++ "\n" ++ $site ) else pure site
    let mut estimated : Option Term := none
    let mut unit : Option Term := none
    if let some bound := cost then
      let some bodyCost := if amortized then body.work else body.estimate
        | throwErrorAt bound "Annotate every nested loop with iterations_at_most \
          or amortized_potential"
      -- For an increasing index, use the upper endpoint in the dependent body cost.
      -- This is a candidate envelope, not an axiom: preservation VCs must prove it pays.
      let envelope ← if amortized then pure bodyCost else match bound with
        | `($upper:term - $index:ident) => substitute index.getId upper bodyCost
        | _ => pure bodyCost
      unit := some envelope
      let initial := initialBound.getD bound
      estimated := some (← `($initial * ($envelope + 1) + 1))
    let mut invTerm ← `(True)
    for k in (List.range inv.size).reverse do
      let fact : Term := ⟨← inv[k]!.raw.replaceM fun node => do
        match node with
        | `(at_loop_entry($e:term)) => return some (← bindViews rs (← `($entry)) e).raw
        | _ => return none⟩
      if cost.isSome then
        if loopName.isSome && label[k]!.isNone then
          throwErrorAt inv[k]! "Give every invariant in a named loop a stable string name"
        let title := label[k]!.map (·.getString) |>.getD "loop invariant"
        let name ← `( $(quote (title ++ " initialized / preserved at ")) ++ $site )
        invTerm ← if loopName.isSome then `(InvariantFact $(quote title) $fact ∧ $invTerm)
          else `(Obligation $name $fact ∧ $invTerm)
      else invTerm ← `($fact ∧ $invTerm)
    invTerm ← bindViews rs (← `($s)) invTerm
    invTerm ← `($guardFact $s ∧ $invTerm)
    for i in [:rs.size] do
      if active.contains rs[i]!.name.getId && !body.writes.contains i then
        invTerm ← `($(← project rs i (← `($s))) = $(← project rs i (← `($entry))) ∧ $invTerm)
    let loopInv ← `(fun ($s : $(← stateType rs)) ($remaining : Nat) => $invTerm)
    let work ← body.work.mapM fun amount => `(1 + $amount)
    let loop : Fragment := ⟨← `(Program.loop $test $(body.program)),
      ← `(Plan.atEntry (fun ($entry : $(← stateType rs)) =>
        Plan.loop $test $loopInv $(body.plan))), none, body.writes, pure, work⟩
    let loop ← if let some bound := cost then do
      let frozen ← bindViews rs (← `($entry)) unit.get!
      let measure ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) bound))
      let invariantFn ← `(fun ($s : $(← stateType rs)) => $invTerm)
      let plan ← if amortized then
          `(Plan.atEntry (fun ($entry : $(← stateType rs)) =>
            Plan.workLoop $site $test $invariantFn $measure ($frozen + 1) $(body.plan)))
        else `(Plan.atEntry (fun ($entry : $(← stateType rs)) =>
          Plan.countedLoop $site $test $invariantFn $measure $frozen $(body.plan)))
      pure { loop with plan, estimate := estimated }
      else pure loop
    let mut part ← seq before loop
    if let some done := done then
      let fact ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) done))
      part ← seq part
        ⟨← `(Program.identity), ← `(Plan.assert $fact), some (← `(0)), #[], pure, some (← `(0))⟩
    return { part with plan := ← scopePlan (loopScope.getD scope) part.plan }
  statement (active : Array Name) (stx : TSyntax `doElem) :
      TermElabM (Fragment × Array Name) := withRef stx do
    match stx with
    | `(doElem| let mut $x:ident := $e:term)
    | `(doElem| let mut $x:ident : Nat := $e:term)
    | `(doElem| let $x:ident := $e:term)
    | `(doElem| let $x:ident : Nat := $e:term) => declare active x e
    | `(doElem| ($left:ident, $right:ident) := $proc:term) =>
      let i ← resource rs active left
      let j ← resource rs active right
      if i == j then throwErrorAt stx "A procedure cannot receive the same owned resource twice"
      unless rs[i]!.mutable && rs[j]!.mutable do
        throwErrorAt stx "Procedure outputs require mutable resources"
      checkStatic rs proc
      let proc ← if inferBudget then `(contract% ($proc)) else pure proc
      let amount ← `(($proc).credits ($(rs[i]!.name), $(rs[j]!.name)))
      let part : Fragment := ⟨← `(Program.call ($proc).body),
        ← `(Plan.callAt $(← sourceSite stx) $proc),
        some amount, #[i,j], pure, some amount⟩
      return (← focusPair rs i j part, active)
    | `(doElem| $target:ident := $value:term) =>
      let i ← resource rs active target
      unless rs[i]!.mutable do throwErrorAt target "Immutable local; use 'let mut'"
      let part ← if isNat rs[i]! then assignment rs active i value else call active target value
      return (part, active)
    | `(doElem| $a:ident[$i:term] := $e:term) =>
      let slot ← resource rs active a
      let index ← expression rs active i
      let value ← expression rs active e
      let part ← operation (← `(Composition.write $(← path rs slot) $index $value)) #[slot]
        (← `(Value.credits (S := $(← stateType rs)) $index +
          Value.credits (S := $(← stateType rs)) $value + 3))
      let updated ← `(($a).set! $i $e)
      return ({ part with transfer := fun t => substitute a.getId updated t }, active)
    | `(doElem| $f:ident($args:term,*)) =>
      return (← receiver active f args, active)
    | `(doElem| if $q:term then $yes:doSeq else $no:doSeq) =>
      let (before, test, _) ← condition rs active q
      let yes ← statements rs yes inferBudget active true scope
      let no ← statements rs no inferBudget active true scope
      let estimate ← match yes.estimate, no.estimate with
        | some x, some y => pure (some (← `(1 + max $x $y)))
        | _, _ => pure none
      let work ← match yes.work, no.work with
        | some x, some y => pure (some (← `(1 + max $x $y)))
        | _, _ => pure none
      let part : Fragment := ⟨← `(Program.branch $test $(yes.program) $(no.program)),
        ← `(Plan.branch $test $(yes.plan) $(no.plan)), estimate, yes.writes ++ no.writes,
        (fun t => do `(max $(← yes.transfer t) $(← no.transfer t))), work⟩
      return (← seq before part, active)
    | `(doElem| if $q:term then $yes:doSeq) =>
      statement active (← `(doElem| if $q then $yes else pure ()))
    | `(doElem| named $name:ident do $body:doSeq) =>
      let key := if scope.isEmpty then name.getId.toString else scope ++ "." ++ name.getId.toString
      return (← statements rs body inferBudget active true key, active)
    | `(doElem| while $q:term named $name:ident
        $[invariant $[$label:str]? $inv:term]*
        $cost:loopCost $[done_with $done]? $[decreasing $measure]? do $body:doSeq) =>
      return (← loop active q label inv (some ⟨cost.raw[1]⟩) done measure body
        (cost.raw.getKind == ``workPotential || cost.raw.getKind == ``boundedWork)
        (if cost.raw.getKind == ``boundedWork then some ⟨cost.raw[3]⟩ else none)
        (some name), active)
    | `(doElem| while $q:term
        $[invariant $[$label:str]? $inv:term]*
        $cost:loopCost $[done_with $done]? $[decreasing $measure]? do $body:doSeq) =>
      return (← loop active q label inv (some ⟨cost.raw[1]⟩) done measure body
        (cost.raw.getKind == ``workPotential || cost.raw.getKind == ``boundedWork)
        (if cost.raw.getKind == ``boundedWork then some ⟨cost.raw[3]⟩ else none), active)
    | `(doElem| while $q:term
        $[invariant $[$label:str]? $inv:term
        ]* $[done_with $done]? $[decreasing $measure]? do $body:doSeq) =>
      return (← loop active q label inv none done measure body, active)
    | `(doElem| assert $fact:term) =>
      let s := mkIdent (← mkFreshUserName `state)
      let predicate ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) fact))
      return (⟨← `(Program.identity), ← `(Plan.assert $predicate),
        some (← `(0)), #[], pure, some (← `(0))⟩, active)
    | `(doElem| return) | `(doElem| return ()) | `(doElem| pure ()) => return (← skip, active)
    | `(doElem| $e:term) =>
      let (head, args) ← receiverApplication e
      return (← receiver active head args, active)
    | _ => throwErrorAt stx "Use scalar assignment, indexed array update, a verified call, \
        conditional, annotated loop, or assertion"


end AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
