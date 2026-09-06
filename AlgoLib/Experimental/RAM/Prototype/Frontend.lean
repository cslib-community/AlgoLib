/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Velvet.Syntax
import AlgoLib.Experimental.RAM.Prototype.Mutable
import AlgoLib.Experimental.RAM.Prototype.Procedures

/-!
# Velvet surface syntax with a checked RAM backend

Uses upstream Velvet's binders, Lean `do` parser, mutable assignments, array notation,
and annotated nested-loop grammar. The RAM elaborator builds ONE `Program` and an
indexed proof plan. Both the Loom interpretation and compiler consume that program.
All register naming, array framing, guard materialization, annotation lifting and
credit propagation are implementation details of this module and Mutable.

This module also exports `ram_do` for certified data-structure interfaces and
procedure composition. Mutable `ram method` uses natural-number locals and one input array.
Upstream Velvet's full frontend remains available through `method`; unsupported RAM
operations are rejected here rather than treated as uncharged Lean computations.
`decreasing`, `done_with`, and assertions generate real obligations; they are not erased
before verification. Only their checked proof annotations disappear at compilation.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Meta Parser
open Authoring

private structure Fragment where
  program : Term
  plan : Term
  writes : Array String := #[]
  arrayWrites : Bool := false

private def skipFragment : TermElabM Fragment :=
  return ⟨← `(Program.skip), ← `(Plan.skip), #[], false⟩

private def actionFragment (a : Term) : TermElabM Fragment :=
  return ⟨← `(Program.action $a), ← `(Plan.action $a), #[], false⟩

private def sequence (a b : Fragment) : TermElabM Fragment :=
  return ⟨← `(Program.seq $(a.program) $(b.program)), ← `(Plan.seq $(a.plan) $(b.plan)),
    a.writes ++ b.writes, a.arrayWrites || b.arrayWrites⟩

private def sequences (xs : Array Fragment) : TermElabM Fragment := do
  let mut result ← skipFragment
  for x in xs.reverse do result ← sequence x result
  return result

private structure Binding where
  user : Ident
  name : String
  mutable : Bool

private structure Context where
  array : Ident
  old : Ident
  bindings : Array Binding := #[]
  nested : Bool := false

private def lookup (ctx : Context) (x : Ident) : TermElabM Binding := do
  match ctx.bindings.find? (fun b => b.user.getId == x.getId) with
  | some b => return b
  | none => throwErrorAt x "Unknown RAM local '{x}'; ghost terms cannot occur in executable code"

private def fresh (stem : String) : TermElabM String :=
  return (← mkFreshUserName (Name.mkSimple stem)).toString

/-- Bind annotation identifiers to ordinary arrays/naturals, never to RAM stores. -/
private def atState (ctx : Context) (state : Term) (body : Term) : TermElabM Term := do
  let mut term := body
  for b in ctx.bindings.reverse do
    term ← `(let $(b.user) : Nat := ($state).locals $(quote b.name); $term)
  term ← `(let $(ctx.array) : Array Nat := ($state).array; $term)
  return term

private def statePredicate (ctx : Context) (body : Term) : TermElabM Term := do
  let s ← mkFreshUserName `state
  let state := mkIdent s
  let term ← atState ctx (← `($state)) body
  `(fun ($state : Mutable.State) => $term)

private structure Expression where
  before : Array Fragment := #[]
  value : Term

private partial def expression (ctx : Context) (stx : Term) : TermElabM Expression := do
  match stx with
  | `(($e:term)) => expression ctx e
  | `($n:num) => return ⟨#[], ← `(Mutable.Value.literal $n)⟩
  | `($a:term[$i:term]!) | `($a:term[$i:term]) =>
    unless a.raw.isIdent && a.raw.getId == ctx.array.getId do
      throwErrorAt a "RAM indexing requires the mutable input array"
    let index ← expression ctx i
    let name ← fresh "arrayRead"
    let load ← actionFragment (← `(Mutable.read $(quote name) $(index.value)))
    return ⟨index.before.push load, ← `(Mutable.Value.local $(quote name))⟩
  | `($a:term + $b:term) => binary ctx a b ``Mutable.Value.add
  | `($a:term - $b:term) => binary ctx a b ``Mutable.Value.sub
  | `($a:term * $b:term) => binary ctx a b ``Mutable.Value.mul
  | _ =>
    if stx.raw.isIdent then
      if stx.raw.getId == ctx.array.getId.str "size" then
        return ⟨#[], ← `(Mutable.Value.size)⟩
      let b ← lookup ctx ⟨stx.raw⟩
      return ⟨#[], ← `(Mutable.Value.local $(quote b.name))⟩
    match stx with
    | `(($a:term).size) =>
      unless a.raw.isIdent && a.raw.getId == ctx.array.getId do
        throwErrorAt a "Only the mutable array's size is an executable RAM expression"
      return ⟨#[], ← `(Mutable.Value.size)⟩
    | _ => throwErrorAt stx "Unsupported RAM expression: {stx}"
where
  binary (ctx : Context) (a b : Term) (constructor : Name) : TermElabM Expression := do
    let a ← expression ctx a
    let b ← expression ctx b
    return ⟨a.before ++ b.before, ← `($(mkIdent constructor) $(a.value) $(b.value))⟩

private structure Condition where
  before : Fragment
  guard : Term

private def condition (ctx : Context) (stx : Term) : TermElabM Condition := do
  let (a, b, op, negate) ← match stx with
    | `($a:term < $b:term) => pure (a, b, ``Checked.Language.Comparison.lt, false)
    | `($a:term ≤ $b:term) => pure (a, b, ``Checked.Language.Comparison.le, false)
    | `($a:term > $b:term) => pure (b, a, ``Checked.Language.Comparison.lt, false)
    | `($a:term ≥ $b:term) => pure (b, a, ``Checked.Language.Comparison.le, false)
    | `($a:term = $b:term) => pure (a, b, ``Checked.Language.Comparison.eq, false)
    | `($a:term ≠ $b:term) => pure (a, b, ``Checked.Language.Comparison.eq, true)
    | _ => throwErrorAt stx "RAM guards require a comparison of natural-number expressions"
  let a ← expression ctx a
  let b ← expression ctx b
  let x ← fresh "guardLeft"
  let y ← fresh "guardRight"
  let ax ← actionFragment (← `(Mutable.assign $(quote x) $(a.value)))
  let assignRight ← actionFragment (← `(Mutable.assign $(quote y) $(b.value)))
  let before ← sequences (a.before ++ b.before ++ #[ax, assignRight])
  let guard ← `(Mutable.compare $(mkIdent op) $(quote x) $(quote y))
  if !negate then return ⟨before, guard⟩
  let flag ← fresh "guardNot"
  let one ← fresh "guardOne"
  let yes ← actionFragment (← `(Mutable.assign $(quote flag) (.literal 0)))
  let no ← actionFragment (← `(Mutable.assign $(quote flag) (.literal 1)))
  let branch : Fragment := ⟨← `(Program.branch $guard $(yes.program) $(no.program)),
    ← `(Plan.branch $guard $(yes.plan) $(no.plan)), #[], false⟩
  let init ← actionFragment (← `(Mutable.assign $(quote one) (.literal 1)))
  return ⟨← sequence before (← sequence branch init),
    ← `(Mutable.compare .eq $(quote flag) $(quote one))⟩

private def getItems (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Parser.Term.doSeqBracketed then stx[1].getArgs.map (·[0])
  else if stx.getKind == ``Parser.Term.doSeqIndent then stx[0].getArgs.map (·[0])
  else #[]

private partial def statements (ctx : Context) (body : TSyntax ``Parser.Term.doSeq) :
    TermElabM Fragment := do
  let mut ctx := ctx
  let mut result := #[]
  let items := getItems body.raw
  for index in [:items.size] do
    let item := items[index]!
    if item.getKind == ``Parser.Term.doReturn && index + 1 < items.size then
      throwErrorAt item "RAM return must be the final statement; early return is not supported"
    let (part, next) ← statement ctx ⟨item⟩
    result := result.push part
    ctx := next
  sequences result
where
  statement (ctx : Context) (stx : TSyntax `doElem) :
      TermElabM (Fragment × Context) := withRef stx do
    match stx with
    | `(doElem| let mut $x:ident := $e:term) => declare ctx x e true
    | `(doElem| let mut $x:ident : Nat := $e:term) => declare ctx x e true
    | `(doElem| let $x:ident := $e:term) => declare ctx x e false
    | `(doElem| let $x:ident : Nat := $e:term) => declare ctx x e false
    | `(doElem| $x:ident := $e:term) =>
      let b ← lookup ctx x
      unless b.mutable do throwErrorAt x "'{x}' is immutable; declare it with 'let mut'"
      let part ← assignExpression ctx b.name e
      return ({ part with writes := part.writes.push b.name }, ctx)
    | `(doElem| $a:ident[$i:term] := $e:term) =>
      unless a.getId == ctx.array.getId do
        throwErrorAt a "RAM array updates require the mutable input array"
      let i ← expression ctx i
      let e ← expression ctx e
      let put ← actionFragment (← `(Mutable.write $(i.value) $(e.value)))
      let part ← sequences (i.before ++ e.before ++ #[put])
      return ({ part with arrayWrites := true }, ctx)
    | `(doElem| if $q:term then $yes:doSeq else $no:doSeq) =>
      let cond ← condition ctx q
      let yes ← statements { ctx with nested := true } yes
      let no ← statements { ctx with nested := true } no
      let branch : Fragment := ⟨← `(Program.branch $(cond.guard) $(yes.program) $(no.program)),
        ← `(Plan.branch $(cond.guard) $(yes.plan) $(no.plan)),
        yes.writes ++ no.writes, yes.arrayWrites || no.arrayWrites⟩
      return (← sequence cond.before branch, ctx)
    | `(doElem| if $q:term then $yes:doSeq) =>
      statement ctx (← `(doElem| if $q then $yes else pure ()))
    | `(doElem| while $q:term
        $[invariant $[$label:str]? $inv:term
        ]*
        $[done_with $done]?
        $[decreasing $measure]?
        do $body:doSeq) =>
      let cond ← condition ctx q
      let body ← statements { ctx with nested := true } body
      let body ← sequence body cond.before
      let entry := mkIdent (← mkFreshUserName `entry)
      let state := mkIdent (← mkFreshUserName `state)
      let creditIdent := mkIdent `remaining
      let mut invTerm ← `(True)
      for fact in inv.reverse do invTerm ← `($fact ∧ $invTerm)
      let stateInv ← atState ctx (← `($state)) invTerm
      let mut frame ← `(True)
      for binding in ctx.bindings do
        unless body.writes.contains binding.name do
          frame ← `(($state).locals $(quote binding.name) =
            ($entry).locals $(quote binding.name) ∧ $frame)
      unless body.arrayWrites do
        frame ← `(($state).array = ($entry).array ∧ $frame)
      let predicate ← statePredicate ctx q
      let loopInv ← `(fun ($state : Mutable.State) ($creditIdent : Nat) =>
        $stateInv ∧ $frame ∧ ($(cond.guard)).test $state = decide ($predicate $state))
      let loopPlan ← match measure with
        | none => `(Plan.loop $(cond.guard) $loopInv $(body.plan))
        | some measure =>
          let variant ← statePredicate ctx measure
          `(Plan.loopVariant $(cond.guard) $loopInv $variant $(body.plan))
      let plan ← match done with
        | some done =>
          let post ← statePredicate ctx done
          `(Plan.ensure $post $loopPlan)
        | none => pure loopPlan
      let plan ← `(Plan.atEntry (fun ($entry : Mutable.State) => $plan))
      let loop : Fragment := ⟨← `(Program.loop $(cond.guard) $(body.program)), plan,
        body.writes, body.arrayWrites⟩
      return (← sequence cond.before loop, ctx)
    | `(doElem| assert $assertion:term) =>
      let predicate ← statePredicate ctx assertion
      return (⟨← `(Program.skip), ← `(Plan.assert $predicate), #[], false⟩, ctx)
    | `(doElem| return) | `(doElem| return ()) =>
      if ctx.nested then
        throwErrorAt stx "RAM return is supported only at method exit"
      return (← skipFragment, ctx)
    | `(doElem| pure ()) =>
      return (← skipFragment, ctx)
    | _ => throwErrorAt stx "Unsupported RAM statement: {stx}"
  assignExpression (ctx : Context) (name : String) (e : Term) : TermElabM Fragment := do
    let e ← expression ctx e
    let set ← actionFragment (← `(Mutable.assign $(quote name) $(e.value)))
    sequences (e.before.push set)
  declare (ctx : Context) (x : Ident) (e : Term) (isMutable : Bool) :
      TermElabM (Fragment × Context) := do
    if x.getId == ctx.array.getId || x.getId == ctx.old.getId || x.getId == `remaining then
      throwErrorAt x
        "This name belongs to the array interface or proof context; choose a fresh local"
    if ctx.bindings.any (fun b => b.user.getId == x.getId) then
      throwErrorAt x "Shadowing a RAM local is not allowed; choose a fresh variable name"
    let name ← fresh x.getId.toString
    let part ← assignExpression ctx name e
    return (part, { ctx with bindings := ctx.bindings.push ⟨x, name, isMutable⟩ })

def termBeforeCost := withForbidden "credits" (withForbidden "time" termBeforeReqEnsDo)
attribute [run_builtin_parser_attribute_hooks] termBeforeCost
builtin_initialize register_parser_alias termBeforeCost

declare_syntax_cat ramRequire
declare_syntax_cat ramEnsures
declare_syntax_cat ramCredits
declare_syntax_cat ramTime
syntax "require" termBeforeCost : ramRequire
syntax "ensures" termBeforeCost : ramEnsures
syntax "credits" termBeforeCost : ramCredits
syntax "time" Term.termBeforeDo : ramTime
syntax "ram" "method" ident leafny_binder* "return" "(" ident ":" term ")"
  ramRequire* ramEnsures* ramCredits (ramTime)? "do" Term.doSeq : command

elab_rules : command
  | `(command| ram method $name:ident $binders:leafny_binder* return ($ret:ident : $retTy:term)
      $pres:ramRequire* $posts:ramEnsures* $creditClause:ramCredits $[$timeClause:ramTime]?
      do $body:doSeq) => do
    let `(ramCredits| credits $creditBudget:term) := creditClause | throwUnsupportedSyntax
    let timeBudget ← match timeClause with
      | some timeClause =>
        let `(ramTime| time $bound:term) := timeClause | throwUnsupportedSyntax
        pure bound
      | none => `(Mutable.model.overhead * $creditBudget)
    let pre : Array Term := pres.map (fun x => ⟨x.raw[1]⟩)
    let post : Array Term := posts.map (fun x => ⟨x.raw[1]⟩)
    unless binders.size == 1 do
      throwError "This RAM entry point requires one mutable Array Nat input"
    let `(leafny_binder| (mut $array:ident : Array Nat)) := binders[0]!
      | throwErrorAt binders[0]! "This RAM entry point requires '(mut arr : Array Nat)'"
    unless retTy.raw.isIdent && retTy.raw.getId == `Unit do
      throwErrorAt retTy "A RAM array method returns Unit and the updated mutable array"
    let old := mkIdent (array.getId.appendAfter "Old")
    if array.getId == `remaining || ret.getId == `remaining ||
        ret.getId == array.getId || ret.getId == old.getId then
      throwError "Use distinct input/output names and reserve 'remaining' for proof credits"
    let (fragment, pre, post) ← Command.runTermElabM fun _ => do
      let fragment ← statements { array, old } body
      let mut precondition ← `(True)
      for p in pre.reverse do precondition ← `($p ∧ $precondition)
      let mut postcondition ← `(True)
      for p in post.reverse do postcondition ← `($p ∧ $postcondition)
      return (fragment, precondition, postcondition)
    let planName := mkIdent (name.getId.appendAfter "Annotations")
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      def $name : Method Mutable.interface where
        body := $(fragment.program)
        «requires» := fun $old => let $array := $old; $pre
        «ensures» := fun $old $array => let $ret := (); $post
        «credits» := fun $old => let $array := $old; $creditBudget
        «time» := fun $old => let $array := $old; $timeBudget))
    elabCommand (← `(command|
      def $planName ($old : Array Nat) : Plan ($name).body := $(fragment.plan)))

/-- Open the obligations after `prove_ram` has unfolded the method and annotations. -/
macro "ram_vc" : tactic =>
  `(tactic| simp [Obligations, Plan.vc, Mutable.interface, Mutable.initial,
    Mutable.assign, Mutable.read, Mutable.write, Mutable.compare, Mutable.Value.eval,
    Mutable.State.set, Function.update_apply, Mutable.Value.compile, Mutable.address,
    Checked.Language.Expr.cost, Checked.Language.Comparison.eval, Mutable.model] at *)

/-- Collect scalar/array views that should appear as ordinary variables in proof goals. -/
private partial def views (e : Expr) : Array (Expr × Name) := Id.run do
  if e.isAppOfArity ``Mutable.State.locals 2 then
    let args := e.getAppArgs
    if args[0]!.isFVar then
      if let .lit (.strVal key) := args[1]! then
        return #[(e, Name.mkSimple ((key.splitOn ".").head!))]
  if e.isAppOfArity ``Mutable.State.array 1 && e.getAppArgs[0]!.isFVar then
    return #[(e, `arr)]
  match e with
  | .app f a => return views f ++ views a
  | .forallE _ a b _ | .lam _ a b _ => return views a ++ views b
  | .letE _ t v b _ => return views t ++ views v ++ views b
  | .mdata _ b | .proj _ _ b => return views b
  | _ => return #[]

/-- Present generated goals using ordinary arrays and local variable names. -/
elab "ram_names" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let mut candidates := views (← goal.getType)
  let mut hyps := #[]
  let mut states := #[]
  for decl in ← getLCtx do
    candidates := candidates ++ views decl.type
    if ← isProp decl.type then hyps := hyps.push decl.fvarId
    if decl.type.isConstOf ``Mutable.State then states := states.push decl.fvarId
  let mut args : Array GeneralizeArg := #[]
  for (e, name) in candidates do
    unless args.any (fun a => a.expr == e) do
      args := args.push { expr := e, xName? := some name }
  let (_, _, goal) ← goal.generalizeHyp args hyps
  let mut goal := goal
  for state in states do goal ← goal.tryClear state
  Lean.Elab.Tactic.replaceMainGoal [goal]

/-- Solve the plumbing automatically; supplied rules are ordinary mathematical lemmas. -/
macro "ram_solve" "[" rules:Lean.Parser.Tactic.grindParam,* "]" : tactic =>
  `(tactic| (
    ram_vc
    repeat' (first | (with_reducible intro) | (apply And.intro) | (split))
    all_goals ram_names
    all_goals grind only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
      $rules,*]))

syntax "prove_ram" ident "by" tacticSeq : command
elab_rules : command
  | `(command| prove_ram $name:ident by $proof:tacticSeq) => do
    let plan := mkIdent (name.getId.appendAfter "Annotations")
    let checked := mkIdent (name.getId.appendAfter "Verification")
    let verified := mkIdent (name.getId.appendAfter "Verified")
    let combined ← `(tacticSeq|
      unfold $name $plan
      ($proof))
    elabCommand (← `(command|
      theorem $checked : Obligations $name $plan := by $combined:tacticSeq))
    elabCommand (← `(command|
      def $verified : VerifiedMethod Mutable.interface := certify $name $checked))

end AlgoLib.Experimental.RAM.Prototype.Frontend
