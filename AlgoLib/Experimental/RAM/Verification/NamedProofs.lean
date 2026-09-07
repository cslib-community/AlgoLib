/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Verification.ProofGoals

/-!
# Structural obligation decomposition (internal)

The generated API uses this module to split source quantifiers, labelled facts,
and branches with ordinary checked introduction/case rules. Typed source shapes
are required; no tuple-arity guessing or normalization-first proof engine remains.
All leaves, including True, are retained for persistent obligation identities.
Proof installation and completion live in GeneratedObligations.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Meta Tactic Parser

/-- Explicit source binding provenance captured while opening a tagged source quantifier.
`role` describes a quantified snapshot, not an inferred pre/post state of a statement. -/
structure SourceBinding where
  name : Name
  source : String
  role : String
  deriving Inhabited, Repr

/-- A leaf retains its own binder context and diagnostic location. -/
structure NamedGoal where
  goal : MVarId
  key : String
  site : String
  bindings : Array SourceBinding := #[]
  responsibility : String := "result"
  deriving Inhabited

/-- Recover the source statement for diagnostics without using its position as identity. -/
def sourceRef (site : String) (fallback : Syntax) : CoreM Syntax := do
  let parts := site.splitOn ":"
  if site.contains (← getFileName) && parts.length ≥ 3 then
    if let some line := parts[parts.length - 2]!.toNat? then
      if let some column := parts.getLast!.toNat? then
        let pos := (← getFileMap).ofPosition ⟨line, column - 1⟩
        return .atom (.synthetic pos pos true) ""
  return fallback

private def phase : String → String
  | "loop invariant initialized" => "initialize"
  | "loop invariant preserved" => "preserve"
  | "iteration bound positive" => "terminate.positive"
  | "iteration bound decreases" | "remaining work decreases" => "terminate.decrease"
  | "loop allowance sufficient" => "account.initial"
  | "iteration allowance sufficient" => "account.iteration"
  | "statement allowance sufficient" => "account.statement"
  | "procedure allowance sufficient" => "account.call"
  | "array index within bounds / operation precondition" => "safety"
  | "procedure precondition" => "requires"
  | "loop exit" => "exit"
  | _ => "result"

private def stringValue (e : Expr) : MetaM String := do
  match ← whnf e with
  | .lit (.strVal s) => return s
  | _ => return ""

/-- Interpret only the explicit frontend shape; a mismatch is an elaboration error. -/
private partial def exposeShape (goal : MVarId) (value : FVarId) (shape : Expr)
    (suffix role : String) : MetaM (MVarId × Array SourceBinding) := goal.withContext do
  let shape ← whnf shape
  let args := shape.getAppArgs
  if shape.isAppOfArity ``Composition.SourceShape.pair 2 then
    unless (← whnf (← value.getType)).isAppOfArity ``Prod 2 do
      throwError "Source metadata does not match the typed program state"
    let children ← goal.cases value
    let some child := children[0]? | throwError "Cannot expose typed source state"
    let (goal, left) ← exposeShape child.mvarId child.fields[0]!.fvarId! args[0]! suffix role
    let (goal, right) ← exposeShape goal child.fields[1]!.fvarId! args[1]! suffix role
    return (goal, left ++ right)
  if shape.isAppOfArity ``Composition.SourceShape.leaf 3 then
    let hidden := (← whnf args[2]!).isConstOf ``Bool.true
    let sourceName ← stringValue args[1]!
    let stem := if hidden then "__proof_guard" else sourceName ++ suffix
    let name := (← getLCtx).getUnusedName (Name.mkSimple stem)
    let goal ← goal.rename value name
    return (goal, if hidden then #[] else #[{ name, source := sourceName, role }])
  throwError "Invalid source binding metadata"

partial def splitNamed (goal : MVarId) (shapes : Expr × Expr)
    (key := "result") (site := "")
    (bindings : Array SourceBinding := #[]) (snapshot : Nat := 0)
    (responsibility : String := "result") :
    TacticM (Array NamedGoal) := goal.withContext do
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOfArity ``Composition.SourceForall 3 then
    let role ← stringValue ty.getAppArgs[1]!
    let quantified ← withTransparency .all (whnf ty)
    let (value, child) ← (← goal.change quantified).intro1P
    let next := if role == "current" then snapshot + 1 else snapshot
    let (child, added) ← child.withContext do
      let (fullShape, inputShape) := shapes
      if role == "input" then return ← exposeShape child value inputShape "Input" "original input"
      if role == "current" then
        return ← exposeShape child value fullShape ("State" ++ toString next)
          ("quantified loop state " ++ toString next)
      if role == "result" then
        let name := (← getLCtx).getUnusedName `result
        return (← child.rename value name,
          #[{ name, source := "result", role := "procedure result" }])
      return (child, #[])
    return ← splitNamed child shapes key site
      (bindings ++ added) next responsibility
  if ty.isAppOfArity ``Composition.ObligationAt 3 then
    let args := ty.getAppArgs
    let label ← stringValue args[0]!
    let location ← stringValue args[1]!
    let parts := location.splitOn "\n"
    let scope := if parts.length > 1 then parts.head! else "method"
    let location := parts.getLast!
    return ← splitNamed (← goal.change args[2]!) shapes
      (scope ++ "." ++ phase label) location bindings snapshot (phase label)
  if ty.isAppOfArity ``Composition.InvariantFact 2 then
    let args := ty.getAppArgs
    return ← splitNamed (← goal.change args[1]!) shapes
      (key ++ "." ++ (← stringValue args[0]!)) site
      bindings snapshot responsibility
  if ty.isAppOfArity ``Composition.Obligation 2 then
    return ← splitNamed (← goal.change ty.getAppArgs[1]!)
      shapes key site
        bindings snapshot responsibility
  if ty.isForall then
    let (_, child) ← goal.intro1P
    return ← splitNamed child shapes key site
        bindings snapshot responsibility
  if ty.isAppOfArity ``And 2 then
    let children ← goal.apply (mkConst ``And.intro)
    return (← children.toArray.mapM
      (fun child => splitNamed child shapes key site
        bindings snapshot responsibility)).flatten
  if ty.isAppOf ``ite || ty.isAppOf ``dite then
    setGoals [goal]
    evalTactic (← `(tactic| split))
    return (← (← getGoals).toArray.mapM
      (fun child => splitNamed child shapes key site
        bindings snapshot responsibility)).flatten
  let reduced ← withTransparency .reducible (whnf ty)
  if reduced != ty then
    return ← splitNamed (← goal.change reduced) shapes key site
        bindings snapshot responsibility
  goal.setTag (Name.mkSimple key)
  return #[{ goal, key, site, bindings, responsibility }]

/-- Eliminate frontend guard copies in favor of the expressions in the paper program. -/
def hideGuards (goal : MVarId) : MetaM MVarId := goal.withContext do
  let names := (← getLCtx).foldl (init := []) fun names decl =>
    if decl.userName.toString.startsWith "__proof_guard" then decl.userName :: names else names
  let mut goal := goal
  for name in names do
    goal ← goal.withContext do
      let some decl := (← getLCtx).findFromUserName? name | return goal
      let goal := (← substVar? goal decl.fvarId).getD goal
      goal.withContext do
        if (← getLCtx).contains decl.fvarId then goal.tryClear decl.fvarId else pure goal
  return goal

/-- Symbolic execution has its own budget; respect larger or unlimited caller settings. -/
def proofOptions (opts : Options) : Options :=
  let limit := opts.getNat `maxHeartbeats 200000
  if limit == 0 then opts else opts.set `maxHeartbeats (max 2000000 limit)

declare_syntax_cat namedProofBlock
syntax "case " ident " => " "by " tacticSeq : namedProofBlock

end AlgoLib.Experimental.RAM.Prototype.Frontend
