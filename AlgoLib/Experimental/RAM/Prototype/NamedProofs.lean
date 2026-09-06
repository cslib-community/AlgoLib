/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.ProofGoals

/-!
# Stable, independently checked mathematical proof blocks

The root metavariable is an indexed reconstruction tree: splitting uses ordinary
forall introduction, conjunction introduction, and case analysis. Leaves retain
their justified local contexts. Named blocks can only fill selected leaves;
no unchecked global assumptions are introduced. The kernel checks the reconstructed
root at the original
Algorithm.Obligations type, then the existing certification/compiler chain applies.
Names select mathematical responsibilities, never goal positions or source lines.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Meta Tactic Parser

/-- A leaf retains its own binder context and diagnostic location. -/
structure NamedGoal where
  goal : MVarId
  key : String
  site : String
  deriving Inhabited

/-- The root records the checked constructors connecting every leaf to the original VC. -/
structure NamedTree where
  root : MVarId
  leaves : Array NamedGoal

/-- Recover the source statement for diagnostics without using its position as identity. -/
private def sourceRef (site : String) (fallback : Syntax) : CoreM Syntax := do
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

private partial def productSize (ty : Expr) : MetaM Nat := do
  let ty ← whnf ty
  if ty.isAppOfArity ``Prod 2 then
    return (← productSize ty.getAppArgs[0]!) + (← productSize ty.getAppArgs[1]!)
  return 1

private partial def exposeState (goal : MVarId) (value : FVarId) (names : List String) :
    MetaM MVarId := goal.withContext do
  let ty ← whnf (← value.getType)
  if ty.isAppOfArity ``Prod 2 then
    let n ← productSize ty.getAppArgs[0]!
    let children ← goal.cases value
    let some child := children[0]? | throwError "Cannot expose source state"
    let goal ← exposeState child.mvarId child.fields[0]!.fvarId! (names.take n)
    return ← exposeState goal child.fields[1]!.fvarId! (names.drop n)
  let stem := names.head!
  let ctx ← getLCtx
  goal.rename value (ctx.getUnusedName (Name.mkSimple stem))

private partial def readNames (value : Expr) : MetaM (List String) := do
  let value ← whnf value
  if value.isAppOfArity ``List.cons 3 then
    return (← stringValue value.getAppArgs[1]!) :: (← readNames value.getAppArgs[2]!)
  return []

private def methodViews (name : Ident) (suffix := "ProofViews") : TermElabM (List String) := do
  let views := mkIdent (name.getId.appendAfter suffix)
  readNames (← elabTerm (← `($views)) none)

private partial def splitNamed (goal : MVarId) (views inputViews : List String)
    (key := "result") (site := "") : TacticM (Array NamedGoal) := goal.withContext do
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOfArity ``Composition.ObligationAt 3 then
    let args := ty.getAppArgs
    let label ← stringValue args[0]!
    let location ← stringValue args[1]!
    let parts := location.splitOn "\n"
    let scope := if parts.length > 1 then parts.head! else "method"
    let location := parts.getLast!
    return ← splitNamed (← goal.change args[2]!) views inputViews
      (scope ++ "." ++ phase label) location
  if ty.isAppOfArity ``Composition.InvariantFact 2 then
    let args := ty.getAppArgs
    return ← splitNamed (← goal.change args[1]!) views inputViews
      (key ++ "." ++ (← stringValue args[0]!)) site
  if ty.isAppOfArity ``Composition.Obligation 2 then
    return ← splitNamed (← goal.change ty.getAppArgs[1]!) views inputViews key site
  if ty.isConstOf ``True then
    goal.assign (mkConst ``True.intro)
    return #[]
  if ty.isForall then
    let binder := ty.bindingName!
    let (value, child) ← goal.intro1P
    let child ← child.withContext do
      let ty ← value.getType
      let size ← productSize ty
      if size > 1 then
        exposeState child value (if size == views.length then views
          else if size == inputViews.length then inputViews else List.replicate size "result")
      else if binder == `a && inputViews.length == 1 then
        exposeState child value inputViews
      else pure child
    return ← splitNamed child views inputViews key site
  if ty.isAppOfArity ``And 2 then
    let children ← goal.apply (mkConst ``And.intro)
    return (← children.toArray.mapM
      (fun child => splitNamed child views inputViews key site)).flatten
  if ty.isAppOf ``ite || ty.isAppOf ``dite then
    setGoals [goal]
    evalTactic (← `(tactic| split))
    return (← (← getGoals).toArray.mapM
      (fun child => splitNamed child views inputViews key site)).flatten
  let reduced ← withTransparency .reducible (whnf ty)
  if reduced != ty then return ← splitNamed (← goal.change reduced) views inputViews key site
  goal.setTag (Name.mkSimple key)
  return #[⟨goal, key, site⟩]

/-- Eliminate frontend guard copies in favor of the expressions in the paper program. -/
private def hideGuards (goal : MVarId) : MetaM MVarId := goal.withContext do
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

/-- Symbolic execution and proof-tree construction do not use algorithm-specific lemmas. -/
def namedTree (root : MVarId) (views : List String := [])
    (inputViews : List String := []) : TacticM NamedTree := do
  setGoals [root]
  evalTactic (← `(tactic| named_normalize))
  let mut leaves := #[]
  for goal in ← getGoals do leaves := leaves ++ (← splitNamed goal views inputViews)
  let mut normalized := #[]
  for leaf in leaves do
    setGoals [leaf.goal]
    evalTactic (← `(tactic| (
      try dsimp only [Prod.fst, Prod.snd] at *
      try simp_all only [Composition.InvariantFact, Composition.Obligation,
        Composition.ObligationAt])))
    let children ← getGoals
    for child in children do
      let child ← hideGuards child
      child.setTag (Name.mkSimple leaf.key)
      normalized := normalized.push { leaf with goal := child }
  return ⟨root, normalized⟩

private def routine (leaf : NamedGoal) : TacticM Bool := do
  if ← leaf.goal.isAssigned then return true
  setGoals [leaf.goal]
  evalTactic (← `(tactic| first | omega | assumption | rfl | simp))
  return (← getGoals).isEmpty

private def tryRoutine (leaf : NamedGoal) : TacticM Bool := do
  let saved ← saveState
  try
    if ← routine leaf then return true
  catch _ => pure ()
  saved.restore
  return false

private def selects (stem key : String) := key == stem || key.startsWith (stem ++ ".")

/-- Symbolic execution has its own budget; respect larger or unlimited caller settings. -/
private def proofOptions (opts : Options) : Options :=
  let limit := opts.getNat `maxHeartbeats 200000
  if limit == 0 then opts else opts.set `maxHeartbeats (max 2000000 limit)

declare_syntax_cat namedProofBlock
syntax "case " ident " => " "by " tacticSeq : namedProofBlock
syntax "named_proof_blocks " ident namedProofBlock* : tactic

elab_rules : tactic
  | `(tactic| named_proof_blocks $alg:ident $blocks:namedProofBlock*) => withOptions proofOptions do
    let root ← getMainGoal
    let tree ← namedTree root (← methodViews alg) (← methodViews alg "ProofInputViews")
    let mut claimed : Array String := #[]
    for block in blocks do
      let `(namedProofBlock| case $name:ident => by $proof:tacticSeq) := block
        | throwUnsupportedSyntax
      let key := name.getId.toString
      unless tree.leaves.any (fun leaf => selects key leaf.key) do
        throwErrorAt name "Unknown proof obligation '{key}'. \
          Use #named_goals to inspect stable names."
      if claimed.any (fun old => selects old key || selects key old) then
        throwErrorAt name "Duplicate or overlapping proof block '{key}'"
      claimed := claimed.push key
      for leaf in tree.leaves do
        if selects key leaf.key then
          let checked := leaf.goal
          setGoals [checked]
          withRef proof do evalTactic proof
          unless (← getGoals).isEmpty do
            throwErrorAt proof "Proof block '{key}' is incomplete.\n\
              {MessageData.ofGoal (← getMainGoal)}"
          let evidence ← instantiateMVars (mkMVar checked)
          if evidence.hasSorry || evidence.hasMVar then
            throwErrorAt proof "Named proof blocks must contain complete, admission-free proofs"
    let mut openGoals := #[]
    for leaf in tree.leaves do
      unless ← tryRoutine leaf do openGoals := openGoals.push leaf
    unless openGoals.isEmpty do
      let names := openGoals.toList.map (·.key) |>.eraseDups
      let ref ← sourceRef openGoals[0]!.site alg.raw
      throwErrorAt ref "Unproved named obligations: {String.intercalate ", " names}\n\
        Add case blocks, or use #named_goals for their mathematical contexts.\n\
        {MessageData.ofGoal openGoals[0]!.goal}"
    let proof ← instantiateMVars (mkMVar tree.root)
    if proof.hasMVar then throwError "Internal error: the reconstruction tree has an open leaf"
    if proof.hasSorry then
      throwError "Named verification requires complete proofs; sorry is not accepted"
    setGoals []

/-- Preview every stable key, automatic status, and open mathematical context. -/
syntax "#named_goals " ident (" only " ident)? : command
elab_rules : command
  | `(command| #named_goals $name:ident $[only $focus:ident]?) => Command.runTermElabM fun _ =>
      withOptions proofOptions do
    let obligations := mkIdent (name.getId.appendAfter "Obligations")
    let type ← Term.elabType (← `($obligations))
    let root ← mkFreshExprSyntheticOpaqueMVar type
    discard <| Tactic.run root.mvarId! do
      evalTactic (← `(tactic| unfold $obligations $name))
      let tree ← namedTree (← getMainGoal) (← methodViews name)
        (← methodViews name "ProofInputViews")
      let leaves := tree.leaves.filter fun leaf =>
        focus.all (fun selected => selects selected.getId.toString leaf.key)
      if leaves.isEmpty then
        throwErrorAt name "No matching mathematical obligations"
      let keys := leaves.toList.map (·.key) |>.eraseDups
      for key in keys do
        let group := leaves.filter (·.key == key)
        let mut remaining := #[]
        for leaf in group do
          unless ← tryRoutine leaf do remaining := remaining.push leaf
        let ref ← sourceRef group[0]!.site name.raw
        if remaining.isEmpty then
          logInfoAt ref m!"[automatic] {key} ({group.size} paths)"
        else
          let contexts := remaining.toList.map (fun leaf => MessageData.ofGoal leaf.goal)
          logInfoAt ref m!"[open] {key} ({remaining.size} paths)\n\
            {MessageData.joinSep contexts m!"\n\n"}"

end AlgoLib.Experimental.RAM.Prototype.Frontend
