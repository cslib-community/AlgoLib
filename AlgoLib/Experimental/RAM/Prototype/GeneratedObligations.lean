/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.NamedProofs

/-!
# Generated, persistent obligation declarations

Generation freezes closed propositions before simplification or algorithm automation.
Each named responsibility is a proposition declaration, including all its execution
paths. A kernel-checked assembly theorem consumes precisely these propositions and
reconstructs the existing `Algorithm.Obligations`. Neither Loom nor RAM is changed.

The registry is navigation metadata only. Proofs are ordinary Lean declarations;
importing a specification module reuses the generated propositions and assembly proof.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Meta Tactic Parser

/-- Persistent navigation information; the declaration named by `typeName` is authoritative. -/
structure ObligationEntry where
  alg : Name
  key : String
  typeName : Name
  proofName : Name
  site : String
  deriving Inhabited

initialize obligationRegistry :
    SimplePersistentEnvExtension ObligationEntry (Array ObligationEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

private def apiName (alg : Name) : Name := alg ++ `ObligationAPI
private def keyName (key : String) : Name :=
  key.splitOn "." |>.foldl Name.str .anonymous

private def entriesFor (alg : Name) : CoreM (Array ObligationEntry) :=
  return obligationRegistry.getState (← getEnv) |>.filter (·.alg == alg)

private def resolveMethod (alg : Ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo alg

private def checkedDecl (name : Name) (type value : Expr) (isTheorem : Bool) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar || value.hasSorry || type.hasFVar || value.hasFVar then
    throwError "Generated declaration {name} contains unfinished evidence or an open context"
  let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
  if isTheorem then
    addDecl (.thmDecl { name, levelParams := levels, type, value })
  else
    addDecl (.defnDecl {
      name := name
      levelParams := levels
      type := type
      value := value
      hints := .abbrev
      safety := .safe })

private def contextVariables : MetaM (Array Expr) := do
  return (← getLCtx).foldl (init := #[]) fun xs d => xs.push d.toExpr

/-- A conjunction retains every path, including paths automation can already solve. -/
private def conjunction (types : Array Expr) : Expr :=
  match types.toList.reverse with
  | [] => mkConst ``True
  | last :: rest => rest.foldl (fun q p => mkApp2 (mkConst ``And) p q) last

private def projectProof (types : Array Expr) (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  if index + 1 == types.size then return proof
  mkAppM ``And.left #[proof]

/-- Expose conjunction hypotheses without unfolding mathematical predicates. -/
private partial def splitHypotheses (goal : MVarId) : MetaM MVarId := goal.withContext do
  for decl in ← getLCtx do
    if decl.type.isAppOfArity ``And 2 then
      let children ← goal.cases decl.fvarId
      let some child := children[0]? | throwError "Expected conjunction fields"
      return ← splitHypotheses child.mvarId
  return goal

syntax "generate_obligation_spec " ident : command
elab_rules : command
  | `(command| generate_obligation_spec $alg:ident) =>
      withScope (fun s => { s with opts := proofOptions s.opts }) do
    let methodName ← resolveMethod alg
    unless (← liftCoreM <| entriesFor methodName).isEmpty do
      throwErrorAt alg "Obligations for {methodName} have already been generated"
    runTermElabM fun _ => do
      let obligations := mkIdent (methodName.appendAfter "Obligations")
      let type ← elabType (← `($obligations))
      let root ← mkFreshExprSyntheticOpaqueMVar type
      discard <| Tactic.run root.mvarId! do
        evalTactic (← `(tactic| unfold $obligations $alg; paper_unfold))
        let fullShape ← Term.elabTerm (← `($(mkIdent (methodName.appendAfter "ProofShape")))) none
        let inputShapeName := mkIdent (methodName.appendAfter "ProofInputShape")
        let inputShape ← Term.elabTerm (← `($inputShapeName)) none
        let mut leaves := #[]
        for goal in ← getGoals do
          leaves := leaves ++ (← splitNamed goal (← methodViews alg)
            (← methodViews alg "ProofInputViews") "result" "" true (some (fullShape, inputShape)))
        leaves ← leaves.mapM fun leaf => do
          let goal ← splitHypotheses leaf.goal
          let goal ← hideGuards goal
          return { leaf with goal }
        let keys := leaves.toList.map (·.key) |>.eraseDups
        let groups ← keys.toArray.mapM fun key => do
          let group := leaves.filter (·.key == key)
          let types ← group.mapM fun leaf => leaf.goal.withContext do
            mkForallFVars (← contextVariables) (← leaf.goal.getType)
          let typeName := apiName methodName ++ keyName key
          checkedDecl typeName (mkSort .zero) (conjunction types) false
          let entry : ObligationEntry := {
            alg := methodName
            key := key
            typeName := typeName
            proofName := typeName.appendAfter "_proof"
            site := group[0]!.site }
          modifyEnv (obligationRegistry.addEntry · entry)
          return (group, types, typeName)
        let rec assemble (i : Nat) (args : Array Expr) : MetaM Expr := do
          if h : i < groups.size then
            let (group, types, typeName) := groups[i]
            withLocalDeclD (Name.mkSimple ("evidence" ++ toString i)) (mkConst typeName)
                fun evidence => do
              for j in [:group.size] do
                let leaf := group[j]!
                let proof ← projectProof types evidence j
                leaf.goal.withContext do
                  leaf.goal.assign (mkAppN proof (← contextVariables))
              assemble (i + 1) (args.push evidence)
          else
            mkLambdaFVars args (← instantiateMVars root)
        let proof ← assemble 0 #[]
        checkedDecl (apiName methodName ++ `assemble) (← inferType proof) proof true
        setGoals []

-- Only unfold the frozen proposition at the head, never the source algorithm.
elab "open_frozen_obligation" : tactic => do
  let goal ← getMainGoal
  let type ← goal.getType
  let some value := (← getEnv).find? type.getAppFn.constName!
    | throwError "Expected generated obligation"
  let some value := value.value? | throwError "Expected proposition definition"
  replaceMainGoal [← goal.change value]


/-- Split only API conjunctions and telescopes, never a user's mathematical definition. -/
private partial def openResponsibility (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  if type.isForall then
    let (_, child) ← goal.intro1P
    return ← openResponsibility child
  if type.isAppOfArity ``And 2 then
    let children ← goal.apply (mkConst ``And.intro)
    return (← children.mapM openResponsibility).flatten
  return [goal]

/-- Keep the explicitly checked normalized proof as an argument of the certificate. -/
theorem checkedBlock {P : Prop} (evidence : P) (_checked : True) : P := evidence

private def runObligation (proof : TSyntax ``Parser.Tactic.tacticSeq)
    (checkExplicit : Bool) : TacticM Unit := withoutRecover do
  let root ← getMainGoal
  let type ← root.getType
  let entry := (obligationRegistry.getState (← getEnv)).find?
    (·.typeName == type.getAppFn.constName!)
  let key := entry.map (·.key) |>.getD "obligation"
  let work ← mkFreshExprSyntheticOpaqueMVar type
  setGoals [work.mvarId!]
  evalTactic (← `(tactic| open_frozen_obligation))
  setGoals (← openResponsibility (← getMainGoal))
  let goals ← getGoals
  let original ← saveState
  let mut usedBlock := false
  for goal in goals do
    setGoals [← splitHypotheses goal]
    evalTactic (← `(tactic| try simp_all [Composition.InvariantFact,
      Composition.Obligation, Composition.ObligationAt, Composition.SourceForall]))
    for child in ← getGoals do
      let child ← hideGuards child
      child.setTag (Name.mkSimple key)
      setGoals [child]
      usedBlock := true
      try evalTactic proof
      catch ex => throwError "{ex.toMessageData}\n{MessageData.ofGoal child}"
      unless (← getGoals).isEmpty do throwError "Incomplete obligation proof"
  let mut evidence ← instantiateMVars work
  if checkExplicit && !usedBlock then
    let solved ← saveState
    original.restore
    let rawSuccess ← try
      for goal in goals do
        setGoals [← splitHypotheses goal]
        evalTactic proof
        unless (← getGoals).isEmpty do throwError "Incomplete obligation proof"
      pure true
    catch _ => pure false
    if rawSuccess then
      evidence ← instantiateMVars work
    else
      solved.restore
      -- The simplifier proved the responsibility. Still elaborate and check the
      -- supplied block against the normalized proposition, retaining its evidence.
      let checked ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
      checked.mvarId!.setTag (Name.mkSimple key)
      setGoals [checked.mvarId!]
      evalTactic proof
      unless (← getGoals).isEmpty do throwError "Incomplete obligation proof"
      evidence ← mkAppM ``checkedBlock #[evidence, ← instantiateMVars checked]
  if evidence.hasSorry || evidence.hasMVar then
    throwError "Obligation proofs must be complete and admission-free"
  root.assign evidence
  setGoals []

/-- Open one frozen responsibility and check an explicit proof, even if automation solves it. -/
syntax "obligation_proof " "by " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| obligation_proof by $proof:tacticSeq) => runObligation proof true

syntax "automatic_obligation_proof " "by " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| automatic_obligation_proof by $proof:tacticSeq) => runObligation proof false

private def proveEntry (entry : ObligationEntry) (proof : TSyntax ``Parser.Tactic.tacticSeq)
    (automatic := false) :
    CommandElabM Unit := do
  if (← getEnv).contains entry.proofName then
    throwError "Obligation {entry.key} already has a proof"
  let name := mkIdent (`_root_ ++ entry.proofName)
  let type := mkIdent entry.typeName
  if automatic then
    elabCommand (← `(command| theorem $name : $type := by automatic_obligation_proof by $proof))
  else
    elabCommand (← `(command| theorem $name : $type := by obligation_proof by $proof))
  let info ← liftCoreM <| getConstInfo entry.proofName
  if info.value?.any Expr.hasSorry then throwError "Obligation proofs must be admission-free"

/-- Cache routine evidence without dropping its proposition from the API. -/
private def cacheAutomatic (entry : ObligationEntry) : CommandElabM Unit :=
  runTermElabM fun _ => do
    let root ← mkFreshExprSyntheticOpaqueMVar (mkConst entry.typeName)
    discard <| Tactic.run root.mvarId! do
      let saved ← saveState
      try
        runObligation (← `(tacticSeq| first | omega | assumption | rfl | simp)) false
        checkedDecl (entry.typeName.appendAfter "_automatic") (mkConst entry.typeName)
          (← instantiateMVars root) true
      catch _ => saved.restore
      setGoals []

/-- Freeze the API first, then cache any routine proofs in the specification module. -/
syntax "generate_obligations " ident : command
elab_rules : command
  | `(command| generate_obligations $alg:ident) =>
      withScope (fun s => { s with opts := proofOptions s.opts }) do
    elabCommand (← `(command| generate_obligation_spec $alg))
    let name ← resolveMethod alg
    for entry in ← liftCoreM <| entriesFor name do cacheAutomatic entry

syntax "prove_obligation " ident " by " tacticSeq : command
elab_rules : command
  | `(command| prove_obligation $name:ident by $proof:tacticSeq) =>
      withScope (fun s => { s with opts := proofOptions s.opts }) do
    let resolved ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
    let some entry := (obligationRegistry.getState (← getEnv)).find? (·.typeName == resolved)
      | throwErrorAt name "Expected a generated obligation declaration"
    proveEntry entry proof

syntax "complete_algorithm " ident : command
elab_rules : command
  | `(command| complete_algorithm $alg:ident) =>
      withScope (fun s => { s with opts := proofOptions s.opts }) do
    let name ← resolveMethod alg
    let entries ← liftCoreM <| entriesFor name
    if entries.isEmpty then throwErrorAt alg "Run generate_obligations first"
    for entry in entries do
      unless (← getEnv).contains entry.proofName ||
          (← getEnv).contains (entry.typeName.appendAfter "_automatic") do
        proveEntry entry (← `(tacticSeq| first | omega | assumption | rfl | simp)) true
    let verification := mkIdent (`_root_ ++ name.appendAfter "Verification")
    let obligations := mkIdent (name.appendAfter "Obligations")
    let assembly := mkIdent (apiName name ++ `assemble)
    let env ← getEnv
    let proofs := entries.map fun entry =>
      let chosen := if env.contains entry.proofName then entry.proofName
        else entry.typeName.appendAfter "_automatic"
      (⟨mkIdent chosen⟩ : Term)
    elabCommand (← `(command| theorem $verification : $obligations := $assembly $proofs*))
    let procedure := mkIdent (`_root_ ++ name.appendAfter "Procedure")
    let certificate := mkIdent (name.appendAfter "Certificate")
    elabCommand (← `(command| @[reducible] def $procedure := $certificate $verification))

/-- Block syntax is sugar over persistent proposition and proof declarations. -/
def proveGenerated (alg : Ident) (blocks : Array (TSyntax `namedProofBlock)) :
    CommandElabM Unit :=
    withScope (fun s => { s with opts := proofOptions s.opts }) do
  let name ← resolveMethod alg
  if (← liftCoreM <| entriesFor name).isEmpty then
    elabCommand (← `(command| generate_obligations $alg))
  let entries ← liftCoreM <| entriesFor name
  let mut claimed : Array String := #[]
  for block in blocks do
    let `(namedProofBlock| case $key:ident => by $proof:tacticSeq) := block
      | throwUnsupportedSyntax
    let stem := key.getId.toString
    let selects := fun k : String => k == stem || k.startsWith (stem ++ ".")
    let selected := entries.filter (fun entry => selects entry.key)
    if selected.isEmpty then throwErrorAt key "Unknown generated obligation {stem}"
    for entry in selected do
      if claimed.contains entry.key then throwErrorAt key "Overlapping obligation block {stem}"
      claimed := claimed.push entry.key
      proveEntry entry proof
  elabCommand (← `(command| complete_algorithm $alg))

/-- Inspect imported declarations; preview never regenerates an existing specification. -/
syntax "#named_goals " ident (" only " ident)? : command
elab_rules : command
  | `(command| #named_goals $alg:ident $[only $focus:ident]?) =>
      withScope (fun s => { s with opts := proofOptions s.opts }) do
    let name ← resolveMethod alg
    if (← liftCoreM <| entriesFor name).isEmpty then
      elabCommand (← `(command| generate_obligations $alg))
    let entries := (← liftCoreM <| entriesFor name).filter fun entry =>
      focus.all (fun selected => entry.key == selected.getId.toString ||
        entry.key.startsWith (selected.getId.toString ++ "."))
    if entries.isEmpty then throwErrorAt alg "No matching generated obligations"
    for entry in entries do
      let location ← liftCoreM <| sourceRef entry.site alg.raw
      if (← getEnv).contains entry.proofName then
        logInfoAt location m!"[proved] {entry.key}: {entry.proofName}"
      else if (← getEnv).contains (entry.typeName.appendAfter "_automatic") then
        logInfoAt location m!"[automatic, cached] {entry.key}: {entry.typeName}"
      else
        runTermElabM fun _ => do
          let goal ← mkFreshExprSyntheticOpaqueMVar (mkConst entry.typeName)
          discard <| Tactic.run goal.mvarId! do
            evalTactic (← `(tactic| open_frozen_obligation))
            let goals ← openResponsibility (← getMainGoal)
            let mut openGoals := []
            for goal in goals do
              setGoals [← splitHypotheses goal]
              evalTactic (← `(tactic| try simp_all [Composition.InvariantFact,
                Composition.Obligation, Composition.ObligationAt, Composition.SourceForall]))
              for goal in ← getGoals do
                let goal ← hideGuards goal
                goal.setTag (Name.mkSimple entry.key)
                setGoals [goal]
                let saved ← saveState
                try
                  evalTactic (← `(tactic| first | omega | assumption | rfl | simp))
                  if !(← getGoals).isEmpty then
                    saved.restore
                    openGoals := openGoals ++ [goal]
                catch _ =>
                  saved.restore
                  openGoals := openGoals ++ [goal]
            if openGoals.isEmpty then
              logInfoAt location m!"[automatic] {entry.key}: {entry.typeName}"
            else
              logInfoAt location m!"[open] {entry.key}: {entry.typeName}\n{MessageData.joinSep
                (openGoals.map MessageData.ofGoal) m!"\n\n"}"
            setGoals []

end AlgoLib.Experimental.RAM.Prototype.Frontend
