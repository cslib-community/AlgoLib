/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Verification.GeneratedObligations

/-!
# Source-level obligation explorer

Navigation consumes the imported proposition API; it neither compiles a method nor
changes the proposition to prove. Binding roles were captured at source quantifiers.
Lemma recommendations are explicit library metadata, never trusted proof evidence.
Templates deliberately fail until the author supplies a checked argument.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Meta

/-- An explicitly registered mathematical vocabulary for a proof responsibility. -/
structure ObligationLemma where
  predicate : Name
  phase : String
  theoremName : Name
  deriving Inhabited

initialize obligationLemmaRegistry :
    SimplePersistentEnvExtension ObligationLemma (Array ObligationLemma) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

/-- Register checked theorem names; registration does not run tactics or assert applicability. -/
syntax "obligation_lemmas " ident " for " str " => " "[" ident,* "]" : command
elab_rules : command
  | `(command| obligation_lemmas $pred:ident for $phase:str => [$lemmas:ident,*]) => do
    unless ["initialize", "preserve", "terminate", "account", "requires", "safety", "exit",
        "result"].contains phase.getString do
      throwErrorAt phase "Unknown obligation phase"
    let predicate ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo pred
    for theoremId in lemmas.getElems do
      let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theoremId
      unless (← liftCoreM <| getConstInfo name).isTheorem do
        throwErrorAt theoremId "Register a proved theorem, not a definition or an axiom"
      modifyEnv (obligationLemmaRegistry.addEntry ·
        { predicate, phase := phase.getString, theoremName := name })

/-- Explain the mathematical responsibility without inspecting a normalized goal. -/
def obligationPurpose (responsibility : String) : String :=
  let parts := responsibility.splitOn "."
  if parts.contains "initialize" then
    "Establish the named invariant when the loop is entered."
  else if parts.contains "preserve" then
    "Assume the invariant and guard; establish the invariant after the body, on every path."
  else if parts.contains "terminate" then
    if parts.contains "positive" then
      "Show that the iteration measure is positive while the guard holds."
    else "Show that the iteration measure strictly decreases."
  else if parts.contains "account" then
    if parts.contains "initial" then "Show that the initial allowance covers the loop."
    else "Show that the logical allowance pays for this step and the required continuation."
  else if parts.contains "requires" then "Establish the called procedure's public precondition."
  else if parts.contains "safety" then "Establish bounds and public operation preconditions."
  else if parts.contains "exit" then
    "Use the invariant and loop exit to establish the required result."
  else "Establish the method's requested result."

/-- Filtering is by stable responsibility identity, not by goal position. -/
def explorerEntries (methodName : Name) (focus : String) : CoreM (Array ObligationEntry) := do
  return (obligationRegistry.getState (← getEnv)).filter fun e =>
    e.alg == methodName && (focus.isEmpty || e.key == focus || e.key.startsWith (focus ++ "."))

/-- Suggestions require an occurrence in the frozen proposition and an explicit phase match. -/
def obligationSuggestions (entry : ObligationEntry) : CoreM (Array Name) := do
  let some body := (← getConstInfo entry.typeName).value? | return #[]
  let mut result := #[]
  for hint in obligationLemmaRegistry.getState (← getEnv) do
    if (entry.responsibility.splitOn ".").contains hint.phase &&
        (body.find? (·.isConstOf hint.predicate)).isSome && !result.contains hint.theoremName then
      result := result.push hint.theoremName
  return result

private def selectedEntries (alg : Ident) (focus : Option Ident) :
    CommandElabM (Array ObligationEntry) := do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo alg
  let entries ← liftCoreM <| explorerEntries name (focus.map (·.getId.toString) |>.getD "")
  if entries.isEmpty then
    throwErrorAt alg "No matching generated obligations. \
      Import the specification or run generate_obligations first."
  return entries

/-- Print purpose, source, state roles, lemma statements, and the existing exact preview. -/
syntax "#explain_obligation " ident (" only " ident)? : command
elab_rules : command
  | `(command| #explain_obligation $alg:ident $[only $focus:ident]?) => do
    for entry in ← selectedEntries alg focus do
      let location ← liftCoreM <| sourceRef entry.site alg.raw
      logInfoAt location m!"{entry.key}\nPurpose: {obligationPurpose entry.responsibility}\n\
        Source: {entry.site}\nFrozen API: {entry.typeName}\n\
        Execution paths retained: {entry.contexts.size}"
      -- Repeated paths often share the same source telescope. Show each binding once.
      let mut shown : Array (Name × String) := #[]
      for context in entry.contexts do
        for binding in context do
          unless shown.contains (binding.name, binding.role) do
            shown := shown.push (binding.name, binding.role)
            logInfoAt location m!"  {binding.name}: source {binding.source}; {binding.role}"
      let suggestions ← liftCoreM <| obligationSuggestions entry
      if suggestions.isEmpty then
        logInfoAt location "No registered lemma suggestions for this responsibility."
      else
        for theoremId in suggestions do
          let info ← liftCoreM <| getConstInfo theoremId
          logInfoAt location m!"Suggested lemma (check its hypotheses): {theoremId}\n{info.type}"
      let key := mkIdent (entry.key.splitOn "." |>.foldl Name.str .anonymous)
      elabCommand (← `(command| #named_goals $alg only $key))
      logInfoAt location m!"Inspect the full frozen statement with #print {entry.typeName}. \
        All remaining paths must be proved."

/-- A copyable, deliberately incomplete block. This command adds no proof declarations. -/
syntax "#proof_template " ident (" only " ident)? : command
elab_rules : command
  | `(command| #proof_template $alg:ident $[only $focus:ident]?) => do
    for entry in ← selectedEntries alg focus do
      let env ← getEnv
      if env.contains entry.proofName then
        logInfo m!"[proved] {entry.key}; edit its existing proof block."
      else if env.contains (entry.typeName.appendAfter "_automatic") then
        logInfo m!"[automatic, cached] {entry.key}; no proof block is required."
      else
        logInfo m!"-- {obligationPurpose entry.responsibility}\n\
          -- Covers every remaining execution path for this responsibility.\n\
          prove_obligation {entry.typeName} by\n  fail \"Supply the mathematical argument here\""

end AlgoLib.Experimental.RAM.Prototype.Frontend
