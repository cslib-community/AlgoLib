/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.ObligationAPI.Specification

/-!
# Explorer navigation and evidence boundaries

The fixture imports an already generated API. Navigation must retain that API,
report explicitly captured source roles, and suggest only registered theorems for
matching predicates and phases. Templates never supply evidence.
-/
namespace AlgoLib.Experimental.RAM.Tests.ObligationAPI
open Prototype.Frontend Prototype.Composition Lean Elab Command

obligation_lemmas Known for "initialize" => [known]

/-- error: Register a proved theorem, not a definition or an axiom -/
#guard_msgs in
obligation_lemmas Known for "initialize" => [Known]

/-- error: Unknown obligation phase -/
#guard_msgs in
obligation_lemmas Known for "typo" => [known]

run_cmd do
  let entries ← liftCoreM <| explorerEntries ``countdown "count.initialize.known"
  unless entries.size == 1 do throwError "Expected exactly one stable responsibility"
  let entry := entries[0]!
  unless entry.responsibility == "initialize" do
    throwError "Lost the explicit source responsibility"
  -- Changing a navigation key must not change the explanation or suggestion phase.
  let renamed := { entry with key := "preserve.account.initialize.preserve" }
  unless (← liftCoreM <| obligationSuggestions renamed) == #[``known] do
    throwError "Suggestion phase was guessed from a loop or invariant name"
  unless entry.contexts.any (fun xs => xs.any (fun x =>
      x.source == "_counter" && x.name == `_counterInput && x.role == "original input")) do
    throwError "Missing explicitly recorded original input"
  unless (← liftCoreM <| obligationSuggestions entry) == #[``known] do
    throwError "Registered initialization theorem was not discovered"
  let preservation ← liftCoreM <| explorerEntries ``countdown "count.preserve.known"
  unless preservation[0]!.contexts.any (fun xs => xs.any (fun x =>
      x.name == `_counterState1 && x.role == "quantified loop state 1")) do
    throwError "Missing explicitly recorded loop snapshot"
  unless (← liftCoreM <| obligationSuggestions preservation[0]!).isEmpty do
    throwError "Initialization hint leaked into preservation"

set_option linter.hashCommand false in
#guard_msgs (drop info) in
#explain_obligation countdown only count.initialize.known

set_option linter.hashCommand false in
#guard_msgs (drop info) in
#proof_template countdown only count.initialize.known

run_cmd do
  let proofName := (``countdown.ObligationAPI.count.initialize.known).appendAfter "_proof"
  if (← getEnv).contains proofName then
    throwError "A template created proof evidence"

-- A copied unfinished template cannot discharge the proposition.
example : countdown.ObligationAPI.count.initialize.known := by
  fail_if_success obligation_proof by fail "Supply the mathematical argument here"
  obligation_proof by exact known _counterInput

-- Explicit snapshot names work in ordinary proof blocks, not only in printed text.
example : countdown.ObligationAPI.count.preserve.known := by
  obligation_proof by exact known (_counterState1 - 1)

end AlgoLib.Experimental.RAM.Tests.ObligationAPI
