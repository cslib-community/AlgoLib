/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend

/-!
# Regression tests for independently checked proof blocks

The opaque mathematical predicate prevents routine arithmetic from silently solving
initialization and preservation. Failed authoring attempts must leave no certificate.
-/
namespace AlgoLib.Experimental.RAM.Tests.NamedProofs
open Prototype.Frontend Prototype.Composition

/-- Stand-in for an abstract mathematical invariant supplied by an algorithm author. -/
@[irreducible] def Known (n : Nat) : Prop := n ≤ n

theorem known (n : Nat) : Known n := by unfold Known; omega

/-- Abstract counting function; its defining equation is supplied in accounting blocks. -/
@[irreducible] def rank (n : Nat) : Nat := n

theorem rank_eq (n : Nat) : rank n = n := by unfold rank; rfl

ram method countdown (mut x : Nat) return (result : Nat)
  require True
  ensures x = 0
  do
    while 0 < x named count
      invariant "known" Known x
      amortized_work rank x initially_at_most x
      do
        x := x - 1

-- Focused previews inspect obligations without constructing or admitting a certificate.
set_option linter.hashCommand false in
#guard_msgs (drop info) in
#named_goals countdown only count.preserve.known

prove_algorithm countdown where
  case count.initialize.known => by apply known
  case count.preserve.known => by apply known
  case count.terminate => by simp only [rank_eq]; omega
  case count.account => by first | omega | (simp only [rank_eq] at *; omega)
  case count.exit => by first | omega | trivial

/- Moving a loop and adding unrelated local initialization leaves its proof names intact. -/
ram method movedCountdown (mut x : Nat) return (result : Nat)
  require True
  ensures x = 0
  do
    let mut unrelated := 7
    while 0 < x named count
      invariant "known" Known x
      amortized_work rank x initially_at_most x
      do
        x := x - 1

prove_algorithm movedCountdown where
  case count.initialize.known => by apply known
  case count.preserve.known => by apply known
  case count.terminate => by simp only [rank_eq]; omega
  case count.account => by first | omega | (simp only [rank_eq] at *; omega)
  case count.exit => by first | omega | trivial

/- Negative evidence checks target the generated API, not a second normalization engine. -/
example : countdown.ObligationAPI.count.initialize.known := by
  fail_if_success obligation_proof by skip
  fail_if_success obligation_proof by exact Nat.zero_le 0
  obligation_proof by apply known

example : countdown.ObligationAPI.count.account.initial := by
  fail_if_success obligation_proof by omega
  obligation_proof by simp only [rank_eq] at *; omega

/-- error: Unknown generated obligation typo.initialize -/
#guard_msgs in
prove_algorithm countdown where
  case typo.initialize => by trivial

ram method unfinished (mut x : Nat) return (result : Nat)
  ensures Known x
  do
    x := x

generate_obligations unfinished

-- A missing mathematical argument must prevent a completed procedure.
#guard_msgs (drop error) in
complete_algorithm unfinished

open Lean Elab Command in
run_cmd do
  if (← getEnv).contains ((``unfinished).appendAfter "Verification") then
    throwError "Missing proof unexpectedly produced verification"
  let entries ← liftCoreM <| explorerEntries ``unfinished ""
  for entry in entries do
    if (← getEnv).contains entry.proofName then
      throwError "A failed proof left a placeholder declaration"

ram method overlapping (mut x : Nat) return (result : Nat)
  ensures Known x
  do
    x := x

/-- error: Overlapping obligation block result -/
#guard_msgs in
prove_algorithm overlapping where
  case result => by apply known
  case result => by apply known

/-- error: Duplicate named proof scope 'same' -/
#guard_msgs in
ram method duplicateScope (mut x : Nat) return (result : Nat)
  require True
  ensures True
  do
    named same do
      x := 1
    named same do
      x := 2

/-- error: Duplicate invariant name 'known' -/
#guard_msgs in
ram method duplicateInvariant (mut x : Nat) return (result : Nat)
  require True
  ensures True
  do
    while 0 < x named count
      invariant "known" Known x
      invariant "known" Known x
      iterations_at_most x
      do
        x := x - 1

/-- error: Name every invariant in a named loop -/
#guard_msgs in
ram method missingInvariantName (mut x : Nat) return (result : Nat)
  require True
  ensures True
  do
    while 0 < x named count
      invariant Known x
      iterations_at_most x
      do
        x := x - 1

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.NamedProofs.countdownVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms countdownVerification

end AlgoLib.Experimental.RAM.Tests.NamedProofs
