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

/- Missing mathematical proofs, unknown names, overlapping blocks, and invalid evidence fail. -/
set_option linter.unreachableTactic false in
example : countdownObligations := by
  unfold countdownObligations countdown
  fail_if_success named_proof_blocks countdown
    case count.preserve.known => by apply known
    case count.terminate => by simp only [rank_eq]; omega
    case count.account => by first | omega | (simp only [rank_eq] at *; omega)
  fail_if_success named_proof_blocks countdown
    case count.initialize.known => by apply known
    case count.terminate => by simp only [rank_eq]; omega
    case count.account => by first | omega | (simp only [rank_eq] at *; omega)
  fail_if_success named_proof_blocks countdown
    case count.initialize.known => by apply known
    case count.preserve.known => by apply known
    case count.account => by first | omega | (simp only [rank_eq] at *; omega)
  fail_if_success named_proof_blocks countdown
    case count.initialize.known => by apply known
    case count.preserve.known => by apply known
    case count.terminate => by simp only [rank_eq]; omega
  fail_if_success named_proof_blocks countdown
    case count.initialize.known => by skip
  fail_if_success named_proof_blocks countdown
    case typo.initialize => by trivial
  fail_if_success named_proof_blocks countdown
    case count.initialize => by apply known
    case count.initialize.known => by apply known
  fail_if_success named_proof_blocks countdown
    case count.terminate => by exact Nat.zero_le 0
  named_proof_blocks countdown
    case count.initialize.known => by apply known
    case count.preserve.known => by apply known
    case count.terminate => by simp only [rank_eq]; omega
    case count.account => by first | omega | (simp only [rank_eq] at *; omega)

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
