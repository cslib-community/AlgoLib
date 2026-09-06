/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.ObligationAPI.Proofs

/-!
# Stable identities and checked explicit evidence

Even when a new simp lemma can solve an obligation, an invalid or incomplete explicit
block must not be silently skipped. The assembly and its component proofs use only
the standard kernel-checked logical infrastructure.
-/
namespace AlgoLib.Experimental.RAM.Tests.ObligationAPI
open Prototype.Frontend Prototype.Composition

attribute [local simp] known

-- An underscore-prefixed source variable is explicitly public metadata.
example : countdownProofInputShape = SourceShape.leaf 0 "_counter" false := rfl

example : countdown.ObligationAPI.count.initialize.known := by
  fail_if_success obligation_proof by skip
  fail_if_success obligation_proof by exact Nat.zero_le 0
  exact countdown.ObligationAPI.count.initialize.known_proof

example : countdown.ObligationAPI.count.preserve.known := by
  fail_if_success obligation_proof by exact False.elim
  exact countdown.ObligationAPI.count.preserve.known_proof

set_option linter.hashCommand false in
#guard_msgs (drop info) in
#named_goals countdown only count.preserve.known

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.ObligationAPI.countdownVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms countdownVerification

end AlgoLib.Experimental.RAM.Tests.ObligationAPI
