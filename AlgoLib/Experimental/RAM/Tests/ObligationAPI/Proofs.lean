/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.ObligationAPI.Specification

/-!
# Proofs against an imported generated API

A new simplification lemma does not erase an obligation or make its explicit proof
block unknown. The two blocks below are separate kernel-checked declarations.
-/
namespace AlgoLib.Experimental.RAM.Tests.ObligationAPI
open Prototype.Frontend Prototype.Composition

attribute [local simp] known

prove_obligation countdown.ObligationAPI.count.initialize.known by apply known
prove_obligation countdown.ObligationAPI.count.preserve.known by apply known
complete_algorithm countdown

example : countdown.ObligationAPI.count.initialize.known :=
  countdown.ObligationAPI.count.initialize.known_proof

example : countdown.ObligationAPI.count.preserve.known :=
  countdown.ObligationAPI.count.preserve.known_proof

example : countdownObligations := countdownVerification

/-- An incompatible mathematical statement cannot reuse a generated proof. -/
example : True := by
  fail_if_success exact countdown.ObligationAPI.count.preserve.known_proof
  trivial

end AlgoLib.Experimental.RAM.Tests.ObligationAPI
