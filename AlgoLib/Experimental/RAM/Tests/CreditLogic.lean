/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Semantics

/-!
# A reusable algorithm proof with no RAM dependency

This entire file imports only the logical credit semantics. `increment` costs one
logical credit. `twice` has a two-credit procedure contract; `four` composes two calls.
The one proof `four_correct` is reused by two implementations in BackendReuse.lean.
Neither register names nor instruction counts occur in the algorithm or its proof.
-/
namespace AlgoLib.Experimental.RAM.Tests.CreditLogic
open Authoring

/-- One unit of abstract work; its implementations are registered elsewhere. -/
def increment : Action Nat where
  requires _ := True
  effect n := n + 1
  work _ := 1

/-- A verified procedure that can be used without reopening its body. -/
def twice : Procedure Nat where
  body := .seq (.action increment) (.action increment)
  requires _ := True
  effect n := n + 2
  work _ := 2
  verification := by
    apply VC.correct
    intro n _
    simp [VC, increment, Nat.add_assoc]

/-- Two procedure calls compose their logical budgets. -/
def four : Program Nat := .seq (.action twice.call) (.action twice.call)

/-- The algorithm proof is independent of every execution backend. -/
theorem four_correct : Correct four (fun _ => True) (fun n out => out = n + 4)
    (fun _ => 4) := by
  apply VC.correct
  intro n _
  simp [four, VC, Procedure.call, twice, Nat.add_assoc]

/-- Credit logic itself rules out underpayment before any compiler is selected. -/
theorem insufficient (n : Nat) : ¬ VC four (fun _ _ => True) n 3 := by
  simp [four, VC, Procedure.call, twice]

end AlgoLib.Experimental.RAM.Tests.CreditLogic
