/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Contracts.ResourceRefinement
import AlgoLib.Experimental.RAM.Compiler.Native.Ownership

/-!
# Native ownership-aware linking

Instantiate the shared resource-refinement laws with native integer commands.
Client proofs use the same logical Program, VC, and credit contracts as before.
The final theorem exposes actual integer execution, exact observation, ownership
framing, and the bound obtained from the implementation's resource calibration.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Native
open Prototype.Composition (Program Operation VC)

abbrev implementationBackend : Ownership.Backend where
  memory := ownershipModel
  Command := Cmd
  Condition := Condition
  Eval := Eval
  test := Condition.eval
  testCost := Condition.cost
  skip := .skip
  seq := .seq
  branch := .branch
  loop := .loop
  skip_sound := Eval.skip
  seq_sound := Eval.seq
  ifTrue_sound := Eval.ifTrue
  ifFalse_sound := Eval.ifFalse
  whileFalse_sound := Eval.whileFalse
  whileTrue_sound := Eval.whileTrue

abbrev Refinement (rate : Nat) (P : Representation A) (Q : Representation B) (p : Program A B) :=
  Ownership.Refinement implementationBackend rate P Q p
abbrev Primitive (rate : Nat) (P : Representation A) (op : Operation A B)
    (Q : Representation B) := Ownership.Primitive implementationBackend rate P op Q
abbrev TestImplementation (rate : Nat) (P : Representation A) (test : A → Bool) :=
  Ownership.TestImplementation implementationBackend rate P test
abbrev Supported := Ownership.Supported implementationBackend
abbrev Linked (rate : Nat) (P : Representation A) (p : Program A B) (Q : Representation B) :=
  Ownership.Linked implementationBackend rate P p Q

/-- All compiler and resource transport follows from the leaf contracts and source VCs. -/
theorem client_linking {A B : Type} {rate : Nat} {P : Representation A}
    {Q : Representation B} {p : Program A B} (supported : Supported rate P Q p) (post : B → Prop)
    (a : A) (budget : Nat) (proof : VC p (fun b _ => post b) a budget)
    (r : Footprint) (machine : Integer.State) (saved : Nat)
    (rep : P.holds a r (observe machine) saved) :
    ∃ steps final b left, Integer.Exec supported.compile.code.compile machine steps final ∧
      Q.holds b r (observe final) left ∧ post b ∧ Writes r (observe machine) (observe final) ∧
      steps + left ≤ rate * budget + saved := by
  obtain ⟨k, b, run, hk, hb⟩ := VC.sound p _ a budget proof
  obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := supported.compile.sound run r _ saved rep
  obtain ⟨final, ram, equal⟩ := exec.compile machine rfl
  exact ⟨steps, final, b, left, ram, equal ▸ hQ, hb, equal ▸ hw,
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _)⟩

end AlgoLib.Experimental.RAM.Native
