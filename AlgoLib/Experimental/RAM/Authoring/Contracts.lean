/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Semantics

/-!
# Backend-independent input/output algorithms and credit contracts

`Specification` contains the program, ordinary mathematical input/output views,
and logical credit budget. Its verification conditions mention no RAM model,
representation, compiler, instruction count, or backend conversion factor.
`Interface.realize` in Methods.lean later attaches a separately verified backend.
-/
namespace AlgoLib.Experimental.RAM.Authoring

/-- Completeness for the independent mathematical semantics. Used internally to
turn a previously checked loop contract into the generated method obligation. -/
theorem Run.vc {State : Type} (p : Program State) :
    ∀ {s t : State} {k : Nat}, Run p s k t →
      ∀ (Q : State → Nat → Prop) (c : Nat), k ≤ c → Q t (c-k) → VC p Q s c := by
  induction p with
  | skip =>
    intro s t k h Q c hc hQ
    cases h
    simpa [VC] using hQ
  | action a =>
    intro s t k h Q c hc hQ
    cases h with
    | action _ _ safe => exact ⟨safe, hc, hQ⟩
  | seq a b iha ihb =>
    intro s t k h Q c hc hQ
    cases h with
    | @seq _ _ _ u _ i j ha hb =>
      apply iha ha (VC b Q) c (by omega)
      apply ihb hb Q (c-i) (by omega)
      simpa [Nat.sub_sub] using hQ
  | branch q a b iha ihb =>
    intro s t k h Q c hc hQ
    cases h with
    | ifTrue yes ha =>
      refine ⟨by omega, ?_⟩
      simp only [yes, ↓reduceIte]
      apply iha ha Q (c-1) (by omega)
      simpa [Nat.sub_sub, Nat.add_comm] using hQ
    | ifFalse no hb =>
      refine ⟨by omega, ?_⟩
      simp only [no, Bool.false_eq_true, ↓reduceIte]
      apply ihb hb Q (c-1) (by omega)
      simpa [Nat.sub_sub, Nat.add_comm] using hQ
  | loop q body ih =>
    intro s t k h Q c hc hQ
    let I := fun u d => ∃ j z, Run (.loop q body) u j z ∧ j ≤ d ∧ Q z (d-j)
    refine ⟨I, ⟨k, t, h, hc, hQ⟩, ?_⟩
    intro u d ⟨j, z, run, hj, hz⟩
    cases run with
    | whileFalse no =>
      exact ⟨by omega, by simpa [no] using hz⟩
    | @whileTrue _ _ _ v _ i l yes hb hl =>
      refine ⟨by omega, ?_⟩
      simp only [yes, ↓reduceIte]
      apply ih hb I (d-1) (by omega)
      exact ⟨l, z, hl, by omega, by simpa [Nat.sub_sub, Nat.add_assoc] using hz⟩

/-- A complete logical algorithm, including input/output, with no backend parameter. -/
structure Specification (State Input Output : Type) where
  body : Program State
  initial : Input → State
  observes : State → Output → Prop
  requires : Input → Prop
  ensures : Input → Output → Prop
  credits : Input → Nat

/-- Logical correctness and local credit obligations; no machine costs occur here. -/
def Specification.VCs {State Input Output : Type}
    (spec : Specification State Input Output) : Prop :=
  ∀ i, spec.requires i → VC spec.body
    (fun t _ => ∀ out, spec.observes t out → spec.ensures i out) (spec.initial i) (spec.credits i)

/-- Pure soundness for a complete logical algorithm, reused by every backend. -/
theorem Specification.correct {State Input Output : Type}
    (spec : Specification State Input Output) (proof : spec.VCs)
    (i : Input) (hi : spec.requires i) :
    ∃ k t, Run spec.body (spec.initial i) k t ∧ k ≤ spec.credits i ∧
      ∀ out, spec.observes t out → spec.ensures i out :=
  VC.sound _ _ _ _ (proof i hi)

end AlgoLib.Experimental.RAM.Authoring
