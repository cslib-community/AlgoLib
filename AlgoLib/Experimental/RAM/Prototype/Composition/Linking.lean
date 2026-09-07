/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts
import AlgoLib.Experimental.RAM.Prototype.Composition.Ownership
import AlgoLib.Experimental.RAM.Prototype.Composition.ResourceRefinement
import AlgoLib.Experimental.RAM.Backend.Language.IntegerExecution

/-!
# Resource-aware, ownership-preserving client linking

Only primitives and tests require implementation proofs. `Supported.compile`
reconstructs every composite certificate, including frames, loops and finite calls.
The potential inequality telescopes through sequence; a frame's potential is
preserved by locality, rather than exposed in the client's invariant.

`client_linking` connects every supported client's logical VCs to actual RAM Exec,
reusing the existing compiler theorem. `Linked` typeclass instances reconstruct the
structural witness. No whole-client simulation is a premise of linker acceptance.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

/-- Historical implementation semantics, retained while private libraries migrate.
Certificate composition itself is shared with the native implementation backend. -/
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

abbrev Supported.compile (h : Supported rate P Q p) : Refinement rate P Q p :=
  Ownership.Supported.compile h
abbrev Supported.code (h : Supported rate P Q p) : Cmd := Ownership.Supported.code h
abbrev Supported.seq (f : Supported rate P Q p) (g : Supported rate Q R q) :
    Supported rate P R (.seq p q) := Ownership.Supported.seq f g
abbrev Supported.frame (f : Supported rate P Q p) (F : Representation R) :
    Supported rate (P.sep F) (Q.sep F) (.frame p _) := Ownership.Supported.frame f F
abbrev Refinement.weaken (f : Refinement rate P Q p) (larger : rate ≤ rate') :
    Refinement rate' P Q p := Ownership.Refinement.weaken f larger
abbrev Refinement.compose (f : Refinement rate P Q p) (g : Refinement rate' Q R q) :
    Refinement (max rate rate') P R (.seq p q) := Ownership.Refinement.compose f g

theorem Supported.compile_code (h : Supported rate P Q p) : h.compile.code = h.code :=
  Ownership.Supported.compile_code h

theorem Supported.compile_seq (f : Supported rate P Q p) (g : Supported rate Q R q) :
    (Supported.seq f g).compile.code = .seq f.compile.code g.compile.code := rfl

theorem Supported.compile_frame (f : Supported rate P Q p) (F : Representation R) :
    (Supported.frame f F).compile.code = f.compile.code := rfl

/-- Every client VC proof links to actual RAM execution. Initial private resources
are included in the bound; final private resources remain owned, not discarded. -/
theorem client_linking {A B : Type} {rate : Nat} {P : Representation A}
    {Q : Representation B} {p : Program A B} (supported : Supported rate P Q p) (post : B → Prop)
    (a : A) (budget : Nat) (proof : VC p (fun b _ => post b) a budget)
    (r : Footprint) (initial : Store) (saved : Nat)
    (rep : P.holds a r initial saved) :
    ∃ steps final b left, Integer.Exec (Native.Natural.command supported.compile.code).compile
      (integerEncode initial) steps final ∧
      Q.holds b r (integerObserve final) left ∧ post b ∧ Writes r initial (integerObserve final) ∧
      steps + 2 * left ≤ 2 * (rate * budget + saved) := by
  obtain ⟨k, b, run, hk, hb⟩ := VC.sound p _ a budget proof
  obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := supported.compile.sound run r _ saved rep
  obtain ⟨actual, native, overhead⟩ := Native.Natural.preserves exec
  obtain ⟨final, ram, equal⟩ := native.compile _ (Native.observe_encode _)
  have observation : integerObserve final = t := by simp [integerObserve, equal]
  exact ⟨actual, final, b, left, ram, observation.symm ▸ hQ, hb,
    observation.symm ▸ hw, by nlinarith⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
