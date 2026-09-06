/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts
import AlgoLib.Experimental.RAM.Prototype.Composition.Ownership

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

/-- Internal output of certificate reconstruction. -/
structure Refinement (rate : Nat) (P : Representation A) (Q : Representation B)
    (p : Program A B) where
  code : Cmd
  sound : ∀ {a k b}, Run p a k b → ∀ r s saved, P.holds a r s saved →
    ∃ steps t left, Eval code s steps t ∧ Q.holds b r t left ∧ Writes r s t ∧
      steps + left ≤ rate * k + saved

/-- Primitive authors implement a typed abstract operation, including its ownership contract. -/
class Primitive (rate : Nat) (P : Representation A) (op : Operation A B)
    (Q : outParam (Representation B)) where
  code : Cmd
  correct : ∀ a, op.requires a → ∀ r s saved, P.holds a r s saved →
    ∃ steps t left, Eval code s steps t ∧ Q.holds (op.effect a) r t left ∧ Writes r s t ∧
      steps + left ≤ rate * op.charge a + saved

class TestImplementation (rate : Nat) (P : Representation A) (test : A → Bool) where
  condition : Condition
  correct : ∀ a r s saved, P.holds a r s saved → condition.eval s = test a
  cost : condition.cost ≤ rate

/-- Query lifting borrows the selected component and leaves all ownership unchanged. -/
instance [impl : TestImplementation rate P test] :
    TestImplementation rate (P.sep Q) (testLeft test) where
  condition := impl.condition
  correct a r s saved rep := by
    obtain ⟨r₁, r₂, p₁, p₂, _, _, _, hp, _⟩ := rep
    exact impl.correct a.1 r₁ s p₁ hp
  cost := impl.cost

instance (P : Representation A) [impl : TestImplementation rate Q test] :
    TestImplementation rate (P.sep Q) (testRight test) where
  condition := impl.condition
  correct a r s saved rep := by
    obtain ⟨r₁, r₂, p₁, p₂, _, _, _, _, hq⟩ := rep
    exact impl.correct a.2 r₂ s p₂ hq
  cost := impl.cost

inductive Supported (rate : Nat) :
    {A B : Type} → Representation A → Representation B → Program A B → Type 1 where
  | identity (P) : Supported rate P P .identity
  | swap (P : Representation A) (Q : Representation B) :
      Supported rate (P.sep Q) (Q.sep P) .swap
  | invoke (impl : Primitive rate P op Q) : Supported rate P Q (.invoke op)
  | seq : Supported rate P Q p → Supported rate Q R q → Supported rate P R (.seq p q)
  | frame (h : Supported rate P Q p) (F : Representation R) :
      Supported rate (P.sep F) (Q.sep F) (.frame p _)
  | branch (impl : TestImplementation rate P test) : Supported rate P Q p → Supported rate P Q q →
      Supported rate P Q (.branch test p q)
  | loop (impl : TestImplementation rate P test) : Supported rate P P p →
      Supported rate P P (.loop test p)
  | call : Supported rate P Q p → Supported rate P Q (.call p)

private def identityRef (rate : Nat) (P : Representation A) : Refinement rate P P .identity where
  code := .skip
  sound run r s saved rep := by
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨0, s, saved, .skip _, rep, Writes.refl _ _, by omega⟩

private def swapRef (rate : Nat) (P : Representation A) (Q : Representation B) :
    Refinement rate (P.sep Q) (Q.sep P) .swap where
  code := .skip
  sound run r s saved rep := by
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨0, s, saved, .skip _, (Representation.sep_comm P Q).mp rep, Writes.refl _ _, by omega⟩

private def invokeRef (impl : Primitive rate P op Q) : Refinement rate P Q (.invoke op) where
  code := impl.code
  sound run r s saved rep := by
    obtain ⟨safe, rfl, rfl⟩ := run
    exact impl.correct _ safe r s saved rep

private def seqRef (f : Refinement rate P Q p) (g : Refinement rate Q R q) :
    Refinement rate P R (.seq p q) where
  code := .seq f.code g.code
  sound run r s saved rep := by
    obtain ⟨_, _, _, hp, hq, rfl⟩ := run
    obtain ⟨i, t, left, he, hr, hw, hc⟩ := f.sound hp r s saved rep
    obtain ⟨j, u, last, hf, hs, hv, hd⟩ := g.sound hq r t left hr
    exact ⟨i + j, u, last, .seq he hf, hs, hw.trans hv, by nlinarith⟩

private def frameRef (f : Refinement rate P Q p) (F : Representation R) :
    Refinement rate (P.sep F) (Q.sep F) (.frame p _) where
  code := f.code
  sound run r s saved rep := by
    obtain ⟨hp, equal⟩ := run
    obtain ⟨r₁, r₂, p₁, p₂, hd, rfl, rfl, hP, hF⟩ := rep
    obtain ⟨i, t, left, he, hQ, hw, hc⟩ := f.sound hp r₁ s p₁ hP
    exact ⟨i, t, left + p₂, he, ⟨r₁, r₂, left, p₂, hd, rfl, rfl, hQ, equal ▸ F.frame hF hd hw⟩,
      hw.mono Finset.subset_union_left, by omega⟩

private def branchRef (impl : TestImplementation rate P test)
    (f : Refinement rate P Q p) (g : Refinement rate P Q q) :
    Refinement rate P Q (.branch test p q) where
  code := .branch impl.condition f.code g.code
  sound := by
    intro a k b run r s saved rep
    obtain ⟨i, rfl, hp⟩ := run
    cases ht : test a with
    | true =>
      obtain ⟨i, t, left, he, hr, hw, hc⟩ :=
        f.sound (a := a) (k := i) (b := b) (by simpa [ht] using hp) r s saved rep
      exact ⟨_, t, left, .ifTrue ((impl.correct _ _ _ _ rep).trans ht) he, hr, hw,
        by have := impl.cost; nlinarith⟩
    | false =>
      obtain ⟨i, t, left, he, hr, hw, hc⟩ :=
        g.sound (a := a) (k := i) (b := b) (by simpa [ht] using hp) r s saved rep
      exact ⟨_, t, left, .ifFalse ((impl.correct _ _ _ _ rep).trans ht) he, hr, hw,
        by have := impl.cost; nlinarith⟩

private def loopRef (impl : TestImplementation rate P test) (f : Refinement rate P P p) :
    Refinement rate P P (.loop test p) where
  code := .loop impl.condition f.code
  sound := by
    intro a k b run r s saved rep
    have go : ∀ k a b, Run (.loop test p) a k b → ∀ s saved, P.holds a r s saved →
        ∃ steps t left, Eval (.loop impl.condition f.code) s steps t ∧
          P.holds b r t left ∧ Writes r s t ∧ steps + left ≤ rate * k + saved := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro a b run s saved rep
        cases run with
        | done ht =>
          exact ⟨_, s, saved, .whileFalse ((impl.correct _ _ _ _ rep).trans ht), rep,
            Writes.refl _ _, by have := impl.cost; omega⟩
        | @step _ i _ j _ ht hb hl =>
          obtain ⟨steps, t, left, he, hr, hw, hc⟩ := f.sound hb r s saved rep
          obtain ⟨steps', u, last, hf, hs, hv, hd⟩ := ih j (by omega) _ _ hl t left hr
          exact ⟨_, u, last, .whileTrue ((impl.correct _ _ _ _ rep).trans ht) he hf,
            hs, hw.trans hv, by have := impl.cost; nlinarith⟩
    exact go k a b run s saved rep

private def callRef (f : Refinement rate P Q p) : Refinement rate P Q (.call p) where
  code := f.code
  sound run r s saved rep := by
    exact f.sound run r s saved rep

/-- Total structural reconstruction; no client-specific translation proof occurs. -/
def Supported.compile : Supported rate P Q p → Refinement rate P Q p
  | .identity P => identityRef _ P
  | .swap P Q => swapRef _ P Q
  | .invoke impl => invokeRef impl
  | .seq f g => seqRef f.compile g.compile
  | .frame f F => frameRef f.compile F
  | .branch impl f g => branchRef impl f.compile g.compile
  | .loop impl f => loopRef impl f.compile
  | .call f => callRef f.compile

/-- Erase certificates before comparing code. This avoids reducing nested semantic
proof packages merely to inspect their executable component. -/
def Supported.code : Supported rate P Q p → Cmd
  | .identity _ => .skip
  | .swap _ _ => .skip
  | .invoke impl => impl.code
  | .seq f g => .seq f.code g.code
  | .frame f _ => f.code
  | .branch impl f g => .branch impl.condition f.code g.code
  | .loop impl f => .loop impl.condition f.code
  | .call f => f.code

/-- Certificate erasure returns exactly the existing verified compilation's code. -/
theorem Supported.compile_code (h : Supported rate P Q p) : h.compile.code = h.code := by
  induction h <;> simp_all [Supported.compile, Supported.code, identityRef, swapRef,
    invokeRef, seqRef, frameRef, branchRef, loopRef, callRef]

/-- Interpretation preserves sequential composition at the generated-code level. -/
theorem Supported.compile_seq (f : Supported rate P Q p) (g : Supported rate Q R q) :
    (Supported.seq f g).compile.code = .seq f.compile.code g.compile.code := rfl

/-- Framing changes no executable code and introduces no runtime copying. -/
theorem Supported.compile_frame (f : Supported rate P Q p) (F : Representation R) :
    (Supported.frame f F).compile.code = f.compile.code := rfl

/-- Different certified calibrations can be embedded in a common calibration. -/
def Refinement.weaken (f : Refinement rate P Q p) (larger : rate ≤ rate') :
    Refinement rate' P Q p where
  code := f.code
  sound h r s saved rep := by
    obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := f.sound h r s saved rep
    exact ⟨steps, t, left, exec, hQ, hw, hc.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ larger) _)⟩

/-- A common conversion rate is inferred using max; private potentials still telescope. -/
def Refinement.compose (f : Refinement rate P Q p) (g : Refinement rate' Q R q) :
    Refinement (max rate rate') P R (.seq p q) :=
  seqRef (f.weaken (Nat.le_max_left _ _)) (g.weaken (Nat.le_max_right _ _))

/-- Type-directed linking is indexed by the exact program and its ownership interfaces. -/
class Linked (rate : Nat) (P : Representation A) (p : Program A B)
    (Q : outParam (Representation B)) where
  supported : Supported rate P Q p

instance : Linked rate P .identity P := ⟨.identity P⟩
instance (P : Representation A) (Q : Representation B) :
    Linked rate (P.sep Q) .swap (Q.sep P) := ⟨.swap P Q⟩
instance [i : Primitive rate P op Q] : Linked rate P (.invoke op) Q := ⟨.invoke i⟩
instance [f : Linked rate P p Q] [g : Linked rate Q q R] : Linked rate P (.seq p q) R :=
  ⟨.seq f.supported g.supported⟩
instance [f : Linked rate P p Q] : Linked rate (P.sep F) (.frame p _) (Q.sep F) :=
  ⟨.frame f.supported F⟩
instance [i : TestImplementation rate P test] [f : Linked rate P p Q] [g : Linked rate P q Q] :
    Linked rate P (.branch test p q) Q := ⟨.branch i f.supported g.supported⟩
instance [i : TestImplementation rate P test] [f : Linked rate P p P] :
    Linked rate P (.loop test p) P := ⟨.loop i f.supported⟩
instance [f : Linked rate P p Q] : Linked rate P (.call p) Q := ⟨.call f.supported⟩

/-- Every client VC proof links to actual RAM execution. Initial private resources
are included in the bound; final private resources remain owned, not discarded. -/
theorem client_linking {A B : Type} {rate : Nat} {P : Representation A}
    {Q : Representation B} {p : Program A B} (supported : Supported rate P Q p) (post : B → Prop)
    (a : A) (budget : Nat) (proof : VC p (fun b _ => post b) a budget)
    (r : Footprint) (machine : Checked.State) (saved : Nat)
    (rep : P.holds a r (observe machine) saved) :
    ∃ steps final b left, Checked.Exec supported.compile.code.compile machine steps final ∧
      Q.holds b r (observe final) left ∧ post b ∧ Writes r (observe machine) (observe final) ∧
      steps + left ≤ rate * budget + saved := by
  obtain ⟨k, b, run, hk, hb⟩ := VC.sound p _ a budget proof
  obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := supported.compile.sound run r _ saved rep
  obtain ⟨final, ram, equal⟩ := exec.compile machine rfl
  exact ⟨steps, final, b, left, ram, equal ▸ hQ, hb, equal ▸ hw,
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _)⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
