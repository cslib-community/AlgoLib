/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Contracts.Ownership
import AlgoLib.Experimental.RAM.Language.Contracts

/-!
# Compositional refinement independent of the implementation store

The logical program and its credits stay fixed. An implementation backend supplies
counted command semantics and their composition laws. Primitive certificates then
reconstruct whole-client certificates, preserving ownership and private potential.
This shared reconstruction supports migration from natural to native integer
storage without duplicating the client-linking logic.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Ownership
open Prototype.Composition (Program Run Operation VC testLeft testRight)

structure Backend where
  memory : Model
  Command : Type
  Condition : Type
  Eval : Command → memory.State → Nat → memory.State → Prop
  test : Condition → memory.State → Bool
  testCost : Condition → Nat
  skip : Command
  seq : Command → Command → Command
  branch : Condition → Command → Command → Command
  loop : Condition → Command → Command
  skip_sound : ∀ s, Eval skip s 0 s
  seq_sound : ∀ {a b s u t i j}, Eval a s i u → Eval b u j t → Eval (seq a b) s (i+j) t
  ifTrue_sound : ∀ {q a b s t k}, test q s = true → Eval a s k t →
    Eval (branch q a b) s (testCost q+k) t
  ifFalse_sound : ∀ {q a b s t k}, test q s = false → Eval b s k t →
    Eval (branch q a b) s (testCost q+k) t
  whileFalse_sound : ∀ {q b s}, test q s = false → Eval (loop q b) s (testCost q) s
  whileTrue_sound : ∀ {q b s u t i j}, test q s = true → Eval b s i u → Eval (loop q b) u j t →
    Eval (loop q b) s (testCost q+i+j) t

variable {backend : Backend}

/-- Internal output of certificate reconstruction. -/
structure Refinement (backend : Backend) (rate : Nat) (P : Representation backend.memory A) (Q : Representation backend.memory B)
    (p : Program A B) where
  code : backend.Command
  sound : ∀ {a k b}, Run p a k b → ∀ r s saved, P.holds a r s saved →
    ∃ steps t left, backend.Eval code s steps t ∧ Q.holds b r t left ∧ Writes r s t ∧
      steps + left ≤ rate * k + saved

/-- Primitive authors implement a typed abstract operation, including its ownership contract. -/
class Primitive (backend : Backend) (rate : Nat) (P : Representation backend.memory A) (op : Operation A B)
    (Q : outParam (Representation backend.memory B)) where
  code : backend.Command
  correct : ∀ a, op.requires a → ∀ r s saved, P.holds a r s saved →
    ∃ steps t left, backend.Eval code s steps t ∧ Q.holds (op.effect a) r t left ∧ Writes r s t ∧
      steps + left ≤ rate * op.charge a + saved

class TestImplementation (backend : Backend) (rate : Nat) (P : Representation backend.memory A) (test : A → Bool) where
  condition : backend.Condition
  correct : ∀ a r s saved, P.holds a r s saved → backend.test condition s = test a
  cost : backend.testCost condition ≤ rate

/-- Query lifting borrows the selected component and leaves all ownership unchanged. -/
instance [impl : TestImplementation backend rate P test] :
    TestImplementation backend rate (P.sep Q) (testLeft test) where
  condition := impl.condition
  correct a r s saved rep := by
    obtain ⟨r₁, r₂, p₁, p₂, _, _, _, hp, _⟩ := rep
    exact impl.correct a.1 r₁ s p₁ hp
  cost := impl.cost

instance (P : Representation backend.memory A) [impl : TestImplementation backend rate Q test] :
    TestImplementation backend rate (P.sep Q) (testRight test) where
  condition := impl.condition
  correct a r s saved rep := by
    obtain ⟨r₁, r₂, p₁, p₂, _, _, _, _, hq⟩ := rep
    exact impl.correct a.2 r₂ s p₂ hq
  cost := impl.cost

inductive Supported (backend : Backend) (rate : Nat) :
    {A B : Type} → Representation backend.memory A → Representation backend.memory B → Program A B → Type 1 where
  | identity (P) : Supported backend rate P P .identity
  | swap (P : Representation backend.memory A) (Q : Representation backend.memory B) :
      Supported backend rate (P.sep Q) (Q.sep P) .swap
  | invoke (impl : Primitive backend rate P op Q) : Supported backend rate P Q (.invoke op)
  | seq : Supported backend rate P Q p → Supported backend rate Q R q → Supported backend rate P R (.seq p q)
  | frame (h : Supported backend rate P Q p) (F : Representation backend.memory R) :
      Supported backend rate (P.sep F) (Q.sep F) (.frame p _)
  | branch (impl : TestImplementation backend rate P test) : Supported backend rate P Q p → Supported backend rate P Q q →
      Supported backend rate P Q (.branch test p q)
  | loop (impl : TestImplementation backend rate P test) : Supported backend rate P P p →
      Supported backend rate P P (.loop test p)
  | call : Supported backend rate P Q p → Supported backend rate P Q (.call p)

private def identityRef (rate : Nat) (P : Representation backend.memory A) : Refinement backend rate P P .identity where
  code := backend.skip
  sound run r s saved rep := by
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨0, s, saved, backend.skip_sound _, rep, Writes.refl _ _, by omega⟩

private def swapRef (rate : Nat) (P : Representation backend.memory A) (Q : Representation backend.memory B) :
    Refinement backend rate (P.sep Q) (Q.sep P) .swap where
  code := backend.skip
  sound run r s saved rep := by
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨0, s, saved, backend.skip_sound _, (Representation.sep_comm P Q).mp rep, Writes.refl _ _, by omega⟩

private def invokeRef (impl : Primitive backend rate P op Q) : Refinement backend rate P Q (.invoke op) where
  code := impl.code
  sound run r s saved rep := by
    obtain ⟨safe, rfl, rfl⟩ := run
    exact impl.correct _ safe r s saved rep

private def seqRef (f : Refinement backend rate P Q p) (g : Refinement backend rate Q R q) :
    Refinement backend rate P R (.seq p q) where
  code := backend.seq f.code g.code
  sound run r s saved rep := by
    obtain ⟨_, _, _, hp, hq, rfl⟩ := run
    obtain ⟨i, t, left, he, hr, hw, hc⟩ := f.sound hp r s saved rep
    obtain ⟨j, u, last, hf, hs, hv, hd⟩ := g.sound hq r t left hr
    exact ⟨i + j, u, last, backend.seq_sound he hf, hs, hw.trans hv, by nlinarith⟩

private def frameRef (f : Refinement backend rate P Q p) (F : Representation backend.memory R) :
    Refinement backend rate (P.sep F) (Q.sep F) (.frame p _) where
  code := f.code
  sound run r s saved rep := by
    obtain ⟨hp, equal⟩ := run
    obtain ⟨r₁, r₂, p₁, p₂, hd, rfl, rfl, hP, hF⟩ := rep
    obtain ⟨i, t, left, he, hQ, hw, hc⟩ := f.sound hp r₁ s p₁ hP
    exact ⟨i, t, left + p₂, he, ⟨r₁, r₂, left, p₂, hd, rfl, rfl, hQ, equal ▸ F.frame hF hd hw⟩,
      hw.mono Finset.subset_union_left, by omega⟩

private def branchRef (impl : TestImplementation backend rate P test)
    (f : Refinement backend rate P Q p) (g : Refinement backend rate P Q q) :
    Refinement backend rate P Q (.branch test p q) where
  code := backend.branch impl.condition f.code g.code
  sound := by
    intro a k b run r s saved rep
    obtain ⟨i, rfl, hp⟩ := run
    cases ht : test a with
    | true =>
      obtain ⟨i, t, left, he, hr, hw, hc⟩ :=
        f.sound (a := a) (k := i) (b := b) (by simpa [ht] using hp) r s saved rep
      exact ⟨_, t, left, backend.ifTrue_sound ((impl.correct _ _ _ _ rep).trans ht) he, hr, hw,
        by have := impl.cost; nlinarith⟩
    | false =>
      obtain ⟨i, t, left, he, hr, hw, hc⟩ :=
        g.sound (a := a) (k := i) (b := b) (by simpa [ht] using hp) r s saved rep
      exact ⟨_, t, left, backend.ifFalse_sound ((impl.correct _ _ _ _ rep).trans ht) he, hr, hw,
        by have := impl.cost; nlinarith⟩

private def loopRef (impl : TestImplementation backend rate P test) (f : Refinement backend rate P P p) :
    Refinement backend rate P P (.loop test p) where
  code := backend.loop impl.condition f.code
  sound := by
    intro a k b run r s saved rep
    have go : ∀ k a b, Run (.loop test p) a k b → ∀ s saved, P.holds a r s saved →
        ∃ steps t left, backend.Eval (backend.loop impl.condition f.code) s steps t ∧
          P.holds b r t left ∧ Writes r s t ∧ steps + left ≤ rate * k + saved := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro a b run s saved rep
        cases run with
        | done ht =>
          exact ⟨_, s, saved, backend.whileFalse_sound ((impl.correct _ _ _ _ rep).trans ht), rep,
            Writes.refl _ _, by have := impl.cost; omega⟩
        | @step _ i _ j _ ht hb hl =>
          obtain ⟨steps, t, left, he, hr, hw, hc⟩ := f.sound hb r s saved rep
          obtain ⟨steps', u, last, hf, hs, hv, hd⟩ := ih j (by omega) _ _ hl t left hr
          exact ⟨_, u, last, backend.whileTrue_sound ((impl.correct _ _ _ _ rep).trans ht) he hf,
            hs, hw.trans hv, by have := impl.cost; nlinarith⟩
    exact go k a b run s saved rep

private def callRef (f : Refinement backend rate P Q p) : Refinement backend rate P Q (.call p) where
  code := f.code
  sound run r s saved rep := by
    exact f.sound run r s saved rep

/-- Total structural reconstruction; no client-specific translation proof occurs. -/
def Supported.compile : Supported backend rate P Q p → Refinement backend rate P Q p
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
def Supported.code : Supported backend rate P Q p → backend.Command
  | .identity _ => backend.skip
  | .swap _ _ => backend.skip
  | .invoke impl => impl.code
  | .seq f g => backend.seq f.code g.code
  | .frame f _ => f.code
  | .branch impl f g => backend.branch impl.condition f.code g.code
  | .loop impl f => backend.loop impl.condition f.code
  | .call f => f.code

/-- Certificate erasure returns exactly the existing verified compilation's code. -/
theorem Supported.compile_code (h : Supported backend rate P Q p) : h.compile.code = h.code := by
  induction h <;> simp_all [Supported.compile, Supported.code, identityRef, swapRef,
    invokeRef, seqRef, frameRef, branchRef, loopRef, callRef]

/-- Interpretation preserves sequential composition at the generated-code level. -/
theorem Supported.compile_seq (f : Supported backend rate P Q p) (g : Supported backend rate Q R q) :
    (Supported.seq f g).compile.code = backend.seq f.compile.code g.compile.code := rfl

/-- Framing changes no executable code and introduces no runtime copying. -/
theorem Supported.compile_frame (f : Supported backend rate P Q p) (F : Representation backend.memory R) :
    (Supported.frame f F).compile.code = f.compile.code := rfl

/-- Different certified calibrations can be embedded in a common calibration. -/
def Refinement.weaken (f : Refinement backend rate P Q p) (larger : rate ≤ rate') :
    Refinement backend rate' P Q p where
  code := f.code
  sound h r s saved rep := by
    obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := f.sound h r s saved rep
    exact ⟨steps, t, left, exec, hQ, hw, hc.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ larger) _)⟩

/-- A common conversion rate is inferred using max; private potentials still telescope. -/
def Refinement.compose (f : Refinement backend rate P Q p) (g : Refinement backend rate' Q R q) :
    Refinement backend (max rate rate') P R (.seq p q) :=
  seqRef (f.weaken (Nat.le_max_left _ _)) (g.weaken (Nat.le_max_right _ _))

/-- Type-directed linking is indexed by the exact program and its ownership interfaces. -/
class Linked (backend : Backend) (rate : Nat) (P : Representation backend.memory A) (p : Program A B)
    (Q : outParam (Representation backend.memory B)) where
  supported : Supported backend rate P Q p

instance : Linked backend rate P .identity P := ⟨.identity P⟩
instance (P : Representation backend.memory A) (Q : Representation backend.memory B) :
    Linked backend rate (P.sep Q) .swap (Q.sep P) := ⟨.swap P Q⟩
instance [i : Primitive backend rate P op Q] : Linked backend rate P (.invoke op) Q := ⟨.invoke i⟩
instance [f : Linked backend rate P p Q] [g : Linked backend rate Q q R] : Linked backend rate P (.seq p q) R :=
  ⟨.seq f.supported g.supported⟩
instance [f : Linked backend rate P p Q] : Linked backend rate (P.sep F) (.frame p _) (Q.sep F) :=
  ⟨.frame f.supported F⟩
instance [i : TestImplementation backend rate P test] [f : Linked backend rate P p Q] [g : Linked backend rate P q Q] :
    Linked backend rate P (.branch test p q) Q := ⟨.branch i f.supported g.supported⟩
instance [i : TestImplementation backend rate P test] [f : Linked backend rate P p P] :
    Linked backend rate P (.loop test p) P := ⟨.loop i f.supported⟩
instance [f : Linked backend rate P p Q] : Linked backend rate P (.call p) Q := ⟨.call f.supported⟩

end AlgoLib.Experimental.RAM.Ownership
