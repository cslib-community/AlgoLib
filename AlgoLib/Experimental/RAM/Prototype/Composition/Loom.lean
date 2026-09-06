/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts
import AlgoLib.Experimental.RAM.Prototype.LoomObservation

/-!
# Composition-preserving interpretation in actual Loom

The same typed client has a finite costed interpretation in Loom's existing
MAlgOrdered instance. Identity and sequencing commute with interpretation.
Logical VCs establish upstream WP. No RAM representation or potential occurs here.
Credit belongs to Loom's authors for the algebra/WP infrastructure; we reuse it.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- Owned values are typed arguments/results; Unit is the ambient computation state. -/
def denote (p : Program A B) (a : A) : Computation Unit B := fun _ k _ b => Run p a k b

theorem denote_identity (a : A) : denote (.identity : Program A A) a = Computation.pure a := by
  funext s k t b
  cases s; cases t
  apply propext
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, _, rfl⟩
    exact Run.identity _

theorem denote_seq (p : Program A B) (q : Program B C) (a : A) :
    denote (.seq p q) a = Computation.bind (denote p a) (denote q) := by
  funext s k t b
  apply propext
  constructor
  · intro h
    obtain ⟨i, v, j, hp, hq, rfl⟩ := h
    exact ⟨i, (), v, j, hp, hq, rfl⟩
  · rintro ⟨i, _, v, j, hp, hq, rfl⟩
    exact Run.seq hp hq

/-- Associativity is inherited from the existing, proved observation law. -/
theorem denote_assoc (p : Program A B) (q : Program B C) (r : Program C D) (a : A) :
    denote (.seq (.seq p q) r) a = denote (.seq p (.seq q r)) a := by
  simp only [denote_seq, Computation.bind_assoc]
  congr 1
  funext b
  exact (denote_seq q r b).symm

/-- The existing Loom WP receives the generated mathematical obligations. -/
theorem VC.loom (p : Program A B) (post : B → Nat → Prop) (a : A) (budget : Nat)
    (proof : VC p post a budget) :
    _root_.wp (denote p a) (fun b _ c => post b c) () budget := by
  rw [loom_wp_eq]
  obtain ⟨k, b, run, hk, hQ⟩ := VC.sound p post a budget proof
  exact ⟨k, (), b, run, hk, hQ⟩

/-- Contract-directed obligations establish actual Loom WP for the same body. -/
theorem Algorithm.loom_correct (m : Algorithm A B) (proof : m.Obligations)
    (a : A) (valid : m.requires a) :
    _root_.wp (denote m.body a) (fun b _ _ => m.ensures a b) () (m.credits a) := by
  rw [loom_wp_eq]
  obtain ⟨k, b, run, post, paid⟩ := (m.certify proof).correct a valid
  exact ⟨k, (), b, run, paid, post⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
