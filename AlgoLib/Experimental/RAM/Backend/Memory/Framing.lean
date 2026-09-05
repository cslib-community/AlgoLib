/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Verification
import Mathlib.Tactic

/-!
# Reusable physical framing

Proves that writes outside a read footprint preserve an assertion, and composes these facts into
functional and cost contracts.

Concrete representations supply footprint and disjointness evidence once. Algorithm-level
unchanged fields are handled separately by logical substitution.

## Further details

# Reusable footprint framing

Library representations declare which addresses they read. A mutation certifies
which addresses it may write. Disjointness then frames *any* such representation,
including conjunctions, without unfolding its invariant. This is a footprint
rule, not a claim to implement a complete separation-logic ownership solver.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language.Framing

abbrev Heap := Nat → Nat

/-- An upper bound on changed cells; it is safe to overapproximate it. -/
def WritesOnly (W : Set Nat) (before after : Heap) : Prop :=
  ∀ p, p ∉ W → after p = before p

/-- An assertion's truth depends only on its declared footprint. -/
def ReadsOnly (R : Set Nat) (P : Heap → Prop) : Prop :=
  ∀ before after, (∀ p ∈ R, after p = before p) → P before → P after

theorem frame {R W : Set Nat} {P : Heap → Prop} {before after : Heap}
    (reads : ReadsOnly R P) (writes : WritesOnly W before after)
    (separate : Disjoint R W) (h : P before) : P after := by
  apply reads before after _ h
  intro p hp
  exact writes p (fun hw => (Set.disjoint_left.mp separate) hp hw)

theorem ReadsOnly.and {R S : Set Nat} {P Q : Heap → Prop}
    (p : ReadsOnly R P) (q : ReadsOnly S Q) : ReadsOnly (R ∪ S) (fun m => P m ∧ Q m) := by
  intro m n h hn
  exact ⟨p m n (fun x hx => h x (Or.inl hx)) hn.1,
    q m n (fun x hx => h x (Or.inr hx)) hn.2⟩

theorem WritesOnly.seq {W V : Set Nat} {a b c : Heap}
    (h : WritesOnly W a b) (k : WritesOnly V b c) : WritesOnly (W ∪ V) a c := by
  intro p hp
  exact (k p (fun hv => hp (Or.inr hv))).trans (h p (fun hw => hp (Or.inl hw)))

theorem write (m : Heap) (p v : Nat) : WritesOnly {p} m (Function.update m p v) := by
  intro q hq
  exact Function.update_of_ne hq _ _

/-- Automatic framing for one symbolic heap update. The caller supplies only
footprint disjointness; the represented data structure is never expanded. -/
theorem frame_write {R : Set Nat} {P : Heap → Prop} (reads : ReadsOnly R P)
    {m : Heap} {p v : Nat} (outside : p ∉ R) (h : P m) : P (Function.update m p v) := by
  apply frame reads (write m p v) _ h
  rw [Set.disjoint_left]
  intro x hx he
  exact outside ((Set.mem_singleton_iff.mp he) ▸ hx)

/-- Cellwise representations, such as arrays and graph tables, register one
read-footprint contract and receive all future frame proofs from it. -/
theorem cells (R : Set Nat) (value : Nat → Nat) :
    ReadsOnly R (fun m => ∀ p ∈ R, m p = value p) := by
  intro m n he h p hp
  exact (he p hp).trans (h p hp)

/-- Frame an entire functional/time contract. The preserved assertion and the
original postcondition compose without changing the procedure's budget. -/
theorem frame_contract {c : Cmd} {P : Store → Prop} {Q : Store → Store → Prop}
    {budget : Store → Nat} {W : Store → Set Nat} {R : Set Nat} {F : Heap → Prop}
    (contract : Contract c P (fun s t => Q s t ∧ WritesOnly (W s) s.heap t.heap) budget)
    (reads : ReadsOnly R F) (separate : ∀ s, P s → Disjoint R (W s)) :
    Contract c (fun s => P s ∧ F s.heap) (fun s t => Q s t ∧ F t.heap) budget := by
  intro s hs
  obtain ⟨k, t, ht, hQ, hk⟩ := contract s hs.1
  exact ⟨k, t, ht, ⟨hQ.1, frame reads hQ.2 (separate s hs.1) hs.2⟩, hk⟩

end AlgoLib.Experimental.RAM.Checked.Language.Framing
