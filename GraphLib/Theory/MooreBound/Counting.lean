/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting lemmas for the Moore bounds

Two purely set-theoretic counting lemmas. Neither mentions a graph: they are the
skeleton on which both Moore bounds are built, and they live in `GraphLib.Set`
so that the graph development can stay free of ad-hoc cardinality reasoning.

## Main results

* `GraphLib.Set.ncard_biUnion_finset_eq_sum` — the size of a disjoint finite union is the
  sum of the sizes.
* `GraphLib.Set.mul_ncard_le_ncard_of_children` — if every element of `L` owns at least `k`
  elements of `N`, and distinct elements own disjoint sets, then `k * |L| ≤ |N|`.
-/

namespace GraphLib

namespace Set

lemma ncard_biUnion_finset_eq_sum {ι β : Type*} (s : Finset ι)
    (f : ι → Set β)
    (hfin : ∀ i ∈ s, (f i).Finite)
    (hdisj : ∀ ⦃i j : ι⦄, i ∈ s → j ∈ s → i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  have h := _root_.Set.Finite.ncard_biUnion s.finite_toSet (s := f)
    (fun i hi => hfin i (by simpa using hi))
    (fun i hi j hj hij => hdisj (by simpa using hi) (by simpa using hj) hij)
  rwa [finsum_mem_coe_finset] at h

/-- Counting skeleton: if every element of a finite set `L` has a "child set" `F v` of size
at least `k` inside `N`, and distinct elements have disjoint child sets, then
`k * |L| ≤ |N|`. Purely set-theoretic; no graph theory is involved. -/
lemma mul_ncard_le_ncard_of_children {β : Type*} {L N : Set β} {F : β → Set β} {k : ℕ}
    (hLfin : L.Finite) (hNfin : N.Finite)
    (hFsub : ∀ v ∈ L, F v ⊆ N)
    (hFcard : ∀ v ∈ L, k ≤ (F v).ncard)
    (hFdisj : ∀ ⦃v v' : β⦄, v ∈ L → v' ∈ L → v ≠ v' → Disjoint (F v) (F v')) :
    k * L.ncard ≤ N.ncard := by
  classical
  have hFfin : ∀ v ∈ L, (F v).Finite := fun v hv => hNfin.subset (hFsub v hv)
  have hbUsub : (⋃ v ∈ hLfin.toFinset, F v) ⊆ N :=
    Set.iUnion_subset fun v => Set.iUnion_subset fun hv => hFsub v (by simpa using hv)
  have hsum := ncard_biUnion_finset_eq_sum hLfin.toFinset F
    (fun v hv => hFfin v (by rwa [Set.Finite.mem_toFinset] at hv))
    (fun v v' hv hv' hne => hFdisj (by rwa [Set.Finite.mem_toFinset] at hv)
      (by rwa [Set.Finite.mem_toFinset] at hv') hne)
  have hle_sum : ∑ _v ∈ hLfin.toFinset, k ≤ ∑ v ∈ hLfin.toFinset, (F v).ncard :=
    Finset.sum_le_sum (fun v hv => hFcard v (by rwa [Set.Finite.mem_toFinset] at hv))
  have hconst : ∑ _v ∈ hLfin.toFinset, k = k * L.ncard := by
    rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card _ hLfin, mul_comm]
  calc k * L.ncard
      = ∑ _v ∈ hLfin.toFinset, k := hconst.symm
    _ ≤ ∑ v ∈ hLfin.toFinset, (F v).ncard := hle_sum
    _ = (⋃ v ∈ hLfin.toFinset, F v).ncard := hsum.symm
    _ ≤ N.ncard := Set.ncard_le_ncard hbUsub hNfin

end Set

end GraphLib
