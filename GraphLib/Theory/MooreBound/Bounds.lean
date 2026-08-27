/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Theory.MooreBound.HalfLayers

/-!
# The Moore bounds

The two counting theorems themselves. Everything they stand on lives in the other
files of the `MooreBound` folder; see the umbrella module
`GraphLib.Theory.MooreBound`.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

open MooreBound

/-! ## The Moore bounds -/

/-- Odd-girth version of the Moore bound. -/
theorem mooreBound_odd (G : SimpleGraph α) (δ r : ℕ)
    [Finite V(G)]
    [Fintype E(G)] [DecidableEq α]
    (hne : V(G).Nonempty)
    (hmin : ∀ v : α, v ∈ V(G) → δ ≤ G.degree v)
    (hgirth : (2 * r + 1 : ℕ∞) ≤ G.girth) :
    1 + δ * (∑ i ∈ Finset.range r, (δ - 1) ^ i) ≤ V(G).ncard := by
  have hV : V(G).Finite := G.vertexSet_finite
  obtain ⟨x, hx⟩ := hne
  -- any index sum that is at most `2 * r` stays strictly below the girth
  have hlt_girth : ∀ n : ℕ, n ≤ 2 * r → (n : ℕ∞) < G.girth := by
    intro n hn
    have hn' : (n : ℕ∞) ≤ (2 * r : ℕ∞) := by exact_mod_cast hn
    have hr_lt : (2 * r : ℕ∞) < (2 * r + 1 : ℕ∞) := by
      exact_mod_cast Nat.lt_succ_self (2 * r)
    exact hn'.trans_lt (hr_lt.trans_le hgirth)
  -- the layers `0, 1, …, r` are pairwise disjoint
  have hdisj : ∀ ⦃i j : ℕ⦄, i ∈ Finset.range (r + 1) → j ∈ Finset.range (r + 1) →
      i ≠ j → Disjoint (rootLayer G x i) (rootLayer G x j) := by
    intro i j hi hj hij
    rw [Finset.mem_range] at hi hj
    exact disjoint_rootLayer_of_ne_of_lt_girth G hij (hlt_girth _ (by omega))
  have hsum_eq := Set.ncard_biUnion_finset_eq_sum (Finset.range (r + 1))
    (fun i => rootLayer G x i)
    (fun i _ => hV.subset (rootLayer_subset_vertexSet G x i)) hdisj
  -- the union of the layers is contained in the vertex set
  have hsub : (⋃ i ∈ Finset.range (r + 1), rootLayer G x i) ⊆ V(G) := by
    exact Set.iUnion_subset fun i => Set.iUnion_subset fun _ =>
      rootLayer_subset_vertexSet G x i
  have hcard_le : ∑ i ∈ Finset.range (r + 1), (rootLayer G x i).ncard ≤ V(G).ncard := by
    rw [← hsum_eq]; exact Set.ncard_le_ncard hsub hV
  -- lower bound each nonzero layer
  have hsum_lb : δ * (∑ i ∈ Finset.range r, (δ - 1) ^ i) ≤
      ∑ i ∈ Finset.range r, (rootLayer G x (i + 1)).ncard := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum
      (fun i hi => le_ncard_rootLayer_succ G hx hmin (by
        have hi' : i < r := Finset.mem_range.mp hi
        exact_mod_cast hlt_girth (2 * (i + 1)) (by omega)))
  have hsplit : ∑ i ∈ Finset.range (r + 1), (rootLayer G x i).ncard
      = (∑ i ∈ Finset.range r, (rootLayer G x (i + 1)).ncard) + (rootLayer G x 0).ncard :=
    Finset.sum_range_succ' (fun i => (rootLayer G x i).ncard) r
  calc 1 + δ * (∑ i ∈ Finset.range r, (δ - 1) ^ i)
      ≤ 1 + ∑ i ∈ Finset.range r, (rootLayer G x (i + 1)).ncard := by omega
    _ = (rootLayer G x 0).ncard + ∑ i ∈ Finset.range r, (rootLayer G x (i + 1)).ncard := by
        rw [ncard_rootLayer_zero G hx]
    _ = ∑ i ∈ Finset.range (r + 1), (rootLayer G x i).ncard := by rw [hsplit]; omega
    _ ≤ V(G).ncard := hcard_le

/-- Even-girth version of the Moore bound. -/
theorem mooreBound_even (G : SimpleGraph α) (δ r : ℕ)
    [Finite V(G)]
    [Fintype E(G)] [DecidableEq α]
    (hne : V(G).Nonempty)
    (hδ : 2 ≤ δ)
    (hmin : ∀ v : α, v ∈ V(G) → δ ≤ G.degree v)
    (hgirth : (2 * r : ℕ∞) ≤ G.girth) :
    2 * (∑ i ∈ Finset.range r, (δ - 1) ^ i) ≤ V(G).ncard := by
  classical
  have hV : V(G).Finite := G.vertexSet_finite
  -- a central edge `x -- y`
  have hmin2 : ∀ v : α, v ∈ V(G) → 2 ≤ G.degree v :=
    fun v hv => le_trans hδ (hmin v hv)
  obtain ⟨x, y, hxy⟩ := exists_adj_of_nonempty_of_two_le_degree G hne hmin2
  -- any index below `2 * r` stays strictly below the girth
  have hlt_girth : ∀ n : ℕ, n < 2 * r → (n : ℕ∞) < G.girth := by
    intro n hn
    have hn' : (n : ℕ∞) < (2 * r : ℕ∞) := by exact_mod_cast hn
    exact hn'.trans_le hgirth
  -- two half-trees grown from the ends of the edge
  have hSideDisj : ∀ (a b : α) ⦃i j : ℕ⦄,
      i ∈ Finset.range r → j ∈ Finset.range r → i ≠ j →
        Disjoint (halfLayer G a b i) (halfLayer G a b j) := by
    intro a b i j hi hj hij
    rw [Finset.mem_range] at hi hj
    exact disjoint_halfLayer_of_ne_of_lt_girth G hij (hlt_girth _ (by omega))
  have hAdisj : ∀ ⦃i j : ℕ⦄, i ∈ Finset.range r → j ∈ Finset.range r → i ≠ j →
      Disjoint (halfLayer G x y i) (halfLayer G x y j) := hSideDisj x y
  have hBdisj : ∀ ⦃i j : ℕ⦄, i ∈ Finset.range r → j ∈ Finset.range r → i ≠ j →
      Disjoint (halfLayer G y x i) (halfLayer G y x j) := hSideDisj y x
  have hSideSub : ∀ a b : α, (⋃ i ∈ Finset.range r, halfLayer G a b i) ⊆ V(G) := by
    intro a b
    exact Set.iUnion_subset fun i => Set.iUnion_subset fun _ =>
      halfLayer_subset_vertexSet G a b i
  have hAsub : (⋃ i ∈ Finset.range r, halfLayer G x y i) ⊆ V(G) := hSideSub x y
  have hBsub : (⋃ i ∈ Finset.range r, halfLayer G y x i) ⊆ V(G) := hSideSub y x
  have hAfin := hV.subset hAsub
  have hBfin := hV.subset hBsub
  -- the two half-trees are disjoint from each other
  have hABdisj : Disjoint (⋃ i ∈ Finset.range r, halfLayer G x y i)
      (⋃ i ∈ Finset.range r, halfLayer G y x i) := by
    rw [Set.disjoint_left]
    intro v hvA hvB
    simp only [Set.mem_iUnion, exists_prop] at hvA hvB
    obtain ⟨i, hi, hvi⟩ := hvA
    obtain ⟨j, hj, hvj⟩ := hvB
    rw [Finset.mem_range] at hi hj
    exact Set.disjoint_left.mp
      (disjoint_halfLayer_opposite_of_lt_girth G hxy (hlt_girth _ (by omega))) hvi hvj
  -- lower bounds on the two half-trees
  have hSideLb : ∀ {a b : α}, G.Adj a b →
      (∑ i ∈ Finset.range r, (δ - 1) ^ i) ≤
        (⋃ i ∈ Finset.range r, halfLayer G a b i).ncard := by
    intro a b hab
    rw [Set.ncard_biUnion_finset_eq_sum (Finset.range r) (fun i => halfLayer G a b i)
      (fun i _ => hV.subset (halfLayer_subset_vertexSet G a b i)) (hSideDisj a b)]
    exact Finset.sum_le_sum
      (fun i hi => le_ncard_halfLayer G hab hmin (by
        have hi' : i < r := Finset.mem_range.mp hi
        exact_mod_cast hlt_girth (2 * i) (by omega)))
  have hAlb := hSideLb hxy
  have hBlb := hSideLb hxy.symm
  have hABsub : (⋃ i ∈ Finset.range r, halfLayer G x y i) ∪
      (⋃ i ∈ Finset.range r, halfLayer G y x i) ⊆ V(G) := Set.union_subset hAsub hBsub
  calc 2 * (∑ i ∈ Finset.range r, (δ - 1) ^ i)
      = (∑ i ∈ Finset.range r, (δ - 1) ^ i) + (∑ i ∈ Finset.range r, (δ - 1) ^ i) := by
        rw [two_mul]
    _ ≤ (⋃ i ∈ Finset.range r, halfLayer G x y i).ncard +
        (⋃ i ∈ Finset.range r, halfLayer G y x i).ncard := Nat.add_le_add hAlb hBlb
    _ = ((⋃ i ∈ Finset.range r, halfLayer G x y i) ∪
        (⋃ i ∈ Finset.range r, halfLayer G y x i)).ncard :=
        (Set.ncard_union_eq hABdisj hAfin hBfin).symm
    _ ≤ V(G).ncard := Set.ncard_le_ncard hABsub hV

end SimpleGraph

end GraphLib
