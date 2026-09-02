/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import AlgoLib.Theory.Graph.Structures.SimpleGraph_only.MooreBound.Core

/-!
# Moore bounds: the rooted layers

The breadth-first layers around a root vertex: `IsRootedPath` (a path of a given
length from the root), the layer `rootLayer` it cuts out, and the growth estimate
that makes successive layers multiply by `δ - 1`. This is the family behind the
odd Moore bound.

Part of the `MooreBound` folder; see the umbrella module
`AlgoLib.Theory.Structures.SimpleGraph_only.MooreBound`.
-/

variable {α : Type*}

namespace AlgoLib

open scoped AlgoLib

namespace SimpleGraph

namespace MooreBound

/-! ## Rooted layers -/

/-- A vertex `v` is reached from the root `x` by a realized simple path of
length `i`. -/
@[grind] def IsRootedPath (G : SimpleGraph α) (x : α) (i : ℕ) (v : α) : Prop :=
  ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.head = x ∧ p.tail = v ∧ p.length = i

namespace IsRootedPath

/-- A chosen path witnessing a rooted path. -/
noncomputable def path {G : SimpleGraph α} {x v : α} {i : ℕ}
    (h : IsRootedPath G x i v) : SimplePath α :=
  Classical.choose h

/-- The chosen witness path for a rooted path is realized in the graph. -/
lemma path_isSimplePathIn {G : SimpleGraph α} {x v : α} {i : ℕ}
    (h : IsRootedPath G x i v) : G.IsSimplePathIn h.path :=
  (Classical.choose_spec h).1

/-- The chosen witness path for a rooted path starts at the root. -/
lemma path_head {G : SimpleGraph α} {x v : α} {i : ℕ}
    (h : IsRootedPath G x i v) : h.path.head = x :=
  (Classical.choose_spec h).2.1

/-- The chosen witness path for a rooted path ends at the endpoint. -/
lemma path_tail {G : SimpleGraph α} {x v : α} {i : ℕ}
    (h : IsRootedPath G x i v) : h.path.tail = v :=
  (Classical.choose_spec h).2.2.1

/-- The chosen witness path for a rooted path has the prescribed length. -/
lemma path_length {G : SimpleGraph α} {x v : α} {i : ℕ}
    (h : IsRootedPath G x i v) : h.path.length = i :=
  (Classical.choose_spec h).2.2.2

/-- The root of a rooted path is a vertex of the ambient graph. -/
@[grind →] lemma head_mem (G : SimpleGraph α) {x v : α} {i : ℕ}
    (h : IsRootedPath G x i v) : x ∈ V(G) := by
  obtain ⟨p, hp, hhead, _, _⟩ := h
  rw [← hhead]
  exact IsSimpleWalkIn.head_mem G hp

/-- The endpoint of a rooted path is a vertex of the ambient graph. -/
@[grind →] lemma tail_mem (G : SimpleGraph α) {x v : α} {i : ℕ}
    (h : IsRootedPath G x i v) : v ∈ V(G) := by
  obtain ⟨p, hp, _, htail, _⟩ := h
  rw [← htail]
  exact IsSimpleWalkIn.tail_mem G hp

/-- The singleton path witnesses a rooted path of length zero. -/
lemma singleton (G : SimpleGraph α) {x : α} (hx : x ∈ V(G)) :
    IsRootedPath G x 0 x :=
  ⟨SimplePath.singleton x, IsSimplePathIn.singleton G hx, rfl, rfl, rfl⟩

/-- Extending a rooted path by a fresh adjacent vertex gives a rooted path in
the next layer. -/
lemma succ_of_adj_not_mem (G : SimpleGraph α) {x v u : α} {i : ℕ}
    (h : IsRootedPath G x i v) (hadj : G.Adj v u)
    (hnot : u ∉ h.path.vertices) :
    IsRootedPath G x (i + 1) u := by
  have hdisj : ∀ z : α, z ∈ h.path.vertices →
      z ∈ (SimplePath.singleton u).vertices → False := by
    grind
  have hstep : G.Adj h.path.tail (SimplePath.singleton u).head := by
    simpa only [SimplePath.head_singleton, h.path_tail] using hadj
  refine ⟨h.path.append (SimplePath.singleton u) hdisj,
    IsSimpleWalkIn.append G h.path_isSimplePathIn
      (IsSimplePathIn.singleton G hadj.right_mem) hstep, ?_, ?_, ?_⟩ <;>
    simp [h.path_head, h.path_length]

end IsRootedPath

/-- The vertices reached from `x` by realized simple paths of length `i`. -/
def rootLayer (G : SimpleGraph α) (x : α) (i : ℕ) : Set α :=
  {v | IsRootedPath G x i v}

/-- Membership in a rooted layer is witnessed by a realized rooted path of the
prescribed length. -/
@[simp, grind =] lemma mem_rootLayer (G : SimpleGraph α) {x v : α} {i : ℕ} :
    v ∈ rootLayer G x i ↔ IsRootedPath G x i v := Iff.rfl

/-- Every rooted layer is contained in the ambient vertex set. -/
lemma rootLayer_subset_vertexSet (G : SimpleGraph α) (x : α) (i : ℕ) :
    rootLayer G x i ⊆ V(G) := by grind

/-- The zero-th rooted layer is the singleton root. -/
@[simp] lemma rootLayer_zero (G : SimpleGraph α) {x : α} (hx : x ∈ V(G)) :
    rootLayer G x 0 = {x} := by
  ext v; constructor
  · grind
  · grind[IsRootedPath.singleton]

/-- The zero-th rooted layer has one vertex. -/
lemma ncard_rootLayer_zero (G : SimpleGraph α) {x : α} (hx : x ∈ V(G)) :
    (rootLayer G x 0).ncard = 1 := by grind [Set.ncard_singleton,rootLayer_zero]

/-! ## Neighbours and the first rooted layer -/

/-- The neighbours of `x` inject into the first rooted layer at `x`. -/
lemma neighborSet_subset_rootLayer_one (G : SimpleGraph α) {x : α} (hx : x ∈ V(G)) :
    G.neighborSet x ⊆ rootLayer G x 1 := by
  intro u hu
  have hxu : G.Adj x u := hu.symm
  have hdisj : ∀ z : α, z ∈ (SimplePath.singleton x).vertices →
      z ∈ (SimplePath.singleton u).vertices → False := by
    grind
  refine ⟨(SimplePath.singleton x).append (SimplePath.singleton u) hdisj,
    IsSimpleWalkIn.append G (IsSimplePathIn.singleton G hx)
      (IsSimplePathIn.singleton G hxu.right_mem) hxu, ?_, ?_, ?_⟩ <;>
    simp

/-- The first rooted layer has at least the degree of the root. -/
lemma degree_le_ncard_rootLayer_one (G : SimpleGraph α) (hV : V(G).Finite)
    {x : α} (hx : x ∈ V(G)) :
    G.degree x ≤ (rootLayer G x 1).ncard := by
  have hroot_fin : (rootLayer G x 1).Finite :=
    hV.subset (rootLayer_subset_vertexSet G x 1)
  simpa [degree] using
    Set.ncard_le_ncard (neighborSet_subset_rootLayer_one G hx) hroot_fin

/-! ## Odd rooted-layer counting -/

/-- Distinct rooted layers are disjoint when the sum of their indices is below
the girth. -/
lemma disjoint_rootLayer_of_ne_of_lt_girth (G : SimpleGraph α) {x : α} {i j : ℕ}
    (hij : i ≠ j) (hgirth : (((i + j : ℕ) : ℕ∞)) < G.girth) :
    Disjoint (rootLayer G x i) (rootLayer G x j) := by
  classical
  rw [Set.disjoint_left]
  intro v hvi hvj
  obtain ⟨p, hp, hpx, hpv, hplen⟩ := hvi
  obtain ⟨q, hq, hqx, hqv, hqlen⟩ := hvj
  have hne : p.vertices ≠ q.vertices := fun hvertices => hij (by
    rw [← hplen, ← hqlen]; exact congrArg VertexSeq.length hvertices)
  obtain ⟨c, hc, hcle⟩ := IsSimpleCycleIn.exists_length_le_add_of_two_paths G hp hq
    (hpx.trans hqx.symm) (hpv.trans hqv.symm) hne
  have hlong := girth.lt_cycle_length G hc hgirth
  omega

/-- Successive odd Moore layers grow by a factor of at least `δ - 1` after the
first layer. -/
lemma mul_ncard_rootLayer_le_succ_of_lt_girth (G : SimpleGraph α)
    (hV : V(G).Finite) {δ i : ℕ} {x : α}
    (hmin : ∀ v : α, v ∈ V(G) → δ ≤ G.degree v)
    (hgirth : (2 * (i + 2) : ℕ∞) < G.girth) :
    (δ - 1) * (rootLayer G x (i + 1)).ncard ≤
      (rootLayer G x (i + 2)).ncard := by
  classical
  have hLfin : (rootLayer G x (i + 1)).Finite :=
    hV.subset (rootLayer_subset_vertexSet G x (i + 1))
  have hNfin : (rootLayer G x (i + 2)).Finite :=
    hV.subset (rootLayer_subset_vertexSet G x (i + 2))
  -- child set: the fresh neighbours of a chosen witness path for `v`
  set F : α → Set α := fun v =>
    if h : IsRootedPath G x (i + 1) v then freshNeighborSet G h.path else ∅ with hFdef
  have hFv : ∀ v, (hv : IsRootedPath G x (i + 1) v) →
      F v = freshNeighborSet G hv.path := by
    intro v hv; simp only [hFdef, dif_pos hv]
  have hgirth' : (2 * (((i + 1 : ℕ) : ℕ∞) + 1)) < G.girth := by
    push_cast; convert hgirth using 2
  refine Set.mul_ncard_le_ncard_of_children (F := F) hLfin hNfin ?_ ?_ ?_
  · -- children lie in the next layer
    intro v hv u hu
    have hvR : IsRootedPath G x (i + 1) v := hv
    rw [hFv v hvR] at hu
    obtain ⟨hadj, hnot⟩ := hu
    exact IsRootedPath.succ_of_adj_not_mem G hvR (hvR.path_tail ▸ hadj) hnot
  · -- each child set has at least `δ - 1` elements
    intro v hv
    have hvR : IsRootedPath G x (i + 1) v := hv
    rw [hFv v hvR]
    exact pred_le_ncard_freshNeighborSet G hV hmin hvR.path_isSimplePathIn
      hvR.path_tail hvR.path_length (by omega) hgirth'
  · -- distinct source vertices produce disjoint child sets: a common fresh neighbour
    -- would give two distinct length-`(i+2)` paths from `x` to it
    intro v v' hv hv' hne
    rw [Set.disjoint_left]
    intro u hu hu'
    have hvR : IsRootedPath G x (i + 1) v := hv
    have hv'R : IsRootedPath G x (i + 1) v' := hv'
    rw [hFv v hvR] at hu
    rw [hFv v' hv'R] at hu'
    obtain ⟨hadj, hnot⟩ := hu
    obtain ⟨hadj', hnot'⟩ := hu'
    exact false_of_two_paths_of_common_fresh_neighbor G
      hvR.path_isSimplePathIn hv'R.path_isSimplePathIn hvR.path_head hv'R.path_head
      hvR.path_length hv'R.path_length
      (by rw [hvR.path_tail, hv'R.path_tail]; exact hne) hadj hadj' hnot hnot' hgirth'

/-- Nonzero rooted layers in the odd Moore tree have the expected lower bound. -/
lemma le_ncard_rootLayer_succ (G : SimpleGraph α) (hV : V(G).Finite)
    {δ i : ℕ} {x : α}
    (hx : x ∈ V(G))
    (hmin : ∀ v : α, v ∈ V(G) → δ ≤ G.degree v)
    (hgirth : (2 * (i + 1) : ℕ∞) < G.girth) :
    δ * (δ - 1) ^ i ≤ (rootLayer G x (i + 1)).ncard := by
  induction i with
  | zero =>
      simpa using (hmin x hx).trans (degree_le_ncard_rootLayer_one G hV hx)
  | succ i ih =>
      have hgirthPrev : (2 * (i + 1) : ℕ∞) < G.girth := by
        apply lt_of_le_of_lt _ hgirth
        exact_mod_cast (show 2 * (i + 1) ≤ 2 * (i + 1 + 1) by omega)
      have hprev : δ * (δ - 1) ^ i ≤ (rootLayer G x (i + 1)).ncard :=
        ih hgirthPrev
      have hgirthGrowth : (2 * (i + 2) : ℕ∞) < G.girth := by
        simpa [Nat.add_assoc] using hgirth
      have hgrowth :=
        mul_ncard_rootLayer_le_succ_of_lt_girth
          G hV (δ := δ) (i := i) (x := x) hmin hgirthGrowth
      calc
        δ * (δ - 1) ^ (i + 1) = (δ - 1) * (δ * (δ - 1) ^ i) := by
          rw [pow_succ]
          ac_rfl
        _ ≤ (δ - 1) * (rootLayer G x (i + 1)).ncard :=
          Nat.mul_le_mul_left _ hprev
        _ ≤ (rootLayer G x (i + 2)).ncard := hgrowth

end MooreBound

end SimpleGraph

end AlgoLib
