/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Theory.MooreBound.RootedLayers

/-!
# Moore bounds: the half-layers around a central edge

The breadth-first layers grown from one endpoint of a central edge while avoiding
the other: `IsAvoidingRootedPath`, the layer `halfLayer` it cuts out, and the
growth and disjointness estimates. This is the family behind the even Moore bound.

Part of the `MooreBound` folder; see the umbrella module
`GraphLib.Theory.MooreBound`.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

namespace MooreBound

/-! ## Even half-layer counting -/

/-- A rooted path from the first endpoint `x` of an ordered central edge that
avoids its other endpoint `banned`. -/
@[grind] def IsAvoidingRootedPath (G : SimpleGraph α) (x banned : α) (i : ℕ)
    (v : α) : Prop :=
  ∃ p : SimplePath α,
    G.IsSimplePathIn p ∧ p.head = x ∧ p.tail = v ∧ p.length = i ∧
      banned ∉ p.vertices

namespace IsAvoidingRootedPath

/-- A chosen path witnessing an avoiding rooted path. -/
noncomputable def path {G : SimpleGraph α} {x banned v : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) : SimplePath α :=
  Classical.choose h

/-- The chosen witness path is realized in the ambient graph. -/
lemma path_isSimplePathIn {G : SimpleGraph α} {x banned v : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) : G.IsSimplePathIn h.path :=
  (Classical.choose_spec h).1

/-- The chosen witness path starts at the root. -/
lemma path_head {G : SimpleGraph α} {x banned v : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) : h.path.head = x :=
  (Classical.choose_spec h).2.1

/-- The chosen witness path ends at the half-layer vertex. -/
lemma path_tail {G : SimpleGraph α} {x banned v : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) : h.path.tail = v :=
  (Classical.choose_spec h).2.2.1

/-- The chosen witness path has the prescribed length. -/
lemma path_length {G : SimpleGraph α} {x banned v : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) : h.path.length = i :=
  (Classical.choose_spec h).2.2.2.1

/-- The chosen witness path avoids the banned vertex. -/
lemma path_not_banned {G : SimpleGraph α} {x banned v : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) : banned ∉ h.path.vertices :=
  (Classical.choose_spec h).2.2.2.2

/-- An avoiding rooted path is, in particular, a rooted path. -/
lemma isRootedPath {G : SimpleGraph α} {x banned v : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) : IsRootedPath G x i v :=
  ⟨h.path, h.path_isSimplePathIn, h.path_head, h.path_tail, h.path_length⟩

/-- The singleton path witnesses the zero-th half-layer, provided the banned
vertex is different from the root. -/
lemma singleton (G : SimpleGraph α) {x banned : α} (hx : x ∈ V(G))
    (hxb : x ≠ banned) : IsAvoidingRootedPath G x banned 0 x := by
  refine ⟨SimplePath.singleton x, IsSimplePathIn.singleton G hx, rfl, rfl, rfl, ?_⟩
  change banned ∉ VertexSeq.singleton x
  simpa only [VertexSeq.mem_singleton] using hxb.symm

/-- Extending an avoiding rooted path by a fresh neighbour different from the
banned vertex stays in the next half-layer. -/
lemma succ_of_adj_not_mem (G : SimpleGraph α) {x banned v u : α} {i : ℕ}
    (h : IsAvoidingRootedPath G x banned i v) (hadj : G.Adj v u)
    (hnot : u ∉ h.path.vertices) (hub : u ≠ banned) :
    IsAvoidingRootedPath G x banned (i + 1) u := by
  have hdisj : ∀ z : α, z ∈ h.path.vertices →
      z ∈ (SimplePath.singleton u).vertices → False := by
    grind
  have hstep : G.Adj h.path.tail (SimplePath.singleton u).head := by
    simpa only [SimplePath.head_singleton, h.path_tail] using hadj
  have hnb := h.path_not_banned
  refine ⟨h.path.append (SimplePath.singleton u) hdisj,
    IsSimpleWalkIn.append G h.path_isSimplePathIn
      (IsSimplePathIn.singleton G hadj.right_mem) hstep, ?_, ?_, ?_, ?_⟩ <;>
    simp [h.path_head, h.path_length]
  grind

end IsAvoidingRootedPath

/-- The vertices reached from `x` by rooted paths avoiding `banned`. -/
def halfLayer (G : SimpleGraph α) (x banned : α) (i : ℕ) : Set α :=
  {v | IsAvoidingRootedPath G x banned i v}

/-- Membership in a half-layer is witnessed by an avoiding rooted path that
avoids the banned endpoint. -/
@[simp, grind =] lemma mem_halfLayer (G : SimpleGraph α) {x banned v : α} {i : ℕ} :
    v ∈ halfLayer G x banned i ↔ IsAvoidingRootedPath G x banned i v :=
  Iff.rfl

/-- Every half-layer is contained in the ambient vertex set. -/
lemma halfLayer_subset_vertexSet (G : SimpleGraph α) (x banned : α) (i : ℕ) :
    halfLayer G x banned i ⊆ V(G) := by
  intro v hv
  exact IsRootedPath.tail_mem G hv.isRootedPath

/-- The zero-th half-layer is the singleton root. -/
@[simp] lemma halfLayer_zero (G : SimpleGraph α) {x banned : α} (hx : x ∈ V(G))
    (hxb : x ≠ banned) : halfLayer G x banned 0 = {x} := by
  ext v
  constructor <;> grind [IsAvoidingRootedPath.singleton]

/-- The zero-th half-layer has one vertex. -/
lemma ncard_halfLayer_zero (G : SimpleGraph α) {x banned : α}
    (hx : x ∈ V(G)) (hxb : x ≠ banned) :
    (halfLayer G x banned 0).ncard = 1 := by
  rw [halfLayer_zero G hx hxb]
  exact Set.ncard_singleton x

/-- Prefixing an avoiding rooted path from the opposite endpoint by the central
edge gives an ordinary rooted path from this endpoint. -/
lemma isRootedPath_of_adj_of_isAvoidingRootedPath (G : SimpleGraph α) {x y v : α}
    {i : ℕ} (hxy : G.Adj x y) (h : IsAvoidingRootedPath G y x i v) :
    IsRootedPath G x (i + 1) v := by
  have hnb := h.path_not_banned
  have hdisj : ∀ z : α, z ∈ (SimplePath.singleton x).vertices →
      z ∈ h.path.vertices → False := by
    grind
  have hstep : G.Adj (SimplePath.singleton x).tail h.path.head := by
    simpa only [SimplePath.tail_singleton, h.path_head] using hxy
  refine ⟨(SimplePath.singleton x).append h.path hdisj,
    IsSimpleWalkIn.append G (IsSimplePathIn.singleton G hxy.left_mem)
      h.path_isSimplePathIn hstep, ?_, ?_, ?_⟩ <;>
    simp [h.path_tail, h.path_length]

/-- The endpoint of a sufficiently short avoiding rooted path is not adjacent
to the banned endpoint of the central edge. -/
lemma not_adj_banned_of_isAvoidingRootedPath_of_lt_girth (G : SimpleGraph α)
    {x banned v : α} {i : ℕ}
    (hxb : G.Adj x banned) (h : IsAvoidingRootedPath G x banned i v)
    (hpos : i ≠ 0) (hgirth : (i + 2 : ℕ∞) < G.girth) :
    ¬ G.Adj v banned := by
  classical
  intro hvb
  have hnb := h.path_not_banned
  have hdisj : ∀ z : α, z ∈ h.path.vertices →
      z ∈ (SimplePath.singleton banned).vertices → False := by
    grind
  set q : SimplePath α := h.path.append (SimplePath.singleton banned) hdisj with hqdef
  have hq_len : q.length = i + 1 := by
    simp [hqdef, h.path_length]
  have hq_two : 2 ≤ q.length := by omega
  have hq_real : G.IsSimplePathIn q :=
    IsSimpleWalkIn.append G h.path_isSimplePathIn
      (IsSimplePathIn.singleton G hxb.right_mem)
      (by simpa only [SimplePath.head_singleton, h.path_tail] using hvb)
  have hends : q.tail = banned ∧ q.head = x := by
    simp [hqdef, h.path_head]
  have hclose : G.Adj q.tail q.head := by
    rw [hends.1, hends.2]; exact hxb.symm
  have hcle : (SimpleCycle.ofPathClosing q hq_two).length ≤ i + 2 := by
    change 1 + q.length ≤ i + 2
    omega
  exact absurd (girth.lt_cycle_length G
    (IsSimpleCycleIn.ofPathClosing G hq_real hclose hq_two) hgirth) (not_lt_of_ge hcle)

/-- The first half-layer has at least `δ - 1` vertices. -/
lemma pred_le_ncard_halfLayer_one (G : SimpleGraph α) (hV : V(G).Finite)
    {δ : ℕ} {x banned : α}
    (hxb : G.Adj x banned)
    (hmin : ∀ v : α, v ∈ V(G) → δ ≤ G.degree v) :
    δ - 1 ≤ (halfLayer G x banned 1).ncard := by
  classical
  have hsub : G.neighborSet x \ {banned} ⊆ halfLayer G x banned 1 := by
    rintro u ⟨hux, hub⟩
    have hxu : G.Adj x u := hux.symm
    have hub' : u ≠ banned := by simpa [Set.mem_singleton_iff] using hub
    have hdisj : ∀ z : α, z ∈ (SimplePath.singleton x).vertices →
        z ∈ (SimplePath.singleton u).vertices → False := by
      grind
    refine ⟨(SimplePath.singleton x).append (SimplePath.singleton u) hdisj,
      IsSimpleWalkIn.append G (IsSimplePathIn.singleton G hxb.left_mem)
        (IsSimplePathIn.singleton G hxu.right_mem) hxu, ?_, ?_, ?_, ?_⟩ <;>
      simp
    grind
  have hhalf_fin : (halfLayer G x banned 1).Finite :=
    hV.subset (halfLayer_subset_vertexSet G x banned 1)
  have hpred : G.degree x - 1 ≤ (G.neighborSet x \ {banned}).ncard := by
    simpa [degree] using Set.pred_ncard_le_ncard_diff_singleton (G.neighborSet x) banned
  exact (Nat.sub_le_sub_right (hmin x hxb.left_mem) 1).trans
    (hpred.trans (Set.ncard_le_ncard hsub hhalf_fin))

/-- Successive nonzero half-layers grow by a factor of at least `δ - 1`. -/
lemma mul_ncard_halfLayer_le_succ_of_lt_girth (G : SimpleGraph α)
    (hV : V(G).Finite) {δ i : ℕ} {x banned : α}
    (hxb : G.Adj x banned)
    (hmin : ∀ v : α, v ∈ V(G) → δ ≤ G.degree v)
    (hgirth : (2 * (i + 2) : ℕ∞) < G.girth) :
    (δ - 1) * (halfLayer G x banned (i + 1)).ncard ≤
      (halfLayer G x banned (i + 2)).ncard := by
  classical
  have hLfin : (halfLayer G x banned (i + 1)).Finite :=
    hV.subset (halfLayer_subset_vertexSet G x banned (i + 1))
  have hNfin : (halfLayer G x banned (i + 2)).Finite :=
    hV.subset (halfLayer_subset_vertexSet G x banned (i + 2))
  set F : α → Set α := fun v =>
    if h : IsAvoidingRootedPath G x banned (i + 1) v then freshNeighborSet G h.path else ∅
    with hFdef
  have hFv : ∀ v, (hv : IsAvoidingRootedPath G x banned (i + 1) v) →
      F v = freshNeighborSet G hv.path := by
    intro v hv
    simp only [hFdef, dif_pos hv]
  have hgirth' : (2 * (((i + 1 : ℕ) : ℕ∞) + 1)) < G.girth := by
    push_cast; convert hgirth using 2
  refine GraphLib.Set.mul_ncard_le_ncard_of_children (F := F) hLfin hNfin ?_ ?_ ?_
  · -- children lie in the next half-layer: a child cannot be the banned endpoint,
    -- since that would close a cycle shorter than the girth
    intro v hv u hu
    have hvO : IsAvoidingRootedPath G x banned (i + 1) v := hv
    rw [hFv v hvO] at hu
    obtain ⟨hadj, hnot⟩ := hu
    have hub : u ≠ banned := by
      intro hub
      subst hub
      have hshort : (i + 1 + 2 : ℕ∞) < G.girth := by
        apply lt_of_le_of_lt _ hgirth
        exact_mod_cast (show i + 1 + 2 ≤ 2 * (i + 2) by omega)
      exact not_adj_banned_of_isAvoidingRootedPath_of_lt_girth G hxb hvO (by omega) hshort
        (hvO.path_tail ▸ hadj)
    exact IsAvoidingRootedPath.succ_of_adj_not_mem G hvO (hvO.path_tail ▸ hadj) hnot hub
  · -- each child set has at least `δ - 1` elements
    intro v hv
    have hvO : IsAvoidingRootedPath G x banned (i + 1) v := hv
    rw [hFv v hvO]
    exact pred_le_ncard_freshNeighborSet G hV hmin hvO.path_isSimplePathIn
      hvO.path_tail hvO.path_length (by omega) hgirth'
  · -- distinct source vertices produce disjoint child sets
    intro v v' hv hv' hne
    rw [Set.disjoint_left]
    intro u hu hu'
    have hvO : IsAvoidingRootedPath G x banned (i + 1) v := hv
    have hv'O : IsAvoidingRootedPath G x banned (i + 1) v' := hv'
    rw [hFv v hvO] at hu
    rw [hFv v' hv'O] at hu'
    obtain ⟨hadj, hnot⟩ := hu
    obtain ⟨hadj', hnot'⟩ := hu'
    exact false_of_two_paths_of_common_fresh_neighbor G
      hvO.path_isSimplePathIn hv'O.path_isSimplePathIn hvO.path_head hv'O.path_head
      hvO.path_length hv'O.path_length
      (by rw [hvO.path_tail, hv'O.path_tail]; exact hne) hadj hadj' hnot hnot' hgirth'

/-- Distinct same-side half-layers are disjoint when the sum of their indices
is below the girth. -/
lemma disjoint_halfLayer_of_ne_of_lt_girth (G : SimpleGraph α)
    {x banned : α} {i j : ℕ} (hij : i ≠ j)
    (hgirth : ((i + j : ℕ) : ℕ∞) < G.girth) :
    Disjoint (halfLayer G x banned i) (halfLayer G x banned j) := by
  classical
  rw [Set.disjoint_left]
  intro v hvi hvj
  obtain ⟨p, hp, hpx, hpv, hplen, _⟩ := hvi
  obtain ⟨q, hq, hqx, hqv, hqlen, _⟩ := hvj
  have hne : p.vertices ≠ q.vertices := fun hvertices => hij (by
    rw [← hplen, ← hqlen]; exact congrArg VertexSeq.length hvertices)
  obtain ⟨c, hc, hcle⟩ := IsSimpleCycleIn.exists_length_le_add_of_two_paths G hp hq
    (hpx.trans hqx.symm) (hpv.trans hqv.symm) hne
  have hlong := girth.lt_cycle_length G hc hgirth
  omega

/-- Opposite half-layers below radius `r` are disjoint under an even girth
lower bound. -/
lemma disjoint_halfLayer_opposite_of_lt_girth (G : SimpleGraph α)
    {x y : α} {i j : ℕ}
    (hxy : G.Adj x y) (hgirth : ((i + j + 1 : ℕ) : ℕ∞) < G.girth) :
    Disjoint (halfLayer G x y i) (halfLayer G y x j) := by
  classical
  rw [Set.disjoint_left]
  intro v hvi hvj
  obtain ⟨p, hp, hpx, hpv, hplen, hpy⟩ := hvi
  obtain ⟨qOpp, hqOpp, hqOpp_y, hqOpp_v, hqOpp_len, hqOpp_notx⟩ := hvj
  have hdisj : ∀ z : α, z ∈ (SimplePath.singleton x).vertices →
      z ∈ qOpp.vertices → False := by
    grind
  have hstep : G.Adj (SimplePath.singleton x).tail qOpp.head := by
    simpa only [SimplePath.tail_singleton, hqOpp_y] using hxy
  set q : SimplePath α := (SimplePath.singleton x).append qOpp hdisj with hqdef
  have hq : G.IsSimplePathIn q :=
    IsSimpleWalkIn.append G (IsSimplePathIn.singleton G hxy.left_mem) hqOpp hstep
  have hqx : q.head = x := by
    simp [hqdef]
  have hqv : q.tail = v := by
    simp [hqdef, hqOpp_v]
  have hqlen : q.length = j + 1 := by
    simp [hqdef, hqOpp_len]
  -- `p` avoids `y`, but the prefixed path `q` visits it, so they are distinct
  have hne : p.vertices ≠ q.vertices := by
    have hyq : y ∈ q.vertices := by
      simp [hqdef, ← hqOpp_y]
    exact fun heq => hpy (heq ▸ hyq)
  obtain ⟨c, hc, hcle⟩ := IsSimpleCycleIn.exists_length_le_add_of_two_paths G hp hq
    (hpx.trans hqx.symm) (hpv.trans hqv.symm) hne
  have hlong := girth.lt_cycle_length G hc hgirth
  omega

/-- Nonzero same-side half-layer growth plus the first-layer estimate give the
expected lower bound for every half-layer below radius `r`. -/
lemma le_ncard_halfLayer (G : SimpleGraph α) (hV : V(G).Finite)
    {δ i : ℕ} {x banned : α}
    (hxb : G.Adj x banned)
    (hmin : ∀ v : α, v ∈ V(G) → δ ≤ G.degree v)
    (hgirth : (2 * i : ℕ∞) < G.girth) :
    (δ - 1) ^ i ≤ (halfLayer G x banned i).ncard := by
  induction i with
  | zero =>
      rw [pow_zero, ncard_halfLayer_zero G hxb.left_mem hxb.ne]
  | succ i ih =>
      cases i with
      | zero =>
          simpa using pred_le_ncard_halfLayer_one G hV hxb hmin
      | succ i =>
          have hgirthPrev : (2 * (i + 1) : ℕ∞) < G.girth := by
            apply lt_of_le_of_lt _ hgirth
            exact_mod_cast (show 2 * (i + 1) ≤ 2 * (i + 1 + 1) by omega)
          have hprev : (δ - 1) ^ (i + 1) ≤
              (halfLayer G x banned (i + 1)).ncard := ih hgirthPrev
          have hgirthGrowth : (2 * (i + 2) : ℕ∞) < G.girth := by
            simpa [Nat.add_assoc] using hgirth
          have hgrowth :=
            mul_ncard_halfLayer_le_succ_of_lt_girth
              G hV (δ := δ) (i := i) (x := x) (banned := banned)
              hxb hmin hgirthGrowth
          calc
            (δ - 1) ^ (i + 1 + 1) = (δ - 1) * (δ - 1) ^ (i + 1) := by
              rw [pow_succ]
              ac_rfl
            _ ≤ (δ - 1) * (halfLayer G x banned (i + 1)).ncard :=
              Nat.mul_le_mul_left _ hprev
            _ ≤ (halfLayer G x banned (i + 2)).ncard := hgrowth

end MooreBound

end SimpleGraph

end GraphLib
