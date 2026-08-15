/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Theory.Girth
import GraphLib.Theory.MooreBound.Counting

/-!
# Moore bounds: fresh neighbours and the shared counting core

The parts of the Moore argument that do not mention a layer family: the fresh
neighbours of a path's tail, the short cycle a chord would create, and the two
lemmas (`pred_le_ncard_freshNeighborSet`, `false_of_two_paths_of_common_fresh_neighbor`)
that the odd and even layer families both consume.

Part of the `MooreBound` folder; see the umbrella module
`GraphLib.Theory.MooreBound`.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Degree helpers

TEMPORARY: these three lemmas are pure `neighborSet` / `degree` API with no
dependence on the Moore development. They logically belong in
`GraphLib/Graph/Degree.lean` (alongside the `neighborSet` / `degree` definitions
they use, which are themselves temporarily housed in
`GraphLib.Theory.Girth`; see the section note there).
They live here at the top of the file only so that the Moore proofs below can use
them while `Degree.lean` is being developed by a collaborator. Do not treat this
placement as a precedent: no further degree API should be added here, and these
should move to `Graph/Degree.lean` once it is ready. -/

/-- Every neighbour of a vertex is a vertex of the ambient graph. -/
lemma neighborSet_subset_vertexSet (G : SimpleGraph α) (v : α) :
    G.neighborSet v ⊆ V(G) := by
  intro u hu
  exact SimpleGraph.Adj.left_mem hu

/-- A vertex with degree at least two has a neighbour different from any fixed
vertex. -/
lemma exists_neighbor_ne_of_two_le_degree (G : SimpleGraph α) {v w : α}
    (hdeg : 2 ≤ G.degree v) :
    ∃ u : α, G.Adj v u ∧ u ≠ w := by
  classical
  obtain ⟨u, hu, huw⟩ := Set.exists_ne_of_one_lt_ncard
    (by simpa [degree] using lt_of_lt_of_le Nat.one_lt_two hdeg) w
  exact ⟨u, hu.symm, huw⟩

/-- A nonempty graph whose vertices all have degree at least two contains an
edge. -/
lemma exists_adj_of_nonempty_of_two_le_degree (G : SimpleGraph α)
    (hne : V(G).Nonempty)
    (hmin : ∀ v : α, v ∈ V(G) → 2 ≤ G.degree v) :
    ∃ x y : α, G.Adj x y := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hxy, _⟩ := exists_neighbor_ne_of_two_le_degree
    (G := G) (v := x) (w := x) (hmin x hx)
  exact ⟨x, y, hxy⟩

namespace MooreBound

/-! ## Fresh neighbours -/

/-- The fresh neighbours of the tail of a path: neighbours that have not
already appeared on the path. -/
def freshNeighborSet (G : SimpleGraph α) (p : SimplePath α) : Set α :=
  {u | G.Adj p.tail u ∧ u ∉ p.vertices}

/-- Fresh neighbours are vertices of the ambient graph. -/
lemma freshNeighborSet_subset_vertexSet (G : SimpleGraph α) (p : SimplePath α) :
    freshNeighborSet G p ⊆ V(G) := by
  intro u hu
  exact hu.1.right_mem

/-! ## Short cycles from rooted paths -/

/-- Under a girth lower bound, a neighbour of the tail that already lies on a
short realized path can only be the tail itself or the penultimate vertex. -/
lemma eq_tail_or_eq_penultimate_of_adj_mem_of_lt_girth (G : SimpleGraph α)
    {p : SimplePath α} {y : α}
    (hp : G.IsSimplePathIn p) (hy_mem : y ∈ p.vertices)
    (hadj : G.Adj p.tail y) (hpos : p.length ≠ 0)
    (hgirth : ((p.length + 1 : ℕ) : ℕ∞) < G.girth) :
    y = p.tail ∨ y = p.vertices.dropTail.tail := by
  classical
  by_cases hle : (p.vertices.suffixFrom y hy_mem).length ≤ 1
  · exact VertexSeq.eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one
      p.vertices hy_mem hpos hle
  · obtain ⟨c, hc, hc_len⟩ := IsSimpleCycleIn.exists_length_le_succ_of_adj_mem
      G hp hy_mem hadj (by omega)
    have hlong := girth.lt_cycle_length G hc hgirth
    omega

/-- In a graph of sufficiently large girth, all neighbours of the tail except
possibly the penultimate vertex are fresh neighbours. Consequently, the number
of fresh neighbours is at least `degree - 1`. -/
lemma pred_degree_le_ncard_freshNeighborSet_of_lt_girth (G : SimpleGraph α)
    (hV : V(G).Finite) {p : SimplePath α}
    (hp : G.IsSimplePathIn p) (hpos : p.length ≠ 0)
    (hgirth : ((p.length + 1 : ℕ) : ℕ∞) < G.girth) :
    G.degree p.tail - 1 ≤ (freshNeighborSet G p).ncard := by
  classical
  let prev : α := p.vertices.dropTail.tail
  have hsubset : G.neighborSet p.tail \ {prev} ⊆ freshNeighborSet G p := by
    rintro u ⟨hu_neigh, hu_ne_prev⟩
    refine ⟨hu_neigh.symm, ?_⟩
    intro hu_mem
    rcases eq_tail_or_eq_penultimate_of_adj_mem_of_lt_girth
        G hp hu_mem hu_neigh.symm hpos hgirth with hu_tail | hu_prev
    · exact hu_neigh.symm.ne hu_tail.symm
    · exact hu_ne_prev hu_prev
  have hfresh_fin : (freshNeighborSet G p).Finite :=
    hV.subset (freshNeighborSet_subset_vertexSet G p)
  calc
    G.degree p.tail - 1 = (G.neighborSet p.tail).ncard - 1 := rfl
    _ ≤ (G.neighborSet p.tail \ {prev}).ncard :=
      Set.pred_ncard_le_ncard_diff_singleton (G.neighborSet p.tail) prev
    _ ≤ (freshNeighborSet G p).ncard :=
      Set.ncard_le_ncard hsubset hfresh_fin

/-! ## Shared core of the two layer-growth lemmas

`mul_ncard_rootLayer_le_succ_of_lt_girth` (`RootedLayers.lean`) and
`mul_ncard_halfLayer_le_succ_of_lt_girth` (`HalfLayers.lean`) prove the same
statement for two different layer families (rooted paths, and rooted paths
avoiding the far end of a central edge). The lemmas here are exactly the parts of
that argument which do not mention the layer family at all, so both callers share
them:

* `Set.mul_ncard_le_ncard_of_children` (in `Counting.lean`) — the counting
  skeleton;
* `pred_le_ncard_freshNeighborSet` — the per-vertex lower bound;
* `false_of_two_paths_of_common_fresh_neighbor` — the disjointness core. -/

/-- The fresh neighbours of a realized path of length `n ≠ 0` number at least `δ - 1`,
given the minimum-degree hypothesis and a girth bound comfortably above `n`. -/
lemma pred_le_ncard_freshNeighborSet (G : SimpleGraph α) (hV : V(G).Finite)
    {δ n : ℕ} {p : SimplePath α} {v : α}
    (hmin : ∀ w : α, w ∈ V(G) → δ ≤ G.degree w)
    (hp : G.IsSimplePathIn p) (hpt : p.tail = v) (hpl : p.length = n) (hpos : n ≠ 0)
    (hgirth : (2 * (n + 1) : ℕ∞) < G.girth) :
    δ - 1 ≤ (freshNeighborSet G p).ncard := by
  have hp_girth : ((p.length + 1 : ℕ) : ℕ∞) < G.girth := by
    have hle : ((p.length + 1 : ℕ) : ℕ∞) ≤ (2 * (n + 1) : ℕ∞) := by
      rw [hpl]; exact_mod_cast (show n + 1 ≤ 2 * (n + 1) by omega)
    exact hle.trans_lt hgirth
  have hpred := pred_degree_le_ncard_freshNeighborSet_of_lt_girth G hV hp (by omega) hp_girth
  rw [hpt] at hpred
  have hdeg : δ ≤ G.degree v := hmin v (hpt ▸ IsSimpleWalkIn.tail_mem G hp)
  omega

/-- Disjointness core: two realized simple paths of equal length `n` from a common head,
with *distinct* tails, cannot share a fresh neighbour `u`. Extending both by `u` would give
two distinct paths with the same endpoints, hence a cycle of length at most `2 * (n + 1)`,
contradicting the girth bound. -/
lemma false_of_two_paths_of_common_fresh_neighbor (G : SimpleGraph α)
    {p q : SimplePath α} {x u : α} {n : ℕ}
    (hp : G.IsSimplePathIn p) (hq : G.IsSimplePathIn q)
    (hph : p.head = x) (hqh : q.head = x)
    (hpl : p.length = n) (hql : q.length = n)
    (hne : p.tail ≠ q.tail)
    (hpadj : G.Adj p.tail u) (hqadj : G.Adj q.tail u)
    (hpu : u ∉ p.vertices) (hqu : u ∉ q.vertices)
    (hgirth : (2 * (n + 1) : ℕ∞) < G.girth) : False := by
  have hdisjp : ∀ z, z ∈ p.vertices →
      z ∈ (SimplePath.singleton u).vertices → False := by grind
  have hdisjq : ∀ z, z ∈ q.vertices →
      z ∈ (SimplePath.singleton u).vertices → False := by grind
  set p' : SimplePath α := p.append (SimplePath.singleton u) hdisjp with hp'def
  set q' : SimplePath α := q.append (SimplePath.singleton u) hdisjq with hq'def
  have hp'v : p'.vertices = p.vertices.cons u := rfl
  have hq'v : q'.vertices = q.vertices.cons u := rfl
  have hp'real : G.IsSimplePathIn p' :=
    IsVertexSeqIn.append G hp (IsVertexSeqIn.singleton u hpadj.right_mem) hpadj
  have hq'real : G.IsSimplePathIn q' :=
    IsVertexSeqIn.append G hq (IsVertexSeqIn.singleton u hqadj.right_mem) hqadj
  have hp'h : p'.head = x := by simp [hp'v, hph]
  have hq'h : q'.head = x := by simp [hq'v, hqh]
  have hp't : p'.tail = u := by simp [hp'v]
  have hq't : q'.tail = u := by simp [hq'v]
  have hp'l : p'.length = n + 1 := by simp [hp'v, VertexSeq.length, hpl]; omega
  have hq'l : q'.length = n + 1 := by simp [hq'v, VertexSeq.length, hql]; omega
  -- the two extended paths differ, since their penultimate vertices are the distinct tails
  have hdistinct : p'.vertices ≠ q'.vertices := fun heq =>
    hne (congrArg VertexSeq.tail ((VertexSeq.cons.injEq _ _ _ _).mp (hp'v ▸ hq'v ▸ heq)).1)
  obtain ⟨c, hc, hcle⟩ := IsSimpleCycleIn.exists_length_le_add_of_two_paths G
    hp'real hq'real (hp'h.trans hq'h.symm) (hp't.trans hq't.symm) hdistinct
  have hlong := girth.lt_cycle_length G hc hgirth
  have hsum : p'.length + q'.length = 2 * (n + 1) := by omega
  exact (not_lt_of_ge (hcle.trans_eq hsum) hlong).elim

end MooreBound

end SimpleGraph

end GraphLib
