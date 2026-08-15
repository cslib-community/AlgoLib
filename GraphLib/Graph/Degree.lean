/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import Mathlib.Data.Finset.Lattice.Fold
import GraphLib.Graph.Finite

/-!
# Finite-local graph degree

Natural-valued degree is defined only when the relevant local incidence or neighborhood set is
finite. In a general undirected graph, parallel actual edges count separately and each loop
contributes two: once through incidence and once through the loop correction. Directed loops
contribute one to each of out-degree and in-degree.
-/

namespace GraphLib

open scoped GraphLib

variable {α β : Type*}

/-! ## Local degree -/

/-- The degree of `v` in a general graph. Parallel actual edges count separately and each loop
contributes two. Only the incidence set at `v` must be finite. -/
noncomputable def Graph.degree (G : Graph α β) (v : α) [Finite (G.incidenceSet v)] : ℕ :=
  (G.incidenceFinset v).card + (G.loopFinset v).card

/-- The degree of `v` in a simple graph, defined when its neighborhood is finite. -/
noncomputable def SimpleGraph.degree (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] : ℕ :=
  (G.neighborFinset v).card

/-- The number of actual arcs whose source is `v`, defined when that local incidence set is
finite. A directed loop contributes one. -/
noncomputable def DiGraph.outDegree (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] : ℕ :=
  (G.outIncidenceFinset v).card

/-- The number of actual arcs whose target is `v`, defined when that local incidence set is
finite. A directed loop contributes one. -/
noncomputable def DiGraph.inDegree (G : DiGraph α β) (v : α)
    [Finite (G.inIncidenceSet v)] : ℕ :=
  (G.inIncidenceFinset v).card

/-- The out-degree of `v` in a simple directed graph. -/
noncomputable def SimpleDiGraph.outDegree (G : SimpleDiGraph α) (v : α)
    [Finite (G.outIncidenceSet v)] : ℕ :=
  (G.outIncidenceFinset v).card

/-- The in-degree of `v` in a simple directed graph. -/
noncomputable def SimpleDiGraph.inDegree (G : SimpleDiGraph α) (v : α)
    [Finite (G.inIncidenceSet v)] : ℕ :=
  (G.inIncidenceFinset v).card

theorem Graph.card_incidenceFinset_add_card_loopFinset_eq_degree
    (G : Graph α β) (v : α) [Finite (G.incidenceSet v)] :
    (G.incidenceFinset v).card + (G.loopFinset v).card = G.degree v := rfl

theorem SimpleGraph.card_neighborFinset_eq_degree
    (G : SimpleGraph α) (v : α) [Finite (G.neighborSet v)] :
    (G.neighborFinset v).card = G.degree v := rfl

theorem DiGraph.card_outIncidenceFinset_eq_outDegree
    (G : DiGraph α β) (v : α) [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceFinset v).card = G.outDegree v := rfl

theorem DiGraph.card_inIncidenceFinset_eq_inDegree
    (G : DiGraph α β) (v : α) [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceFinset v).card = G.inDegree v := rfl

theorem SimpleDiGraph.card_outIncidenceFinset_eq_outDegree
    (G : SimpleDiGraph α) (v : α) [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceFinset v).card = G.outDegree v := rfl

theorem SimpleDiGraph.card_inIncidenceFinset_eq_inDegree
    (G : SimpleDiGraph α) (v : α) [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceFinset v).card = G.inDegree v := rfl

theorem Graph.ncard_incidenceSet_add_ncard_loopSet_eq_degree
    (G : Graph α β) (v : α) [Finite (G.incidenceSet v)] :
    (G.incidenceSet v).ncard + (G.loopSet v).ncard = G.degree v := by
  rw [G.ncard_incidenceSet, G.ncard_loopSet]
  rfl

theorem SimpleGraph.ncard_neighborSet_eq_degree
    (G : SimpleGraph α) (v : α) [Finite (G.neighborSet v)] :
    (G.neighborSet v).ncard = G.degree v := by
  rw [G.ncard_neighborSet]
  rfl

theorem DiGraph.ncard_outIncidenceSet_eq_outDegree
    (G : DiGraph α β) (v : α) [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceSet v).ncard = G.outDegree v := by
  rw [G.ncard_outIncidenceSet]
  rfl

theorem DiGraph.ncard_inIncidenceSet_eq_inDegree
    (G : DiGraph α β) (v : α) [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceSet v).ncard = G.inDegree v := by
  rw [G.ncard_inIncidenceSet]
  rfl

theorem SimpleDiGraph.ncard_outIncidenceSet_eq_outDegree
    (G : SimpleDiGraph α) (v : α) [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceSet v).ncard = G.outDegree v := by
  rw [G.ncard_outIncidenceSet]
  rfl

theorem SimpleDiGraph.ncard_inIncidenceSet_eq_inDegree
    (G : SimpleDiGraph α) (v : α) [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceSet v).ncard = G.inDegree v := by
  rw [G.ncard_inIncidenceSet]
  rfl

/-! ## Degree outside the vertex set -/

@[simp] theorem Graph.degree_eq_zero_of_not_mem (G : Graph α β) (v : α)
    [Finite (G.incidenceSet v)] (hv : v ∉ V(G)) : G.degree v = 0 := by
  have hi : G.incidenceFinset v = ∅ := by
    ext e
    simp only [G.mem_incidenceFinset, Finset.notMem_empty, iff_false]
    exact fun h => hv h.vertex_mem
  have hl : G.loopFinset v = ∅ := by
    ext e
    simp only [G.mem_loopFinset, Finset.notMem_empty, iff_false]
    exact fun h => hv h.left_mem
  simp [degree, hi, hl]

@[simp] theorem SimpleGraph.degree_eq_zero_of_not_mem (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] (hv : v ∉ V(G)) : G.degree v = 0 := by
  have hn : G.neighborFinset v = ∅ := by
    ext u
    simp only [G.mem_neighborFinset, Finset.notMem_empty, iff_false]
    exact fun h => hv h.left_mem
  simp [degree, hn]

@[simp] theorem DiGraph.outDegree_eq_zero_of_not_mem (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] (hv : v ∉ V(G)) : G.outDegree v = 0 := by
  have hi : G.outIncidenceFinset v = ∅ := by
    ext a
    simp only [G.mem_outIncidenceFinset, Finset.notMem_empty, iff_false]
    exact fun h => hv (h.2 ▸ G.source_mem a h.1)
  simp [outDegree, hi]

@[simp] theorem DiGraph.inDegree_eq_zero_of_not_mem (G : DiGraph α β) (v : α)
    [Finite (G.inIncidenceSet v)] (hv : v ∉ V(G)) : G.inDegree v = 0 := by
  have hi : G.inIncidenceFinset v = ∅ := by
    ext a
    simp only [G.mem_inIncidenceFinset, Finset.notMem_empty, iff_false]
    exact fun h => hv (h.2 ▸ G.target_mem a h.1)
  simp [inDegree, hi]

@[simp] theorem SimpleDiGraph.outDegree_eq_zero_of_not_mem
    (G : SimpleDiGraph α) (v : α) [Finite (G.outIncidenceSet v)]
    (hv : v ∉ V(G)) : G.outDegree v = 0 := by
  have hi : G.outIncidenceFinset v = ∅ := by
    ext a
    simp only [G.mem_outIncidenceFinset, Finset.notMem_empty, iff_false]
    exact fun h => hv (h.2 ▸ G.source_mem a h.1)
  simp [outDegree, hi]

@[simp] theorem SimpleDiGraph.inDegree_eq_zero_of_not_mem
    (G : SimpleDiGraph α) (v : α) [Finite (G.inIncidenceSet v)]
    (hv : v ∉ V(G)) : G.inDegree v = 0 := by
  have hi : G.inIncidenceFinset v = ∅ := by
    ext a
    simp only [G.mem_inIncidenceFinset, Finset.notMem_empty, iff_false]
    exact fun h => hv (h.2 ▸ G.target_mem a h.1)
  simp [inDegree, hi]

/-! ## Simple positive degree -/

theorem SimpleGraph.degree_pos_iff_exists_adj (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] :
    0 < G.degree v ↔ ∃ u, G.Adj v u := by
  rw [← G.card_neighborFinset_eq_degree]
  rw [Finset.card_pos]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (G.mem_neighborFinset v u).mp hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (G.mem_neighborFinset v u).mpr hu⟩

theorem SimpleGraph.degree_eq_zero_iff_forall_not_adj (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] :
    G.degree v = 0 ↔ ∀ u, ¬ G.Adj v u := by
  constructor
  · intro hzero u hadj
    have hpos := (G.degree_pos_iff_exists_adj v).2 ⟨u, hadj⟩
    omega
  · intro h
    by_contra hne
    obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).1 (Nat.pos_of_ne_zero hne)
    exact h u hu

/-- In a simple graph, neighbors of `v` are in bijection with the actual edges incident with
`v`, so the two finite cardinalities agree. -/
theorem SimpleGraph.card_incidenceFinset_eq_degree (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] [Finite (G.incidenceSet v)] :
    (G.incidenceFinset v).card = G.degree v := by
  rw [← G.card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun u _ => s(v, u))
  · intro u hu
    have hadj := (G.mem_neighborFinset v u).mp hu
    exact (G.mem_incidenceFinset v).mpr ⟨(G.adj_iff v u).mp hadj, by simp⟩
  · intro u hu w hw heq
    have huv : u ≠ v := ((G.mem_neighborFinset v u).mp hu |>.ne).symm
    have hwv : w ≠ v := ((G.mem_neighborFinset v w).mp hw |>.ne).symm
    simpa [Sym2.eq_iff, huv, hwv] using heq
  · intro e he
    have hinc := (G.mem_incidenceFinset v).mp he
    induction e with
    | h u w =>
      simp only [SimpleGraph.Inc, Sym2.mem_iff] at hinc
      rcases hinc.2 with rfl | rfl
      · refine ⟨w, ?_, rfl⟩
        exact (G.mem_neighborFinset v w).mpr ((G.adj_iff v w).mpr hinc.1)
      · refine ⟨u, ?_, Sym2.eq_swap⟩
        apply (G.mem_neighborFinset v u).mpr
        apply (G.adj_iff v u).mpr
        rw [show s(v, u) = s(u, v) from Sym2.eq_swap]
        exact hinc.1

@[simp] theorem SimpleGraph.loopFinset_eq_empty (G : SimpleGraph α) (v : α)
    [Finite (G.loopSet v)] : G.loopFinset v = ∅ := by
  ext e
  simp only [G.mem_loopFinset, Finset.notMem_empty, iff_false]
  exact fun h => h.adj.ne rfl

theorem SimpleGraph.card_incidenceFinset_add_card_loopFinset_eq_degree
    (G : SimpleGraph α) (v : α) [Finite (G.neighborSet v)] [Finite (G.incidenceSet v)] :
    (G.incidenceFinset v).card + (G.loopFinset v).card = G.degree v := by
  rw [G.card_incidenceFinset_eq_degree, G.loopFinset_eq_empty]
  simp

/-! ## Edge-cardinality bounds -/

/-- A vertex degree in a finite-edge general graph is at most twice the number of actual edges.
The factor two is sharp for a vertex carrying only loops. -/
theorem Graph.degree_le_two_mul_card_edgeFinset (G : Graph α β) (v : α) [Finite E(G)] :
    G.degree v ≤ 2 * G.edgeFinset.card := by
  have hi : (G.incidenceFinset v).card ≤ G.edgeFinset.card :=
    Finset.card_le_card fun e he =>
      G.mem_edgeFinset.mpr ((G.mem_incidenceFinset v).mp he).edge_mem
  have hl : (G.loopFinset v).card ≤ G.edgeFinset.card :=
    Finset.card_le_card fun e he => G.mem_edgeFinset.mpr ((G.mem_loopFinset v).mp he).edge_mem
  simpa [degree, two_mul] using Nat.add_le_add hi hl

theorem SimpleGraph.degree_le_card_edgeFinset (G : SimpleGraph α) (v : α) [Finite V(G)] :
    G.degree v ≤ G.edgeFinset.card := by
  rw [← G.card_incidenceFinset_eq_degree]
  exact Finset.card_le_card (G.incidenceFinset_subset_edgeFinset v)

theorem DiGraph.outDegree_le_card_edgeFinset (G : DiGraph α β) (v : α) [Finite E(G)] :
    G.outDegree v ≤ G.edgeFinset.card :=
  Finset.card_le_card fun _a ha => G.mem_edgeFinset.mpr ((G.mem_outIncidenceFinset v).mp ha).1

theorem DiGraph.inDegree_le_card_edgeFinset (G : DiGraph α β) (v : α) [Finite E(G)] :
    G.inDegree v ≤ G.edgeFinset.card :=
  Finset.card_le_card fun _a ha => G.mem_edgeFinset.mpr ((G.mem_inIncidenceFinset v).mp ha).1

theorem SimpleDiGraph.outDegree_le_card_edgeFinset
    (G : SimpleDiGraph α) (v : α) [Finite E(G)] :
    G.outDegree v ≤ G.edgeFinset.card :=
  Finset.card_le_card fun _a ha => G.mem_edgeFinset.mpr ((G.mem_outIncidenceFinset v).mp ha).1

theorem SimpleDiGraph.inDegree_le_card_edgeFinset
    (G : SimpleDiGraph α) (v : α) [Finite E(G)] :
    G.inDegree v ≤ G.edgeFinset.card :=
  Finset.card_le_card fun _a ha => G.mem_edgeFinset.mpr ((G.mem_inIncidenceFinset v).mp ha).1

/-! ## Subgraph monotonicity -/

theorem Graph.degree_mono {H G : Graph α β} (hHG : H ≤ G) (v : α)
    [Finite (H.incidenceSet v)] [Finite (G.incidenceSet v)] : H.degree v ≤ G.degree v := by
  rw [← H.ncard_incidenceSet_add_ncard_loopSet_eq_degree,
    ← G.ncard_incidenceSet_add_ncard_loopSet_eq_degree]
  apply Nat.add_le_add
  · exact Set.ncard_le_ncard (fun _ h => hHG.inc h) (Set.toFinite _)
  · exact Set.ncard_le_ncard (fun _ h => hHG.isLink h) (Set.toFinite _)

theorem SimpleGraph.degree_mono {H G : SimpleGraph α} (hHG : H ≤ G) (v : α)
    [Finite (H.neighborSet v)] [Finite (G.neighborSet v)] : H.degree v ≤ G.degree v := by
  rw [← H.ncard_neighborSet_eq_degree, ← G.ncard_neighborSet_eq_degree]
  exact Set.ncard_le_ncard (H.neighborSet_mono hHG v) (Set.toFinite _)

theorem DiGraph.outDegree_mono {H G : DiGraph α β} (hHG : H ≤ G) (v : α)
    [Finite (H.outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    H.outDegree v ≤ G.outDegree v := by
  rw [← H.ncard_outIncidenceSet_eq_outDegree, ← G.ncard_outIncidenceSet_eq_outDegree]
  exact Set.ncard_le_ncard (fun _ h => ⟨hHG.edgeSet_subset h.1, h.2⟩) (Set.toFinite _)

theorem DiGraph.inDegree_mono {H G : DiGraph α β} (hHG : H ≤ G) (v : α)
    [Finite (H.inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    H.inDegree v ≤ G.inDegree v := by
  rw [← H.ncard_inIncidenceSet_eq_inDegree, ← G.ncard_inIncidenceSet_eq_inDegree]
  exact Set.ncard_le_ncard (fun _ h => ⟨hHG.edgeSet_subset h.1, h.2⟩) (Set.toFinite _)

theorem SimpleDiGraph.outDegree_mono {H G : SimpleDiGraph α} (hHG : H ≤ G) (v : α)
    [Finite (H.outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    H.outDegree v ≤ G.outDegree v := by
  rw [← H.ncard_outIncidenceSet_eq_outDegree, ← G.ncard_outIncidenceSet_eq_outDegree]
  exact Set.ncard_le_ncard (fun _ h => ⟨hHG.edgeSet_subset h.1, h.2⟩) (Set.toFinite _)

theorem SimpleDiGraph.inDegree_mono {H G : SimpleDiGraph α} (hHG : H ≤ G) (v : α)
    [Finite (H.inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    H.inDegree v ≤ G.inDegree v := by
  rw [← H.ncard_inIncidenceSet_eq_inDegree, ← G.ncard_inIncidenceSet_eq_inDegree]
  exact Set.ncard_le_ncard (fun _ h => ⟨hHG.edgeSet_subset h.1, h.2⟩) (Set.toFinite _)

/-! ## Transformation monotonicity -/

theorem Graph.degree_induce (G : Graph α β) (S : Set α) (v : α)
    [Finite ((G.induce S).incidenceSet v)] [Finite (G.incidenceSet v)] :
    (G.induce S).degree v ≤ G.degree v :=
  Graph.degree_mono (G.induce_le S) v

theorem Graph.degree_deleteEdges (G : Graph α β) (F : Set (Edge α β)) (v : α)
    [Finite ((G.deleteEdges F).incidenceSet v)] [Finite (G.incidenceSet v)] :
    (G.deleteEdges F).degree v ≤ G.degree v :=
  Graph.degree_mono (G.deleteEdges_le F) v

theorem Graph.degree_deleteEdge (G : Graph α β) (e : Edge α β) (v : α)
    [Finite ((G.deleteEdge e).incidenceSet v)] [Finite (G.incidenceSet v)] :
    (G.deleteEdge e).degree v ≤ G.degree v :=
  Graph.degree_mono (G.deleteEdge_le e) v

theorem Graph.degree_deleteVerts (G : Graph α β) (S : Set α) (v : α)
    [Finite ((G.deleteVerts S).incidenceSet v)] [Finite (G.incidenceSet v)] :
    (G.deleteVerts S).degree v ≤ G.degree v :=
  Graph.degree_mono (G.deleteVerts_le S) v

theorem Graph.degree_deleteVert (G : Graph α β) (u v : α)
    [Finite ((G.deleteVert u).incidenceSet v)] [Finite (G.incidenceSet v)] :
    (G.deleteVert u).degree v ≤ G.degree v :=
  Graph.degree_mono (G.deleteVert_le u) v

theorem Graph.degree_deleteEdgesBetween (G : Graph α β) (u w v : α)
    [Finite ((G.deleteEdgesBetween u w).incidenceSet v)] [Finite (G.incidenceSet v)] :
    (G.deleteEdgesBetween u w).degree v ≤ G.degree v :=
  Graph.degree_mono (G.deleteEdgesBetween_le u w) v

theorem SimpleGraph.degree_induce (G : SimpleGraph α) (S : Set α) (v : α)
    [Finite ((G.induce S).neighborSet v)] [Finite (G.neighborSet v)] :
    (G.induce S).degree v ≤ G.degree v :=
  SimpleGraph.degree_mono (G.induce_le S) v

theorem SimpleGraph.degree_deleteEdges (G : SimpleGraph α) (F : Set (Sym2 α)) (v : α)
    [Finite ((G.deleteEdges F).neighborSet v)] [Finite (G.neighborSet v)] :
    (G.deleteEdges F).degree v ≤ G.degree v :=
  SimpleGraph.degree_mono (G.deleteEdges_le F) v

theorem SimpleGraph.degree_deleteEdge (G : SimpleGraph α) (e : Sym2 α) (v : α)
    [Finite ((G.deleteEdge e).neighborSet v)] [Finite (G.neighborSet v)] :
    (G.deleteEdge e).degree v ≤ G.degree v :=
  SimpleGraph.degree_mono (G.deleteEdge_le e) v

theorem SimpleGraph.degree_deleteVerts (G : SimpleGraph α) (S : Set α) (v : α)
    [Finite ((G.deleteVerts S).neighborSet v)] [Finite (G.neighborSet v)] :
    (G.deleteVerts S).degree v ≤ G.degree v :=
  SimpleGraph.degree_mono (G.deleteVerts_le S) v

theorem SimpleGraph.degree_deleteVert (G : SimpleGraph α) (u v : α)
    [Finite ((G.deleteVert u).neighborSet v)] [Finite (G.neighborSet v)] :
    (G.deleteVert u).degree v ≤ G.degree v :=
  SimpleGraph.degree_mono (G.deleteVert_le u) v

theorem SimpleGraph.degree_deleteEdgesBetween (G : SimpleGraph α) (u w v : α)
    [Finite ((G.deleteEdgesBetween u w).neighborSet v)] [Finite (G.neighborSet v)] :
    (G.deleteEdgesBetween u w).degree v ≤ G.degree v :=
  SimpleGraph.degree_mono (G.deleteEdgesBetween_le u w) v

theorem DiGraph.outDegree_induce (G : DiGraph α β) (S : Set α) (v : α)
    [Finite ((G.induce S).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.induce S).outDegree v ≤ G.outDegree v :=
  DiGraph.outDegree_mono (G.induce_le S) v

theorem DiGraph.inDegree_induce (G : DiGraph α β) (S : Set α) (v : α)
    [Finite ((G.induce S).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.induce S).inDegree v ≤ G.inDegree v :=
  DiGraph.inDegree_mono (G.induce_le S) v

theorem DiGraph.outDegree_deleteEdges (G : DiGraph α β) (F : Set (Arc α β)) (v : α)
    [Finite ((G.deleteEdges F).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteEdges F).outDegree v ≤ G.outDegree v :=
  DiGraph.outDegree_mono (G.deleteEdges_le F) v

theorem DiGraph.inDegree_deleteEdges (G : DiGraph α β) (F : Set (Arc α β)) (v : α)
    [Finite ((G.deleteEdges F).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteEdges F).inDegree v ≤ G.inDegree v :=
  DiGraph.inDegree_mono (G.deleteEdges_le F) v

theorem DiGraph.outDegree_deleteEdge (G : DiGraph α β) (a : Arc α β) (v : α)
    [Finite ((G.deleteEdge a).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteEdge a).outDegree v ≤ G.outDegree v :=
  DiGraph.outDegree_mono (G.deleteEdge_le a) v

theorem DiGraph.inDegree_deleteEdge (G : DiGraph α β) (a : Arc α β) (v : α)
    [Finite ((G.deleteEdge a).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteEdge a).inDegree v ≤ G.inDegree v :=
  DiGraph.inDegree_mono (G.deleteEdge_le a) v

theorem DiGraph.outDegree_deleteVerts (G : DiGraph α β) (S : Set α) (v : α)
    [Finite ((G.deleteVerts S).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteVerts S).outDegree v ≤ G.outDegree v :=
  DiGraph.outDegree_mono (G.deleteVerts_le S) v

theorem DiGraph.inDegree_deleteVerts (G : DiGraph α β) (S : Set α) (v : α)
    [Finite ((G.deleteVerts S).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteVerts S).inDegree v ≤ G.inDegree v :=
  DiGraph.inDegree_mono (G.deleteVerts_le S) v

theorem DiGraph.outDegree_deleteVert (G : DiGraph α β) (u v : α)
    [Finite ((G.deleteVert u).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteVert u).outDegree v ≤ G.outDegree v :=
  DiGraph.outDegree_mono (G.deleteVert_le u) v

theorem DiGraph.inDegree_deleteVert (G : DiGraph α β) (u v : α)
    [Finite ((G.deleteVert u).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteVert u).inDegree v ≤ G.inDegree v :=
  DiGraph.inDegree_mono (G.deleteVert_le u) v

theorem DiGraph.outDegree_deleteArcsFromTo (G : DiGraph α β) (u w v : α)
    [Finite ((G.deleteArcsFromTo u w).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteArcsFromTo u w).outDegree v ≤ G.outDegree v :=
  DiGraph.outDegree_mono (G.deleteArcsFromTo_le u w) v

theorem DiGraph.inDegree_deleteArcsFromTo (G : DiGraph α β) (u w v : α)
    [Finite ((G.deleteArcsFromTo u w).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteArcsFromTo u w).inDegree v ≤ G.inDegree v :=
  DiGraph.inDegree_mono (G.deleteArcsFromTo_le u w) v

theorem SimpleDiGraph.outDegree_induce (G : SimpleDiGraph α) (S : Set α) (v : α)
    [Finite ((G.induce S).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.induce S).outDegree v ≤ G.outDegree v :=
  SimpleDiGraph.outDegree_mono (G.induce_le S) v

theorem SimpleDiGraph.inDegree_induce (G : SimpleDiGraph α) (S : Set α) (v : α)
    [Finite ((G.induce S).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.induce S).inDegree v ≤ G.inDegree v :=
  SimpleDiGraph.inDegree_mono (G.induce_le S) v

theorem SimpleDiGraph.outDegree_deleteEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) (v : α)
    [Finite ((G.deleteEdges F).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteEdges F).outDegree v ≤ G.outDegree v :=
  SimpleDiGraph.outDegree_mono (G.deleteEdges_le F) v

theorem SimpleDiGraph.inDegree_deleteEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) (v : α)
    [Finite ((G.deleteEdges F).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteEdges F).inDegree v ≤ G.inDegree v :=
  SimpleDiGraph.inDegree_mono (G.deleteEdges_le F) v

theorem SimpleDiGraph.outDegree_deleteEdge (G : SimpleDiGraph α) (a : α × α) (v : α)
    [Finite ((G.deleteEdge a).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteEdge a).outDegree v ≤ G.outDegree v :=
  SimpleDiGraph.outDegree_mono (G.deleteEdge_le a) v

theorem SimpleDiGraph.inDegree_deleteEdge (G : SimpleDiGraph α) (a : α × α) (v : α)
    [Finite ((G.deleteEdge a).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteEdge a).inDegree v ≤ G.inDegree v :=
  SimpleDiGraph.inDegree_mono (G.deleteEdge_le a) v

theorem SimpleDiGraph.outDegree_deleteVerts (G : SimpleDiGraph α) (S : Set α) (v : α)
    [Finite ((G.deleteVerts S).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteVerts S).outDegree v ≤ G.outDegree v :=
  SimpleDiGraph.outDegree_mono (G.deleteVerts_le S) v

theorem SimpleDiGraph.inDegree_deleteVerts (G : SimpleDiGraph α) (S : Set α) (v : α)
    [Finite ((G.deleteVerts S).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteVerts S).inDegree v ≤ G.inDegree v :=
  SimpleDiGraph.inDegree_mono (G.deleteVerts_le S) v

theorem SimpleDiGraph.outDegree_deleteVert (G : SimpleDiGraph α) (u v : α)
    [Finite ((G.deleteVert u).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteVert u).outDegree v ≤ G.outDegree v :=
  SimpleDiGraph.outDegree_mono (G.deleteVert_le u) v

theorem SimpleDiGraph.inDegree_deleteVert (G : SimpleDiGraph α) (u v : α)
    [Finite ((G.deleteVert u).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteVert u).inDegree v ≤ G.inDegree v :=
  SimpleDiGraph.inDegree_mono (G.deleteVert_le u) v

theorem SimpleDiGraph.outDegree_deleteArcsFromTo (G : SimpleDiGraph α) (u w v : α)
    [Finite ((G.deleteArcsFromTo u w).outIncidenceSet v)] [Finite (G.outIncidenceSet v)] :
    (G.deleteArcsFromTo u w).outDegree v ≤ G.outDegree v :=
  SimpleDiGraph.outDegree_mono (G.deleteArcsFromTo_le u w) v

theorem SimpleDiGraph.inDegree_deleteArcsFromTo (G : SimpleDiGraph α) (u w v : α)
    [Finite ((G.deleteArcsFromTo u w).inIncidenceSet v)] [Finite (G.inIncidenceSet v)] :
    (G.deleteArcsFromTo u w).inDegree v ≤ G.inDegree v :=
  SimpleDiGraph.inDegree_mono (G.deleteArcsFromTo_le u w) v

/-! ## Basic degree consequences used by the Moore development -/

/-- A vertex of simple degree at least two has a neighbor different from any fixed vertex. -/
theorem SimpleGraph.exists_neighbor_ne_of_two_le_degree (G : SimpleGraph α) {v w : α}
    [Finite (G.neighborSet v)] (hdeg : 2 ≤ G.degree v) :
    ∃ u : α, G.Adj v u ∧ u ≠ w := by
  obtain ⟨u, hu, huw⟩ := Set.exists_ne_of_one_lt_ncard
    (by rw [G.ncard_neighborSet_eq_degree v]; exact lt_of_lt_of_le Nat.one_lt_two hdeg) w
  exact ⟨u, hu, huw⟩

/-- A nonempty simple graph of minimum degree at least two contains an edge. -/
theorem SimpleGraph.exists_adj_of_nonempty_of_two_le_degree (G : SimpleGraph α)
    [Finite V(G)] (hne : V(G).Nonempty)
    (hmin : ∀ v : α, v ∈ V(G) → 2 ≤ G.degree v) :
    ∃ u v : α, G.Adj u v := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, huv, _⟩ := G.exists_neighbor_ne_of_two_le_degree
    (v := u) (w := u) (hmin u hu)
  exact ⟨u, v, huv⟩

/-! ## Finite-graph extrema -/

private theorem Graph.vertexFinset_nonempty (G : Graph α β) [Finite V(G)] [Nonempty V(G)] :
    G.vertexFinset.Nonempty := by
  let v : V(G) := Classical.choice (inferInstance : Nonempty V(G))
  exact ⟨v, G.mem_vertexFinset.mpr v.property⟩

private theorem SimpleGraph.vertexFinset_nonempty (G : SimpleGraph α) [Finite V(G)]
    [Nonempty V(G)] : G.vertexFinset.Nonempty := by
  let v : V(G) := Classical.choice (inferInstance : Nonempty V(G))
  exact ⟨v, G.mem_vertexFinset.mpr v.property⟩

private theorem DiGraph.vertexFinset_nonempty (G : DiGraph α β) [Finite V(G)] [Nonempty V(G)] :
    G.vertexFinset.Nonempty := by
  let v : V(G) := Classical.choice (inferInstance : Nonempty V(G))
  exact ⟨v, G.mem_vertexFinset.mpr v.property⟩

private theorem SimpleDiGraph.vertexFinset_nonempty (G : SimpleDiGraph α) [Finite V(G)]
    [Nonempty V(G)] : G.vertexFinset.Nonempty := by
  let v : V(G) := Classical.choice (inferInstance : Nonempty V(G))
  exact ⟨v, G.mem_vertexFinset.mpr v.property⟩

/-- The maximum degree of a finite general graph; it is zero when the vertex set is empty. -/
noncomputable def Graph.maxDegree (G : Graph α β) [Finite V(G)] [Finite E(G)] : ℕ :=
  G.vertexFinset.sup fun v => G.degree v

/-- The minimum degree of a finite nonempty general graph. -/
noncomputable def Graph.minDegree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] : ℕ :=
  G.vertexFinset.inf' G.vertexFinset_nonempty fun v => G.degree v

/-- The maximum degree of a finite simple graph; it is zero when the vertex set is empty. -/
noncomputable def SimpleGraph.maxDegree (G : SimpleGraph α) [Finite V(G)] : ℕ :=
  G.vertexFinset.sup fun v => G.degree v

/-- The minimum degree of a finite nonempty simple graph. -/
noncomputable def SimpleGraph.minDegree (G : SimpleGraph α) [Finite V(G)] [Nonempty V(G)] : ℕ :=
  G.vertexFinset.inf' G.vertexFinset_nonempty fun v => G.degree v

/-- The maximum out-degree of a finite general directed graph; it is zero when the vertex set is
empty. -/
noncomputable def DiGraph.maxOutDegree (G : DiGraph α β) [Finite V(G)] [Finite E(G)] : ℕ :=
  G.vertexFinset.sup fun v => G.outDegree v

/-- The minimum out-degree of a finite nonempty general directed graph. -/
noncomputable def DiGraph.minOutDegree (G : DiGraph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] : ℕ :=
  G.vertexFinset.inf' G.vertexFinset_nonempty fun v => G.outDegree v

/-- The maximum in-degree of a finite general directed graph; it is zero when the vertex set is
empty. -/
noncomputable def DiGraph.maxInDegree (G : DiGraph α β) [Finite V(G)] [Finite E(G)] : ℕ :=
  G.vertexFinset.sup fun v => G.inDegree v

/-- The minimum in-degree of a finite nonempty general directed graph. -/
noncomputable def DiGraph.minInDegree (G : DiGraph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] : ℕ :=
  G.vertexFinset.inf' G.vertexFinset_nonempty fun v => G.inDegree v

/-- The maximum out-degree of a finite simple directed graph; it is zero when the vertex set is
empty. -/
noncomputable def SimpleDiGraph.maxOutDegree (G : SimpleDiGraph α) [Finite V(G)] : ℕ :=
  G.vertexFinset.sup fun v => G.outDegree v

/-- The minimum out-degree of a finite nonempty simple directed graph. -/
noncomputable def SimpleDiGraph.minOutDegree (G : SimpleDiGraph α) [Finite V(G)]
    [Nonempty V(G)] : ℕ :=
  G.vertexFinset.inf' G.vertexFinset_nonempty fun v => G.outDegree v

/-- The maximum in-degree of a finite simple directed graph; it is zero when the vertex set is
empty. -/
noncomputable def SimpleDiGraph.maxInDegree (G : SimpleDiGraph α) [Finite V(G)] : ℕ :=
  G.vertexFinset.sup fun v => G.inDegree v

/-- The minimum in-degree of a finite nonempty simple directed graph. -/
noncomputable def SimpleDiGraph.minInDegree (G : SimpleDiGraph α) [Finite V(G)]
    [Nonempty V(G)] : ℕ :=
  G.vertexFinset.inf' G.vertexFinset_nonempty fun v => G.inDegree v

/-! ### Undirected extrema API -/

theorem Graph.degree_le_maxDegree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    {v : α} (hv : v ∈ V(G)) : G.degree v ≤ G.maxDegree :=
  Finset.le_sup (f := fun v => G.degree v) (G.mem_vertexFinset.mpr hv)

theorem Graph.maxDegree_le_of_forall_degree_le (G : Graph α β) [Finite V(G)] [Finite E(G)]
    {d : ℕ} (h : ∀ v, v ∈ V(G) → G.degree v ≤ d) : G.maxDegree ≤ d :=
  Finset.sup_le fun v hv => h v (G.mem_vertexFinset.mp hv)

theorem Graph.exists_maxDegree_eq_degree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] : ∃ v, v ∈ V(G) ∧ G.maxDegree = G.degree v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup G.vertexFinset
    G.vertexFinset_nonempty (fun v => G.degree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmax⟩

theorem Graph.minDegree_le_degree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] {v : α} (hv : v ∈ V(G)) : G.minDegree ≤ G.degree v :=
  Finset.inf'_le (f := fun v => G.degree v) (G.mem_vertexFinset.mpr hv)

theorem Graph.le_minDegree_of_forall_le_degree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] {d : ℕ} (h : ∀ v, v ∈ V(G) → d ≤ G.degree v) :
    d ≤ G.minDegree :=
  Finset.le_inf' G.vertexFinset_nonempty (fun v => G.degree v) fun v hv =>
    h v (G.mem_vertexFinset.mp hv)

theorem Graph.exists_minDegree_eq_degree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] : ∃ v, v ∈ V(G) ∧ G.minDegree = G.degree v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_mem_eq_inf' G.vertexFinset_nonempty
    (fun v => G.degree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmin⟩

theorem Graph.minDegree_le_maxDegree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] : G.minDegree ≤ G.maxDegree := by
  obtain ⟨v, hv, hmin⟩ := G.exists_minDegree_eq_degree
  rw [hmin]
  exact G.degree_le_maxDegree hv

theorem SimpleGraph.degree_le_maxDegree (G : SimpleGraph α) [Finite V(G)]
    {v : α} (hv : v ∈ V(G)) : G.degree v ≤ G.maxDegree :=
  Finset.le_sup (f := fun v => G.degree v) (G.mem_vertexFinset.mpr hv)

theorem SimpleGraph.maxDegree_le_of_forall_degree_le (G : SimpleGraph α) [Finite V(G)]
    {d : ℕ} (h : ∀ v, v ∈ V(G) → G.degree v ≤ d) : G.maxDegree ≤ d :=
  Finset.sup_le fun v hv => h v (G.mem_vertexFinset.mp hv)

theorem SimpleGraph.exists_maxDegree_eq_degree (G : SimpleGraph α) [Finite V(G)]
    [Nonempty V(G)] : ∃ v, v ∈ V(G) ∧ G.maxDegree = G.degree v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup G.vertexFinset
    G.vertexFinset_nonempty (fun v => G.degree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmax⟩

theorem SimpleGraph.minDegree_le_degree (G : SimpleGraph α) [Finite V(G)] [Nonempty V(G)]
    {v : α} (hv : v ∈ V(G)) : G.minDegree ≤ G.degree v :=
  Finset.inf'_le (f := fun v => G.degree v) (G.mem_vertexFinset.mpr hv)

theorem SimpleGraph.le_minDegree_of_forall_le_degree (G : SimpleGraph α) [Finite V(G)]
    [Nonempty V(G)] {d : ℕ} (h : ∀ v, v ∈ V(G) → d ≤ G.degree v) :
    d ≤ G.minDegree :=
  Finset.le_inf' G.vertexFinset_nonempty (fun v => G.degree v) fun v hv =>
    h v (G.mem_vertexFinset.mp hv)

theorem SimpleGraph.exists_minDegree_eq_degree (G : SimpleGraph α) [Finite V(G)]
    [Nonempty V(G)] : ∃ v, v ∈ V(G) ∧ G.minDegree = G.degree v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_mem_eq_inf' G.vertexFinset_nonempty
    (fun v => G.degree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmin⟩

theorem SimpleGraph.minDegree_le_maxDegree (G : SimpleGraph α) [Finite V(G)] [Nonempty V(G)] :
    G.minDegree ≤ G.maxDegree := by
  obtain ⟨v, hv, hmin⟩ := G.exists_minDegree_eq_degree
  rw [hmin]
  exact G.degree_le_maxDegree hv

/-! ### Directed extrema API -/

theorem DiGraph.outDegree_le_maxOutDegree (G : DiGraph α β) [Finite V(G)] [Finite E(G)]
    {v : α} (hv : v ∈ V(G)) : G.outDegree v ≤ G.maxOutDegree :=
  Finset.le_sup (f := fun v => G.outDegree v) (G.mem_vertexFinset.mpr hv)

theorem DiGraph.maxOutDegree_le_of_forall_outDegree_le (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → G.outDegree v ≤ d) : G.maxOutDegree ≤ d :=
  Finset.sup_le fun v hv => h v (G.mem_vertexFinset.mp hv)

theorem DiGraph.exists_maxOutDegree_eq_outDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.maxOutDegree = G.outDegree v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup G.vertexFinset
    G.vertexFinset_nonempty (fun v => G.outDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmax⟩

theorem DiGraph.minOutDegree_le_outDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] {v : α} (hv : v ∈ V(G)) :
    G.minOutDegree ≤ G.outDegree v :=
  Finset.inf'_le (f := fun v => G.outDegree v) (G.mem_vertexFinset.mpr hv)

theorem DiGraph.le_minOutDegree_of_forall_le_outDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → d ≤ G.outDegree v) : d ≤ G.minOutDegree :=
  Finset.le_inf' G.vertexFinset_nonempty (fun v => G.outDegree v) fun v hv =>
    h v (G.mem_vertexFinset.mp hv)

theorem DiGraph.exists_minOutDegree_eq_outDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.minOutDegree = G.outDegree v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_mem_eq_inf' G.vertexFinset_nonempty
    (fun v => G.outDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmin⟩

theorem DiGraph.minOutDegree_le_maxOutDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] : G.minOutDegree ≤ G.maxOutDegree := by
  obtain ⟨v, hv, hmin⟩ := G.exists_minOutDegree_eq_outDegree
  rw [hmin]
  exact G.outDegree_le_maxOutDegree hv

theorem DiGraph.inDegree_le_maxInDegree (G : DiGraph α β) [Finite V(G)] [Finite E(G)]
    {v : α} (hv : v ∈ V(G)) : G.inDegree v ≤ G.maxInDegree :=
  Finset.le_sup (f := fun v => G.inDegree v) (G.mem_vertexFinset.mpr hv)

theorem DiGraph.maxInDegree_le_of_forall_inDegree_le (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → G.inDegree v ≤ d) : G.maxInDegree ≤ d :=
  Finset.sup_le fun v hv => h v (G.mem_vertexFinset.mp hv)

theorem DiGraph.exists_maxInDegree_eq_inDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.maxInDegree = G.inDegree v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup G.vertexFinset
    G.vertexFinset_nonempty (fun v => G.inDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmax⟩

theorem DiGraph.minInDegree_le_inDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] {v : α} (hv : v ∈ V(G)) :
    G.minInDegree ≤ G.inDegree v :=
  Finset.inf'_le (f := fun v => G.inDegree v) (G.mem_vertexFinset.mpr hv)

theorem DiGraph.le_minInDegree_of_forall_le_inDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → d ≤ G.inDegree v) : d ≤ G.minInDegree :=
  Finset.le_inf' G.vertexFinset_nonempty (fun v => G.inDegree v) fun v hv =>
    h v (G.mem_vertexFinset.mp hv)

theorem DiGraph.exists_minInDegree_eq_inDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.minInDegree = G.inDegree v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_mem_eq_inf' G.vertexFinset_nonempty
    (fun v => G.inDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmin⟩

theorem DiGraph.minInDegree_le_maxInDegree (G : DiGraph α β)
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] : G.minInDegree ≤ G.maxInDegree := by
  obtain ⟨v, hv, hmin⟩ := G.exists_minInDegree_eq_inDegree
  rw [hmin]
  exact G.inDegree_le_maxInDegree hv

theorem SimpleDiGraph.outDegree_le_maxOutDegree (G : SimpleDiGraph α) [Finite V(G)]
    {v : α} (hv : v ∈ V(G)) : G.outDegree v ≤ G.maxOutDegree :=
  Finset.le_sup (f := fun v => G.outDegree v) (G.mem_vertexFinset.mpr hv)

theorem SimpleDiGraph.maxOutDegree_le_of_forall_outDegree_le
    (G : SimpleDiGraph α) [Finite V(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → G.outDegree v ≤ d) : G.maxOutDegree ≤ d :=
  Finset.sup_le fun v hv => h v (G.mem_vertexFinset.mp hv)

theorem SimpleDiGraph.exists_maxOutDegree_eq_outDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.maxOutDegree = G.outDegree v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup G.vertexFinset
    G.vertexFinset_nonempty (fun v => G.outDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmax⟩

theorem SimpleDiGraph.minOutDegree_le_outDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] {v : α} (hv : v ∈ V(G)) :
    G.minOutDegree ≤ G.outDegree v :=
  Finset.inf'_le (f := fun v => G.outDegree v) (G.mem_vertexFinset.mpr hv)

theorem SimpleDiGraph.le_minOutDegree_of_forall_le_outDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → d ≤ G.outDegree v) : d ≤ G.minOutDegree :=
  Finset.le_inf' G.vertexFinset_nonempty (fun v => G.outDegree v) fun v hv =>
    h v (G.mem_vertexFinset.mp hv)

theorem SimpleDiGraph.exists_minOutDegree_eq_outDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.minOutDegree = G.outDegree v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_mem_eq_inf' G.vertexFinset_nonempty
    (fun v => G.outDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmin⟩

theorem SimpleDiGraph.minOutDegree_le_maxOutDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] :
    G.minOutDegree ≤ G.maxOutDegree := by
  obtain ⟨v, hv, hmin⟩ := G.exists_minOutDegree_eq_outDegree
  rw [hmin]
  exact G.outDegree_le_maxOutDegree hv

theorem SimpleDiGraph.inDegree_le_maxInDegree (G : SimpleDiGraph α) [Finite V(G)]
    {v : α} (hv : v ∈ V(G)) : G.inDegree v ≤ G.maxInDegree :=
  Finset.le_sup (f := fun v => G.inDegree v) (G.mem_vertexFinset.mpr hv)

theorem SimpleDiGraph.maxInDegree_le_of_forall_inDegree_le
    (G : SimpleDiGraph α) [Finite V(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → G.inDegree v ≤ d) : G.maxInDegree ≤ d :=
  Finset.sup_le fun v hv => h v (G.mem_vertexFinset.mp hv)

theorem SimpleDiGraph.exists_maxInDegree_eq_inDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.maxInDegree = G.inDegree v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup G.vertexFinset
    G.vertexFinset_nonempty (fun v => G.inDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmax⟩

theorem SimpleDiGraph.minInDegree_le_inDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] {v : α} (hv : v ∈ V(G)) :
    G.minInDegree ≤ G.inDegree v :=
  Finset.inf'_le (f := fun v => G.inDegree v) (G.mem_vertexFinset.mpr hv)

theorem SimpleDiGraph.le_minInDegree_of_forall_le_inDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] {d : ℕ}
    (h : ∀ v, v ∈ V(G) → d ≤ G.inDegree v) : d ≤ G.minInDegree :=
  Finset.le_inf' G.vertexFinset_nonempty (fun v => G.inDegree v) fun v hv =>
    h v (G.mem_vertexFinset.mp hv)

theorem SimpleDiGraph.exists_minInDegree_eq_inDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] :
    ∃ v, v ∈ V(G) ∧ G.minInDegree = G.inDegree v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_mem_eq_inf' G.vertexFinset_nonempty
    (fun v => G.inDegree v)
  exact ⟨v, G.mem_vertexFinset.mp hv, hmin⟩

theorem SimpleDiGraph.minInDegree_le_maxInDegree
    (G : SimpleDiGraph α) [Finite V(G)] [Nonempty V(G)] :
    G.minInDegree ≤ G.maxInDegree := by
  obtain ⟨v, hv, hmin⟩ := G.exists_minInDegree_eq_inDegree
  rw [hmin]
  exact G.inDegree_le_maxInDegree hv

end GraphLib
