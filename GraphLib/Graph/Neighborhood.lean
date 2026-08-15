/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Reverse

/-!
# Graph neighborhoods

This file defines neighborhoods as adjacency fibers for all four graph types. Undirected
neighborhoods are symmetric. Directed neighborhoods distinguish outgoing from incoming
adjacency. A loop places its vertex in its own neighborhood, while parallel actual edges do not
change a neighborhood set.
-/

namespace GraphLib

open scoped GraphLib

variable {α β : Type*}

/-! ## Definitions and membership -/

/-- The vertices adjacent to `v` in a general undirected graph. A loop at `v` includes `v`. -/
def Graph.neighborSet (G : Graph α β) (v : α) : Set α :=
  {u | G.Adj v u}

/-- The vertices adjacent to `v` in a simple undirected graph. -/
def SimpleGraph.neighborSet (G : SimpleGraph α) (v : α) : Set α :=
  {u | G.Adj v u}

/-- The targets of arcs whose source is `v` in a general directed graph. -/
def DiGraph.outNeighborSet (G : DiGraph α β) (v : α) : Set α :=
  {u | G.Adj v u}

/-- The sources of arcs whose target is `v` in a general directed graph. -/
def DiGraph.inNeighborSet (G : DiGraph α β) (v : α) : Set α :=
  {u | G.Adj u v}

/-- The targets of arcs whose source is `v` in a simple directed graph. -/
def SimpleDiGraph.outNeighborSet (G : SimpleDiGraph α) (v : α) : Set α :=
  {u | G.Adj v u}

/-- The sources of arcs whose target is `v` in a simple directed graph. -/
def SimpleDiGraph.inNeighborSet (G : SimpleDiGraph α) (v : α) : Set α :=
  {u | G.Adj u v}

@[simp] theorem Graph.mem_neighborSet (G : Graph α β) (v u : α) :
    u ∈ G.neighborSet v ↔ G.Adj v u := Iff.rfl

@[simp] theorem SimpleGraph.mem_neighborSet (G : SimpleGraph α) (v u : α) :
    u ∈ G.neighborSet v ↔ G.Adj v u := Iff.rfl

@[simp] theorem DiGraph.mem_outNeighborSet (G : DiGraph α β) (v u : α) :
    u ∈ G.outNeighborSet v ↔ G.Adj v u := Iff.rfl

@[simp] theorem DiGraph.mem_inNeighborSet (G : DiGraph α β) (v u : α) :
    u ∈ G.inNeighborSet v ↔ G.Adj u v := Iff.rfl

@[simp] theorem SimpleDiGraph.mem_outNeighborSet (G : SimpleDiGraph α) (v u : α) :
    u ∈ G.outNeighborSet v ↔ G.Adj v u := Iff.rfl

@[simp] theorem SimpleDiGraph.mem_inNeighborSet (G : SimpleDiGraph α) (v u : α) :
    u ∈ G.inNeighborSet v ↔ G.Adj u v := Iff.rfl

/-! ## Vertex-set containment and empty fibers -/

theorem Graph.neighborSet_subset_vertexSet (G : Graph α β) (v : α) :
    G.neighborSet v ⊆ V(G) := fun _ h => h.right_mem

theorem SimpleGraph.neighborSet_subset_vertexSet (G : SimpleGraph α) (v : α) :
    G.neighborSet v ⊆ V(G) := fun _ h => h.right_mem

theorem DiGraph.outNeighborSet_subset_vertexSet (G : DiGraph α β) (v : α) :
    G.outNeighborSet v ⊆ V(G) := fun _ h => h.target_mem

theorem DiGraph.inNeighborSet_subset_vertexSet (G : DiGraph α β) (v : α) :
    G.inNeighborSet v ⊆ V(G) := fun _ h => h.source_mem

theorem SimpleDiGraph.outNeighborSet_subset_vertexSet (G : SimpleDiGraph α) (v : α) :
    G.outNeighborSet v ⊆ V(G) := fun _ h => h.target_mem

theorem SimpleDiGraph.inNeighborSet_subset_vertexSet (G : SimpleDiGraph α) (v : α) :
    G.inNeighborSet v ⊆ V(G) := fun _ h => h.source_mem

@[simp] theorem Graph.neighborSet_eq_empty_of_not_mem (G : Graph α β) {v : α}
    (hv : v ∉ V(G)) : G.neighborSet v = ∅ := by
  ext u
  simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  exact fun h => hv h.left_mem

@[simp] theorem SimpleGraph.neighborSet_eq_empty_of_not_mem (G : SimpleGraph α) {v : α}
    (hv : v ∉ V(G)) : G.neighborSet v = ∅ := by
  ext u
  simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  exact fun h => hv h.left_mem

@[simp] theorem DiGraph.outNeighborSet_eq_empty_of_not_mem (G : DiGraph α β) {v : α}
    (hv : v ∉ V(G)) : G.outNeighborSet v = ∅ := by
  ext u
  simp only [mem_outNeighborSet, Set.mem_empty_iff_false, iff_false]
  exact fun h => hv h.source_mem

@[simp] theorem DiGraph.inNeighborSet_eq_empty_of_not_mem (G : DiGraph α β) {v : α}
    (hv : v ∉ V(G)) : G.inNeighborSet v = ∅ := by
  ext u
  simp only [mem_inNeighborSet, Set.mem_empty_iff_false, iff_false]
  exact fun h => hv h.target_mem

@[simp] theorem SimpleDiGraph.outNeighborSet_eq_empty_of_not_mem
    (G : SimpleDiGraph α) {v : α} (hv : v ∉ V(G)) : G.outNeighborSet v = ∅ := by
  ext u
  simp only [mem_outNeighborSet, Set.mem_empty_iff_false, iff_false]
  exact fun h => hv h.source_mem

@[simp] theorem SimpleDiGraph.inNeighborSet_eq_empty_of_not_mem
    (G : SimpleDiGraph α) {v : α} (hv : v ∉ V(G)) : G.inNeighborSet v = ∅ := by
  ext u
  simp only [mem_inNeighborSet, Set.mem_empty_iff_false, iff_false]
  exact fun h => hv h.target_mem

/-! ## Symmetry and subgraph monotonicity -/

theorem Graph.mem_neighborSet_comm (G : Graph α β) (u v : α) :
    u ∈ G.neighborSet v ↔ v ∈ G.neighborSet u := G.adj_comm v u

theorem SimpleGraph.mem_neighborSet_comm (G : SimpleGraph α) (u v : α) :
    u ∈ G.neighborSet v ↔ v ∈ G.neighborSet u := G.adj_comm v u

theorem Graph.neighborSet_mono {H G : Graph α β} (hHG : H ≤ G) (v : α) :
    H.neighborSet v ⊆ G.neighborSet v := fun _ h => h.mono hHG

theorem SimpleGraph.neighborSet_mono {H G : SimpleGraph α} (hHG : H ≤ G) (v : α) :
    H.neighborSet v ⊆ G.neighborSet v := fun _ h => h.mono hHG

theorem DiGraph.outNeighborSet_mono {H G : DiGraph α β} (hHG : H ≤ G) (v : α) :
    H.outNeighborSet v ⊆ G.outNeighborSet v := fun _ h => h.mono hHG

theorem DiGraph.inNeighborSet_mono {H G : DiGraph α β} (hHG : H ≤ G) (v : α) :
    H.inNeighborSet v ⊆ G.inNeighborSet v := fun _ h => h.mono hHG

theorem SimpleDiGraph.outNeighborSet_mono {H G : SimpleDiGraph α} (hHG : H ≤ G) (v : α) :
    H.outNeighborSet v ⊆ G.outNeighborSet v := fun _ h => h.mono hHG

theorem SimpleDiGraph.inNeighborSet_mono {H G : SimpleDiGraph α} (hHG : H ≤ G) (v : α) :
    H.inNeighborSet v ⊆ G.inNeighborSet v := fun _ h => h.mono hHG

/-! ## Induction, restriction, and deletion -/

@[simp] theorem Graph.neighborSet_induce (G : Graph α β) (S : Set α) (v : α) :
    (G.induce S).neighborSet v = {u | v ∈ S ∧ u ∈ G.neighborSet v ∩ S} := by
  ext u
  simp [neighborSet, and_left_comm]

@[simp] theorem SimpleGraph.neighborSet_induce (G : SimpleGraph α) (S : Set α) (v : α) :
    (G.induce S).neighborSet v = {u | v ∈ S ∧ u ∈ G.neighborSet v ∩ S} := by
  ext u
  simp [neighborSet, and_left_comm]

@[simp] theorem DiGraph.outNeighborSet_induce (G : DiGraph α β) (S : Set α) (v : α) :
    (G.induce S).outNeighborSet v = {u | v ∈ S ∧ u ∈ G.outNeighborSet v ∩ S} := by
  ext u
  simp [outNeighborSet, and_left_comm]

@[simp] theorem DiGraph.inNeighborSet_induce (G : DiGraph α β) (S : Set α) (v : α) :
    (G.induce S).inNeighborSet v = {u | v ∈ S ∧ u ∈ G.inNeighborSet v ∩ S} := by
  ext u
  simp only [inNeighborSet, Set.mem_setOf_eq, DiGraph.induce_adj, Set.mem_inter_iff]
  tauto

@[simp] theorem SimpleDiGraph.outNeighborSet_induce
    (G : SimpleDiGraph α) (S : Set α) (v : α) :
    (G.induce S).outNeighborSet v = {u | v ∈ S ∧ u ∈ G.outNeighborSet v ∩ S} := by
  ext u
  simp [outNeighborSet, and_left_comm]

@[simp] theorem SimpleDiGraph.inNeighborSet_induce
    (G : SimpleDiGraph α) (S : Set α) (v : α) :
    (G.induce S).inNeighborSet v = {u | v ∈ S ∧ u ∈ G.inNeighborSet v ∩ S} := by
  ext u
  simp only [inNeighborSet, Set.mem_setOf_eq, SimpleDiGraph.induce_adj, Set.mem_inter_iff]
  tauto

theorem Graph.neighborSet_restrictEdges_subset (G : Graph α β)
    (F : Set (Edge α β)) (v : α) :
    (G.restrictEdges F).neighborSet v ⊆ G.neighborSet v :=
  Graph.neighborSet_mono (G.restrictEdges_le F) v

theorem SimpleGraph.neighborSet_restrictEdges_subset (G : SimpleGraph α)
    (F : Set (Sym2 α)) (v : α) :
    (G.restrictEdges F).neighborSet v ⊆ G.neighborSet v :=
  SimpleGraph.neighborSet_mono (G.restrictEdges_le F) v

theorem DiGraph.outNeighborSet_restrictEdges_subset (G : DiGraph α β)
    (F : Set (Arc α β)) (v : α) :
    (G.restrictEdges F).outNeighborSet v ⊆ G.outNeighborSet v :=
  DiGraph.outNeighborSet_mono (G.restrictEdges_le F) v

theorem DiGraph.inNeighborSet_restrictEdges_subset (G : DiGraph α β)
    (F : Set (Arc α β)) (v : α) :
    (G.restrictEdges F).inNeighborSet v ⊆ G.inNeighborSet v :=
  DiGraph.inNeighborSet_mono (G.restrictEdges_le F) v

theorem SimpleDiGraph.outNeighborSet_restrictEdges_subset (G : SimpleDiGraph α)
    (F : Set (α × α)) (v : α) :
    (G.restrictEdges F).outNeighborSet v ⊆ G.outNeighborSet v :=
  SimpleDiGraph.outNeighborSet_mono (G.restrictEdges_le F) v

theorem SimpleDiGraph.inNeighborSet_restrictEdges_subset (G : SimpleDiGraph α)
    (F : Set (α × α)) (v : α) :
    (G.restrictEdges F).inNeighborSet v ⊆ G.inNeighborSet v :=
  SimpleDiGraph.inNeighborSet_mono (G.restrictEdges_le F) v

theorem Graph.neighborSet_deleteEdges_subset (G : Graph α β)
    (F : Set (Edge α β)) (v : α) :
    (G.deleteEdges F).neighborSet v ⊆ G.neighborSet v :=
  Graph.neighborSet_mono (G.deleteEdges_le F) v

theorem SimpleGraph.neighborSet_deleteEdges_subset (G : SimpleGraph α)
    (F : Set (Sym2 α)) (v : α) :
    (G.deleteEdges F).neighborSet v ⊆ G.neighborSet v :=
  SimpleGraph.neighborSet_mono (G.deleteEdges_le F) v

theorem DiGraph.outNeighborSet_deleteEdges_subset (G : DiGraph α β)
    (F : Set (Arc α β)) (v : α) :
    (G.deleteEdges F).outNeighborSet v ⊆ G.outNeighborSet v :=
  DiGraph.outNeighborSet_mono (G.deleteEdges_le F) v

theorem DiGraph.inNeighborSet_deleteEdges_subset (G : DiGraph α β)
    (F : Set (Arc α β)) (v : α) :
    (G.deleteEdges F).inNeighborSet v ⊆ G.inNeighborSet v :=
  DiGraph.inNeighborSet_mono (G.deleteEdges_le F) v

theorem SimpleDiGraph.outNeighborSet_deleteEdges_subset (G : SimpleDiGraph α)
    (F : Set (α × α)) (v : α) :
    (G.deleteEdges F).outNeighborSet v ⊆ G.outNeighborSet v :=
  SimpleDiGraph.outNeighborSet_mono (G.deleteEdges_le F) v

theorem SimpleDiGraph.inNeighborSet_deleteEdges_subset (G : SimpleDiGraph α)
    (F : Set (α × α)) (v : α) :
    (G.deleteEdges F).inNeighborSet v ⊆ G.inNeighborSet v :=
  SimpleDiGraph.inNeighborSet_mono (G.deleteEdges_le F) v

@[simp] theorem Graph.neighborSet_deleteVerts (G : Graph α β) (S : Set α) (v : α) :
    (G.deleteVerts S).neighborSet v =
      {u | v ∉ S ∧ u ∈ G.neighborSet v \ S} := by
  simp only [Graph.deleteVerts, neighborSet_induce]
  ext u
  simp [Set.mem_diff]

@[simp] theorem SimpleGraph.neighborSet_deleteVerts
    (G : SimpleGraph α) (S : Set α) (v : α) :
    (G.deleteVerts S).neighborSet v =
      {u | v ∉ S ∧ u ∈ G.neighborSet v \ S} := by
  simp only [SimpleGraph.deleteVerts, neighborSet_induce]
  ext u
  simp [Set.mem_diff]

@[simp] theorem DiGraph.outNeighborSet_deleteVerts
    (G : DiGraph α β) (S : Set α) (v : α) :
    (G.deleteVerts S).outNeighborSet v =
      {u | v ∉ S ∧ u ∈ G.outNeighborSet v \ S} := by
  simp only [DiGraph.deleteVerts, outNeighborSet_induce]
  ext u
  simp [Set.mem_diff]

@[simp] theorem DiGraph.inNeighborSet_deleteVerts
    (G : DiGraph α β) (S : Set α) (v : α) :
    (G.deleteVerts S).inNeighborSet v =
      {u | v ∉ S ∧ u ∈ G.inNeighborSet v \ S} := by
  simp only [DiGraph.deleteVerts, inNeighborSet_induce]
  ext u
  simp [Set.mem_diff]

@[simp] theorem SimpleDiGraph.outNeighborSet_deleteVerts
    (G : SimpleDiGraph α) (S : Set α) (v : α) :
    (G.deleteVerts S).outNeighborSet v =
      {u | v ∉ S ∧ u ∈ G.outNeighborSet v \ S} := by
  simp only [SimpleDiGraph.deleteVerts, outNeighborSet_induce]
  ext u
  simp [Set.mem_diff]

@[simp] theorem SimpleDiGraph.inNeighborSet_deleteVerts
    (G : SimpleDiGraph α) (S : Set α) (v : α) :
    (G.deleteVerts S).inNeighborSet v =
      {u | v ∉ S ∧ u ∈ G.inNeighborSet v \ S} := by
  simp only [SimpleDiGraph.deleteVerts, inNeighborSet_induce]
  ext u
  simp [Set.mem_diff]

/-! ## Directed reversal -/

@[simp] theorem DiGraph.outNeighborSet_reverse (G : DiGraph α β) (v : α) :
    G.reverse.outNeighborSet v = G.inNeighborSet v := by
  ext u
  simp [outNeighborSet, inNeighborSet]

@[simp] theorem DiGraph.inNeighborSet_reverse (G : DiGraph α β) (v : α) :
    G.reverse.inNeighborSet v = G.outNeighborSet v := by
  ext u
  simp [outNeighborSet, inNeighborSet]

@[simp] theorem SimpleDiGraph.outNeighborSet_reverse (G : SimpleDiGraph α) (v : α) :
    G.reverse.outNeighborSet v = G.inNeighborSet v := by
  ext u
  simp [outNeighborSet, inNeighborSet]

@[simp] theorem SimpleDiGraph.inNeighborSet_reverse (G : SimpleDiGraph α) (v : α) :
    G.reverse.inNeighborSet v = G.outNeighborSet v := by
  ext u
  simp [outNeighborSet, inNeighborSet]

end GraphLib
