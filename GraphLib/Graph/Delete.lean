/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Subgraph

/-!
# Graph deletion

This file defines same-carrier edge and vertex deletion for all four GraphLib graph families.
Deleting an edge means deleting an actual edge or arc value. The endpoint-wide operations
`deleteEdgesBetween` and `deleteArcsFromTo` are separate because they remove every parallel
actual value with the specified endpoints.
-/

namespace GraphLib
variable {α β : Type*}

open scoped GraphLib

/-! ## Definitions -/

/-- Delete the actual bundled edges in `F`, retaining every vertex. -/
def Graph.deleteEdges (G : Graph α β) (F : Set (Edge α β)) : Graph α β :=
  G.restrictEdges Fᶜ

/-- Delete one actual bundled edge, retaining every vertex. -/
def Graph.deleteEdge (G : Graph α β) (e : Edge α β) : Graph α β :=
  G.deleteEdges {e}

/-- Delete the actual endpoint-pair edges in `F`, retaining every vertex. -/
def SimpleGraph.deleteEdges (G : SimpleGraph α) (F : Set (Sym2 α)) : SimpleGraph α :=
  G.restrictEdges Fᶜ

/-- Delete one actual endpoint-pair edge, retaining every vertex. -/
def SimpleGraph.deleteEdge (G : SimpleGraph α) (e : Sym2 α) : SimpleGraph α :=
  G.deleteEdges {e}

/-- Delete the actual bundled arcs in `F`, retaining every vertex. -/
def DiGraph.deleteEdges (G : DiGraph α β) (F : Set (Arc α β)) : DiGraph α β :=
  G.restrictEdges Fᶜ

/-- Delete one actual bundled arc, retaining every vertex. -/
def DiGraph.deleteEdge (G : DiGraph α β) (a : Arc α β) : DiGraph α β :=
  G.deleteEdges {a}

/-- Delete the actual ordered-pair arcs in `F`, retaining every vertex. -/
def SimpleDiGraph.deleteEdges (G : SimpleDiGraph α) (F : Set (α × α)) : SimpleDiGraph α :=
  G.restrictEdges Fᶜ

/-- Delete one actual ordered-pair arc, retaining every vertex. -/
def SimpleDiGraph.deleteEdge (G : SimpleDiGraph α) (a : α × α) : SimpleDiGraph α :=
  G.deleteEdges {a}

/-- Delete the vertices in `S` and every actual edge incident with one of them. -/
def Graph.deleteVerts (G : Graph α β) (S : Set α) : Graph α β :=
  G.induce Sᶜ

/-- Delete one vertex and every actual edge incident with it. -/
def Graph.deleteVert (G : Graph α β) (v : α) : Graph α β :=
  G.deleteVerts {v}

/-- Delete the vertices in `S` and every edge incident with one of them. -/
def SimpleGraph.deleteVerts (G : SimpleGraph α) (S : Set α) : SimpleGraph α :=
  G.induce Sᶜ

/-- Delete one vertex and every edge incident with it. -/
def SimpleGraph.deleteVert (G : SimpleGraph α) (v : α) : SimpleGraph α :=
  G.deleteVerts {v}

/-- Delete the vertices in `S` and every actual arc incident with one of them. -/
def DiGraph.deleteVerts (G : DiGraph α β) (S : Set α) : DiGraph α β :=
  G.induce Sᶜ

/-- Delete one vertex and every actual arc incident with it. -/
def DiGraph.deleteVert (G : DiGraph α β) (v : α) : DiGraph α β :=
  G.deleteVerts {v}

/-- Delete the vertices in `S` and every arc incident with one of them. -/
def SimpleDiGraph.deleteVerts (G : SimpleDiGraph α) (S : Set α) : SimpleDiGraph α :=
  G.induce Sᶜ

/-- Delete one vertex and every arc incident with it. -/
def SimpleDiGraph.deleteVert (G : SimpleDiGraph α) (v : α) : SimpleDiGraph α :=
  G.deleteVerts {v}

/-- Delete every actual bundled edge whose unordered endpoints are `u` and `v`. -/
def Graph.deleteEdgesBetween (G : Graph α β) (u v : α) : Graph α β :=
  G.deleteEdges {e | e.endpoints = s(u, v)}

/-- Delete the edge whose unordered endpoints are `u` and `v`, if present. -/
def SimpleGraph.deleteEdgesBetween (G : SimpleGraph α) (u v : α) : SimpleGraph α :=
  G.deleteEdges {e | e = s(u, v)}

/-- Delete every actual bundled arc from source `u` to target `v`. -/
def DiGraph.deleteArcsFromTo (G : DiGraph α β) (u v : α) : DiGraph α β :=
  G.deleteEdges {a | a.source = u ∧ a.target = v}

/-- Delete the arc from source `u` to target `v`, if present. -/
def SimpleDiGraph.deleteArcsFromTo (G : SimpleDiGraph α) (u v : α) : SimpleDiGraph α :=
  G.deleteEdges {a | a.1 = u ∧ a.2 = v}

/-! ## General undirected graphs -/

namespace Graph

@[simp] theorem vertexSet_deleteEdges (G : Graph α β) (F : Set (Edge α β)) :
    V(G.deleteEdges F) = V(G) := rfl

@[simp] theorem edgeSet_deleteEdges (G : Graph α β) (F : Set (Edge α β)) :
    E(G.deleteEdges F) = E(G) \ F := rfl

@[simp] theorem mem_vertexSet_deleteEdges (G : Graph α β) (F : Set (Edge α β)) (v : α) :
    v ∈ V(G.deleteEdges F) ↔ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_deleteEdges (G : Graph α β) (F : Set (Edge α β))
    (e : Edge α β) : e ∈ E(G.deleteEdges F) ↔ e ∈ E(G) ∧ e ∉ F := Iff.rfl

@[simp] theorem deleteEdges_isLink (G : Graph α β) (F : Set (Edge α β))
    (e : Edge α β) (u v : α) :
    (G.deleteEdges F).IsLink e u v ↔ G.IsLink e u v ∧ e ∉ F := by
  simp [deleteEdges]
  tauto

@[simp] theorem deleteEdges_inc (G : Graph α β) (F : Set (Edge α β))
    (e : Edge α β) (v : α) :
    (G.deleteEdges F).Inc e v ↔ G.Inc e v ∧ e ∉ F := by
  simp [deleteEdges]

/-- Adjacency after deletion is witnessed by an actual edge not in the deleted set. -/
@[simp] theorem deleteEdges_adj (G : Graph α β) (F : Set (Edge α β)) (u v : α) :
    (G.deleteEdges F).Adj u v ↔ ∃ e, G.IsLink e u v ∧ e ∉ F := by
  simp only [adj_iff_exists_isLink, deleteEdges_isLink]

@[simp] theorem deleteEdges_le (G : Graph α β) (F : Set (Edge α β)) :
    G.deleteEdges F ≤ G := G.restrictEdges_le Fᶜ

@[simp] theorem deleteEdges_empty (G : Graph α β) : G.deleteEdges ∅ = G := by
  simp [deleteEdges]

@[simp] theorem edgeSet_deleteEdges_univ (G : Graph α β) : E(G.deleteEdges Set.univ) = ∅ := by
  simp

@[simp] theorem deleteEdges_deleteEdges (G : Graph α β) (F K : Set (Edge α β)) :
    (G.deleteEdges F).deleteEdges K = G.deleteEdges (F ∪ K) := by
  ext <;> simp [Set.mem_union, and_left_comm, and_assoc]

@[simp] theorem deleteEdges_idem (G : Graph α β) (F : Set (Edge α β)) :
    (G.deleteEdges F).deleteEdges F = G.deleteEdges F := by simp

theorem deleteEdges_mono {G H : Graph α β} {F K : Set (Edge α β)}
    (hGH : G ≤ H) (hKF : K ⊆ F) : G.deleteEdges F ≤ H.deleteEdges K :=
  G.restrictEdges_mono hGH (Set.compl_subset_compl.mpr hKF)

theorem deleteEdges_mono_left {G H : Graph α β} (hGH : G ≤ H) (F : Set (Edge α β)) :
    G.deleteEdges F ≤ H.deleteEdges F := deleteEdges_mono hGH (fun _ h => h)

theorem deleteEdges_anti_right (G : Graph α β) {F K : Set (Edge α β)} (hFK : F ⊆ K) :
    G.deleteEdges K ≤ G.deleteEdges F := deleteEdges_mono le_rfl hFK

theorem deleteEdges_singleton (G : Graph α β) (e : Edge α β) :
    G.deleteEdges {e} = G.deleteEdge e := rfl

@[simp] theorem vertexSet_deleteEdge (G : Graph α β) (e : Edge α β) :
    V(G.deleteEdge e) = V(G) := rfl

@[simp] theorem mem_edgeSet_deleteEdge (G : Graph α β) (e f : Edge α β) :
    f ∈ E(G.deleteEdge e) ↔ f ∈ E(G) ∧ f ≠ e := by simp [deleteEdge]

@[simp] theorem not_mem_edgeSet_deleteEdge (G : Graph α β) (e : Edge α β) :
    e ∉ E(G.deleteEdge e) := fun h => (G.mem_edgeSet_deleteEdge e e).mp h |>.2 rfl

@[simp] theorem deleteEdge_le (G : Graph α β) (e : Edge α β) :
    G.deleteEdge e ≤ G := G.deleteEdges_le {e}

@[simp] theorem deleteEdge_of_not_mem (G : Graph α β) {e : Edge α β} (he : e ∉ E(G)) :
    G.deleteEdge e = G := by
  apply Graph.ext
  · rfl
  · ext f
    rw [mem_edgeSet_deleteEdge]
    constructor
    · exact And.left
    · intro hf
      exact ⟨hf, fun hfe => he (hfe ▸ hf)⟩

theorem deleteEdge_comm (G : Graph α β) (e f : Edge α β) :
    (G.deleteEdge e).deleteEdge f = (G.deleteEdge f).deleteEdge e := by
  simp only [deleteEdge, deleteEdges_deleteEdges]
  rw [Set.union_comm]

@[simp] theorem deleteEdge_idem (G : Graph α β) (e : Edge α β) :
    (G.deleteEdge e).deleteEdge e = G.deleteEdge e := by simp [deleteEdge]

@[simp] theorem vertexSet_deleteVerts (G : Graph α β) (S : Set α) :
    V(G.deleteVerts S) = V(G) \ S := by ext; simp [deleteVerts, and_comm]

@[simp] theorem mem_vertexSet_deleteVerts (G : Graph α β) (S : Set α) (v : α) :
    v ∈ V(G.deleteVerts S) ↔ v ∈ V(G) ∧ v ∉ S := by simp [deleteVerts, and_comm]

@[simp] theorem mem_edgeSet_deleteVerts (G : Graph α β) (S : Set α) (e : Edge α β) :
    e ∈ E(G.deleteVerts S) ↔ e ∈ E(G) ∧ ∀ v ∈ e.endpoints, v ∉ S := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_isLink (G : Graph α β) (S : Set α)
    (e : Edge α β) (u v : α) :
    (G.deleteVerts S).IsLink e u v ↔ G.IsLink e u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).IsLink e u v ↔ _
  rw [Graph.induce_isLink]
  simp

@[simp] theorem deleteVerts_inc (G : Graph α β) (S : Set α)
    (e : Edge α β) (v : α) :
    (G.deleteVerts S).Inc e v ↔ G.Inc e v ∧ ∀ w ∈ e.endpoints, w ∉ S := by
  change (G.induce Sᶜ).Inc e v ↔ _
  rw [Graph.induce_inc]
  simp

@[simp] theorem deleteVerts_adj (G : Graph α β) (S : Set α) (u v : α) :
    (G.deleteVerts S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).Adj u v ↔ _
  rw [Graph.induce_adj]
  simp

@[simp] theorem deleteVerts_le (G : Graph α β) (S : Set α) : G.deleteVerts S ≤ G :=
  G.induce_le Sᶜ

@[simp] theorem deleteVerts_empty (G : Graph α β) : G.deleteVerts ∅ = G := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_univ (G : Graph α β) : G.deleteVerts Set.univ = ⊥ := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_deleteVerts (G : Graph α β) (S T : Set α) :
    (G.deleteVerts S).deleteVerts T = G.deleteVerts (S ∪ T) := by
  simp only [deleteVerts, induce_induce]
  congr 1
  ext v
  simp

@[simp] theorem deleteVerts_idem (G : Graph α β) (S : Set α) :
    (G.deleteVerts S).deleteVerts S = G.deleteVerts S := by simp

theorem deleteVerts_mono {G H : Graph α β} {S T : Set α}
    (hGH : G ≤ H) (hTS : T ⊆ S) : G.deleteVerts S ≤ H.deleteVerts T :=
  induce_mono hGH (Set.compl_subset_compl.mpr hTS)

theorem deleteVerts_mono_left {G H : Graph α β} (hGH : G ≤ H) (S : Set α) :
    G.deleteVerts S ≤ H.deleteVerts S := deleteVerts_mono hGH (fun _ h => h)

theorem deleteVerts_anti_right (G : Graph α β) {S T : Set α} (hST : S ⊆ T) :
    G.deleteVerts T ≤ G.deleteVerts S := deleteVerts_mono le_rfl hST

theorem deleteVerts_singleton (G : Graph α β) (v : α) :
    G.deleteVerts {v} = G.deleteVert v := rfl

@[simp] theorem mem_vertexSet_deleteVert (G : Graph α β) (u v : α) :
    u ∈ V(G.deleteVert v) ↔ u ∈ V(G) ∧ u ≠ v := by simp [deleteVert]

@[simp] theorem not_mem_vertexSet_deleteVert (G : Graph α β) (v : α) :
    v ∉ V(G.deleteVert v) := fun h => (G.mem_vertexSet_deleteVert v v).mp h |>.2 rfl

@[simp] theorem deleteVert_le (G : Graph α β) (v : α) : G.deleteVert v ≤ G :=
  G.deleteVerts_le {v}

@[simp] theorem deleteVert_of_not_mem (G : Graph α β) {v : α} (hv : v ∉ V(G)) :
    G.deleteVert v = G := by
  apply Graph.ext
  · ext u
    rw [mem_vertexSet_deleteVert]
    constructor
    · exact And.left
    · intro hu
      exact ⟨hu, fun huv => hv (huv ▸ hu)⟩
  · ext e
    change e ∈ E(G.deleteVerts {v}) ↔ e ∈ E(G)
    rw [mem_edgeSet_deleteVerts]
    simp only [Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro he
      exact ⟨he, fun u hu huv => hv (huv ▸ G.endpoints_mem e he u hu)⟩

theorem deleteVert_comm (G : Graph α β) (u v : α) :
    (G.deleteVert u).deleteVert v = (G.deleteVert v).deleteVert u := by
  simp only [deleteVert, deleteVerts_deleteVerts]
  rw [Set.union_comm]

@[simp] theorem deleteVert_idem (G : Graph α β) (v : α) :
    (G.deleteVert v).deleteVert v = G.deleteVert v := by simp [deleteVert]

theorem deleteEdges_deleteVerts (G : Graph α β) (F : Set (Edge α β)) (S : Set α) :
    (G.deleteEdges F).deleteVerts S = (G.deleteVerts S).deleteEdges F := by
  ext <;> simp [deleteEdges, deleteVerts, and_assoc, and_comm]

@[simp] theorem mem_edgeSet_deleteEdgesBetween (G : Graph α β) (u v : α) (e : Edge α β) :
    e ∈ E(G.deleteEdgesBetween u v) ↔ e ∈ E(G) ∧ e.endpoints ≠ s(u, v) := by
  simp [deleteEdgesBetween]

@[simp] theorem deleteEdgesBetween_le (G : Graph α β) (u v : α) :
    G.deleteEdgesBetween u v ≤ G := G.deleteEdges_le _

@[simp] theorem deleteEdgesBetween_isLink (G : Graph α β) (u v : α)
    (e : Edge α β) (x y : α) :
    (G.deleteEdgesBetween u v).IsLink e x y ↔
      G.IsLink e x y ∧ e.endpoints ≠ s(u, v) := by
  simp [deleteEdgesBetween]
  tauto

@[simp] theorem deleteEdgesBetween_inc (G : Graph α β) (u v : α)
    (e : Edge α β) (x : α) :
    (G.deleteEdgesBetween u v).Inc e x ↔
      G.Inc e x ∧ e.endpoints ≠ s(u, v) := by
  simp [deleteEdgesBetween]

@[simp] theorem deleteEdgesBetween_adj (G : Graph α β) (u v x y : α) :
    (G.deleteEdgesBetween u v).Adj x y ↔
      ∃ e, G.IsLink e x y ∧ e.endpoints ≠ s(u, v) := by
  simp [deleteEdgesBetween]

@[simp] theorem deleteEdgesBetween_comm (G : Graph α β) (u v : α) :
    G.deleteEdgesBetween u v = G.deleteEdgesBetween v u := by
  simp only [deleteEdgesBetween, Sym2.eq_swap]

end Graph

/-! ## Simple undirected graphs -/

namespace SimpleGraph

@[simp] theorem vertexSet_deleteEdges (G : SimpleGraph α) (F : Set (Sym2 α)) :
    V(G.deleteEdges F) = V(G) := rfl

@[simp] theorem edgeSet_deleteEdges (G : SimpleGraph α) (F : Set (Sym2 α)) :
    E(G.deleteEdges F) = E(G) \ F := rfl

@[simp] theorem mem_edgeSet_deleteEdges (G : SimpleGraph α) (F : Set (Sym2 α)) (e : Sym2 α) :
    e ∈ E(G.deleteEdges F) ↔ e ∈ E(G) ∧ e ∉ F := Iff.rfl

@[simp] theorem deleteEdges_isLink (G : SimpleGraph α) (F : Set (Sym2 α))
    (e : Sym2 α) (u v : α) :
    (G.deleteEdges F).IsLink e u v ↔ G.IsLink e u v ∧ e ∉ F := by
  simp [deleteEdges]
  tauto

@[simp] theorem deleteEdges_inc (G : SimpleGraph α) (F : Set (Sym2 α))
    (e : Sym2 α) (v : α) :
    (G.deleteEdges F).Inc e v ↔ G.Inc e v ∧ e ∉ F := by
  simp [deleteEdges]

@[simp] theorem deleteEdges_adj (G : SimpleGraph α) (F : Set (Sym2 α)) (u v : α) :
    (G.deleteEdges F).Adj u v ↔ G.Adj u v ∧ s(u, v) ∉ F := by
  simp [deleteEdges, SimpleGraph.adj_iff]

@[simp] theorem deleteEdges_le (G : SimpleGraph α) (F : Set (Sym2 α)) :
    G.deleteEdges F ≤ G := G.restrictEdges_le Fᶜ

@[simp] theorem deleteEdges_empty (G : SimpleGraph α) : G.deleteEdges ∅ = G := by
  simp [deleteEdges]

@[simp] theorem deleteEdges_deleteEdges (G : SimpleGraph α) (F K : Set (Sym2 α)) :
    (G.deleteEdges F).deleteEdges K = G.deleteEdges (F ∪ K) := by
  ext <;> simp [Set.mem_union, and_left_comm, and_assoc]

@[simp] theorem deleteEdges_idem (G : SimpleGraph α) (F : Set (Sym2 α)) :
    (G.deleteEdges F).deleteEdges F = G.deleteEdges F := by simp

theorem deleteEdges_mono {G H : SimpleGraph α} {F K : Set (Sym2 α)}
    (hGH : G ≤ H) (hKF : K ⊆ F) : G.deleteEdges F ≤ H.deleteEdges K :=
  G.restrictEdges_mono hGH (Set.compl_subset_compl.mpr hKF)

theorem deleteEdges_mono_left {G H : SimpleGraph α} (hGH : G ≤ H) (F : Set (Sym2 α)) :
    G.deleteEdges F ≤ H.deleteEdges F := deleteEdges_mono hGH (fun _ h => h)

theorem deleteEdges_anti_right (G : SimpleGraph α) {F K : Set (Sym2 α)} (hFK : F ⊆ K) :
    G.deleteEdges K ≤ G.deleteEdges F := deleteEdges_mono le_rfl hFK

theorem deleteEdges_singleton (G : SimpleGraph α) (e : Sym2 α) :
    G.deleteEdges {e} = G.deleteEdge e := rfl

@[simp] theorem mem_edgeSet_deleteEdge (G : SimpleGraph α) (e f : Sym2 α) :
    f ∈ E(G.deleteEdge e) ↔ f ∈ E(G) ∧ f ≠ e := by simp [deleteEdge]

@[simp] theorem not_mem_edgeSet_deleteEdge (G : SimpleGraph α) (e : Sym2 α) :
    e ∉ E(G.deleteEdge e) := fun h => (G.mem_edgeSet_deleteEdge e e).mp h |>.2 rfl

@[simp] theorem deleteEdge_le (G : SimpleGraph α) (e : Sym2 α) : G.deleteEdge e ≤ G :=
  G.deleteEdges_le {e}

@[simp] theorem deleteEdge_of_not_mem (G : SimpleGraph α) {e : Sym2 α} (he : e ∉ E(G)) :
    G.deleteEdge e = G := by
  apply SimpleGraph.ext
  · rfl
  · ext f
    rw [mem_edgeSet_deleteEdge]
    constructor
    · exact And.left
    · intro hf
      exact ⟨hf, fun hfe => he (hfe ▸ hf)⟩

theorem deleteEdge_comm (G : SimpleGraph α) (e f : Sym2 α) :
    (G.deleteEdge e).deleteEdge f = (G.deleteEdge f).deleteEdge e := by
  simp only [deleteEdge, deleteEdges_deleteEdges]
  rw [Set.union_comm]

@[simp] theorem deleteEdge_idem (G : SimpleGraph α) (e : Sym2 α) :
    (G.deleteEdge e).deleteEdge e = G.deleteEdge e := by simp [deleteEdge]

@[simp] theorem vertexSet_deleteVerts (G : SimpleGraph α) (S : Set α) :
    V(G.deleteVerts S) = V(G) \ S := by ext; simp [deleteVerts, and_comm]

@[simp] theorem mem_vertexSet_deleteVerts (G : SimpleGraph α) (S : Set α) (v : α) :
    v ∈ V(G.deleteVerts S) ↔ v ∈ V(G) ∧ v ∉ S := by simp [deleteVerts, and_comm]

@[simp] theorem mem_edgeSet_deleteVerts (G : SimpleGraph α) (S : Set α) (e : Sym2 α) :
    e ∈ E(G.deleteVerts S) ↔ e ∈ E(G) ∧ ∀ v ∈ e, v ∉ S := by simp [deleteVerts]

@[simp] theorem deleteVerts_isLink (G : SimpleGraph α) (S : Set α)
    (e : Sym2 α) (u v : α) :
    (G.deleteVerts S).IsLink e u v ↔ G.IsLink e u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).IsLink e u v ↔ _
  rw [SimpleGraph.induce_isLink]
  simp

@[simp] theorem deleteVerts_inc (G : SimpleGraph α) (S : Set α)
    (e : Sym2 α) (v : α) :
    (G.deleteVerts S).Inc e v ↔ G.Inc e v ∧ ∀ w ∈ e, w ∉ S := by
  change (G.induce Sᶜ).Inc e v ↔ _
  rw [SimpleGraph.induce_inc]
  simp

@[simp] theorem deleteVerts_adj (G : SimpleGraph α) (S : Set α) (u v : α) :
    (G.deleteVerts S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).Adj u v ↔ _
  rw [SimpleGraph.induce_adj]
  simp

@[simp] theorem deleteVerts_le (G : SimpleGraph α) (S : Set α) : G.deleteVerts S ≤ G :=
  G.induce_le Sᶜ

@[simp] theorem deleteVerts_empty (G : SimpleGraph α) : G.deleteVerts ∅ = G := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_univ (G : SimpleGraph α) : G.deleteVerts Set.univ = ⊥ := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_deleteVerts (G : SimpleGraph α) (S T : Set α) :
    (G.deleteVerts S).deleteVerts T = G.deleteVerts (S ∪ T) := by
  simp only [deleteVerts, induce_induce]
  congr 1
  ext v
  simp

@[simp] theorem deleteVerts_idem (G : SimpleGraph α) (S : Set α) :
    (G.deleteVerts S).deleteVerts S = G.deleteVerts S := by simp

theorem deleteVerts_mono {G H : SimpleGraph α} {S T : Set α}
    (hGH : G ≤ H) (hTS : T ⊆ S) : G.deleteVerts S ≤ H.deleteVerts T :=
  induce_mono hGH (Set.compl_subset_compl.mpr hTS)

theorem deleteVerts_mono_left {G H : SimpleGraph α} (hGH : G ≤ H) (S : Set α) :
    G.deleteVerts S ≤ H.deleteVerts S := deleteVerts_mono hGH (fun _ h => h)

theorem deleteVerts_anti_right (G : SimpleGraph α) {S T : Set α} (hST : S ⊆ T) :
    G.deleteVerts T ≤ G.deleteVerts S := deleteVerts_mono le_rfl hST

theorem deleteVerts_singleton (G : SimpleGraph α) (v : α) :
    G.deleteVerts {v} = G.deleteVert v := rfl

@[simp] theorem mem_vertexSet_deleteVert (G : SimpleGraph α) (u v : α) :
    u ∈ V(G.deleteVert v) ↔ u ∈ V(G) ∧ u ≠ v := by simp [deleteVert]

@[simp] theorem not_mem_vertexSet_deleteVert (G : SimpleGraph α) (v : α) :
    v ∉ V(G.deleteVert v) := fun h => (G.mem_vertexSet_deleteVert v v).mp h |>.2 rfl

@[simp] theorem deleteVert_le (G : SimpleGraph α) (v : α) : G.deleteVert v ≤ G :=
  G.deleteVerts_le {v}

@[simp] theorem deleteVert_of_not_mem (G : SimpleGraph α) {v : α} (hv : v ∉ V(G)) :
    G.deleteVert v = G := by
  apply SimpleGraph.ext
  · ext u
    rw [mem_vertexSet_deleteVert]
    constructor
    · exact And.left
    · intro hu
      exact ⟨hu, fun huv => hv (huv ▸ hu)⟩
  · ext e
    change e ∈ E(G.deleteVerts {v}) ↔ e ∈ E(G)
    rw [mem_edgeSet_deleteVerts]
    simp only [Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro he
      exact ⟨he, fun u hu huv => hv (huv ▸ G.endpoints_mem e he u hu)⟩

theorem deleteVert_comm (G : SimpleGraph α) (u v : α) :
    (G.deleteVert u).deleteVert v = (G.deleteVert v).deleteVert u := by
  simp only [deleteVert, deleteVerts_deleteVerts]
  rw [Set.union_comm]

@[simp] theorem deleteVert_idem (G : SimpleGraph α) (v : α) :
    (G.deleteVert v).deleteVert v = G.deleteVert v := by simp [deleteVert]

theorem deleteEdges_deleteVerts (G : SimpleGraph α) (F : Set (Sym2 α)) (S : Set α) :
    (G.deleteEdges F).deleteVerts S = (G.deleteVerts S).deleteEdges F := by
  ext <;> simp [deleteEdges, deleteVerts, and_assoc, and_comm]

@[simp] theorem mem_edgeSet_deleteEdgesBetween (G : SimpleGraph α) (u v : α) (e : Sym2 α) :
    e ∈ E(G.deleteEdgesBetween u v) ↔ e ∈ E(G) ∧ e ≠ s(u, v) := by
  simp [deleteEdgesBetween]

@[simp] theorem deleteEdgesBetween_le (G : SimpleGraph α) (u v : α) :
    G.deleteEdgesBetween u v ≤ G := G.deleteEdges_le _

@[simp] theorem deleteEdgesBetween_isLink (G : SimpleGraph α) (u v : α)
    (e : Sym2 α) (x y : α) :
    (G.deleteEdgesBetween u v).IsLink e x y ↔
      G.IsLink e x y ∧ e ≠ s(u, v) := by
  simp [deleteEdgesBetween]
  tauto

@[simp] theorem deleteEdgesBetween_inc (G : SimpleGraph α) (u v : α)
    (e : Sym2 α) (x : α) :
    (G.deleteEdgesBetween u v).Inc e x ↔
      G.Inc e x ∧ e ≠ s(u, v) := by
  simp [deleteEdgesBetween]

@[simp] theorem deleteEdgesBetween_adj (G : SimpleGraph α) (u v x y : α) :
    (G.deleteEdgesBetween u v).Adj x y ↔
      G.Adj x y ∧ s(x, y) ≠ s(u, v) := by
  simp [deleteEdgesBetween]

@[simp] theorem deleteEdgesBetween_comm (G : SimpleGraph α) (u v : α) :
    G.deleteEdgesBetween u v = G.deleteEdgesBetween v u := by
  simp only [deleteEdgesBetween, Sym2.eq_swap]

end SimpleGraph

/-! ## General directed graphs -/

namespace DiGraph

@[simp] theorem vertexSet_deleteEdges (G : DiGraph α β) (F : Set (Arc α β)) :
    V(G.deleteEdges F) = V(G) := rfl

@[simp] theorem edgeSet_deleteEdges (G : DiGraph α β) (F : Set (Arc α β)) :
    E(G.deleteEdges F) = E(G) \ F := rfl

@[simp] theorem mem_edgeSet_deleteEdges (G : DiGraph α β) (F : Set (Arc α β)) (a : Arc α β) :
    a ∈ E(G.deleteEdges F) ↔ a ∈ E(G) ∧ a ∉ F := Iff.rfl

@[simp] theorem deleteEdges_isArc (G : DiGraph α β) (F : Set (Arc α β))
    (a : Arc α β) (u v : α) :
    (G.deleteEdges F).IsArc a u v ↔ G.IsArc a u v ∧ a ∉ F := by
  simp [deleteEdges]
  tauto

@[simp] theorem deleteEdges_inc (G : DiGraph α β) (F : Set (Arc α β))
    (a : Arc α β) (v : α) :
    (G.deleteEdges F).Inc a v ↔ G.Inc a v ∧ a ∉ F := by
  simp [deleteEdges]

/-- Directed adjacency after deletion is witnessed by an actual arc not in the deleted set. -/
@[simp] theorem deleteEdges_adj (G : DiGraph α β) (F : Set (Arc α β)) (u v : α) :
    (G.deleteEdges F).Adj u v ↔ ∃ a, G.IsArc a u v ∧ a ∉ F := by
  simp only [adj_iff_exists_isArc, deleteEdges_isArc]

@[simp] theorem deleteEdges_le (G : DiGraph α β) (F : Set (Arc α β)) :
    G.deleteEdges F ≤ G := G.restrictEdges_le Fᶜ

@[simp] theorem deleteEdges_empty (G : DiGraph α β) : G.deleteEdges ∅ = G := by
  simp [deleteEdges]

@[simp] theorem deleteEdges_deleteEdges (G : DiGraph α β) (F K : Set (Arc α β)) :
    (G.deleteEdges F).deleteEdges K = G.deleteEdges (F ∪ K) := by
  ext <;> simp [Set.mem_union, and_left_comm, and_assoc]

@[simp] theorem deleteEdges_idem (G : DiGraph α β) (F : Set (Arc α β)) :
    (G.deleteEdges F).deleteEdges F = G.deleteEdges F := by simp

theorem deleteEdges_mono {G H : DiGraph α β} {F K : Set (Arc α β)}
    (hGH : G ≤ H) (hKF : K ⊆ F) : G.deleteEdges F ≤ H.deleteEdges K :=
  G.restrictEdges_mono hGH (Set.compl_subset_compl.mpr hKF)

theorem deleteEdges_mono_left {G H : DiGraph α β} (hGH : G ≤ H) (F : Set (Arc α β)) :
    G.deleteEdges F ≤ H.deleteEdges F := deleteEdges_mono hGH (fun _ h => h)

theorem deleteEdges_anti_right (G : DiGraph α β) {F K : Set (Arc α β)} (hFK : F ⊆ K) :
    G.deleteEdges K ≤ G.deleteEdges F := deleteEdges_mono le_rfl hFK

theorem deleteEdges_singleton (G : DiGraph α β) (a : Arc α β) :
    G.deleteEdges {a} = G.deleteEdge a := rfl

@[simp] theorem mem_edgeSet_deleteEdge (G : DiGraph α β) (a b : Arc α β) :
    b ∈ E(G.deleteEdge a) ↔ b ∈ E(G) ∧ b ≠ a := by simp [deleteEdge]

@[simp] theorem not_mem_edgeSet_deleteEdge (G : DiGraph α β) (a : Arc α β) :
    a ∉ E(G.deleteEdge a) := fun h => (G.mem_edgeSet_deleteEdge a a).mp h |>.2 rfl

@[simp] theorem deleteEdge_le (G : DiGraph α β) (a : Arc α β) : G.deleteEdge a ≤ G :=
  G.deleteEdges_le {a}

@[simp] theorem deleteEdge_of_not_mem (G : DiGraph α β) {a : Arc α β} (ha : a ∉ E(G)) :
    G.deleteEdge a = G := by
  apply DiGraph.ext
  · rfl
  · ext b
    rw [mem_edgeSet_deleteEdge]
    constructor
    · exact And.left
    · intro hb
      exact ⟨hb, fun hba => ha (hba ▸ hb)⟩

theorem deleteEdge_comm (G : DiGraph α β) (a b : Arc α β) :
    (G.deleteEdge a).deleteEdge b = (G.deleteEdge b).deleteEdge a := by
  simp only [deleteEdge, deleteEdges_deleteEdges]
  rw [Set.union_comm]

@[simp] theorem deleteEdge_idem (G : DiGraph α β) (a : Arc α β) :
    (G.deleteEdge a).deleteEdge a = G.deleteEdge a := by simp [deleteEdge]

@[simp] theorem vertexSet_deleteVerts (G : DiGraph α β) (S : Set α) :
    V(G.deleteVerts S) = V(G) \ S := by ext; simp [deleteVerts, and_comm]

@[simp] theorem mem_vertexSet_deleteVerts (G : DiGraph α β) (S : Set α) (v : α) :
    v ∈ V(G.deleteVerts S) ↔ v ∈ V(G) ∧ v ∉ S := by simp [deleteVerts, and_comm]

@[simp] theorem mem_edgeSet_deleteVerts (G : DiGraph α β) (S : Set α) (a : Arc α β) :
    a ∈ E(G.deleteVerts S) ↔ a ∈ E(G) ∧ a.source ∉ S ∧ a.target ∉ S := by
  change a ∈ E(G.induce Sᶜ) ↔ _
  rw [DiGraph.mem_edgeSet_induce]
  simp [and_left_comm]

@[simp] theorem deleteVerts_isArc (G : DiGraph α β) (S : Set α)
    (a : Arc α β) (u v : α) :
    (G.deleteVerts S).IsArc a u v ↔ G.IsArc a u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).IsArc a u v ↔ _
  rw [DiGraph.induce_isArc]
  simp

@[simp] theorem deleteVerts_inc (G : DiGraph α β) (S : Set α)
    (a : Arc α β) (v : α) :
    (G.deleteVerts S).Inc a v ↔ G.Inc a v ∧ a.source ∉ S ∧ a.target ∉ S := by
  change (G.induce Sᶜ).Inc a v ↔ _
  rw [DiGraph.induce_inc]
  simp [and_left_comm]

@[simp] theorem deleteVerts_adj (G : DiGraph α β) (S : Set α) (u v : α) :
    (G.deleteVerts S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).Adj u v ↔ _
  rw [DiGraph.induce_adj]
  simp

@[simp] theorem deleteVerts_le (G : DiGraph α β) (S : Set α) : G.deleteVerts S ≤ G :=
  G.induce_le Sᶜ

@[simp] theorem deleteVerts_empty (G : DiGraph α β) : G.deleteVerts ∅ = G := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_univ (G : DiGraph α β) : G.deleteVerts Set.univ = ⊥ := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_deleteVerts (G : DiGraph α β) (S T : Set α) :
    (G.deleteVerts S).deleteVerts T = G.deleteVerts (S ∪ T) := by
  simp only [deleteVerts, induce_induce]
  congr 1
  ext v
  simp

@[simp] theorem deleteVerts_idem (G : DiGraph α β) (S : Set α) :
    (G.deleteVerts S).deleteVerts S = G.deleteVerts S := by simp

theorem deleteVerts_mono {G H : DiGraph α β} {S T : Set α}
    (hGH : G ≤ H) (hTS : T ⊆ S) : G.deleteVerts S ≤ H.deleteVerts T :=
  induce_mono hGH (Set.compl_subset_compl.mpr hTS)

theorem deleteVerts_mono_left {G H : DiGraph α β} (hGH : G ≤ H) (S : Set α) :
    G.deleteVerts S ≤ H.deleteVerts S := deleteVerts_mono hGH (fun _ h => h)

theorem deleteVerts_anti_right (G : DiGraph α β) {S T : Set α} (hST : S ⊆ T) :
    G.deleteVerts T ≤ G.deleteVerts S := deleteVerts_mono le_rfl hST

theorem deleteVerts_singleton (G : DiGraph α β) (v : α) :
    G.deleteVerts {v} = G.deleteVert v := rfl

@[simp] theorem mem_vertexSet_deleteVert (G : DiGraph α β) (u v : α) :
    u ∈ V(G.deleteVert v) ↔ u ∈ V(G) ∧ u ≠ v := by simp [deleteVert]

@[simp] theorem not_mem_vertexSet_deleteVert (G : DiGraph α β) (v : α) :
    v ∉ V(G.deleteVert v) := fun h => (G.mem_vertexSet_deleteVert v v).mp h |>.2 rfl

@[simp] theorem deleteVert_le (G : DiGraph α β) (v : α) : G.deleteVert v ≤ G :=
  G.deleteVerts_le {v}

@[simp] theorem deleteVert_of_not_mem (G : DiGraph α β) {v : α} (hv : v ∉ V(G)) :
    G.deleteVert v = G := by
  apply DiGraph.ext
  · ext u
    rw [mem_vertexSet_deleteVert]
    constructor
    · exact And.left
    · intro hu
      exact ⟨hu, fun huv => hv (huv ▸ hu)⟩
  · ext a
    change a ∈ E(G.deleteVerts {v}) ↔ a ∈ E(G)
    rw [mem_edgeSet_deleteVerts]
    simp only [Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro ha
      exact ⟨ha, fun hs => hv (hs ▸ G.source_mem a ha),
        fun ht => hv (ht ▸ G.target_mem a ha)⟩

theorem deleteVert_comm (G : DiGraph α β) (u v : α) :
    (G.deleteVert u).deleteVert v = (G.deleteVert v).deleteVert u := by
  simp only [deleteVert, deleteVerts_deleteVerts]
  rw [Set.union_comm]

@[simp] theorem deleteVert_idem (G : DiGraph α β) (v : α) :
    (G.deleteVert v).deleteVert v = G.deleteVert v := by simp [deleteVert]

theorem deleteEdges_deleteVerts (G : DiGraph α β) (F : Set (Arc α β)) (S : Set α) :
    (G.deleteEdges F).deleteVerts S = (G.deleteVerts S).deleteEdges F := by
  ext <;> simp [deleteEdges, deleteVerts, and_left_comm, and_assoc, and_comm]

@[simp] theorem mem_edgeSet_deleteArcsFromTo (G : DiGraph α β) (u v : α) (a : Arc α β) :
    a ∈ E(G.deleteArcsFromTo u v) ↔
      a ∈ E(G) ∧ ¬ (a.source = u ∧ a.target = v) := by
  simp [deleteArcsFromTo]

@[simp] theorem deleteArcsFromTo_le (G : DiGraph α β) (u v : α) :
    G.deleteArcsFromTo u v ≤ G := G.deleteEdges_le _

@[simp] theorem deleteArcsFromTo_isArc (G : DiGraph α β) (u v : α)
    (a : Arc α β) (x y : α) :
    (G.deleteArcsFromTo u v).IsArc a x y ↔
      G.IsArc a x y ∧ ¬ (a.source = u ∧ a.target = v) := by
  simp [deleteArcsFromTo]
  tauto

@[simp] theorem deleteArcsFromTo_inc (G : DiGraph α β) (u v : α)
    (a : Arc α β) (x : α) :
    (G.deleteArcsFromTo u v).Inc a x ↔
      G.Inc a x ∧ ¬ (a.source = u ∧ a.target = v) := by
  simp [deleteArcsFromTo]

@[simp] theorem deleteArcsFromTo_adj (G : DiGraph α β) (u v x y : α) :
    (G.deleteArcsFromTo u v).Adj x y ↔
      ∃ a, G.IsArc a x y ∧ ¬ (a.source = u ∧ a.target = v) := by
  simp [deleteArcsFromTo]

end DiGraph

/-! ## Simple directed graphs -/

namespace SimpleDiGraph

@[simp] theorem vertexSet_deleteEdges (G : SimpleDiGraph α) (F : Set (α × α)) :
    V(G.deleteEdges F) = V(G) := rfl

@[simp] theorem edgeSet_deleteEdges (G : SimpleDiGraph α) (F : Set (α × α)) :
    E(G.deleteEdges F) = E(G) \ F := rfl

@[simp] theorem mem_edgeSet_deleteEdges (G : SimpleDiGraph α) (F : Set (α × α))
    (a : α × α) : a ∈ E(G.deleteEdges F) ↔ a ∈ E(G) ∧ a ∉ F := Iff.rfl

@[simp] theorem deleteEdges_isArc (G : SimpleDiGraph α) (F : Set (α × α))
    (a : α × α) (u v : α) :
    (G.deleteEdges F).IsArc a u v ↔ G.IsArc a u v ∧ a ∉ F := by
  simp [deleteEdges]
  tauto

@[simp] theorem deleteEdges_inc (G : SimpleDiGraph α) (F : Set (α × α))
    (a : α × α) (v : α) :
    (G.deleteEdges F).Inc a v ↔ G.Inc a v ∧ a ∉ F := by
  simp [deleteEdges]

@[simp] theorem deleteEdges_adj (G : SimpleDiGraph α) (F : Set (α × α)) (u v : α) :
    (G.deleteEdges F).Adj u v ↔ G.Adj u v ∧ (u, v) ∉ F := by
  simp [deleteEdges, SimpleDiGraph.adj_iff]

@[simp] theorem deleteEdges_le (G : SimpleDiGraph α) (F : Set (α × α)) :
    G.deleteEdges F ≤ G := G.restrictEdges_le Fᶜ

@[simp] theorem deleteEdges_empty (G : SimpleDiGraph α) : G.deleteEdges ∅ = G := by
  simp [deleteEdges]

@[simp] theorem deleteEdges_deleteEdges (G : SimpleDiGraph α) (F K : Set (α × α)) :
    (G.deleteEdges F).deleteEdges K = G.deleteEdges (F ∪ K) := by
  ext <;> simp [Set.mem_union, and_left_comm, and_assoc]

@[simp] theorem deleteEdges_idem (G : SimpleDiGraph α) (F : Set (α × α)) :
    (G.deleteEdges F).deleteEdges F = G.deleteEdges F := by simp

theorem deleteEdges_mono {G H : SimpleDiGraph α} {F K : Set (α × α)}
    (hGH : G ≤ H) (hKF : K ⊆ F) : G.deleteEdges F ≤ H.deleteEdges K :=
  G.restrictEdges_mono hGH (Set.compl_subset_compl.mpr hKF)

theorem deleteEdges_mono_left {G H : SimpleDiGraph α} (hGH : G ≤ H) (F : Set (α × α)) :
    G.deleteEdges F ≤ H.deleteEdges F := deleteEdges_mono hGH (fun _ h => h)

theorem deleteEdges_anti_right (G : SimpleDiGraph α) {F K : Set (α × α)} (hFK : F ⊆ K) :
    G.deleteEdges K ≤ G.deleteEdges F := deleteEdges_mono le_rfl hFK

theorem deleteEdges_singleton (G : SimpleDiGraph α) (a : α × α) :
    G.deleteEdges {a} = G.deleteEdge a := rfl

@[simp] theorem mem_edgeSet_deleteEdge (G : SimpleDiGraph α) (a b : α × α) :
    b ∈ E(G.deleteEdge a) ↔ b ∈ E(G) ∧ b ≠ a := by simp [deleteEdge]

@[simp] theorem not_mem_edgeSet_deleteEdge (G : SimpleDiGraph α) (a : α × α) :
    a ∉ E(G.deleteEdge a) := fun h => (G.mem_edgeSet_deleteEdge a a).mp h |>.2 rfl

@[simp] theorem deleteEdge_le (G : SimpleDiGraph α) (a : α × α) : G.deleteEdge a ≤ G :=
  G.deleteEdges_le {a}

@[simp] theorem deleteEdge_of_not_mem (G : SimpleDiGraph α) {a : α × α} (ha : a ∉ E(G)) :
    G.deleteEdge a = G := by
  apply SimpleDiGraph.ext
  · rfl
  · ext b
    rw [mem_edgeSet_deleteEdge]
    constructor
    · exact And.left
    · intro hb
      exact ⟨hb, fun hba => ha (hba ▸ hb)⟩

theorem deleteEdge_comm (G : SimpleDiGraph α) (a b : α × α) :
    (G.deleteEdge a).deleteEdge b = (G.deleteEdge b).deleteEdge a := by
  simp only [deleteEdge, deleteEdges_deleteEdges]
  rw [Set.union_comm]

@[simp] theorem deleteEdge_idem (G : SimpleDiGraph α) (a : α × α) :
    (G.deleteEdge a).deleteEdge a = G.deleteEdge a := by simp [deleteEdge]

@[simp] theorem vertexSet_deleteVerts (G : SimpleDiGraph α) (S : Set α) :
    V(G.deleteVerts S) = V(G) \ S := by ext; simp [deleteVerts, and_comm]

@[simp] theorem mem_vertexSet_deleteVerts (G : SimpleDiGraph α) (S : Set α) (v : α) :
    v ∈ V(G.deleteVerts S) ↔ v ∈ V(G) ∧ v ∉ S := by simp [deleteVerts, and_comm]

@[simp] theorem mem_edgeSet_deleteVerts (G : SimpleDiGraph α) (S : Set α) (a : α × α) :
    a ∈ E(G.deleteVerts S) ↔ a ∈ E(G) ∧ a.1 ∉ S ∧ a.2 ∉ S := by
  change a ∈ E(G.induce Sᶜ) ↔ _
  rw [SimpleDiGraph.mem_edgeSet_induce]
  simp [and_left_comm]

@[simp] theorem deleteVerts_isArc (G : SimpleDiGraph α) (S : Set α)
    (a : α × α) (u v : α) :
    (G.deleteVerts S).IsArc a u v ↔ G.IsArc a u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).IsArc a u v ↔ _
  rw [SimpleDiGraph.induce_isArc]
  simp

@[simp] theorem deleteVerts_inc (G : SimpleDiGraph α) (S : Set α)
    (a : α × α) (v : α) :
    (G.deleteVerts S).Inc a v ↔ G.Inc a v ∧ a.1 ∉ S ∧ a.2 ∉ S := by
  change (G.induce Sᶜ).Inc a v ↔ _
  rw [SimpleDiGraph.induce_inc]
  simp [and_left_comm]

@[simp] theorem deleteVerts_adj (G : SimpleDiGraph α) (S : Set α) (u v : α) :
    (G.deleteVerts S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := by
  change (G.induce Sᶜ).Adj u v ↔ _
  rw [SimpleDiGraph.induce_adj]
  simp

@[simp] theorem deleteVerts_le (G : SimpleDiGraph α) (S : Set α) : G.deleteVerts S ≤ G :=
  G.induce_le Sᶜ

@[simp] theorem deleteVerts_empty (G : SimpleDiGraph α) : G.deleteVerts ∅ = G := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_univ (G : SimpleDiGraph α) : G.deleteVerts Set.univ = ⊥ := by
  simp [deleteVerts]

@[simp] theorem deleteVerts_deleteVerts (G : SimpleDiGraph α) (S T : Set α) :
    (G.deleteVerts S).deleteVerts T = G.deleteVerts (S ∪ T) := by
  simp only [deleteVerts, induce_induce]
  congr 1
  ext v
  simp

@[simp] theorem deleteVerts_idem (G : SimpleDiGraph α) (S : Set α) :
    (G.deleteVerts S).deleteVerts S = G.deleteVerts S := by simp

theorem deleteVerts_mono {G H : SimpleDiGraph α} {S T : Set α}
    (hGH : G ≤ H) (hTS : T ⊆ S) : G.deleteVerts S ≤ H.deleteVerts T :=
  induce_mono hGH (Set.compl_subset_compl.mpr hTS)

theorem deleteVerts_mono_left {G H : SimpleDiGraph α} (hGH : G ≤ H) (S : Set α) :
    G.deleteVerts S ≤ H.deleteVerts S := deleteVerts_mono hGH (fun _ h => h)

theorem deleteVerts_anti_right (G : SimpleDiGraph α) {S T : Set α} (hST : S ⊆ T) :
    G.deleteVerts T ≤ G.deleteVerts S := deleteVerts_mono le_rfl hST

theorem deleteVerts_singleton (G : SimpleDiGraph α) (v : α) :
    G.deleteVerts {v} = G.deleteVert v := rfl

@[simp] theorem mem_vertexSet_deleteVert (G : SimpleDiGraph α) (u v : α) :
    u ∈ V(G.deleteVert v) ↔ u ∈ V(G) ∧ u ≠ v := by simp [deleteVert]

@[simp] theorem not_mem_vertexSet_deleteVert (G : SimpleDiGraph α) (v : α) :
    v ∉ V(G.deleteVert v) := fun h => (G.mem_vertexSet_deleteVert v v).mp h |>.2 rfl

@[simp] theorem deleteVert_le (G : SimpleDiGraph α) (v : α) : G.deleteVert v ≤ G :=
  G.deleteVerts_le {v}

@[simp] theorem deleteVert_of_not_mem (G : SimpleDiGraph α) {v : α} (hv : v ∉ V(G)) :
    G.deleteVert v = G := by
  apply SimpleDiGraph.ext
  · ext u
    rw [mem_vertexSet_deleteVert]
    constructor
    · exact And.left
    · intro hu
      exact ⟨hu, fun huv => hv (huv ▸ hu)⟩
  · ext a
    change a ∈ E(G.deleteVerts {v}) ↔ a ∈ E(G)
    rw [mem_edgeSet_deleteVerts]
    simp only [Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro ha
      exact ⟨ha, fun hs => hv (hs ▸ G.source_mem a ha),
        fun ht => hv (ht ▸ G.target_mem a ha)⟩

theorem deleteVert_comm (G : SimpleDiGraph α) (u v : α) :
    (G.deleteVert u).deleteVert v = (G.deleteVert v).deleteVert u := by
  simp only [deleteVert, deleteVerts_deleteVerts]
  rw [Set.union_comm]

@[simp] theorem deleteVert_idem (G : SimpleDiGraph α) (v : α) :
    (G.deleteVert v).deleteVert v = G.deleteVert v := by simp [deleteVert]

theorem deleteEdges_deleteVerts (G : SimpleDiGraph α) (F : Set (α × α)) (S : Set α) :
    (G.deleteEdges F).deleteVerts S = (G.deleteVerts S).deleteEdges F := by
  ext <;> simp [deleteEdges, deleteVerts, and_left_comm, and_assoc, and_comm]

@[simp] theorem mem_edgeSet_deleteArcsFromTo (G : SimpleDiGraph α) (u v : α) (a : α × α) :
    a ∈ E(G.deleteArcsFromTo u v) ↔ a ∈ E(G) ∧ ¬ (a.1 = u ∧ a.2 = v) := by
  simp [deleteArcsFromTo]

@[simp] theorem deleteArcsFromTo_le (G : SimpleDiGraph α) (u v : α) :
    G.deleteArcsFromTo u v ≤ G := G.deleteEdges_le _

@[simp] theorem deleteArcsFromTo_isArc (G : SimpleDiGraph α) (u v : α)
    (a : α × α) (x y : α) :
    (G.deleteArcsFromTo u v).IsArc a x y ↔
      G.IsArc a x y ∧ ¬ (a.1 = u ∧ a.2 = v) := by
  simp [deleteArcsFromTo]
  tauto

@[simp] theorem deleteArcsFromTo_inc (G : SimpleDiGraph α) (u v : α)
    (a : α × α) (x : α) :
    (G.deleteArcsFromTo u v).Inc a x ↔
      G.Inc a x ∧ ¬ (a.1 = u ∧ a.2 = v) := by
  simp [deleteArcsFromTo]

@[simp] theorem deleteArcsFromTo_adj (G : SimpleDiGraph α) (u v x y : α) :
    (G.deleteArcsFromTo u v).Adj x y ↔
      G.Adj x y ∧ ¬ (x = u ∧ y = v) := by
  simp [deleteArcsFromTo]

end SimpleDiGraph

end GraphLib
