/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Weixuan Yuan
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Card
import GraphLib.Graph.Neighborhood

/-!
# Finite-set views of graphs

This file exposes executable `Finset` views of the finite mathematical sets used by GraphLib.
Global views are enumerated by `Fintype` instances on the corresponding set subtypes, and local
views are obtained by filtering those global enumerations.

For general graphs, finiteness of the vertex set and finiteness of the actual bundled edge set
are independent. For simple graphs only, finite vertices imply finite edges. Local neighborhood
and incidence finiteness is derived from the corresponding ambient finite set.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ δ : Type*}

/-! ## Finiteness bridges and instances -/

/-- A finite vertex subtype gives a finite vertex set. -/
theorem Graph.vertexSet_finite (G : Graph α β) [Finite V(G)] : V(G).Finite :=
  Set.toFinite V(G)

/-- A finite vertex subtype gives a finite vertex set. -/
theorem SimpleGraph.vertexSet_finite (G : SimpleGraph α) [Finite V(G)] : V(G).Finite :=
  Set.toFinite V(G)

/-- A finite vertex subtype gives a finite vertex set. -/
theorem DiGraph.vertexSet_finite (G : DiGraph α β) [Finite V(G)] : V(G).Finite :=
  Set.toFinite V(G)

/-- A finite vertex subtype gives a finite vertex set. -/
theorem SimpleDiGraph.vertexSet_finite (G : SimpleDiGraph α) [Finite V(G)] : V(G).Finite :=
  Set.toFinite V(G)

/-- A finite actual-edge subtype gives a finite actual-edge set. -/
theorem Graph.edgeSet_finite (G : Graph α β) [Finite E(G)] : E(G).Finite :=
  Set.toFinite E(G)

/-- A finite actual-edge subtype gives a finite actual-edge set. -/
theorem SimpleGraph.edgeSet_finite (G : SimpleGraph α) [Finite E(G)] : E(G).Finite :=
  Set.toFinite E(G)

/-- A finite actual-arc subtype gives a finite actual-arc set. -/
theorem DiGraph.edgeSet_finite (G : DiGraph α β) [Finite E(G)] : E(G).Finite :=
  Set.toFinite E(G)

/-- A finite actual-arc subtype gives a finite actual-arc set. -/
theorem SimpleDiGraph.edgeSet_finite (G : SimpleDiGraph α) [Finite E(G)] : E(G).Finite :=
  Set.toFinite E(G)

/-! ### Finiteness inherited by subgraphs -/

/-- A subgraph of a finite-vertex general graph has finitely many vertices. -/
theorem Graph.IsSubgraph.vertexSet_finite {H G : Graph α β} (h : H ≤ G)
    [Finite V(G)] : V(H).Finite :=
  G.vertexSet_finite.subset h.vertexSet_subset

/-- A subgraph of a finite-edge general graph has finitely many actual edges. -/
theorem Graph.IsSubgraph.edgeSet_finite {H G : Graph α β} (h : H ≤ G)
    [Finite E(G)] : E(H).Finite :=
  G.edgeSet_finite.subset h.edgeSet_subset

/-- A subgraph of a finite-vertex simple graph has finitely many vertices. -/
theorem SimpleGraph.IsSubgraph.vertexSet_finite {H G : SimpleGraph α} (h : H ≤ G)
    [Finite V(G)] : V(H).Finite :=
  G.vertexSet_finite.subset h.vertexSet_subset

/-- A subgraph of a finite-edge simple graph has finitely many actual edges. -/
theorem SimpleGraph.IsSubgraph.edgeSet_finite {H G : SimpleGraph α} (h : H ≤ G)
    [Finite E(G)] : E(H).Finite :=
  G.edgeSet_finite.subset h.edgeSet_subset

/-- A subgraph of a finite-vertex general digraph has finitely many vertices. -/
theorem DiGraph.IsSubgraph.vertexSet_finite {H G : DiGraph α β} (h : H ≤ G)
    [Finite V(G)] : V(H).Finite :=
  G.vertexSet_finite.subset h.vertexSet_subset

/-- A subgraph of a finite-arc general digraph has finitely many actual arcs. -/
theorem DiGraph.IsSubgraph.edgeSet_finite {H G : DiGraph α β} (h : H ≤ G)
    [Finite E(G)] : E(H).Finite :=
  G.edgeSet_finite.subset h.edgeSet_subset

/-- A subgraph of a finite-vertex simple digraph has finitely many vertices. -/
theorem SimpleDiGraph.IsSubgraph.vertexSet_finite {H G : SimpleDiGraph α} (h : H ≤ G)
    [Finite V(G)] : V(H).Finite :=
  G.vertexSet_finite.subset h.vertexSet_subset

/-- A subgraph of a finite-arc simple digraph has finitely many actual arcs. -/
theorem SimpleDiGraph.IsSubgraph.edgeSet_finite {H G : SimpleDiGraph α} (h : H ≤ G)
    [Finite E(G)] : E(H).Finite :=
  G.edgeSet_finite.subset h.edgeSet_subset

/-! ### Finiteness through same-carrier restrictions -/

instance Graph.instFiniteVertexSetInduce (G : Graph α β) (S : Set α) [Finite V(G)] :
    Finite V(G.induce S) := (G.induce_le S).vertexSet_finite.to_subtype

instance Graph.instFiniteEdgeSetInduce (G : Graph α β) (S : Set α) [Finite E(G)] :
    Finite E(G.induce S) := (G.induce_le S).edgeSet_finite.to_subtype

instance Graph.instFiniteVertexSetRestrictEdges (G : Graph α β) (F : Set (Edge α β))
    [Finite V(G)] : Finite V(G.restrictEdges F) :=
  (G.restrictEdges_le F).vertexSet_finite.to_subtype

instance Graph.instFiniteEdgeSetRestrictEdges (G : Graph α β) (F : Set (Edge α β))
    [Finite E(G)] : Finite E(G.restrictEdges F) :=
  (G.restrictEdges_le F).edgeSet_finite.to_subtype

instance SimpleGraph.instFiniteVertexSetInduce (G : SimpleGraph α) (S : Set α)
    [Finite V(G)] : Finite V(G.induce S) :=
  (G.induce_le S).vertexSet_finite.to_subtype

instance SimpleGraph.instFiniteEdgeSetInduce (G : SimpleGraph α) (S : Set α)
    [Finite E(G)] : Finite E(G.induce S) :=
  (G.induce_le S).edgeSet_finite.to_subtype

instance SimpleGraph.instFiniteVertexSetRestrictEdges (G : SimpleGraph α) (F : Set (Sym2 α))
    [Finite V(G)] : Finite V(G.restrictEdges F) :=
  (G.restrictEdges_le F).vertexSet_finite.to_subtype

instance SimpleGraph.instFiniteEdgeSetRestrictEdges (G : SimpleGraph α) (F : Set (Sym2 α))
    [Finite E(G)] : Finite E(G.restrictEdges F) :=
  (G.restrictEdges_le F).edgeSet_finite.to_subtype

instance DiGraph.instFiniteVertexSetInduce (G : DiGraph α β) (S : Set α) [Finite V(G)] :
    Finite V(G.induce S) := (G.induce_le S).vertexSet_finite.to_subtype

instance DiGraph.instFiniteEdgeSetInduce (G : DiGraph α β) (S : Set α) [Finite E(G)] :
    Finite E(G.induce S) := (G.induce_le S).edgeSet_finite.to_subtype

instance DiGraph.instFiniteVertexSetRestrictEdges (G : DiGraph α β) (F : Set (Arc α β))
    [Finite V(G)] : Finite V(G.restrictEdges F) :=
  (G.restrictEdges_le F).vertexSet_finite.to_subtype

instance DiGraph.instFiniteEdgeSetRestrictEdges (G : DiGraph α β) (F : Set (Arc α β))
    [Finite E(G)] : Finite E(G.restrictEdges F) :=
  (G.restrictEdges_le F).edgeSet_finite.to_subtype

instance SimpleDiGraph.instFiniteVertexSetInduce (G : SimpleDiGraph α) (S : Set α)
    [Finite V(G)] : Finite V(G.induce S) :=
  (G.induce_le S).vertexSet_finite.to_subtype

instance SimpleDiGraph.instFiniteEdgeSetInduce (G : SimpleDiGraph α) (S : Set α)
    [Finite E(G)] : Finite E(G.induce S) :=
  (G.induce_le S).edgeSet_finite.to_subtype

instance SimpleDiGraph.instFiniteVertexSetRestrictEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) [Finite V(G)] :
    Finite V(G.restrictEdges F) :=
  (G.restrictEdges_le F).vertexSet_finite.to_subtype

instance SimpleDiGraph.instFiniteEdgeSetRestrictEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) [Finite E(G)] :
    Finite E(G.restrictEdges F) :=
  (G.restrictEdges_le F).edgeSet_finite.to_subtype

/-! ### Finiteness through deletion -/

instance Graph.instFiniteVertexSetDeleteEdges (G : Graph α β) (F : Set (Edge α β))
    [Finite V(G)] : Finite V(G.deleteEdges F) :=
  (G.deleteEdges_le F).vertexSet_finite.to_subtype

instance Graph.instFiniteEdgeSetDeleteEdges (G : Graph α β) (F : Set (Edge α β))
    [Finite E(G)] : Finite E(G.deleteEdges F) :=
  (G.deleteEdges_le F).edgeSet_finite.to_subtype

instance Graph.instFiniteVertexSetDeleteEdge (G : Graph α β) (e : Edge α β)
    [Finite V(G)] : Finite V(G.deleteEdge e) :=
  (G.deleteEdge_le e).vertexSet_finite.to_subtype

instance Graph.instFiniteEdgeSetDeleteEdge (G : Graph α β) (e : Edge α β)
    [Finite E(G)] : Finite E(G.deleteEdge e) :=
  (G.deleteEdge_le e).edgeSet_finite.to_subtype

instance Graph.instFiniteVertexSetDeleteVerts (G : Graph α β) (S : Set α)
    [Finite V(G)] : Finite V(G.deleteVerts S) :=
  (G.deleteVerts_le S).vertexSet_finite.to_subtype

instance Graph.instFiniteEdgeSetDeleteVerts (G : Graph α β) (S : Set α)
    [Finite E(G)] : Finite E(G.deleteVerts S) :=
  (G.deleteVerts_le S).edgeSet_finite.to_subtype

instance Graph.instFiniteVertexSetDeleteVert (G : Graph α β) (v : α)
    [Finite V(G)] : Finite V(G.deleteVert v) :=
  (G.deleteVert_le v).vertexSet_finite.to_subtype

instance Graph.instFiniteEdgeSetDeleteVert (G : Graph α β) (v : α)
    [Finite E(G)] : Finite E(G.deleteVert v) :=
  (G.deleteVert_le v).edgeSet_finite.to_subtype

instance Graph.instFiniteVertexSetDeleteEdgesBetween (G : Graph α β) (u v : α)
    [Finite V(G)] : Finite V(G.deleteEdgesBetween u v) :=
  (G.deleteEdgesBetween_le u v).vertexSet_finite.to_subtype

instance Graph.instFiniteEdgeSetDeleteEdgesBetween (G : Graph α β) (u v : α)
    [Finite E(G)] : Finite E(G.deleteEdgesBetween u v) :=
  (G.deleteEdgesBetween_le u v).edgeSet_finite.to_subtype

instance SimpleGraph.instFiniteVertexSetDeleteEdges (G : SimpleGraph α) (F : Set (Sym2 α))
    [Finite V(G)] : Finite V(G.deleteEdges F) :=
  (G.deleteEdges_le F).vertexSet_finite.to_subtype

instance SimpleGraph.instFiniteEdgeSetDeleteEdges (G : SimpleGraph α) (F : Set (Sym2 α))
    [Finite E(G)] : Finite E(G.deleteEdges F) :=
  (G.deleteEdges_le F).edgeSet_finite.to_subtype

instance SimpleGraph.instFiniteVertexSetDeleteEdge (G : SimpleGraph α) (e : Sym2 α)
    [Finite V(G)] : Finite V(G.deleteEdge e) :=
  (G.deleteEdge_le e).vertexSet_finite.to_subtype

instance SimpleGraph.instFiniteEdgeSetDeleteEdge (G : SimpleGraph α) (e : Sym2 α)
    [Finite E(G)] : Finite E(G.deleteEdge e) :=
  (G.deleteEdge_le e).edgeSet_finite.to_subtype

instance SimpleGraph.instFiniteVertexSetDeleteVerts (G : SimpleGraph α) (S : Set α)
    [Finite V(G)] : Finite V(G.deleteVerts S) :=
  (G.deleteVerts_le S).vertexSet_finite.to_subtype

instance SimpleGraph.instFiniteEdgeSetDeleteVerts (G : SimpleGraph α) (S : Set α)
    [Finite E(G)] : Finite E(G.deleteVerts S) :=
  (G.deleteVerts_le S).edgeSet_finite.to_subtype

instance SimpleGraph.instFiniteVertexSetDeleteVert (G : SimpleGraph α) (v : α)
    [Finite V(G)] : Finite V(G.deleteVert v) :=
  (G.deleteVert_le v).vertexSet_finite.to_subtype

instance SimpleGraph.instFiniteEdgeSetDeleteVert (G : SimpleGraph α) (v : α)
    [Finite E(G)] : Finite E(G.deleteVert v) :=
  (G.deleteVert_le v).edgeSet_finite.to_subtype

instance SimpleGraph.instFiniteVertexSetDeleteEdgesBetween (G : SimpleGraph α) (u v : α)
    [Finite V(G)] : Finite V(G.deleteEdgesBetween u v) :=
  (G.deleteEdgesBetween_le u v).vertexSet_finite.to_subtype

instance SimpleGraph.instFiniteEdgeSetDeleteEdgesBetween (G : SimpleGraph α) (u v : α)
    [Finite E(G)] : Finite E(G.deleteEdgesBetween u v) :=
  (G.deleteEdgesBetween_le u v).edgeSet_finite.to_subtype

instance DiGraph.instFiniteVertexSetDeleteEdges (G : DiGraph α β) (F : Set (Arc α β))
    [Finite V(G)] : Finite V(G.deleteEdges F) :=
  (G.deleteEdges_le F).vertexSet_finite.to_subtype

instance DiGraph.instFiniteEdgeSetDeleteEdges (G : DiGraph α β) (F : Set (Arc α β))
    [Finite E(G)] : Finite E(G.deleteEdges F) :=
  (G.deleteEdges_le F).edgeSet_finite.to_subtype

instance DiGraph.instFiniteVertexSetDeleteEdge (G : DiGraph α β) (a : Arc α β)
    [Finite V(G)] : Finite V(G.deleteEdge a) :=
  (G.deleteEdge_le a).vertexSet_finite.to_subtype

instance DiGraph.instFiniteEdgeSetDeleteEdge (G : DiGraph α β) (a : Arc α β)
    [Finite E(G)] : Finite E(G.deleteEdge a) :=
  (G.deleteEdge_le a).edgeSet_finite.to_subtype

instance DiGraph.instFiniteVertexSetDeleteVerts (G : DiGraph α β) (S : Set α)
    [Finite V(G)] : Finite V(G.deleteVerts S) :=
  (G.deleteVerts_le S).vertexSet_finite.to_subtype

instance DiGraph.instFiniteEdgeSetDeleteVerts (G : DiGraph α β) (S : Set α)
    [Finite E(G)] : Finite E(G.deleteVerts S) :=
  (G.deleteVerts_le S).edgeSet_finite.to_subtype

instance DiGraph.instFiniteVertexSetDeleteVert (G : DiGraph α β) (v : α)
    [Finite V(G)] : Finite V(G.deleteVert v) :=
  (G.deleteVert_le v).vertexSet_finite.to_subtype

instance DiGraph.instFiniteEdgeSetDeleteVert (G : DiGraph α β) (v : α)
    [Finite E(G)] : Finite E(G.deleteVert v) :=
  (G.deleteVert_le v).edgeSet_finite.to_subtype

instance DiGraph.instFiniteVertexSetDeleteArcsFromTo (G : DiGraph α β) (u v : α)
    [Finite V(G)] : Finite V(G.deleteArcsFromTo u v) :=
  (G.deleteArcsFromTo_le u v).vertexSet_finite.to_subtype

instance DiGraph.instFiniteEdgeSetDeleteArcsFromTo (G : DiGraph α β) (u v : α)
    [Finite E(G)] : Finite E(G.deleteArcsFromTo u v) :=
  (G.deleteArcsFromTo_le u v).edgeSet_finite.to_subtype

instance SimpleDiGraph.instFiniteVertexSetDeleteEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) [Finite V(G)] :
    Finite V(G.deleteEdges F) :=
  (G.deleteEdges_le F).vertexSet_finite.to_subtype

instance SimpleDiGraph.instFiniteEdgeSetDeleteEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) [Finite E(G)] :
    Finite E(G.deleteEdges F) :=
  (G.deleteEdges_le F).edgeSet_finite.to_subtype

instance SimpleDiGraph.instFiniteVertexSetDeleteEdge (G : SimpleDiGraph α) (a : α × α)
    [Finite V(G)] : Finite V(G.deleteEdge a) :=
  (G.deleteEdge_le a).vertexSet_finite.to_subtype

instance SimpleDiGraph.instFiniteEdgeSetDeleteEdge (G : SimpleDiGraph α) (a : α × α)
    [Finite E(G)] : Finite E(G.deleteEdge a) :=
  (G.deleteEdge_le a).edgeSet_finite.to_subtype

instance SimpleDiGraph.instFiniteVertexSetDeleteVerts (G : SimpleDiGraph α) (S : Set α)
    [Finite V(G)] : Finite V(G.deleteVerts S) :=
  (G.deleteVerts_le S).vertexSet_finite.to_subtype

instance SimpleDiGraph.instFiniteEdgeSetDeleteVerts (G : SimpleDiGraph α) (S : Set α)
    [Finite E(G)] : Finite E(G.deleteVerts S) :=
  (G.deleteVerts_le S).edgeSet_finite.to_subtype

instance SimpleDiGraph.instFiniteVertexSetDeleteVert (G : SimpleDiGraph α) (v : α)
    [Finite V(G)] : Finite V(G.deleteVert v) :=
  (G.deleteVert_le v).vertexSet_finite.to_subtype

instance SimpleDiGraph.instFiniteEdgeSetDeleteVert (G : SimpleDiGraph α) (v : α)
    [Finite E(G)] : Finite E(G.deleteVert v) :=
  (G.deleteVert_le v).edgeSet_finite.to_subtype

instance SimpleDiGraph.instFiniteVertexSetDeleteArcsFromTo
    (G : SimpleDiGraph α) (u v : α) [Finite V(G)] :
    Finite V(G.deleteArcsFromTo u v) :=
  (G.deleteArcsFromTo_le u v).vertexSet_finite.to_subtype

instance SimpleDiGraph.instFiniteEdgeSetDeleteArcsFromTo
    (G : SimpleDiGraph α) (u v : α) [Finite E(G)] :
    Finite E(G.deleteArcsFromTo u v) :=
  (G.deleteArcsFromTo_le u v).edgeSet_finite.to_subtype

/-! ### Finiteness through maps, relabelings, and reversal -/

instance Graph.instFiniteVertexSetMapVertices (G : Graph α β) (f : α → γ) [Finite V(G)] :
    Finite V(G.mapVertices f) := (G.vertexSet_finite.image f).to_subtype

instance Graph.instFiniteEdgeSetMapVertices (G : Graph α β) (f : α → γ) [Finite E(G)] :
    Finite E(G.mapVertices f) := (G.edgeSet_finite.image (Edge.mapVertices f)).to_subtype

instance DiGraph.instFiniteVertexSetMapVertices (G : DiGraph α β) (f : α → γ) [Finite V(G)] :
    Finite V(G.mapVertices f) := (G.vertexSet_finite.image f).to_subtype

instance DiGraph.instFiniteEdgeSetMapVertices (G : DiGraph α β) (f : α → γ) [Finite E(G)] :
    Finite E(G.mapVertices f) := (G.edgeSet_finite.image (Arc.mapVertices f)).to_subtype

instance SimpleGraph.instFiniteVertexSetMapVertices (G : SimpleGraph α) (f : α → γ)
    [Finite V(G)] : Finite V(G.mapVertices f) :=
  (G.vertexSet_finite.image f).to_subtype

instance SimpleGraph.instFiniteEdgeSetMapVertices (G : SimpleGraph α) (f : α → γ)
    [Finite E(G)] : Finite E(G.mapVertices f) := by
  apply Set.Finite.to_subtype
  refine (G.edgeSet_finite.image (Sym2.map f)).subset ?_
  intro e he
  exact he.1

instance SimpleDiGraph.instFiniteVertexSetMapVertices (G : SimpleDiGraph α) (f : α → γ)
    [Finite V(G)] : Finite V(G.mapVertices f) :=
  (G.vertexSet_finite.image f).to_subtype

instance SimpleDiGraph.instFiniteEdgeSetMapVertices (G : SimpleDiGraph α) (f : α → γ)
    [Finite E(G)] : Finite E(G.mapVertices f) := by
  apply Set.Finite.to_subtype
  refine (G.edgeSet_finite.image fun a => (f a.1, f a.2)).subset ?_
  intro a ha
  exact ha.1

instance Graph.instFiniteVertexSetRelabelVertices (G : Graph α β) (f : α ≃ γ)
    [Finite V(G)] : Finite V(G.relabelVertices f) :=
  (G.vertexSet_finite.image f).to_subtype

instance Graph.instFiniteEdgeSetRelabelVertices (G : Graph α β) (f : α ≃ γ)
    [Finite E(G)] : Finite E(G.relabelVertices f) :=
  (G.edgeSet_finite.image (Edge.relabelVertices f)).to_subtype

instance Graph.instFiniteVertexSetRelabelTags (G : Graph α β) (g : β ≃ δ)
    [Finite V(G)] : Finite V(G.relabelTags g) := by simpa using (inferInstance : Finite V(G))

instance Graph.instFiniteEdgeSetRelabelTags (G : Graph α β) (g : β ≃ δ)
    [Finite E(G)] : Finite E(G.relabelTags g) :=
  (G.edgeSet_finite.image (Edge.relabelTags g)).to_subtype

instance DiGraph.instFiniteVertexSetRelabelVertices (G : DiGraph α β) (f : α ≃ γ)
    [Finite V(G)] : Finite V(G.relabelVertices f) :=
  (G.vertexSet_finite.image f).to_subtype

instance DiGraph.instFiniteEdgeSetRelabelVertices (G : DiGraph α β) (f : α ≃ γ)
    [Finite E(G)] : Finite E(G.relabelVertices f) :=
  (G.edgeSet_finite.image (Arc.relabelVertices f)).to_subtype

instance DiGraph.instFiniteVertexSetRelabelTags (G : DiGraph α β) (g : β ≃ δ)
    [Finite V(G)] : Finite V(G.relabelTags g) := by simpa using (inferInstance : Finite V(G))

instance DiGraph.instFiniteEdgeSetRelabelTags (G : DiGraph α β) (g : β ≃ δ)
    [Finite E(G)] : Finite E(G.relabelTags g) :=
  (G.edgeSet_finite.image (Arc.relabelTags g)).to_subtype

instance SimpleGraph.instFiniteVertexSetRelabelVertices (G : SimpleGraph α) (f : α ≃ γ)
    [Finite V(G)] : Finite V(G.relabelVertices f) :=
  (G.vertexSet_finite.image f).to_subtype

instance SimpleGraph.instFiniteEdgeSetRelabelVertices (G : SimpleGraph α) (f : α ≃ γ)
    [Finite E(G)] : Finite E(G.relabelVertices f) :=
  (G.edgeSet_finite.image (Sym2.map f)).to_subtype

instance SimpleDiGraph.instFiniteVertexSetRelabelVertices (G : SimpleDiGraph α) (f : α ≃ γ)
    [Finite V(G)] : Finite V(G.relabelVertices f) :=
  (G.vertexSet_finite.image f).to_subtype

instance SimpleDiGraph.instFiniteEdgeSetRelabelVertices (G : SimpleDiGraph α) (f : α ≃ γ)
    [Finite E(G)] : Finite E(G.relabelVertices f) :=
  (G.edgeSet_finite.image fun a : α × α => (f a.1, f a.2)).to_subtype

instance DiGraph.instFiniteVertexSetReverse (G : DiGraph α β) [Finite V(G)] :
    Finite V(G.reverse) := by simpa using (inferInstance : Finite V(G))

instance DiGraph.instFiniteEdgeSetReverse (G : DiGraph α β) [Finite E(G)] :
    Finite E(G.reverse) := (G.edgeSet_finite.image Arc.reverse).to_subtype

instance SimpleDiGraph.instFiniteVertexSetReverse (G : SimpleDiGraph α) [Finite V(G)] :
    Finite V(G.reverse) := by simpa using (inferInstance : Finite V(G))

instance SimpleDiGraph.instFiniteEdgeSetReverse (G : SimpleDiGraph α) [Finite E(G)] :
    Finite E(G.reverse) :=
  (G.edgeSet_finite.image fun a => (a.2, a.1)).to_subtype

/-! ### Local finiteness inherited by subgraphs -/

/-- Local undirected incidence remains finite in a subgraph. -/
theorem Graph.IsSubgraph.incidenceSet_finite {H G : Graph α β} (h : H ≤ G) (v : α)
    [Finite (G.incidenceSet v)] : (H.incidenceSet v).Finite :=
  (Set.toFinite (G.incidenceSet v)).subset fun _ he => h.inc he

/-- A local neighborhood remains finite in a simple subgraph. -/
theorem SimpleGraph.IsSubgraph.neighborSet_finite {H G : SimpleGraph α} (h : H ≤ G)
    (v : α) [Finite (G.neighborSet v)] : (H.neighborSet v).Finite :=
  (Set.toFinite (G.neighborSet v)).subset (H.neighborSet_mono h v)

/-- Local outgoing incidence remains finite in a directed subgraph. -/
theorem DiGraph.IsSubgraph.outIncidenceSet_finite {H G : DiGraph α β} (h : H ≤ G)
    (v : α) [Finite (G.outIncidenceSet v)] : (H.outIncidenceSet v).Finite :=
  (Set.toFinite (G.outIncidenceSet v)).subset fun _ ha =>
    ⟨h.edgeSet_subset ha.1, ha.2⟩

/-- Local incoming incidence remains finite in a directed subgraph. -/
theorem DiGraph.IsSubgraph.inIncidenceSet_finite {H G : DiGraph α β} (h : H ≤ G)
    (v : α) [Finite (G.inIncidenceSet v)] : (H.inIncidenceSet v).Finite :=
  (Set.toFinite (G.inIncidenceSet v)).subset fun _ ha =>
    ⟨h.edgeSet_subset ha.1, ha.2⟩

/-- Local outgoing incidence remains finite in a simple directed subgraph. -/
theorem SimpleDiGraph.IsSubgraph.outIncidenceSet_finite {H G : SimpleDiGraph α} (h : H ≤ G)
    (v : α) [Finite (G.outIncidenceSet v)] : (H.outIncidenceSet v).Finite :=
  (Set.toFinite (G.outIncidenceSet v)).subset fun _ ha =>
    ⟨h.edgeSet_subset ha.1, ha.2⟩

/-- Local incoming incidence remains finite in a simple directed subgraph. -/
theorem SimpleDiGraph.IsSubgraph.inIncidenceSet_finite {H G : SimpleDiGraph α} (h : H ≤ G)
    (v : α) [Finite (G.inIncidenceSet v)] : (H.inIncidenceSet v).Finite :=
  (Set.toFinite (G.inIncidenceSet v)).subset fun _ ha =>
    ⟨h.edgeSet_subset ha.1, ha.2⟩

instance Graph.instFiniteIncidenceSetInduce (G : Graph α β) (S : Set α) (v : α)
    [Finite (G.incidenceSet v)] : Finite ((G.induce S).incidenceSet v) :=
  ((G.induce_le S).incidenceSet_finite v).to_subtype

instance Graph.instFiniteIncidenceSetRestrictEdges
    (G : Graph α β) (F : Set (Edge α β)) (v : α) [Finite (G.incidenceSet v)] :
    Finite ((G.restrictEdges F).incidenceSet v) :=
  ((G.restrictEdges_le F).incidenceSet_finite v).to_subtype

instance SimpleGraph.instFiniteNeighborSetInduce (G : SimpleGraph α) (S : Set α) (v : α)
    [Finite (G.neighborSet v)] : Finite ((G.induce S).neighborSet v) :=
  ((G.induce_le S).neighborSet_finite v).to_subtype

instance SimpleGraph.instFiniteNeighborSetRestrictEdges
    (G : SimpleGraph α) (F : Set (Sym2 α)) (v : α) [Finite (G.neighborSet v)] :
    Finite ((G.restrictEdges F).neighborSet v) :=
  ((G.restrictEdges_le F).neighborSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetInduce (G : DiGraph α β) (S : Set α) (v : α)
    [Finite (G.outIncidenceSet v)] : Finite ((G.induce S).outIncidenceSet v) :=
  ((G.induce_le S).outIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteInIncidenceSetInduce (G : DiGraph α β) (S : Set α) (v : α)
    [Finite (G.inIncidenceSet v)] : Finite ((G.induce S).inIncidenceSet v) :=
  ((G.induce_le S).inIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetRestrictEdges
    (G : DiGraph α β) (F : Set (Arc α β)) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.restrictEdges F).outIncidenceSet v) :=
  ((G.restrictEdges_le F).outIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteInIncidenceSetRestrictEdges
    (G : DiGraph α β) (F : Set (Arc α β)) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.restrictEdges F).inIncidenceSet v) :=
  ((G.restrictEdges_le F).inIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetInduce
    (G : SimpleDiGraph α) (S : Set α) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.induce S).outIncidenceSet v) :=
  ((G.induce_le S).outIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetInduce
    (G : SimpleDiGraph α) (S : Set α) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.induce S).inIncidenceSet v) :=
  ((G.induce_le S).inIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetRestrictEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.restrictEdges F).outIncidenceSet v) :=
  ((G.restrictEdges_le F).outIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetRestrictEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.restrictEdges F).inIncidenceSet v) :=
  ((G.restrictEdges_le F).inIncidenceSet_finite v).to_subtype

instance Graph.instFiniteIncidenceSetDeleteEdges
    (G : Graph α β) (F : Set (Edge α β)) (v : α) [Finite (G.incidenceSet v)] :
    Finite ((G.deleteEdges F).incidenceSet v) :=
  ((G.deleteEdges_le F).incidenceSet_finite v).to_subtype

instance Graph.instFiniteIncidenceSetDeleteEdge
    (G : Graph α β) (e : Edge α β) (v : α) [Finite (G.incidenceSet v)] :
    Finite ((G.deleteEdge e).incidenceSet v) :=
  ((G.deleteEdge_le e).incidenceSet_finite v).to_subtype

instance Graph.instFiniteIncidenceSetDeleteVerts
    (G : Graph α β) (S : Set α) (v : α) [Finite (G.incidenceSet v)] :
    Finite ((G.deleteVerts S).incidenceSet v) :=
  ((G.deleteVerts_le S).incidenceSet_finite v).to_subtype

instance Graph.instFiniteIncidenceSetDeleteVert
    (G : Graph α β) (u v : α) [Finite (G.incidenceSet v)] :
    Finite ((G.deleteVert u).incidenceSet v) :=
  ((G.deleteVert_le u).incidenceSet_finite v).to_subtype

instance Graph.instFiniteIncidenceSetDeleteEdgesBetween
    (G : Graph α β) (u w v : α) [Finite (G.incidenceSet v)] :
    Finite ((G.deleteEdgesBetween u w).incidenceSet v) :=
  ((G.deleteEdgesBetween_le u w).incidenceSet_finite v).to_subtype

instance SimpleGraph.instFiniteNeighborSetDeleteEdges
    (G : SimpleGraph α) (F : Set (Sym2 α)) (v : α) [Finite (G.neighborSet v)] :
    Finite ((G.deleteEdges F).neighborSet v) :=
  ((G.deleteEdges_le F).neighborSet_finite v).to_subtype

instance SimpleGraph.instFiniteNeighborSetDeleteEdge
    (G : SimpleGraph α) (e : Sym2 α) (v : α) [Finite (G.neighborSet v)] :
    Finite ((G.deleteEdge e).neighborSet v) :=
  ((G.deleteEdge_le e).neighborSet_finite v).to_subtype

instance SimpleGraph.instFiniteNeighborSetDeleteVerts
    (G : SimpleGraph α) (S : Set α) (v : α) [Finite (G.neighborSet v)] :
    Finite ((G.deleteVerts S).neighborSet v) :=
  ((G.deleteVerts_le S).neighborSet_finite v).to_subtype

instance SimpleGraph.instFiniteNeighborSetDeleteVert
    (G : SimpleGraph α) (u v : α) [Finite (G.neighborSet v)] :
    Finite ((G.deleteVert u).neighborSet v) :=
  ((G.deleteVert_le u).neighborSet_finite v).to_subtype

instance SimpleGraph.instFiniteNeighborSetDeleteEdgesBetween
    (G : SimpleGraph α) (u w v : α) [Finite (G.neighborSet v)] :
    Finite ((G.deleteEdgesBetween u w).neighborSet v) :=
  ((G.deleteEdgesBetween_le u w).neighborSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetDeleteEdges
    (G : DiGraph α β) (F : Set (Arc α β)) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteEdges F).outIncidenceSet v) :=
  ((G.deleteEdges_le F).outIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteInIncidenceSetDeleteEdges
    (G : DiGraph α β) (F : Set (Arc α β)) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteEdges F).inIncidenceSet v) :=
  ((G.deleteEdges_le F).inIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetDeleteEdge
    (G : DiGraph α β) (a : Arc α β) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteEdge a).outIncidenceSet v) :=
  ((G.deleteEdge_le a).outIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteInIncidenceSetDeleteEdge
    (G : DiGraph α β) (a : Arc α β) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteEdge a).inIncidenceSet v) :=
  ((G.deleteEdge_le a).inIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetDeleteVerts
    (G : DiGraph α β) (S : Set α) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteVerts S).outIncidenceSet v) :=
  ((G.deleteVerts_le S).outIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteInIncidenceSetDeleteVerts
    (G : DiGraph α β) (S : Set α) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteVerts S).inIncidenceSet v) :=
  ((G.deleteVerts_le S).inIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetDeleteVert
    (G : DiGraph α β) (u v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteVert u).outIncidenceSet v) :=
  ((G.deleteVert_le u).outIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteInIncidenceSetDeleteVert
    (G : DiGraph α β) (u v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteVert u).inIncidenceSet v) :=
  ((G.deleteVert_le u).inIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetDeleteArcsFromTo
    (G : DiGraph α β) (u w v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteArcsFromTo u w).outIncidenceSet v) :=
  ((G.deleteArcsFromTo_le u w).outIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteInIncidenceSetDeleteArcsFromTo
    (G : DiGraph α β) (u w v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteArcsFromTo u w).inIncidenceSet v) :=
  ((G.deleteArcsFromTo_le u w).inIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetDeleteEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteEdges F).outIncidenceSet v) :=
  ((G.deleteEdges_le F).outIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetDeleteEdges
    (G : SimpleDiGraph α) (F : Set (α × α)) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteEdges F).inIncidenceSet v) :=
  ((G.deleteEdges_le F).inIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetDeleteEdge
    (G : SimpleDiGraph α) (a : α × α) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteEdge a).outIncidenceSet v) :=
  ((G.deleteEdge_le a).outIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetDeleteEdge
    (G : SimpleDiGraph α) (a : α × α) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteEdge a).inIncidenceSet v) :=
  ((G.deleteEdge_le a).inIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetDeleteVerts
    (G : SimpleDiGraph α) (S : Set α) (v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteVerts S).outIncidenceSet v) :=
  ((G.deleteVerts_le S).outIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetDeleteVerts
    (G : SimpleDiGraph α) (S : Set α) (v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteVerts S).inIncidenceSet v) :=
  ((G.deleteVerts_le S).inIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetDeleteVert
    (G : SimpleDiGraph α) (u v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteVert u).outIncidenceSet v) :=
  ((G.deleteVert_le u).outIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetDeleteVert
    (G : SimpleDiGraph α) (u v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteVert u).inIncidenceSet v) :=
  ((G.deleteVert_le u).inIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetDeleteArcsFromTo
    (G : SimpleDiGraph α) (u w v : α) [Finite (G.outIncidenceSet v)] :
    Finite ((G.deleteArcsFromTo u w).outIncidenceSet v) :=
  ((G.deleteArcsFromTo_le u w).outIncidenceSet_finite v).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetDeleteArcsFromTo
    (G : SimpleDiGraph α) (u w v : α) [Finite (G.inIncidenceSet v)] :
    Finite ((G.deleteArcsFromTo u w).inIncidenceSet v) :=
  ((G.deleteArcsFromTo_le u w).inIncidenceSet_finite v).to_subtype

instance DiGraph.instFiniteOutIncidenceSetReverse (G : DiGraph α β) (v : α)
    [Finite (G.inIncidenceSet v)] : Finite (G.reverse.outIncidenceSet v) := by
  rw [G.outIncidenceSet_reverse]
  exact ((Set.toFinite (G.inIncidenceSet v)).image Arc.reverse).to_subtype

instance DiGraph.instFiniteInIncidenceSetReverse (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] : Finite (G.reverse.inIncidenceSet v) := by
  rw [G.inIncidenceSet_reverse]
  exact ((Set.toFinite (G.outIncidenceSet v)).image Arc.reverse).to_subtype

instance SimpleDiGraph.instFiniteOutIncidenceSetReverse (G : SimpleDiGraph α) (v : α)
    [Finite (G.inIncidenceSet v)] : Finite (G.reverse.outIncidenceSet v) := by
  rw [G.outIncidenceSet_reverse]
  exact ((Set.toFinite (G.inIncidenceSet v)).image fun a => (a.2, a.1)).to_subtype

instance SimpleDiGraph.instFiniteInIncidenceSetReverse (G : SimpleDiGraph α) (v : α)
    [Finite (G.outIncidenceSet v)] : Finite (G.reverse.inIncidenceSet v) := by
  rw [G.inIncidenceSet_reverse]
  exact ((Set.toFinite (G.outIncidenceSet v)).image fun a => (a.2, a.1)).to_subtype

/-- The unordered pairs whose endpoints lie in a finite set form a finite set. -/
private theorem sym2OfSubset_finite (S : Set α) (hS : S.Finite) :
    {e : Sym2 α | ∀ v ∈ e, v ∈ S}.Finite := by
  classical
  haveI : Finite S := hS
  haveI : Fintype S := Fintype.ofFinite S
  refine Set.Finite.subset (Set.toFinite (Sym2.map (Subtype.val : S → α) '' Set.univ)) ?_
  intro e he
  induction e with
  | h x y =>
    refine ⟨s(⟨x, he x ?_⟩, ⟨y, he y ?_⟩), trivial, by simp [Sym2.map_mk]⟩ <;> simp

/-- Finite vertices imply finite edges in a simple undirected graph. -/
instance SimpleGraph.instFiniteEdgeSet (G : SimpleGraph α) [Finite V(G)] : Finite E(G) := by
  have hsubset : E(G) ⊆ {e : Sym2 α | ∀ v ∈ e, v ∈ V(G)} :=
    fun e he v hv => G.endpoints_mem e he v hv
  exact ((sym2OfSubset_finite V(G) G.vertexSet_finite).subset hsubset).to_subtype

/-- Finite vertices imply finite arcs in a simple directed graph. -/
instance SimpleDiGraph.instFiniteEdgeSet (G : SimpleDiGraph α) [Finite V(G)] : Finite E(G) := by
  classical
  haveI : Fintype V(G) := Fintype.ofFinite V(G)
  haveI : Fintype (V(G) × V(G)) := inferInstance
  apply Finite.of_injective (β := V(G) × V(G)) fun a =>
    (⟨a.val.1, G.source_mem _ a.property⟩, ⟨a.val.2, G.target_mem _ a.property⟩)
  rintro ⟨⟨u, v⟩, huv⟩ ⟨⟨x, y⟩, hxy⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

/-- Finite vertices imply finite neighborhoods in a general undirected graph. -/
instance Graph.instFiniteNeighborSet (G : Graph α β) (v : α) [Finite V(G)] :
    Finite (G.neighborSet v) :=
  (G.vertexSet_finite.subset (G.neighborSet_subset_vertexSet v)).to_subtype

/-- Finite vertices imply finite neighborhoods in a simple undirected graph. -/
instance SimpleGraph.instFiniteNeighborSet (G : SimpleGraph α) (v : α) [Finite V(G)] :
    Finite (G.neighborSet v) :=
  (G.vertexSet_finite.subset (G.neighborSet_subset_vertexSet v)).to_subtype

/-- Finite vertices imply finite outgoing neighborhoods in a general directed graph. -/
instance DiGraph.instFiniteOutNeighborSet (G : DiGraph α β) (v : α) [Finite V(G)] :
    Finite (G.outNeighborSet v) :=
  (G.vertexSet_finite.subset (G.outNeighborSet_subset_vertexSet v)).to_subtype

/-- Finite vertices imply finite incoming neighborhoods in a general directed graph. -/
instance DiGraph.instFiniteInNeighborSet (G : DiGraph α β) (v : α) [Finite V(G)] :
    Finite (G.inNeighborSet v) :=
  (G.vertexSet_finite.subset (G.inNeighborSet_subset_vertexSet v)).to_subtype

/-- Finite vertices imply finite outgoing neighborhoods in a simple directed graph. -/
instance SimpleDiGraph.instFiniteOutNeighborSet (G : SimpleDiGraph α) (v : α) [Finite V(G)] :
    Finite (G.outNeighborSet v) :=
  (G.vertexSet_finite.subset (G.outNeighborSet_subset_vertexSet v)).to_subtype

/-- Finite vertices imply finite incoming neighborhoods in a simple directed graph. -/
instance SimpleDiGraph.instFiniteInNeighborSet (G : SimpleDiGraph α) (v : α) [Finite V(G)] :
    Finite (G.inNeighborSet v) :=
  (G.vertexSet_finite.subset (G.inNeighborSet_subset_vertexSet v)).to_subtype

/-- Finite actual edges imply finite incidence at each vertex. -/
instance Graph.instFiniteIncidenceSet (G : Graph α β) (v : α) [Finite E(G)] :
    Finite (G.incidenceSet v) :=
  (G.edgeSet_finite.subset (G.incidenceSet_subset_edgeSet v)).to_subtype

/-- Finite actual edges imply finite incidence at each vertex. -/
instance SimpleGraph.instFiniteIncidenceSet (G : SimpleGraph α) (v : α) [Finite E(G)] :
    Finite (G.incidenceSet v) :=
  (G.edgeSet_finite.subset (G.incidenceSet_subset_edgeSet v)).to_subtype

/-- Finite actual arcs imply finite outgoing incidence at each vertex. -/
instance DiGraph.instFiniteOutIncidenceSet (G : DiGraph α β) (v : α) [Finite E(G)] :
    Finite (G.outIncidenceSet v) :=
  (G.edgeSet_finite.subset (G.outIncidenceSet_subset_edgeSet v)).to_subtype

/-- Finite actual arcs imply finite incoming incidence at each vertex. -/
instance DiGraph.instFiniteInIncidenceSet (G : DiGraph α β) (v : α) [Finite E(G)] :
    Finite (G.inIncidenceSet v) :=
  (G.edgeSet_finite.subset (G.inIncidenceSet_subset_edgeSet v)).to_subtype

/-- Finite actual arcs imply finite outgoing incidence at each vertex. -/
instance SimpleDiGraph.instFiniteOutIncidenceSet (G : SimpleDiGraph α) (v : α) [Finite E(G)] :
    Finite (G.outIncidenceSet v) :=
  (G.edgeSet_finite.subset (G.outIncidenceSet_subset_edgeSet v)).to_subtype

/-- Finite actual arcs imply finite incoming incidence at each vertex. -/
instance SimpleDiGraph.instFiniteInIncidenceSet (G : SimpleDiGraph α) (v : α) [Finite E(G)] :
    Finite (G.inIncidenceSet v) :=
  (G.edgeSet_finite.subset (G.inIncidenceSet_subset_edgeSet v)).to_subtype

/-- Finite incidence implies finitely many loops at the vertex. -/
instance Graph.instFiniteLoopSet (G : Graph α β) (v : α) [Finite (G.incidenceSet v)] :
    Finite (G.loopSet v) :=
  ((Set.toFinite (G.incidenceSet v)).subset (G.loopSet_subset_incidenceSet v)).to_subtype

/-- Finite incidence implies finitely many loops at the vertex. -/
instance SimpleGraph.instFiniteLoopSet (G : SimpleGraph α) (v : α)
    [Finite (G.incidenceSet v)] : Finite (G.loopSet v) :=
  ((Set.toFinite (G.incidenceSet v)).subset (G.loopSet_subset_incidenceSet v)).to_subtype

/-- Finite outgoing incidence implies finitely many directed loops at the vertex. -/
instance DiGraph.instFiniteLoopSet (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] : Finite (G.loopSet v) :=
  ((Set.toFinite (G.outIncidenceSet v)).subset
    (G.loopSet_subset_outIncidenceSet v)).to_subtype

/-- Finite outgoing incidence implies finitely many directed loops at the vertex. -/
instance SimpleDiGraph.instFiniteLoopSet (G : SimpleDiGraph α) (v : α)
    [Finite (G.outIncidenceSet v)] : Finite (G.loopSet v) :=
  ((Set.toFinite (G.outIncidenceSet v)).subset
    (G.loopSet_subset_outIncidenceSet v)).to_subtype

/-! ## Vertex and actual-edge finsets -/

/-- The executable finite vertex set of a general graph. -/
def Graph.vertexFinset (G : Graph α β) [Fintype V(G)] : Finset α :=
  V(G).toFinset

/-- The executable finite vertex set of a simple graph. -/
def SimpleGraph.vertexFinset (G : SimpleGraph α) [Fintype V(G)] : Finset α :=
  V(G).toFinset

/-- The executable finite vertex set of a general directed graph. -/
def DiGraph.vertexFinset (G : DiGraph α β) [Fintype V(G)] : Finset α :=
  V(G).toFinset

/-- The executable finite vertex set of a simple directed graph. -/
def SimpleDiGraph.vertexFinset (G : SimpleDiGraph α) [Fintype V(G)] : Finset α :=
  V(G).toFinset

/-- The executable finite actual bundled edge set of a general graph. -/
def Graph.edgeFinset (G : Graph α β) [Fintype E(G)] : Finset (Edge α β) :=
  E(G).toFinset

/-- The executable finite actual edge set of a simple graph. -/
def SimpleGraph.edgeFinset (G : SimpleGraph α) [Fintype E(G)] : Finset (Sym2 α) :=
  E(G).toFinset

/-- The executable finite actual bundled arc set of a general directed graph. -/
def DiGraph.edgeFinset (G : DiGraph α β) [Fintype E(G)] : Finset (Arc α β) :=
  E(G).toFinset

/-- The executable finite actual arc set of a simple directed graph. -/
def SimpleDiGraph.edgeFinset (G : SimpleDiGraph α) [Fintype E(G)] : Finset (α × α) :=
  E(G).toFinset

@[simp] theorem Graph.mem_vertexFinset (G : Graph α β) [Fintype V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem SimpleGraph.mem_vertexFinset (G : SimpleGraph α) [Fintype V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem DiGraph.mem_vertexFinset (G : DiGraph α β) [Fintype V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem SimpleDiGraph.mem_vertexFinset (G : SimpleDiGraph α) [Fintype V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem Graph.coe_vertexFinset (G : Graph α β) [Fintype V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem SimpleGraph.coe_vertexFinset (G : SimpleGraph α) [Fintype V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem DiGraph.coe_vertexFinset (G : DiGraph α β) [Fintype V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem SimpleDiGraph.coe_vertexFinset (G : SimpleDiGraph α) [Fintype V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem Graph.mem_edgeFinset (G : Graph α β) [Fintype E(G)] {e : Edge α β} :
    e ∈ G.edgeFinset ↔ e ∈ E(G) := by simp [edgeFinset]

@[simp] theorem SimpleGraph.mem_edgeFinset (G : SimpleGraph α) [Fintype E(G)] {e : Sym2 α} :
    e ∈ G.edgeFinset ↔ e ∈ E(G) := by simp [edgeFinset]

@[simp] theorem DiGraph.mem_edgeFinset (G : DiGraph α β) [Fintype E(G)] {a : Arc α β} :
    a ∈ G.edgeFinset ↔ a ∈ E(G) := by simp [edgeFinset]

@[simp] theorem SimpleDiGraph.mem_edgeFinset (G : SimpleDiGraph α) [Fintype E(G)] {a : α × α} :
    a ∈ G.edgeFinset ↔ a ∈ E(G) := by simp [edgeFinset]

@[simp] theorem Graph.coe_edgeFinset (G : Graph α β) [Fintype E(G)] :
    (G.edgeFinset : Set (Edge α β)) = E(G) := by simp [edgeFinset]

@[simp] theorem SimpleGraph.coe_edgeFinset (G : SimpleGraph α) [Fintype E(G)] :
    (G.edgeFinset : Set (Sym2 α)) = E(G) := by simp [edgeFinset]

@[simp] theorem DiGraph.coe_edgeFinset (G : DiGraph α β) [Fintype E(G)] :
    (G.edgeFinset : Set (Arc α β)) = E(G) := by simp [edgeFinset]

@[simp] theorem SimpleDiGraph.coe_edgeFinset (G : SimpleDiGraph α) [Fintype E(G)] :
    (G.edgeFinset : Set (α × α)) = E(G) := by simp [edgeFinset]

/-! ## Local neighborhood finsets -/

/-- The executable neighborhood of a vertex in a general graph. -/
def Graph.neighborFinset (G : Graph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] : Finset α :=
  G.vertexFinset.filter fun u =>
    (G.edgeFinset.filter fun e => e.endpoints = s(v, u)).Nonempty

/-- The executable neighborhood of a vertex in a simple graph. -/
def SimpleGraph.neighborFinset (G : SimpleGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] : Finset α :=
  G.vertexFinset.filter fun u =>
    (G.edgeFinset.filter fun e => e = s(v, u)).Nonempty

/-- The executable outgoing neighborhood of a vertex in a general directed graph. -/
def DiGraph.outNeighborFinset (G : DiGraph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] : Finset α :=
  G.vertexFinset.filter fun u =>
    (G.edgeFinset.filter fun a => a.source = v ∧ a.target = u).Nonempty

/-- The executable incoming neighborhood of a vertex in a general directed graph. -/
def DiGraph.inNeighborFinset (G : DiGraph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] : Finset α :=
  G.vertexFinset.filter fun u =>
    (G.edgeFinset.filter fun a => a.source = u ∧ a.target = v).Nonempty

/-- The executable outgoing neighborhood of a vertex in a simple directed graph. -/
def SimpleDiGraph.outNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] : Finset α :=
  G.vertexFinset.filter fun u =>
    (G.edgeFinset.filter fun a => a.1 = v ∧ a.2 = u).Nonempty

/-- The executable incoming neighborhood of a vertex in a simple directed graph. -/
def SimpleDiGraph.inNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] : Finset α :=
  G.vertexFinset.filter fun u =>
    (G.edgeFinset.filter fun a => a.1 = u ∧ a.2 = v).Nonempty

@[simp] theorem Graph.mem_neighborFinset (G : Graph α β) (v u : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    u ∈ G.neighborFinset v ↔ G.Adj v u := by
  simp only [neighborFinset, Finset.mem_filter, G.mem_vertexFinset,
    Finset.filter_nonempty_iff, G.mem_edgeFinset, Graph.Adj, Graph.IsLink]
  constructor
  · rintro ⟨_, e, he, hendpoints⟩
    exact ⟨e, he, hendpoints⟩
  · rintro ⟨e, he, hendpoints⟩
    exact ⟨G.endpoints_mem e he u (hendpoints.symm ▸ (by simp)), e, he, hendpoints⟩

@[simp] theorem SimpleGraph.mem_neighborFinset (G : SimpleGraph α) (v u : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    u ∈ G.neighborFinset v ↔ G.Adj v u := by
  simp only [neighborFinset, Finset.mem_filter, G.mem_vertexFinset,
    Finset.filter_nonempty_iff, G.mem_edgeFinset, SimpleGraph.Adj, SimpleGraph.IsLink]
  constructor
  · rintro ⟨_, e, he, hendpoints⟩
    exact ⟨e, he, hendpoints⟩
  · rintro ⟨e, he, hendpoints⟩
    exact ⟨G.endpoints_mem e he u (hendpoints ▸ (by simp)), e, he, hendpoints⟩

@[simp] theorem DiGraph.mem_outNeighborFinset (G : DiGraph α β) (v u : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    u ∈ G.outNeighborFinset v ↔ G.Adj v u := by
  simp only [outNeighborFinset, Finset.mem_filter, G.mem_vertexFinset,
    Finset.filter_nonempty_iff, G.mem_edgeFinset, DiGraph.Adj, DiGraph.IsArc]
  constructor
  · rintro ⟨_, a, ha, hsource, htarget⟩
    exact ⟨a, ha, hsource, htarget⟩
  · rintro ⟨a, ha, hsource, htarget⟩
    exact ⟨htarget ▸ G.target_mem a ha, a, ha, hsource, htarget⟩

@[simp] theorem DiGraph.mem_inNeighborFinset (G : DiGraph α β) (v u : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    u ∈ G.inNeighborFinset v ↔ G.Adj u v := by
  simp only [inNeighborFinset, Finset.mem_filter, G.mem_vertexFinset,
    Finset.filter_nonempty_iff, G.mem_edgeFinset, DiGraph.Adj, DiGraph.IsArc]
  constructor
  · rintro ⟨_, a, ha, hsource, htarget⟩
    exact ⟨a, ha, hsource, htarget⟩
  · rintro ⟨a, ha, hsource, htarget⟩
    exact ⟨hsource ▸ G.source_mem a ha, a, ha, hsource, htarget⟩

@[simp] theorem SimpleDiGraph.mem_outNeighborFinset (G : SimpleDiGraph α) (v u : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    u ∈ G.outNeighborFinset v ↔ G.Adj v u := by
  simp only [outNeighborFinset, Finset.mem_filter, G.mem_vertexFinset,
    Finset.filter_nonempty_iff, G.mem_edgeFinset, SimpleDiGraph.Adj, SimpleDiGraph.IsArc]
  constructor
  · rintro ⟨_, a, ha, hsource, htarget⟩
    exact ⟨a, ha, hsource, htarget⟩
  · rintro ⟨a, ha, hsource, htarget⟩
    exact ⟨htarget ▸ G.target_mem a ha, a, ha, hsource, htarget⟩

@[simp] theorem SimpleDiGraph.mem_inNeighborFinset (G : SimpleDiGraph α) (v u : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    u ∈ G.inNeighborFinset v ↔ G.Adj u v := by
  simp only [inNeighborFinset, Finset.mem_filter, G.mem_vertexFinset,
    Finset.filter_nonempty_iff, G.mem_edgeFinset, SimpleDiGraph.Adj, SimpleDiGraph.IsArc]
  constructor
  · rintro ⟨_, a, ha, hsource, htarget⟩
    exact ⟨a, ha, hsource, htarget⟩
  · rintro ⟨a, ha, hsource, htarget⟩
    exact ⟨hsource ▸ G.source_mem a ha, a, ha, hsource, htarget⟩

@[simp] theorem Graph.coe_neighborFinset (G : Graph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.neighborFinset v : Set α) = G.neighborSet v := by
  ext u
  simp

@[simp] theorem SimpleGraph.coe_neighborFinset (G : SimpleGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.neighborFinset v : Set α) = G.neighborSet v := by
  ext u
  simp

@[simp] theorem DiGraph.coe_outNeighborFinset (G : DiGraph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.outNeighborFinset v : Set α) = G.outNeighborSet v := by
  ext u
  simp

@[simp] theorem DiGraph.coe_inNeighborFinset (G : DiGraph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.inNeighborFinset v : Set α) = G.inNeighborSet v := by
  ext u
  simp

@[simp] theorem SimpleDiGraph.coe_outNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.outNeighborFinset v : Set α) = G.outNeighborSet v := by
  ext u
  simp

@[simp] theorem SimpleDiGraph.coe_inNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.inNeighborFinset v : Set α) = G.inNeighborSet v := by
  ext u
  simp

theorem Graph.neighborFinset_subset_vertexFinset (G : Graph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    G.neighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_neighborFinset v u).mp hu).right_mem

theorem SimpleGraph.neighborFinset_subset_vertexFinset
    (G : SimpleGraph α) (v : α) [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    G.neighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_neighborFinset v u).mp hu).right_mem

theorem DiGraph.outNeighborFinset_subset_vertexFinset
    (G : DiGraph α β) (v : α) [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    G.outNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_outNeighborFinset v u).mp hu).target_mem

theorem DiGraph.inNeighborFinset_subset_vertexFinset
    (G : DiGraph α β) (v : α) [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    G.inNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_inNeighborFinset v u).mp hu).source_mem

theorem SimpleDiGraph.outNeighborFinset_subset_vertexFinset
    (G : SimpleDiGraph α) (v : α) [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    G.outNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_outNeighborFinset v u).mp hu).target_mem

theorem SimpleDiGraph.inNeighborFinset_subset_vertexFinset
    (G : SimpleDiGraph α) (v : α) [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    G.inNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_inNeighborFinset v u).mp hu).source_mem

@[simp] theorem Graph.ncard_neighborSet (G : Graph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.neighborSet v).ncard = (G.neighborFinset v).card := by
  rw [← G.coe_neighborFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleGraph.ncard_neighborSet (G : SimpleGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.neighborSet v).ncard = (G.neighborFinset v).card := by
  rw [← G.coe_neighborFinset, Set.ncard_coe_finset]

@[simp] theorem DiGraph.ncard_outNeighborSet (G : DiGraph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.outNeighborSet v).ncard = (G.outNeighborFinset v).card := by
  rw [← G.coe_outNeighborFinset, Set.ncard_coe_finset]

@[simp] theorem DiGraph.ncard_inNeighborSet (G : DiGraph α β) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.inNeighborSet v).ncard = (G.inNeighborFinset v).card := by
  rw [← G.coe_inNeighborFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleDiGraph.ncard_outNeighborSet (G : SimpleDiGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.outNeighborSet v).ncard = (G.outNeighborFinset v).card := by
  rw [← G.coe_outNeighborFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleDiGraph.ncard_inNeighborSet (G : SimpleDiGraph α) (v : α)
    [Fintype V(G)] [Fintype E(G)] [DecidableEq α] :
    (G.inNeighborSet v).ncard = (G.inNeighborFinset v).card := by
  rw [← G.coe_inNeighborFinset, Set.ncard_coe_finset]

/-! ## Local incidence and loop finsets -/

/-- The executable actual edges incident with `v` in a general graph. -/
def Graph.incidenceFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (Edge α β) :=
  G.edgeFinset.filter fun e => v ∈ e.endpoints

/-- The executable actual edges incident with `v` in a simple graph. -/
def SimpleGraph.incidenceFinset (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (Sym2 α) :=
  G.edgeFinset.filter fun e => v ∈ e

/-- The executable actual arcs whose source is `v` in a general directed graph. -/
def DiGraph.outIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (Arc α β) :=
  G.edgeFinset.filter fun a => a.source = v

/-- The executable actual arcs whose target is `v` in a general directed graph. -/
def DiGraph.inIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (Arc α β) :=
  G.edgeFinset.filter fun a => a.target = v

/-- The executable actual arcs whose source is `v` in a simple directed graph. -/
def SimpleDiGraph.outIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (α × α) :=
  G.edgeFinset.filter fun a => a.1 = v

/-- The executable actual arcs whose target is `v` in a simple directed graph. -/
def SimpleDiGraph.inIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (α × α) :=
  G.edgeFinset.filter fun a => a.2 = v

/-- The executable actual loops at `v` in a general graph. -/
def Graph.loopFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (Edge α β) :=
  G.edgeFinset.filter fun e => e.endpoints = s(v, v)

/-- The executable actual loops at `v` in a simple graph. -/
def SimpleGraph.loopFinset (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (Sym2 α) :=
  G.edgeFinset.filter fun e => e = s(v, v)

/-- The executable actual directed loops at `v` in a general directed graph. -/
def DiGraph.loopFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (Arc α β) :=
  G.edgeFinset.filter fun a => a.source = v ∧ a.target = v

/-- The executable actual directed loops at `v` in a simple directed graph. -/
def SimpleDiGraph.loopFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] : Finset (α × α) :=
  G.edgeFinset.filter fun a => a.1 = v ∧ a.2 = v

@[simp] theorem Graph.mem_incidenceFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α]
    {e : Edge α β} : e ∈ G.incidenceFinset v ↔ G.Inc e v := by
  simp [incidenceFinset, Graph.Inc]

@[simp] theorem SimpleGraph.mem_incidenceFinset (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] {e : Sym2 α} :
    e ∈ G.incidenceFinset v ↔ G.Inc e v := by
  simp [incidenceFinset, SimpleGraph.Inc]

@[simp] theorem DiGraph.mem_outIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] {a : Arc α β} :
    a ∈ G.outIncidenceFinset v ↔ a ∈ E(G) ∧ a.source = v := by simp [outIncidenceFinset]

@[simp] theorem DiGraph.mem_inIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] {a : Arc α β} :
    a ∈ G.inIncidenceFinset v ↔ a ∈ E(G) ∧ a.target = v := by simp [inIncidenceFinset]

@[simp] theorem SimpleDiGraph.mem_outIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] {a : α × α} :
    a ∈ G.outIncidenceFinset v ↔ a ∈ E(G) ∧ a.1 = v := by simp [outIncidenceFinset]

@[simp] theorem SimpleDiGraph.mem_inIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] {a : α × α} :
    a ∈ G.inIncidenceFinset v ↔ a ∈ E(G) ∧ a.2 = v := by simp [inIncidenceFinset]

@[simp] theorem Graph.mem_loopFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α]
    {e : Edge α β} : e ∈ G.loopFinset v ↔ G.IsLink e v v := by simp [loopFinset]

@[simp] theorem SimpleGraph.mem_loopFinset (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] {e : Sym2 α} :
    e ∈ G.loopFinset v ↔ G.IsLink e v v := by
  simp [loopFinset]

@[simp] theorem DiGraph.mem_loopFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α]
    {a : Arc α β} : a ∈ G.loopFinset v ↔ G.IsArc a v v := by simp [loopFinset]

@[simp] theorem SimpleDiGraph.mem_loopFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] {a : α × α} :
    a ∈ G.loopFinset v ↔ G.IsArc a v v := by
  simp [loopFinset]

@[simp] theorem Graph.coe_incidenceFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.incidenceFinset v : Set (Edge α β)) = G.incidenceSet v := by
  ext e
  simp [Graph.incidenceSet, Graph.Inc]

@[simp] theorem SimpleGraph.coe_incidenceFinset (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.incidenceFinset v : Set (Sym2 α)) = G.incidenceSet v := by
  ext e
  simp [SimpleGraph.incidenceSet, SimpleGraph.Inc]

@[simp] theorem DiGraph.coe_outIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.outIncidenceFinset v : Set (Arc α β)) = G.outIncidenceSet v := by
  ext a
  simp [DiGraph.outIncidenceSet]

@[simp] theorem DiGraph.coe_inIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.inIncidenceFinset v : Set (Arc α β)) = G.inIncidenceSet v := by
  ext a
  simp [DiGraph.inIncidenceSet]

@[simp] theorem SimpleDiGraph.coe_outIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.outIncidenceFinset v : Set (α × α)) = G.outIncidenceSet v := by
  ext a
  simp [SimpleDiGraph.outIncidenceSet]

@[simp] theorem SimpleDiGraph.coe_inIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.inIncidenceFinset v : Set (α × α)) = G.inIncidenceSet v := by
  ext a
  simp [SimpleDiGraph.inIncidenceSet]

@[simp] theorem Graph.coe_loopFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopFinset v : Set (Edge α β)) = G.loopSet v := by
  ext e
  simp [Graph.loopSet, Graph.IsLink]

@[simp] theorem SimpleGraph.coe_loopFinset (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopFinset v : Set (Sym2 α)) = G.loopSet v := by
  ext e
  simp [SimpleGraph.loopSet, SimpleGraph.IsLink]

@[simp] theorem DiGraph.coe_loopFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopFinset v : Set (Arc α β)) = G.loopSet v := by
  ext a
  simp only [loopFinset, Finset.mem_coe, Finset.mem_filter, G.mem_edgeFinset,
    DiGraph.loopSet, DiGraph.IsArc, Set.mem_setOf_eq]

@[simp] theorem SimpleDiGraph.coe_loopFinset (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopFinset v : Set (α × α)) = G.loopSet v := by
  ext a
  simp only [loopFinset, Finset.mem_coe, Finset.mem_filter, G.mem_edgeFinset,
    SimpleDiGraph.loopSet, SimpleDiGraph.IsArc, Set.mem_setOf_eq]

theorem Graph.incidenceFinset_subset_edgeFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    G.incidenceFinset v ⊆ G.edgeFinset := by
  intro e he
  exact G.mem_edgeFinset.mpr ((G.mem_incidenceFinset v).mp he).edge_mem

theorem SimpleGraph.incidenceFinset_subset_edgeFinset
    (G : SimpleGraph α) (v : α) [Fintype E(G)] [DecidableEq α] :
    G.incidenceFinset v ⊆ G.edgeFinset := by
  intro e he
  exact G.mem_edgeFinset.mpr ((G.mem_incidenceFinset v).mp he).edge_mem

theorem DiGraph.outIncidenceFinset_subset_edgeFinset
    (G : DiGraph α β) (v : α) [Fintype E(G)] [DecidableEq α] :
    G.outIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_outIncidenceFinset v).mp ha).1

theorem DiGraph.inIncidenceFinset_subset_edgeFinset
    (G : DiGraph α β) (v : α) [Fintype E(G)] [DecidableEq α] :
    G.inIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_inIncidenceFinset v).mp ha).1

theorem SimpleDiGraph.outIncidenceFinset_subset_edgeFinset
    (G : SimpleDiGraph α) (v : α) [Fintype E(G)] [DecidableEq α] :
    G.outIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_outIncidenceFinset v).mp ha).1

theorem SimpleDiGraph.inIncidenceFinset_subset_edgeFinset
    (G : SimpleDiGraph α) (v : α) [Fintype E(G)] [DecidableEq α] :
    G.inIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_inIncidenceFinset v).mp ha).1

theorem Graph.loopFinset_subset_incidenceFinset (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] : G.loopFinset v ⊆ G.incidenceFinset v := by
  intro e he
  exact (G.mem_incidenceFinset v).mpr ((G.mem_loopFinset v).mp he).inc_left

theorem SimpleGraph.loopFinset_subset_incidenceFinset (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] : G.loopFinset v ⊆ G.incidenceFinset v := by
  intro e he
  exact (G.mem_incidenceFinset v).mpr ((G.mem_loopFinset v).mp he).inc_left

theorem DiGraph.loopFinset_subset_outIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] : G.loopFinset v ⊆ G.outIncidenceFinset v := by
  intro a ha
  exact (G.mem_outIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).source_eq⟩

theorem SimpleDiGraph.loopFinset_subset_outIncidenceFinset
    (G : SimpleDiGraph α) (v : α) [Fintype E(G)] [DecidableEq α] :
    G.loopFinset v ⊆ G.outIncidenceFinset v := by
  intro a ha
  exact (G.mem_outIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).source_eq⟩

theorem DiGraph.loopFinset_subset_inIncidenceFinset (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    G.loopFinset v ⊆ G.inIncidenceFinset v := by
  intro a ha
  exact (G.mem_inIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).target_eq⟩

theorem SimpleDiGraph.loopFinset_subset_inIncidenceFinset
    (G : SimpleDiGraph α) (v : α) [Fintype E(G)] [DecidableEq α] :
    G.loopFinset v ⊆ G.inIncidenceFinset v := by
  intro a ha
  exact (G.mem_inIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).target_eq⟩

@[simp] theorem Graph.ncard_incidenceSet (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.incidenceSet v).ncard = (G.incidenceFinset v).card := by
  rw [← G.coe_incidenceFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleGraph.ncard_incidenceSet (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.incidenceSet v).ncard = (G.incidenceFinset v).card := by
  rw [← G.coe_incidenceFinset, Set.ncard_coe_finset]

@[simp] theorem DiGraph.ncard_outIncidenceSet (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.outIncidenceSet v).ncard = (G.outIncidenceFinset v).card := by
  rw [← G.coe_outIncidenceFinset, Set.ncard_coe_finset]

@[simp] theorem DiGraph.ncard_inIncidenceSet (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.inIncidenceSet v).ncard = (G.inIncidenceFinset v).card := by
  rw [← G.coe_inIncidenceFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleDiGraph.ncard_outIncidenceSet (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.outIncidenceSet v).ncard = (G.outIncidenceFinset v).card := by
  rw [← G.coe_outIncidenceFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleDiGraph.ncard_inIncidenceSet (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.inIncidenceSet v).ncard = (G.inIncidenceFinset v).card := by
  rw [← G.coe_inIncidenceFinset, Set.ncard_coe_finset]

@[simp] theorem Graph.ncard_loopSet (G : Graph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopSet v).ncard = (G.loopFinset v).card := by
  rw [← G.coe_loopFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleGraph.ncard_loopSet (G : SimpleGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopSet v).ncard = (G.loopFinset v).card := by
  rw [← G.coe_loopFinset, Set.ncard_coe_finset]

@[simp] theorem DiGraph.ncard_loopSet (G : DiGraph α β) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopSet v).ncard = (G.loopFinset v).card := by
  rw [← G.coe_loopFinset, Set.ncard_coe_finset]

@[simp] theorem SimpleDiGraph.ncard_loopSet (G : SimpleDiGraph α) (v : α)
    [Fintype E(G)] [DecidableEq α] :
    (G.loopSet v).ncard = (G.loopFinset v).card := by
  rw [← G.coe_loopFinset, Set.ncard_coe_finset]

/-! ## Global cardinal bridges -/

@[simp] theorem Graph.ncard_vertexSet (G : Graph α β) [Fintype V(G)] :
    V(G).ncard = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp] theorem SimpleGraph.ncard_vertexSet (G : SimpleGraph α) [Fintype V(G)] :
    V(G).ncard = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp] theorem DiGraph.ncard_vertexSet (G : DiGraph α β) [Fintype V(G)] :
    V(G).ncard = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp] theorem SimpleDiGraph.ncard_vertexSet (G : SimpleDiGraph α) [Fintype V(G)] :
    V(G).ncard = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp] theorem Graph.ncard_edgeSet (G : Graph α β) [Fintype E(G)] :
    E(G).ncard = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp] theorem SimpleGraph.ncard_edgeSet (G : SimpleGraph α) [Fintype E(G)] :
    E(G).ncard = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp] theorem DiGraph.ncard_edgeSet (G : DiGraph α β) [Fintype E(G)] :
    E(G).ncard = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

@[simp] theorem SimpleDiGraph.ncard_edgeSet (G : SimpleDiGraph α) [Fintype E(G)] :
    E(G).ncard = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

/-! ## Simple cardinality bounds -/

private theorem SimpleGraph.vertexFinset_card_eq (G : SimpleGraph α) [Fintype V(G)] :
    G.vertexFinset.card = Fintype.card V(G) := by
  simp [vertexFinset]

private theorem SimpleGraph.edgeLift (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ E(G)) :
    ∃ s : Sym2 V(G), ¬ s.IsDiag ∧ s.map Subtype.val = e := by
  induction e with
  | h x y =>
    refine ⟨s(⟨x, G.endpoints_mem _ he x (by simp)⟩,
      ⟨y, G.endpoints_mem _ he y (by simp)⟩), ?_, by simp [Sym2.map_mk]⟩
    have hne : ¬ (s(x, y) : Sym2 α).IsDiag := G.loopless _ he
    simpa [Sym2.mk_isDiag_iff, Subtype.ext_iff] using hne

/-- A simple graph has at most `choose |V| 2` actual edges. -/
theorem SimpleGraph.card_edgeFinset_le_card_vertexFinset_choose_two
    (G : SimpleGraph α) [Fintype V(G)] [Fintype E(G)] :
    G.edgeFinset.card ≤ G.vertexFinset.card.choose 2 := by
  classical
  let f : G.edgeFinset → {s : Sym2 V(G) // ¬ s.IsDiag} := fun e =>
    ⟨(G.edgeLift (G.mem_edgeFinset.mp e.property)).choose,
      (G.edgeLift (G.mem_edgeFinset.mp e.property)).choose_spec.1⟩
  have hf : Function.Injective f := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ h
    apply Subtype.ext
    have hs : (G.edgeLift (G.mem_edgeFinset.mp he)).choose =
        (G.edgeLift (G.mem_edgeFinset.mp he')).choose := Subtype.ext_iff.mp h
    have hm := congrArg (Sym2.map Subtype.val) hs
    simpa only [(G.edgeLift (G.mem_edgeFinset.mp he)).choose_spec.2,
      (G.edgeLift (G.mem_edgeFinset.mp he')).choose_spec.2] using hm
  calc
    G.edgeFinset.card = Fintype.card G.edgeFinset := (Fintype.card_coe _).symm
    _ ≤ Fintype.card {s : Sym2 V(G) // ¬ s.IsDiag} := Fintype.card_le_of_injective f hf
    _ = (Fintype.card V(G)).choose 2 := Sym2.card_subtype_not_diag
    _ = G.vertexFinset.card.choose 2 := by rw [G.vertexFinset_card_eq]

private theorem SimpleDiGraph.vertexFinset_card_eq (G : SimpleDiGraph α) [Fintype V(G)] :
    G.vertexFinset.card = Fintype.card V(G) := by
  simp [vertexFinset]

/-- A simple directed graph has at most twice `choose |V| 2` actual arcs. -/
theorem SimpleDiGraph.card_edgeFinset_le_two_mul_card_vertexFinset_choose_two
    (G : SimpleDiGraph α) [Fintype V(G)] [Fintype E(G)] :
    G.edgeFinset.card ≤ 2 * G.vertexFinset.card.choose 2 := by
  classical
  let f : G.edgeFinset → {p : V(G) × V(G) // p.1 ≠ p.2} := fun a =>
    let ha := G.mem_edgeFinset.mp a.property
    ⟨(⟨a.val.1, G.source_mem _ ha⟩, ⟨a.val.2, G.target_mem _ ha⟩), by
      simpa only [ne_eq, Subtype.mk.injEq] using G.loopless _ ha⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨u, v⟩, huv⟩ ⟨⟨x, y⟩, hxy⟩ h
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have hcard : Fintype.card {p : V(G) × V(G) // p.1 ≠ p.2} =
      Fintype.card V(G) * (Fintype.card V(G) - 1) := by
    rw [Fintype.card_subtype]
    have hfilter :
        ((Finset.univ : Finset (V(G) × V(G))).filter fun p => p.1 ≠ p.2) =
          (Finset.univ : Finset V(G)).offDiag := by
      ext p
      simp [Finset.mem_offDiag]
    rw [hfilter, Finset.offDiag_card]
    simp [Finset.card_univ, Nat.mul_sub_one]
  have hchoose : 2 * (Fintype.card V(G)).choose 2 =
      Fintype.card V(G) * (Fintype.card V(G) - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]
  calc
    G.edgeFinset.card = Fintype.card G.edgeFinset := (Fintype.card_coe _).symm
    _ ≤ Fintype.card {p : V(G) × V(G) // p.1 ≠ p.2} :=
      Fintype.card_le_of_injective f hf
    _ = Fintype.card V(G) * (Fintype.card V(G) - 1) := hcard
    _ = 2 * (Fintype.card V(G)).choose 2 := hchoose.symm
    _ = 2 * G.vertexFinset.card.choose 2 := by rw [G.vertexFinset_card_eq]

end GraphLib
