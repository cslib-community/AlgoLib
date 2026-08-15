/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.Sym.Sym2

/-!
# Graph structures

This file defines the four graph carriers used by GraphLib. Every graph stores its vertex set
explicitly. General graphs store bundled actual edges or arcs, while simple graphs use their
endpoint pairs as actual edges.

For `Edge α β` and `Arc α β`, the entire bundled value is the actual identity. The value of type
`β` is only a tag used to discriminate otherwise equal bundles; it need not be globally unique.
Accordingly, `E(G)` always denotes actual edges or arcs. The explicitly lossy endpoint images of
a general graph are `Graph.edgeEndpointPairSet` and `DiGraph.arcEndpointPairSet`.

The conversions `SimpleGraph.toGraph` and `SimpleDiGraph.toDiGraph` are intentionally explicit:
they change the representation of an edge and are not coercions.
-/

namespace GraphLib
variable {α β : Type*}

/-- An undirected actual edge. Its full `(tag, endpoints)` bundle is its identity; the tag need
not be globally unique. -/
structure Edge (α β : Type*) where
  /-- A discriminator within the bundled edge, not a globally unique edge identity. -/
  tag : β
  /-- The unordered pair of endpoints. -/
  endpoints : Sym2 α
deriving DecidableEq

/-- A directed actual arc. Its full `(tag, endpoints)` bundle is its identity; the tag need not
be globally unique. -/
structure Arc (α β : Type*) where
  /-- A discriminator within the bundled arc, not a globally unique arc identity. -/
  tag : β
  /-- The ordered pair `(source, target)` of endpoints. -/
  endpoints : α × α
deriving DecidableEq

namespace Edge

/-- Two bundled edges are equal when both their tags and endpoint pairs are equal. -/
@[ext] theorem ext {e f : Edge α β} (htag : e.tag = f.tag)
    (hendpoints : e.endpoints = f.endpoints) : e = f := by
  cases e
  cases f
  simp_all

end Edge

namespace Arc

/-- Two bundled arcs are equal when both their tags and ordered endpoint pairs are equal. -/
@[ext] theorem ext {a b : Arc α β} (htag : a.tag = b.tag)
    (hendpoints : a.endpoints = b.endpoints) : a = b := by
  cases a
  cases b
  simp_all

/-- The source vertex of a directed arc. -/
@[simp] def source (a : Arc α β) : α := a.endpoints.1

/-- The target vertex of a directed arc. -/
@[simp] def target (a : Arc α β) : α := a.endpoints.2

@[simp] theorem source_mk (tag : β) (u v : α) : source (Arc.mk tag (u, v)) = u := rfl

@[simp] theorem target_mk (tag : β) (u v : α) : target (Arc.mk tag (u, v)) = v := rfl

end Arc

/-- A general undirected graph. Its edge set contains actual bundled `Edge` values, so parallel
edges and loops are preserved and both carrier sets may be infinite. -/
structure Graph (α β : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of actual bundled edges. -/
  edgeSet : Set (Edge α β)
  /-- Every endpoint of an edge is a vertex. -/
  endpoints_mem : ∀ e ∈ edgeSet, ∀ v ∈ e.endpoints, v ∈ vertexSet

/-- A simple undirected graph whose actual edges are unordered pairs of distinct vertices. -/
@[grind]
structure SimpleGraph (α : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of actual edges, represented by unordered endpoint pairs. -/
  edgeSet : Set (Sym2 α)
  /-- Every endpoint of an edge is a vertex. -/
  endpoints_mem : ∀ e ∈ edgeSet, ∀ v ∈ e, v ∈ vertexSet
  /-- No edge is a loop. -/
  loopless : ∀ e ∈ edgeSet, ¬ e.IsDiag

/-- A general directed graph. Its edge set contains actual bundled `Arc` values, so parallel arcs
and loops are preserved and both carrier sets may be infinite. -/
structure DiGraph (α β : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of actual bundled arcs. -/
  edgeSet : Set (Arc α β)
  /-- The source of every arc is a vertex. -/
  source_mem : ∀ a ∈ edgeSet, a.source ∈ vertexSet
  /-- The target of every arc is a vertex. -/
  target_mem : ∀ a ∈ edgeSet, a.target ∈ vertexSet

/-- A simple directed graph whose actual arcs are ordered pairs of distinct vertices. -/
structure SimpleDiGraph (α : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of actual arcs, represented by ordered endpoint pairs. -/
  edgeSet : Set (α × α)
  /-- The source of every arc is a vertex. -/
  source_mem : ∀ a ∈ edgeSet, a.1 ∈ vertexSet
  /-- The target of every arc is a vertex. -/
  target_mem : ∀ a ∈ edgeSet, a.2 ∈ vertexSet
  /-- No arc is a loop. -/
  loopless : ∀ a ∈ edgeSet, a.1 ≠ a.2

/-- Typeclass for graph-like structures that have a vertex set. -/
class HasVertexSet (G : Type*) (V : outParam Type*) where
  /-- The vertex set of the graph. -/
  vertexSet : G → V

/-- Typeclass for graph-like structures that have an actual edge set. -/
class HasEdgeSet (G : Type*) (E : outParam Type*) where
  /-- The set of actual edges or arcs of the graph. -/
  edgeSet : G → E

@[simp] instance {α β : Type*} : HasVertexSet (Graph α β) (Set α) :=
  ⟨Graph.vertexSet⟩

@[simp] instance {α : Type*} : HasVertexSet (SimpleGraph α) (Set α) :=
  ⟨SimpleGraph.vertexSet⟩

@[simp] instance {α β : Type*} : HasVertexSet (DiGraph α β) (Set α) :=
  ⟨DiGraph.vertexSet⟩

@[simp] instance {α : Type*} : HasVertexSet (SimpleDiGraph α) (Set α) :=
  ⟨SimpleDiGraph.vertexSet⟩

@[simp] instance {α β : Type*} : HasEdgeSet (Graph α β) (Set (Edge α β)) :=
  ⟨Graph.edgeSet⟩

@[simp] instance {α : Type*} : HasEdgeSet (SimpleGraph α) (Set (Sym2 α)) :=
  ⟨SimpleGraph.edgeSet⟩

@[simp] instance {α β : Type*} : HasEdgeSet (DiGraph α β) (Set (Arc α β)) :=
  ⟨DiGraph.edgeSet⟩

@[simp] instance {α : Type*} : HasEdgeSet (SimpleDiGraph α) (Set (α × α)) :=
  ⟨SimpleDiGraph.edgeSet⟩

/-- Notation for the vertex set of a graph. -/
scoped notation "V(" G ")" => HasVertexSet.vertexSet G

/-- Notation for the set of actual edges or arcs of a graph. -/
scoped notation "E(" G ")" => HasEdgeSet.edgeSet G

open scoped GraphLib

@[simp] theorem Graph.mem_vertexSet (G : Graph α β) (v : α) :
    v ∈ V(G) ↔ v ∈ G.vertexSet := Iff.rfl

@[simp] theorem SimpleGraph.mem_vertexSet (G : SimpleGraph α) (v : α) :
    v ∈ V(G) ↔ v ∈ G.vertexSet := Iff.rfl

@[simp] theorem DiGraph.mem_vertexSet (G : DiGraph α β) (v : α) :
    v ∈ V(G) ↔ v ∈ G.vertexSet := Iff.rfl

@[simp] theorem SimpleDiGraph.mem_vertexSet (G : SimpleDiGraph α) (v : α) :
    v ∈ V(G) ↔ v ∈ G.vertexSet := Iff.rfl

@[simp] theorem Graph.mem_edgeSet (G : Graph α β) (e : Edge α β) :
    e ∈ E(G) ↔ e ∈ G.edgeSet := Iff.rfl

@[simp] theorem SimpleGraph.mem_edgeSet (G : SimpleGraph α) (e : Sym2 α) :
    e ∈ E(G) ↔ e ∈ G.edgeSet := Iff.rfl

@[simp] theorem DiGraph.mem_edgeSet (G : DiGraph α β) (a : Arc α β) :
    a ∈ E(G) ↔ a ∈ G.edgeSet := Iff.rfl

@[simp] theorem SimpleDiGraph.mem_edgeSet (G : SimpleDiGraph α) (a : α × α) :
    a ∈ E(G) ↔ a ∈ G.edgeSet := Iff.rfl

/-! ## Extensionality -/

/-- General graphs are equal when their vertex sets and actual bundled edge sets are equal. -/
@[ext] theorem Graph.ext {G H : Graph α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) :
    G = H := by
  rcases G with ⟨GV, GE, Gendpoints⟩
  rcases H with ⟨HV, HE, Hendpoints⟩
  change GV = HV at hV
  change GE = HE at hE
  subst HV
  subst HE
  rfl

/-- Simple graphs are equal when their vertex sets and actual edge sets are equal. -/
@[ext] theorem SimpleGraph.ext {G H : SimpleGraph α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G = H := by
  rcases G with ⟨GV, GE, Gendpoints, Gloopless⟩
  rcases H with ⟨HV, HE, Hendpoints, Hloopless⟩
  change GV = HV at hV
  change GE = HE at hE
  subst HV
  subst HE
  rfl

/-- General directed graphs are equal when their vertex sets and actual bundled arc sets are
equal. -/
@[ext] theorem DiGraph.ext {G H : DiGraph α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) :
    G = H := by
  rcases G with ⟨GV, GE, Gsource, Gtarget⟩
  rcases H with ⟨HV, HE, Hsource, Htarget⟩
  change GV = HV at hV
  change GE = HE at hE
  subst HV
  subst HE
  rfl

/-- Simple directed graphs are equal when their vertex sets and actual arc sets are equal. -/
@[ext] theorem SimpleDiGraph.ext {G H : SimpleDiGraph α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G = H := by
  rcases G with ⟨GV, GE, Gsource, Gtarget, Gloopless⟩
  rcases H with ⟨HV, HE, Hsource, Htarget, Hloopless⟩
  change GV = HV at hV
  change GE = HE at hE
  subst HV
  subst HE
  rfl

/-- The lossy image of a general graph's actual edges under the endpoint projection. Parallel
edges with common endpoints are merged in this view. -/
def Graph.edgeEndpointPairSet (G : Graph α β) : Set (Sym2 α) :=
  Edge.endpoints '' E(G)

/-- The lossy image of a general directed graph's actual arcs under the endpoint projection.
Parallel arcs with common source and target are merged in this view. -/
def DiGraph.arcEndpointPairSet (G : DiGraph α β) : Set (α × α) :=
  Arc.endpoints '' E(G)

@[simp] theorem Graph.mem_edgeEndpointPairSet (G : Graph α β) (p : Sym2 α) :
    p ∈ G.edgeEndpointPairSet ↔ ∃ e ∈ E(G), e.endpoints = p := Iff.rfl

@[simp] theorem DiGraph.mem_arcEndpointPairSet (G : DiGraph α β) (p : α × α) :
    p ∈ G.arcEndpointPairSet ↔ ∃ a ∈ E(G), a.endpoints = p := Iff.rfl

/-- Explicitly view a simple graph as a general graph by bundling each endpoint pair as both tag
and endpoints. This conversion changes the edge representation and is intentionally not a
coercion. -/
def SimpleGraph.toGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := G.vertexSet
  edgeSet := (fun e => ⟨e, e⟩) '' G.edgeSet
  endpoints_mem := by
    rintro _ ⟨e, he, rfl⟩ v hv
    exact G.endpoints_mem e he v hv

/-- Explicitly view a simple directed graph as a general directed graph by bundling each ordered
pair as both tag and endpoints. This conversion changes the arc representation and is
intentionally not a coercion. -/
def SimpleDiGraph.toDiGraph (G : SimpleDiGraph α) : DiGraph α (α × α) where
  vertexSet := G.vertexSet
  edgeSet := (fun a => ⟨a, a⟩) '' G.edgeSet
  source_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact G.source_mem a ha
  target_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact G.target_mem a ha

@[simp] theorem SimpleGraph.vertexSet_toGraph (G : SimpleGraph α) :
    V(G.toGraph) = V(G) := rfl

@[simp] theorem SimpleGraph.edgeSet_toGraph (G : SimpleGraph α) :
    E(G.toGraph) = (fun e => Edge.mk e e) '' E(G) := rfl

@[simp] theorem SimpleDiGraph.vertexSet_toDiGraph (G : SimpleDiGraph α) :
    V(G.toDiGraph) = V(G) := rfl

@[simp] theorem SimpleDiGraph.edgeSet_toDiGraph (G : SimpleDiGraph α) :
    E(G.toDiGraph) = (fun a => Arc.mk a a) '' E(G) := rfl

end GraphLib
