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
# Mathematical finite-set views of graphs

This file exposes noncomputable `Finset` views of the finite mathematical sets used by GraphLib.
The views carry exactly the membership semantics of their `Set` counterparts; they are not an
executable graph representation.

For general graphs, finiteness of the vertex set and finiteness of the actual bundled edge set
are independent. For simple graphs only, finite vertices imply finite edges. Local neighborhood
and incidence finiteness is derived from the corresponding ambient finite set.
-/

namespace GraphLib

open scoped GraphLib

variable {α β : Type*}

private noncomputable def finiteSetFinset (s : Set α) [Finite s] : Finset α :=
  (Set.toFinite s).toFinset

@[simp] private theorem mem_finiteSetFinset (s : Set α) [Finite s] (x : α) :
    x ∈ finiteSetFinset s ↔ x ∈ s := by
  simp [finiteSetFinset]

@[simp] private theorem coe_finiteSetFinset (s : Set α) [Finite s] :
    (finiteSetFinset s : Set α) = s := by
  ext x
  simp

@[simp] private theorem ncard_finiteSetFinset (s : Set α) [Finite s] :
    s.ncard = (finiteSetFinset s).card := by
  rw [Set.ncard_eq_toFinset_card s (Set.toFinite s)]
  rfl

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

/-- The finite vertex set of a general graph as a noncomputable `Finset`. -/
noncomputable def Graph.vertexFinset (G : Graph α β) [Finite V(G)] : Finset α :=
  finiteSetFinset V(G)

/-- The finite vertex set of a simple graph as a noncomputable `Finset`. -/
noncomputable def SimpleGraph.vertexFinset (G : SimpleGraph α) [Finite V(G)] : Finset α :=
  finiteSetFinset V(G)

/-- The finite vertex set of a general directed graph as a noncomputable `Finset`. -/
noncomputable def DiGraph.vertexFinset (G : DiGraph α β) [Finite V(G)] : Finset α :=
  finiteSetFinset V(G)

/-- The finite vertex set of a simple directed graph as a noncomputable `Finset`. -/
noncomputable def SimpleDiGraph.vertexFinset (G : SimpleDiGraph α) [Finite V(G)] : Finset α :=
  finiteSetFinset V(G)

/-- The finite actual bundled edge set of a general graph as a noncomputable `Finset`. -/
noncomputable def Graph.edgeFinset (G : Graph α β) [Finite E(G)] : Finset (Edge α β) :=
  finiteSetFinset E(G)

/-- The finite actual edge set of a simple graph as a noncomputable `Finset`. -/
noncomputable def SimpleGraph.edgeFinset (G : SimpleGraph α) [Finite E(G)] : Finset (Sym2 α) :=
  finiteSetFinset E(G)

/-- The finite actual bundled arc set of a general directed graph as a noncomputable `Finset`. -/
noncomputable def DiGraph.edgeFinset (G : DiGraph α β) [Finite E(G)] : Finset (Arc α β) :=
  finiteSetFinset E(G)

/-- The finite actual arc set of a simple directed graph as a noncomputable `Finset`. -/
noncomputable def SimpleDiGraph.edgeFinset (G : SimpleDiGraph α) [Finite E(G)] :
    Finset (α × α) := finiteSetFinset E(G)

@[simp] theorem Graph.mem_vertexFinset (G : Graph α β) [Finite V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem SimpleGraph.mem_vertexFinset (G : SimpleGraph α) [Finite V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem DiGraph.mem_vertexFinset (G : DiGraph α β) [Finite V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem SimpleDiGraph.mem_vertexFinset (G : SimpleDiGraph α) [Finite V(G)] {v : α} :
    v ∈ G.vertexFinset ↔ v ∈ V(G) := by simp [vertexFinset]

@[simp] theorem Graph.coe_vertexFinset (G : Graph α β) [Finite V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem SimpleGraph.coe_vertexFinset (G : SimpleGraph α) [Finite V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem DiGraph.coe_vertexFinset (G : DiGraph α β) [Finite V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem SimpleDiGraph.coe_vertexFinset (G : SimpleDiGraph α) [Finite V(G)] :
    (G.vertexFinset : Set α) = V(G) := by simp [vertexFinset]

@[simp] theorem Graph.mem_edgeFinset (G : Graph α β) [Finite E(G)] {e : Edge α β} :
    e ∈ G.edgeFinset ↔ e ∈ E(G) := by simp [edgeFinset]

@[simp] theorem SimpleGraph.mem_edgeFinset (G : SimpleGraph α) [Finite E(G)] {e : Sym2 α} :
    e ∈ G.edgeFinset ↔ e ∈ E(G) := by simp [edgeFinset]

@[simp] theorem DiGraph.mem_edgeFinset (G : DiGraph α β) [Finite E(G)] {a : Arc α β} :
    a ∈ G.edgeFinset ↔ a ∈ E(G) := by simp [edgeFinset]

@[simp] theorem SimpleDiGraph.mem_edgeFinset (G : SimpleDiGraph α) [Finite E(G)] {a : α × α} :
    a ∈ G.edgeFinset ↔ a ∈ E(G) := by simp [edgeFinset]

@[simp] theorem Graph.coe_edgeFinset (G : Graph α β) [Finite E(G)] :
    (G.edgeFinset : Set (Edge α β)) = E(G) := by simp [edgeFinset]

@[simp] theorem SimpleGraph.coe_edgeFinset (G : SimpleGraph α) [Finite E(G)] :
    (G.edgeFinset : Set (Sym2 α)) = E(G) := by simp [edgeFinset]

@[simp] theorem DiGraph.coe_edgeFinset (G : DiGraph α β) [Finite E(G)] :
    (G.edgeFinset : Set (Arc α β)) = E(G) := by simp [edgeFinset]

@[simp] theorem SimpleDiGraph.coe_edgeFinset (G : SimpleDiGraph α) [Finite E(G)] :
    (G.edgeFinset : Set (α × α)) = E(G) := by simp [edgeFinset]

/-! ## Local neighborhood finsets -/

/-- A finite neighborhood in a general graph as a noncomputable `Finset`. -/
noncomputable def Graph.neighborFinset (G : Graph α β) (v : α)
    [Finite (G.neighborSet v)] : Finset α := finiteSetFinset (G.neighborSet v)

/-- A finite neighborhood in a simple graph as a noncomputable `Finset`. -/
noncomputable def SimpleGraph.neighborFinset (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] : Finset α := finiteSetFinset (G.neighborSet v)

/-- A finite outgoing neighborhood in a general directed graph as a noncomputable `Finset`. -/
noncomputable def DiGraph.outNeighborFinset (G : DiGraph α β) (v : α)
    [Finite (G.outNeighborSet v)] : Finset α := finiteSetFinset (G.outNeighborSet v)

/-- A finite incoming neighborhood in a general directed graph as a noncomputable `Finset`. -/
noncomputable def DiGraph.inNeighborFinset (G : DiGraph α β) (v : α)
    [Finite (G.inNeighborSet v)] : Finset α := finiteSetFinset (G.inNeighborSet v)

/-- A finite outgoing neighborhood in a simple directed graph as a noncomputable `Finset`. -/
noncomputable def SimpleDiGraph.outNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.outNeighborSet v)] : Finset α := finiteSetFinset (G.outNeighborSet v)

/-- A finite incoming neighborhood in a simple directed graph as a noncomputable `Finset`. -/
noncomputable def SimpleDiGraph.inNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.inNeighborSet v)] : Finset α := finiteSetFinset (G.inNeighborSet v)

@[simp] theorem Graph.mem_neighborFinset (G : Graph α β) (v u : α)
    [Finite (G.neighborSet v)] : u ∈ G.neighborFinset v ↔ G.Adj v u := by simp [neighborFinset]

@[simp] theorem SimpleGraph.mem_neighborFinset (G : SimpleGraph α) (v u : α)
    [Finite (G.neighborSet v)] : u ∈ G.neighborFinset v ↔ G.Adj v u := by simp [neighborFinset]

@[simp] theorem DiGraph.mem_outNeighborFinset (G : DiGraph α β) (v u : α)
    [Finite (G.outNeighborSet v)] : u ∈ G.outNeighborFinset v ↔ G.Adj v u := by
  simp [outNeighborFinset]

@[simp] theorem DiGraph.mem_inNeighborFinset (G : DiGraph α β) (v u : α)
    [Finite (G.inNeighborSet v)] : u ∈ G.inNeighborFinset v ↔ G.Adj u v := by
  simp [inNeighborFinset]

@[simp] theorem SimpleDiGraph.mem_outNeighborFinset (G : SimpleDiGraph α) (v u : α)
    [Finite (G.outNeighborSet v)] : u ∈ G.outNeighborFinset v ↔ G.Adj v u := by
  simp [outNeighborFinset]

@[simp] theorem SimpleDiGraph.mem_inNeighborFinset (G : SimpleDiGraph α) (v u : α)
    [Finite (G.inNeighborSet v)] : u ∈ G.inNeighborFinset v ↔ G.Adj u v := by
  simp [inNeighborFinset]

@[simp] theorem Graph.coe_neighborFinset (G : Graph α β) (v : α)
    [Finite (G.neighborSet v)] : (G.neighborFinset v : Set α) = G.neighborSet v := by
  simp [neighborFinset]

@[simp] theorem SimpleGraph.coe_neighborFinset (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] : (G.neighborFinset v : Set α) = G.neighborSet v := by
  simp [neighborFinset]

@[simp] theorem DiGraph.coe_outNeighborFinset (G : DiGraph α β) (v : α)
    [Finite (G.outNeighborSet v)] : (G.outNeighborFinset v : Set α) = G.outNeighborSet v := by
  simp [outNeighborFinset]

@[simp] theorem DiGraph.coe_inNeighborFinset (G : DiGraph α β) (v : α)
    [Finite (G.inNeighborSet v)] : (G.inNeighborFinset v : Set α) = G.inNeighborSet v := by
  simp [inNeighborFinset]

@[simp] theorem SimpleDiGraph.coe_outNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.outNeighborSet v)] : (G.outNeighborFinset v : Set α) = G.outNeighborSet v := by
  simp [outNeighborFinset]

@[simp] theorem SimpleDiGraph.coe_inNeighborFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.inNeighborSet v)] : (G.inNeighborFinset v : Set α) = G.inNeighborSet v := by
  simp [inNeighborFinset]

theorem Graph.neighborFinset_subset_vertexFinset (G : Graph α β) (v : α) [Finite V(G)] :
    G.neighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_neighborFinset v u).mp hu).right_mem

theorem SimpleGraph.neighborFinset_subset_vertexFinset
    (G : SimpleGraph α) (v : α) [Finite V(G)] :
    G.neighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_neighborFinset v u).mp hu).right_mem

theorem DiGraph.outNeighborFinset_subset_vertexFinset
    (G : DiGraph α β) (v : α) [Finite V(G)] :
    G.outNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_outNeighborFinset v u).mp hu).target_mem

theorem DiGraph.inNeighborFinset_subset_vertexFinset
    (G : DiGraph α β) (v : α) [Finite V(G)] :
    G.inNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_inNeighborFinset v u).mp hu).source_mem

theorem SimpleDiGraph.outNeighborFinset_subset_vertexFinset
    (G : SimpleDiGraph α) (v : α) [Finite V(G)] :
    G.outNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_outNeighborFinset v u).mp hu).target_mem

theorem SimpleDiGraph.inNeighborFinset_subset_vertexFinset
    (G : SimpleDiGraph α) (v : α) [Finite V(G)] :
    G.inNeighborFinset v ⊆ G.vertexFinset := by
  intro u hu
  exact G.mem_vertexFinset.mpr ((G.mem_inNeighborFinset v u).mp hu).source_mem

@[simp] theorem Graph.ncard_neighborSet (G : Graph α β) (v : α)
    [Finite (G.neighborSet v)] : (G.neighborSet v).ncard = (G.neighborFinset v).card := by
  simp [neighborFinset]

@[simp] theorem SimpleGraph.ncard_neighborSet (G : SimpleGraph α) (v : α)
    [Finite (G.neighborSet v)] : (G.neighborSet v).ncard = (G.neighborFinset v).card := by
  simp [neighborFinset]

@[simp] theorem DiGraph.ncard_outNeighborSet (G : DiGraph α β) (v : α)
    [Finite (G.outNeighborSet v)] :
    (G.outNeighborSet v).ncard = (G.outNeighborFinset v).card := by simp [outNeighborFinset]

@[simp] theorem DiGraph.ncard_inNeighborSet (G : DiGraph α β) (v : α)
    [Finite (G.inNeighborSet v)] :
    (G.inNeighborSet v).ncard = (G.inNeighborFinset v).card := by simp [inNeighborFinset]

@[simp] theorem SimpleDiGraph.ncard_outNeighborSet (G : SimpleDiGraph α) (v : α)
    [Finite (G.outNeighborSet v)] :
    (G.outNeighborSet v).ncard = (G.outNeighborFinset v).card := by simp [outNeighborFinset]

@[simp] theorem SimpleDiGraph.ncard_inNeighborSet (G : SimpleDiGraph α) (v : α)
    [Finite (G.inNeighborSet v)] :
    (G.inNeighborSet v).ncard = (G.inNeighborFinset v).card := by simp [inNeighborFinset]

/-! ## Local incidence and loop finsets -/

/-- The finite actual edges incident with `v` in a general graph. -/
noncomputable def Graph.incidenceFinset (G : Graph α β) (v : α)
    [Finite (G.incidenceSet v)] : Finset (Edge α β) := finiteSetFinset (G.incidenceSet v)

/-- The finite actual edges incident with `v` in a simple graph. -/
noncomputable def SimpleGraph.incidenceFinset (G : SimpleGraph α) (v : α)
    [Finite (G.incidenceSet v)] : Finset (Sym2 α) := finiteSetFinset (G.incidenceSet v)

/-- The finite actual arcs whose source is `v` in a general directed graph. -/
noncomputable def DiGraph.outIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] : Finset (Arc α β) := finiteSetFinset (G.outIncidenceSet v)

/-- The finite actual arcs whose target is `v` in a general directed graph. -/
noncomputable def DiGraph.inIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.inIncidenceSet v)] : Finset (Arc α β) := finiteSetFinset (G.inIncidenceSet v)

/-- The finite actual arcs whose source is `v` in a simple directed graph. -/
noncomputable def SimpleDiGraph.outIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.outIncidenceSet v)] : Finset (α × α) := finiteSetFinset (G.outIncidenceSet v)

/-- The finite actual arcs whose target is `v` in a simple directed graph. -/
noncomputable def SimpleDiGraph.inIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.inIncidenceSet v)] : Finset (α × α) := finiteSetFinset (G.inIncidenceSet v)

/-- The finite actual loops at `v` in a general graph. -/
noncomputable def Graph.loopFinset (G : Graph α β) (v : α)
    [Finite (G.loopSet v)] : Finset (Edge α β) := finiteSetFinset (G.loopSet v)

/-- The finite actual loops at `v` in a simple graph. -/
noncomputable def SimpleGraph.loopFinset (G : SimpleGraph α) (v : α)
    [Finite (G.loopSet v)] : Finset (Sym2 α) := finiteSetFinset (G.loopSet v)

/-- The finite actual directed loops at `v` in a general directed graph. -/
noncomputable def DiGraph.loopFinset (G : DiGraph α β) (v : α)
    [Finite (G.loopSet v)] : Finset (Arc α β) := finiteSetFinset (G.loopSet v)

/-- The finite actual directed loops at `v` in a simple directed graph. -/
noncomputable def SimpleDiGraph.loopFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.loopSet v)] : Finset (α × α) := finiteSetFinset (G.loopSet v)

@[simp] theorem Graph.mem_incidenceFinset (G : Graph α β) (v : α) [Finite (G.incidenceSet v)]
    {e : Edge α β} : e ∈ G.incidenceFinset v ↔ G.Inc e v := by simp [incidenceFinset]

@[simp] theorem SimpleGraph.mem_incidenceFinset (G : SimpleGraph α) (v : α)
    [Finite (G.incidenceSet v)] {e : Sym2 α} : e ∈ G.incidenceFinset v ↔ G.Inc e v := by
  simp [incidenceFinset]

@[simp] theorem DiGraph.mem_outIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] {a : Arc α β} :
    a ∈ G.outIncidenceFinset v ↔ a ∈ E(G) ∧ a.source = v := by simp [outIncidenceFinset]

@[simp] theorem DiGraph.mem_inIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.inIncidenceSet v)] {a : Arc α β} :
    a ∈ G.inIncidenceFinset v ↔ a ∈ E(G) ∧ a.target = v := by simp [inIncidenceFinset]

@[simp] theorem SimpleDiGraph.mem_outIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.outIncidenceSet v)] {a : α × α} :
    a ∈ G.outIncidenceFinset v ↔ a ∈ E(G) ∧ a.1 = v := by simp [outIncidenceFinset]

@[simp] theorem SimpleDiGraph.mem_inIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.inIncidenceSet v)] {a : α × α} :
    a ∈ G.inIncidenceFinset v ↔ a ∈ E(G) ∧ a.2 = v := by simp [inIncidenceFinset]

@[simp] theorem Graph.mem_loopFinset (G : Graph α β) (v : α) [Finite (G.loopSet v)]
    {e : Edge α β} : e ∈ G.loopFinset v ↔ G.IsLink e v v := by simp [loopFinset]

@[simp] theorem SimpleGraph.mem_loopFinset (G : SimpleGraph α) (v : α)
    [Finite (G.loopSet v)] {e : Sym2 α} : e ∈ G.loopFinset v ↔ G.IsLink e v v := by
  simp [loopFinset]

@[simp] theorem DiGraph.mem_loopFinset (G : DiGraph α β) (v : α) [Finite (G.loopSet v)]
    {a : Arc α β} : a ∈ G.loopFinset v ↔ G.IsArc a v v := by simp [loopFinset]

@[simp] theorem SimpleDiGraph.mem_loopFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.loopSet v)] {a : α × α} : a ∈ G.loopFinset v ↔ G.IsArc a v v := by
  simp [loopFinset]

@[simp] theorem Graph.coe_incidenceFinset (G : Graph α β) (v : α)
    [Finite (G.incidenceSet v)] : (G.incidenceFinset v : Set (Edge α β)) = G.incidenceSet v := by
  simp [incidenceFinset]

@[simp] theorem SimpleGraph.coe_incidenceFinset (G : SimpleGraph α) (v : α)
    [Finite (G.incidenceSet v)] : (G.incidenceFinset v : Set (Sym2 α)) = G.incidenceSet v := by
  simp [incidenceFinset]

@[simp] theorem DiGraph.coe_outIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceFinset v : Set (Arc α β)) = G.outIncidenceSet v := by
  simp [outIncidenceFinset]

@[simp] theorem DiGraph.coe_inIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceFinset v : Set (Arc α β)) = G.inIncidenceSet v := by
  simp [inIncidenceFinset]

@[simp] theorem SimpleDiGraph.coe_outIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceFinset v : Set (α × α)) = G.outIncidenceSet v := by
  simp [outIncidenceFinset]

@[simp] theorem SimpleDiGraph.coe_inIncidenceFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceFinset v : Set (α × α)) = G.inIncidenceSet v := by
  simp [inIncidenceFinset]

@[simp] theorem Graph.coe_loopFinset (G : Graph α β) (v : α) [Finite (G.loopSet v)] :
    (G.loopFinset v : Set (Edge α β)) = G.loopSet v := by simp [loopFinset]

@[simp] theorem SimpleGraph.coe_loopFinset (G : SimpleGraph α) (v : α)
    [Finite (G.loopSet v)] : (G.loopFinset v : Set (Sym2 α)) = G.loopSet v := by
  simp [loopFinset]

@[simp] theorem DiGraph.coe_loopFinset (G : DiGraph α β) (v : α) [Finite (G.loopSet v)] :
    (G.loopFinset v : Set (Arc α β)) = G.loopSet v := by simp [loopFinset]

@[simp] theorem SimpleDiGraph.coe_loopFinset (G : SimpleDiGraph α) (v : α)
    [Finite (G.loopSet v)] : (G.loopFinset v : Set (α × α)) = G.loopSet v := by
  simp [loopFinset]

theorem Graph.incidenceFinset_subset_edgeFinset (G : Graph α β) (v : α) [Finite E(G)] :
    G.incidenceFinset v ⊆ G.edgeFinset := by
  intro e he
  exact G.mem_edgeFinset.mpr ((G.mem_incidenceFinset v).mp he).edge_mem

theorem SimpleGraph.incidenceFinset_subset_edgeFinset
    (G : SimpleGraph α) (v : α) [Finite E(G)] :
    G.incidenceFinset v ⊆ G.edgeFinset := by
  intro e he
  exact G.mem_edgeFinset.mpr ((G.mem_incidenceFinset v).mp he).edge_mem

theorem DiGraph.outIncidenceFinset_subset_edgeFinset
    (G : DiGraph α β) (v : α) [Finite E(G)] :
    G.outIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_outIncidenceFinset v).mp ha).1

theorem DiGraph.inIncidenceFinset_subset_edgeFinset
    (G : DiGraph α β) (v : α) [Finite E(G)] :
    G.inIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_inIncidenceFinset v).mp ha).1

theorem SimpleDiGraph.outIncidenceFinset_subset_edgeFinset
    (G : SimpleDiGraph α) (v : α) [Finite E(G)] :
    G.outIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_outIncidenceFinset v).mp ha).1

theorem SimpleDiGraph.inIncidenceFinset_subset_edgeFinset
    (G : SimpleDiGraph α) (v : α) [Finite E(G)] :
    G.inIncidenceFinset v ⊆ G.edgeFinset := by
  intro a ha
  exact G.mem_edgeFinset.mpr ((G.mem_inIncidenceFinset v).mp ha).1

theorem Graph.loopFinset_subset_incidenceFinset (G : Graph α β) (v : α)
    [Finite (G.incidenceSet v)] : G.loopFinset v ⊆ G.incidenceFinset v := by
  intro e he
  exact (G.mem_incidenceFinset v).mpr ((G.mem_loopFinset v).mp he).inc_left

theorem SimpleGraph.loopFinset_subset_incidenceFinset (G : SimpleGraph α) (v : α)
    [Finite (G.incidenceSet v)] : G.loopFinset v ⊆ G.incidenceFinset v := by
  intro e he
  exact (G.mem_incidenceFinset v).mpr ((G.mem_loopFinset v).mp he).inc_left

theorem DiGraph.loopFinset_subset_outIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] : G.loopFinset v ⊆ G.outIncidenceFinset v := by
  intro a ha
  exact (G.mem_outIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).source_eq⟩

theorem SimpleDiGraph.loopFinset_subset_outIncidenceFinset
    (G : SimpleDiGraph α) (v : α) [Finite (G.outIncidenceSet v)] :
    G.loopFinset v ⊆ G.outIncidenceFinset v := by
  intro a ha
  exact (G.mem_outIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).source_eq⟩

theorem DiGraph.loopFinset_subset_inIncidenceFinset (G : DiGraph α β) (v : α)
    [Finite (G.loopSet v)] [Finite (G.inIncidenceSet v)] :
    G.loopFinset v ⊆ G.inIncidenceFinset v := by
  intro a ha
  exact (G.mem_inIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).target_eq⟩

theorem SimpleDiGraph.loopFinset_subset_inIncidenceFinset
    (G : SimpleDiGraph α) (v : α) [Finite (G.loopSet v)] [Finite (G.inIncidenceSet v)] :
    G.loopFinset v ⊆ G.inIncidenceFinset v := by
  intro a ha
  exact (G.mem_inIncidenceFinset v).mpr
    ⟨((G.mem_loopFinset v).mp ha).edge_mem, ((G.mem_loopFinset v).mp ha).target_eq⟩

@[simp] theorem Graph.ncard_incidenceSet (G : Graph α β) (v : α)
    [Finite (G.incidenceSet v)] :
    (G.incidenceSet v).ncard = (G.incidenceFinset v).card := by simp [incidenceFinset]

@[simp] theorem SimpleGraph.ncard_incidenceSet (G : SimpleGraph α) (v : α)
    [Finite (G.incidenceSet v)] :
    (G.incidenceSet v).ncard = (G.incidenceFinset v).card := by simp [incidenceFinset]

@[simp] theorem DiGraph.ncard_outIncidenceSet (G : DiGraph α β) (v : α)
    [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceSet v).ncard = (G.outIncidenceFinset v).card := by simp [outIncidenceFinset]

@[simp] theorem DiGraph.ncard_inIncidenceSet (G : DiGraph α β) (v : α)
    [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceSet v).ncard = (G.inIncidenceFinset v).card := by simp [inIncidenceFinset]

@[simp] theorem SimpleDiGraph.ncard_outIncidenceSet (G : SimpleDiGraph α) (v : α)
    [Finite (G.outIncidenceSet v)] :
    (G.outIncidenceSet v).ncard = (G.outIncidenceFinset v).card := by simp [outIncidenceFinset]

@[simp] theorem SimpleDiGraph.ncard_inIncidenceSet (G : SimpleDiGraph α) (v : α)
    [Finite (G.inIncidenceSet v)] :
    (G.inIncidenceSet v).ncard = (G.inIncidenceFinset v).card := by simp [inIncidenceFinset]

@[simp] theorem Graph.ncard_loopSet (G : Graph α β) (v : α) [Finite (G.loopSet v)] :
    (G.loopSet v).ncard = (G.loopFinset v).card := by simp [loopFinset]

@[simp] theorem SimpleGraph.ncard_loopSet (G : SimpleGraph α) (v : α)
    [Finite (G.loopSet v)] : (G.loopSet v).ncard = (G.loopFinset v).card := by
  simp [loopFinset]

@[simp] theorem DiGraph.ncard_loopSet (G : DiGraph α β) (v : α) [Finite (G.loopSet v)] :
    (G.loopSet v).ncard = (G.loopFinset v).card := by simp [loopFinset]

@[simp] theorem SimpleDiGraph.ncard_loopSet (G : SimpleDiGraph α) (v : α)
    [Finite (G.loopSet v)] : (G.loopSet v).ncard = (G.loopFinset v).card := by
  simp [loopFinset]

/-! ## Global cardinal bridges -/

@[simp] theorem Graph.ncard_vertexSet (G : Graph α β) [Finite V(G)] :
    V(G).ncard = G.vertexFinset.card := by simp [vertexFinset]

@[simp] theorem SimpleGraph.ncard_vertexSet (G : SimpleGraph α) [Finite V(G)] :
    V(G).ncard = G.vertexFinset.card := by simp [vertexFinset]

@[simp] theorem DiGraph.ncard_vertexSet (G : DiGraph α β) [Finite V(G)] :
    V(G).ncard = G.vertexFinset.card := by simp [vertexFinset]

@[simp] theorem SimpleDiGraph.ncard_vertexSet (G : SimpleDiGraph α) [Finite V(G)] :
    V(G).ncard = G.vertexFinset.card := by simp [vertexFinset]

@[simp] theorem Graph.ncard_edgeSet (G : Graph α β) [Finite E(G)] :
    E(G).ncard = G.edgeFinset.card := by simp [edgeFinset]

@[simp] theorem SimpleGraph.ncard_edgeSet (G : SimpleGraph α) [Finite E(G)] :
    E(G).ncard = G.edgeFinset.card := by simp [edgeFinset]

@[simp] theorem DiGraph.ncard_edgeSet (G : DiGraph α β) [Finite E(G)] :
    E(G).ncard = G.edgeFinset.card := by simp [edgeFinset]

@[simp] theorem SimpleDiGraph.ncard_edgeSet (G : SimpleDiGraph α) [Finite E(G)] :
    E(G).ncard = G.edgeFinset.card := by simp [edgeFinset]

/-! ## Simple cardinality bounds -/

private theorem SimpleGraph.vertexFinset_card_eq (G : SimpleGraph α) [Finite V(G)]
    [Fintype V(G)] : G.vertexFinset.card = Fintype.card V(G) := by
  change (finiteSetFinset V(G)).card = Fintype.card V(G)
  exact (Set.toFinite V(G)).card_toFinset

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
    (G : SimpleGraph α) [Finite V(G)] :
    G.edgeFinset.card ≤ G.vertexFinset.card.choose 2 := by
  classical
  haveI : Fintype V(G) := Fintype.ofFinite V(G)
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

private theorem SimpleDiGraph.vertexFinset_card_eq (G : SimpleDiGraph α) [Finite V(G)]
    [Fintype V(G)] : G.vertexFinset.card = Fintype.card V(G) := by
  change (finiteSetFinset V(G)).card = Fintype.card V(G)
  exact (Set.toFinite V(G)).card_toFinset

/-- A simple directed graph has at most twice `choose |V| 2` actual arcs. -/
theorem SimpleDiGraph.card_edgeFinset_le_two_mul_card_vertexFinset_choose_two
    (G : SimpleDiGraph α) [Finite V(G)] :
    G.edgeFinset.card ≤ 2 * G.vertexFinset.card.choose 2 := by
  classical
  haveI : Fintype V(G) := Fintype.ofFinite V(G)
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
