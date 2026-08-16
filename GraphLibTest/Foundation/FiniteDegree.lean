/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.DegreeSum
import GraphLib.Theory.MooreBound

/-!
# Finite-set and degree foundation tests

Compile-time API checks and concrete Phase 6 fixtures for finite-local degree, loops, parallel
actual edges, directed incidence, and the handshaking identities.
-/

namespace GraphLibTest.Foundation.FiniteDegree

open GraphLib
open scoped GraphLib BigOperators

variable {α β : Type*}

section TypeChecks

variable
  (Gu : Graph α β) (Gs : SimpleGraph α)
  (Gd : DiGraph α β) (Gsd : SimpleDiGraph α) (v : α)

#check (Gu.neighborSet v : Set α)
#check (Gs.neighborSet v : Set α)
#check (Gd.outNeighborSet v : Set α)
#check (Gd.inNeighborSet v : Set α)
#check (Gsd.outNeighborSet v : Set α)
#check (Gsd.inNeighborSet v : Set α)

#check Graph.vertexFinset
#check Graph.edgeFinset
#check Graph.neighborFinset
#check Graph.incidenceFinset
#check Graph.loopFinset
#check DiGraph.outNeighborFinset
#check DiGraph.inNeighborFinset
#check DiGraph.outIncidenceFinset
#check DiGraph.inIncidenceFinset

#check Graph.degree
#check SimpleGraph.degree
#check DiGraph.outDegree
#check DiGraph.inDegree
#check Graph.maxDegree
#check Graph.minDegree
#check DiGraph.maxOutDegree
#check DiGraph.minOutDegree
#check DiGraph.maxInDegree
#check DiGraph.minInDegree

#check Graph.sum_degrees_eq_twice_card_edges
#check SimpleGraph.sum_degrees_eq_twice_card_edges
#check DiGraph.sum_outDegrees_eq_card_edges
#check DiGraph.sum_inDegrees_eq_card_edges
#check SimpleDiGraph.sum_outDegrees_eq_card_edges
#check SimpleDiGraph.sum_inDegrees_eq_card_edges
#check Graph.averageDegree
#check SimpleGraph.averageDegree
#check Graph.degree_induce
#check Graph.degree_deleteEdges
#check DiGraph.outDegree_deleteVerts
#check SimpleDiGraph.inDegree_deleteArcsFromTo
#check DiGraph.outDegree_reverse
#check DiGraph.inDegree_reverse
#check SimpleDiGraph.outDegree_reverse
#check SimpleDiGraph.inDegree_reverse
#check Graph.restrictEdges_induce
#check DiGraph.deleteEdges_induce

#check SimpleGraph.girth.eq_top_iff_isAcyclic
#check SimpleGraph.girth.ne_top_iff_hasSimpleCycle
#check SimpleGraph.girth.ne_top_of_two_le_degree

/-- Finite vertices alone do not manufacture finiteness of general actual edges. -/
example (G : Graph α β) [Finite V(G)] : True := by
  fail_if_success
    have _h : Finite E(G) := inferInstance
  trivial

/-- The same independence holds for general directed actual arcs. -/
example (G : DiGraph α β) [Finite V(G)] : True := by
  fail_if_success
    have _h : Finite E(G) := inferInstance
  trivial

/-- Local finiteness follows all standard finite graph transformations. -/
example (G : Graph α β) [Finite V(G)] [Finite E(G)] (S : Set α)
    (F : Set (Edge α β)) (f : α ≃ α) :
    Finite V((G.induce S).deleteEdges F) ∧
      Finite E((G.restrictEdges F).relabelVertices f) := by
  exact ⟨inferInstance, inferInstance⟩

example (G : DiGraph α β) [Finite V(G)] [Finite E(G)] (S : Set α)
    (F : Set (Arc α β)) (f : β ≃ β) :
    Finite V((G.deleteVerts S).relabelTags f) ∧
      Finite E((G.restrictEdges F).reverse) := by
  exact ⟨inferInstance, inferInstance⟩

example (G : SimpleGraph α) [Finite V(G)] [Finite E(G)] (S : Set α)
    (F : Set (Sym2 α)) :
    Finite V(G.deleteVerts S) ∧ Finite E(G.restrictEdges F) := by
  exact ⟨inferInstance, inferInstance⟩

example (G : SimpleDiGraph α) [Finite V(G)] [Finite E(G)] (S : Set α)
    (F : Set (α × α)) :
    Finite V((G.induce S).reverse) ∧ Finite E(G.deleteEdges F) := by
  exact ⟨inferInstance, inferInstance⟩

end TypeChecks

section ConcreteGraphs

def parallelEdgeFalse : Edge Bool Bool := ⟨false, s(false, true)⟩
def parallelEdgeTrue : Edge Bool Bool := ⟨true, s(false, true)⟩

/-- A finite graph with two parallel actual edges. -/
def finiteParallelGraph : Graph Bool Bool where
  vertexSet := Set.univ
  edgeSet := {parallelEdgeFalse, parallelEdgeTrue}
  endpoints_mem := by
    simp [parallelEdgeFalse, parallelEdgeTrue]

local instance : Finite E(finiteParallelGraph) := by
  apply Set.Finite.to_subtype
  change ({parallelEdgeFalse, parallelEdgeTrue} : Set (Edge Bool Bool)).Finite
  exact (Set.finite_singleton parallelEdgeTrue).insert parallelEdgeFalse

/-- Parallel actual edges do not duplicate a vertex in the neighborhood set. -/
example : (finiteParallelGraph.neighborSet false).ncard = 1 := by
  have hn : finiteParallelGraph.neighborSet false = {true} := by
    ext u
    cases u <;>
      simp [Graph.neighborSet, Graph.Adj, finiteParallelGraph, parallelEdgeFalse,
        parallelEdgeTrue, Graph.IsLink]
  rw [hn, Set.ncard_singleton]

example : finiteParallelGraph.degree false = 2 := by
  rw [← finiteParallelGraph.ncard_incidenceSet_add_ncard_loopSet_eq_degree]
  have hi : finiteParallelGraph.incidenceSet false =
      {parallelEdgeFalse, parallelEdgeTrue} := by
    ext e
    change ((e = parallelEdgeFalse ∨ e = parallelEdgeTrue) ∧ false ∈ e.endpoints) ↔
      e = parallelEdgeFalse ∨ e = parallelEdgeTrue
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rcases h with rfl | rfl <;> simp [parallelEdgeFalse, parallelEdgeTrue]
  have hl : finiteParallelGraph.loopSet false = ∅ := by
    ext e
    change ((e = parallelEdgeFalse ∨ e = parallelEdgeTrue) ∧
      e.endpoints = s(false, false)) ↔ False
    constructor
    · rintro ⟨h, he⟩
      rcases h with rfl | rfl <;>
        simp [parallelEdgeFalse, parallelEdgeTrue] at he
    · intro h
      contradiction
  rw [hi, hl, Set.ncard_pair (by decide), Set.ncard_empty]

example : finiteParallelGraph.degree true = 2 := by
  rw [← finiteParallelGraph.ncard_incidenceSet_add_ncard_loopSet_eq_degree]
  have hi : finiteParallelGraph.incidenceSet true =
      {parallelEdgeFalse, parallelEdgeTrue} := by
    ext e
    change ((e = parallelEdgeFalse ∨ e = parallelEdgeTrue) ∧ true ∈ e.endpoints) ↔
      e = parallelEdgeFalse ∨ e = parallelEdgeTrue
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rcases h with rfl | rfl <;> simp [parallelEdgeFalse, parallelEdgeTrue]
  have hl : finiteParallelGraph.loopSet true = ∅ := by
    ext e
    change ((e = parallelEdgeFalse ∨ e = parallelEdgeTrue) ∧
      e.endpoints = s(true, true)) ↔ False
    constructor
    · rintro ⟨h, he⟩
      rcases h with rfl | rfl <;>
        simp [parallelEdgeFalse, parallelEdgeTrue] at he
    · intro h
      contradiction
  rw [hi, hl, Set.ncard_pair (by decide), Set.ncard_empty]

example : (∑ v ∈ finiteParallelGraph.vertexFinset, finiteParallelGraph.degree v) = 4 := by
  rw [finiteParallelGraph.sum_degrees_eq_twice_card_edges]
  rw [← finiteParallelGraph.ncard_edgeSet]
  change 2 * ({parallelEdgeFalse, parallelEdgeTrue} : Set (Edge Bool Bool)).ncard = 4
  rw [Set.ncard_pair (by decide)]

def loopEdgeFalse : Edge Unit Bool := ⟨false, s((), ())⟩
def loopEdgeTrue : Edge Unit Bool := ⟨true, s((), ())⟩

/-- Two distinct loop edges at one vertex; each contributes two to degree. -/
def twoLoopGraph : Graph Unit Bool where
  vertexSet := Set.univ
  edgeSet := {loopEdgeFalse, loopEdgeTrue}
  endpoints_mem := by
    simp [loopEdgeFalse, loopEdgeTrue]

local instance : Finite E(twoLoopGraph) := by
  apply Set.Finite.to_subtype
  change ({loopEdgeFalse, loopEdgeTrue} : Set (Edge Unit Bool)).Finite
  exact (Set.finite_singleton loopEdgeTrue).insert loopEdgeFalse

/-- Undirected loops place their endpoint in its own neighborhood, once as a set element. -/
example : twoLoopGraph.neighborSet () = {()} := by
  ext u
  rcases u with ⟨⟩
  simp [Graph.neighborSet, Graph.Adj, twoLoopGraph, loopEdgeFalse, loopEdgeTrue,
    Graph.IsLink]

example : twoLoopGraph.degree () = 4 := by
  rw [← twoLoopGraph.ncard_incidenceSet_add_ncard_loopSet_eq_degree]
  have hi : twoLoopGraph.incidenceSet () = {loopEdgeFalse, loopEdgeTrue} := by
    ext e
    change ((e = loopEdgeFalse ∨ e = loopEdgeTrue) ∧ () ∈ e.endpoints) ↔
      e = loopEdgeFalse ∨ e = loopEdgeTrue
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rcases h with rfl | rfl <;> simp [loopEdgeFalse, loopEdgeTrue]
  have hl : twoLoopGraph.loopSet () = {loopEdgeFalse, loopEdgeTrue} := by
    ext e
    change ((e = loopEdgeFalse ∨ e = loopEdgeTrue) ∧ e.endpoints = s((), ())) ↔
      e = loopEdgeFalse ∨ e = loopEdgeTrue
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rcases h with rfl | rfl <;> rfl
  rw [hi, hl, Set.ncard_pair (by decide)]

example : (∑ v ∈ twoLoopGraph.vertexFinset, twoLoopGraph.degree v) = 4 := by
  rw [twoLoopGraph.sum_degrees_eq_twice_card_edges]
  rw [← twoLoopGraph.ncard_edgeSet]
  change 2 * ({loopEdgeFalse, loopEdgeTrue} : Set (Edge Unit Bool)).ncard = 4
  rw [Set.ncard_pair (by decide)]

def directedLoop : Arc Unit Unit := ⟨(), ((), ())⟩

/-- A finite directed graph with one loop. -/
def oneLoopDiGraph : DiGraph Unit Unit where
  vertexSet := Set.univ
  edgeSet := {directedLoop}
  source_mem := by simp [directedLoop]
  target_mem := by simp [directedLoop]

local instance : Finite E(oneLoopDiGraph) := by
  apply Set.Finite.to_subtype
  change ({directedLoop} : Set (Arc Unit Unit)).Finite
  exact Set.finite_singleton directedLoop

example : oneLoopDiGraph.outDegree () = 1 := by
  rw [← oneLoopDiGraph.ncard_outIncidenceSet_eq_outDegree]
  have h : oneLoopDiGraph.outIncidenceSet () = {directedLoop} := by
    ext a
    simp [DiGraph.outIncidenceSet, oneLoopDiGraph, directedLoop]
  rw [h, Set.ncard_singleton]

example : oneLoopDiGraph.inDegree () = 1 := by
  rw [← oneLoopDiGraph.ncard_inIncidenceSet_eq_inDegree]
  have h : oneLoopDiGraph.inIncidenceSet () = {directedLoop} := by
    ext a
    simp [DiGraph.inIncidenceSet, oneLoopDiGraph, directedLoop]
  rw [h, Set.ncard_singleton]

example : (∑ v ∈ oneLoopDiGraph.vertexFinset, oneLoopDiGraph.outDegree v) = 1 := by
  rw [oneLoopDiGraph.sum_outDegrees_eq_card_edges]
  rw [← oneLoopDiGraph.ncard_edgeSet]
  change ({directedLoop} : Set (Arc Unit Unit)).ncard = 1
  rw [Set.ncard_singleton]

example : (∑ v ∈ oneLoopDiGraph.vertexFinset, oneLoopDiGraph.inDegree v) = 1 := by
  rw [oneLoopDiGraph.sum_inDegrees_eq_card_edges]
  rw [← oneLoopDiGraph.ncard_edgeSet]
  change ({directedLoop} : Set (Arc Unit Unit)).ncard = 1
  rw [Set.ncard_singleton]

def infiniteTaggedLoopEdge (n : Nat) : Edge Unit Nat := ⟨n, s((), ())⟩

/-- Finite vertices do not force finiteness of a general graph's actual bundled edges. -/
def finiteVertexInfiniteEdgeGraph : Graph Unit Nat where
  vertexSet := Set.univ
  edgeSet := Set.univ
  endpoints_mem := by simp

example : Finite V(finiteVertexInfiniteEdgeGraph) := inferInstance

example : Infinite E(finiteVertexInfiniteEdgeGraph) := by
  apply Infinite.of_injective fun n : Nat =>
    (⟨infiniteTaggedLoopEdge n, by simp [finiteVertexInfiniteEdgeGraph]⟩ :
      E(finiteVertexInfiniteEdgeGraph))
  intro m n h
  exact congrArg (fun e => e.val.tag) h

/-- An infinite graph can still have finite local degree. -/
def infiniteEdgelessGraph : Graph Nat Unit where
  vertexSet := Set.univ
  edgeSet := ∅
  endpoints_mem := by simp

local instance (v : Nat) : Finite (infiniteEdgelessGraph.incidenceSet v) := by
  apply Set.Finite.to_subtype
  simp [Graph.incidenceSet, Graph.Inc, infiniteEdgelessGraph]

example : infiniteEdgelessGraph.degree 17 = 0 := by
  rw [← infiniteEdgelessGraph.ncard_incidenceSet_add_ncard_loopSet_eq_degree]
  have hi : infiniteEdgelessGraph.incidenceSet 17 = ∅ := by
    ext e
    simp [Graph.incidenceSet, Graph.Inc, infiniteEdgelessGraph]
  have hl : infiniteEdgelessGraph.loopSet 17 = ∅ := by
    ext e
    simp [Graph.loopSet, Graph.IsLink, infiniteEdgelessGraph]
  rw [hi, hl]
  simp only [Set.ncard_empty, add_zero]

example : Set.Infinite V(infiniteEdgelessGraph) := by
  simpa [infiniteEdgelessGraph] using Set.infinite_univ

def finiteSimpleEdge : SimpleGraph Bool where
  vertexSet := Set.univ
  edgeSet := {s(false, true)}
  endpoints_mem := by simp
  loopless := by simp

example : finiteSimpleEdge.degree false = 1 := by
  rw [← finiteSimpleEdge.ncard_neighborSet_eq_degree]
  have hn : finiteSimpleEdge.neighborSet false = {true} := by
    ext u
    cases u <;> simp [SimpleGraph.neighborSet, SimpleGraph.Adj, finiteSimpleEdge]
  rw [hn, Set.ncard_singleton]

example : (∑ v ∈ finiteSimpleEdge.vertexFinset, finiteSimpleEdge.degree v) = 2 := by
  rw [finiteSimpleEdge.sum_degrees_eq_twice_card_edges]
  rw [← finiteSimpleEdge.ncard_edgeSet]
  change 2 * ({s(false, true)} : Set (Sym2 Bool)).ncard = 2
  rw [Set.ncard_singleton]

end ConcreteGraphs

end GraphLibTest.Foundation.FiniteDegree
