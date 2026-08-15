/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Adjacency

/-!
# Actual-edge core tests

Compile-time and small semantic fixtures for the Phase 1 graph foundation.
-/

namespace GraphLibTest.Foundation.Basic

open GraphLib
open scoped GraphLib

variable {α β : Type*}

section TypeChecks

variable
  (Gu : Graph α β) (Gs : SimpleGraph α)
  (Gd : DiGraph α β) (Gsd : SimpleDiGraph α)

#check (E(Gu) : Set (Edge α β))
#check (E(Gs) : Set (Sym2 α))
#check (E(Gd) : Set (Arc α β))
#check (E(Gsd) : Set (α × α))

#check (Gu.edgeEndpointPairSet : Set (Sym2 α))
#check (Gd.arcEndpointPairSet : Set (α × α))

#check Gu.IsLink
#check Gs.IsLink
#check Gd.IsArc
#check Gsd.IsArc
#check Gu.Inc
#check Gd.Inc
#check Gu.Adj
#check Gd.Adj

#check (Gu.incidenceSet : α → Set (Edge α β))
#check (Gd.outIncidenceSet : α → Set (Arc α β))
#check (Gd.inIncidenceSet : α → Set (Arc α β))

#check (Gs.toGraph : Graph α (Sym2 α))
#check (Gsd.toDiGraph : DiGraph α (α × α))

example {G H : Graph α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) : G = H :=
  Graph.ext hV hE

example {G H : DiGraph α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) : G = H :=
  DiGraph.ext hV hE

/-- No implicit simple-to-general conversion is registered. -/
example : True := by
  fail_if_success
    have _h : Coe (SimpleGraph α) (Graph α (Sym2 α)) := inferInstance
  fail_if_success
    have _h : Coe (SimpleDiGraph α) (DiGraph α (α × α)) := inferInstance
  trivial

end TypeChecks

section Fixtures

def parallelEdgeFalse : Edge Nat Bool := ⟨false, s(0, 1)⟩
def parallelEdgeTrue : Edge Nat Bool := ⟨true, s(0, 1)⟩

/-- A graph with two distinct actual edges having common endpoints. -/
def parallelGraph : Graph Nat Bool where
  vertexSet := Set.univ
  edgeSet := {parallelEdgeFalse, parallelEdgeTrue}
  endpoints_mem := by simp

example : parallelEdgeFalse ≠ parallelEdgeTrue := by decide
example : parallelEdgeFalse ∈ E(parallelGraph) := by simp [parallelGraph]
example : parallelEdgeTrue ∈ E(parallelGraph) := by simp [parallelGraph]
example : parallelGraph.IsLink parallelEdgeFalse 0 1 := by
  simp [parallelGraph, parallelEdgeFalse]
example : parallelGraph.IsLink parallelEdgeTrue 0 1 := by
  simp [parallelGraph, parallelEdgeTrue]
example : parallelEdgeFalse ∈ parallelGraph.incidenceSet 0 := by
  simp [parallelGraph, parallelEdgeFalse, Graph.Inc]
example : s(0, 1) ∈ parallelGraph.edgeEndpointPairSet := by
  exact ⟨parallelEdgeFalse, by simp [parallelGraph], rfl⟩

def reusedTagEdgeOne : Edge Nat Unit := ⟨(), s(0, 1)⟩
def reusedTagEdgeTwo : Edge Nat Unit := ⟨(), s(2, 3)⟩

/-- A graph in which one tag is reused at different endpoints. -/
def tagReuseGraph : Graph Nat Unit where
  vertexSet := Set.univ
  edgeSet := {reusedTagEdgeOne, reusedTagEdgeTwo}
  endpoints_mem := by simp

example : reusedTagEdgeOne ≠ reusedTagEdgeTwo := by decide
example : reusedTagEdgeOne ∈ E(tagReuseGraph) := by simp [tagReuseGraph]
example : reusedTagEdgeTwo ∈ E(tagReuseGraph) := by simp [tagReuseGraph]

def testArc : Arc Nat Bool := ⟨true, (4, 5)⟩

/-- A one-arc directed fixture for source/target and incidence tests. -/
def oneArcDiGraph : DiGraph Nat Bool where
  vertexSet := Set.univ
  edgeSet := {testArc}
  source_mem := by simp
  target_mem := by simp

example : testArc.source = 4 := rfl
example : testArc.target = 5 := rfl
example : oneArcDiGraph.IsArc testArc 4 5 := by simp [oneArcDiGraph, testArc]
example : testArc ∈ oneArcDiGraph.outIncidenceSet 4 := by simp [oneArcDiGraph, testArc]
example : testArc ∈ oneArcDiGraph.inIncidenceSet 5 := by simp [oneArcDiGraph, testArc]
example : oneArcDiGraph.Adj 4 5 := by
  exact (by simp [oneArcDiGraph, testArc] : oneArcDiGraph.IsArc testArc 4 5).adj

def parallelArcFalse : Arc Nat Bool := ⟨false, (0, 1)⟩
def parallelArcTrue : Arc Nat Bool := ⟨true, (0, 1)⟩

/-- A directed graph with two distinct actual arcs having common source and target. -/
def parallelDiGraph : DiGraph Nat Bool where
  vertexSet := Set.univ
  edgeSet := {parallelArcFalse, parallelArcTrue}
  source_mem := by simp
  target_mem := by simp

example : parallelArcFalse ≠ parallelArcTrue := by decide
example : parallelArcFalse ∈ E(parallelDiGraph) := by simp [parallelDiGraph]
example : parallelArcTrue ∈ E(parallelDiGraph) := by simp [parallelDiGraph]
example : parallelArcFalse ∈ parallelDiGraph.outIncidenceSet 0 := by
  simp [parallelDiGraph, parallelArcFalse]
example : parallelArcTrue ∈ parallelDiGraph.outIncidenceSet 0 := by
  simp [parallelDiGraph, parallelArcTrue]
example : parallelDiGraph.Adj 0 1 := by
  exact (by simp [parallelDiGraph, parallelArcFalse] :
    parallelDiGraph.IsArc parallelArcFalse 0 1).adj

def reusedTagArcOne : Arc Nat Unit := ⟨(), (0, 1)⟩
def reusedTagArcTwo : Arc Nat Unit := ⟨(), (2, 3)⟩

/-- A directed graph in which one tag is reused at different ordered endpoints. -/
def tagReuseDiGraph : DiGraph Nat Unit where
  vertexSet := Set.univ
  edgeSet := {reusedTagArcOne, reusedTagArcTwo}
  source_mem := by simp
  target_mem := by simp

example : reusedTagArcOne ≠ reusedTagArcTwo := by decide
example : reusedTagArcOne ∈ E(tagReuseDiGraph) := by simp [tagReuseDiGraph]
example : reusedTagArcTwo ∈ E(tagReuseDiGraph) := by simp [tagReuseDiGraph]
example : reusedTagArcOne ∈ tagReuseDiGraph.outIncidenceSet 0 := by
  simp [tagReuseDiGraph, reusedTagArcOne]
example : reusedTagArcTwo ∈ tagReuseDiGraph.inIncidenceSet 3 := by
  simp [tagReuseDiGraph, reusedTagArcTwo]

end Fixtures

end GraphLibTest.Foundation.Basic
