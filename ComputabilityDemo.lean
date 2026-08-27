import GraphLib.Graph.DegreeSum

/-!
# Executable finite-graph demo

This file defines a concrete bundled multigraph with two parallel edges and one loop.  Its
ambient vertex type `Nat` and tag type `Int` are both infinite.  The executable API is backed by
explicit `Fintype` enumerations only of the graph's actual vertex and edge subtypes; no `Finite`
proof is converted into runtime data.
-/

namespace ComputabilityDemo

open GraphLib
open scoped GraphLib BigOperators

def parallelEdge₀ : Edge Nat Int := ⟨0, s(0, 1)⟩
def parallelEdge₁ : Edge Nat Int := ⟨1, s(0, 1)⟩
def loopEdge : Edge Nat Int := ⟨2, s(0, 0)⟩

/-- A two-vertex multigraph inside infinite ambient types, with two parallel edges and a loop. -/
def graph : Graph Nat Int where
  vertexSet := {0, 1}
  edgeSet := {parallelEdge₀, parallelEdge₁, loopEdge}
  endpoints_mem := by simp [parallelEdge₀, parallelEdge₁, loopEdge]

example : Infinite Nat := inferInstance
example : Infinite Int := inferInstance

local instance : Fintype V(graph) := by
  change Fintype ({0, 1} : Set Nat)
  infer_instance

local instance : Fintype E(graph) := by
  change Fintype ({parallelEdge₀, parallelEdge₁, loopEdge} : Set (Edge Nat Int))
  infer_instance

local instance : Nonempty V(graph) :=
  ⟨⟨0, by simp [graph]⟩⟩

-- Global executable enumerations.
#eval graph.vertexFinset.card
#eval 0 ∈ graph.vertexFinset
#eval 1 ∈ graph.vertexFinset
#eval graph.edgeFinset.card

-- Local executable collections at vertex `0`.
#eval (graph.neighborFinset 0).card
#eval 0 ∈ graph.neighborFinset 0
#eval 1 ∈ graph.neighborFinset 0
#eval (graph.incidenceFinset 0).card
#eval (graph.loopFinset 0).card

/-! ## Non-degree queries and quantities -/

/-- Executable adjacency, implemented through the verified finite-neighborhood API. -/
def adjacent (u v : Nat) : Bool :=
  decide (v ∈ graph.neighborFinset u)

/-- Executable `IsLink`, using actual-edge membership rather than arbitrary `Set` membership. -/
def isLink (e : Edge Nat Int) (u v : Nat) : Bool :=
  decide (e ∈ graph.edgeFinset ∧ e.endpoints = s(u, v))

/-- Executable incidence of an actual bundled edge with a vertex. -/
def incident (e : Edge Nat Int) (v : Nat) : Bool :=
  decide (e ∈ graph.edgeFinset ∧ v ∈ e.endpoints)

/-- The number of actual bundled edges with the given unordered endpoint pair. -/
def edgeMultiplicity (u v : Nat) : Nat :=
  (graph.edgeFinset.filter fun e => e.endpoints = s(u, v)).card

/-- The total number of loops, counted once per actual bundled loop. -/
def loopCount : Nat :=
  ∑ v ∈ graph.vertexFinset, (graph.loopFinset v).card

/-- The number of vertices with degree zero. -/
def isolatedVertexCount : Nat :=
  (graph.vertexFinset.filter fun v => graph.degree v = 0).card

/-- An executable finite universal property. -/
def everyVertexHasDegreeAtLeastTwo : Bool :=
  decide ((graph.vertexFinset.filter fun v => graph.degree v < 2).card = 0)

/-- An executable regularity check for this nonempty graph. -/
def isRegular : Bool :=
  decide ((graph.vertexFinset.filter fun v => graph.degree v ≠ graph.degree 0).card = 0)

#eval parallelEdge₀ ∈ graph.edgeFinset
#eval isLink parallelEdge₀ 0 1
#eval incident loopEdge 0
#eval adjacent 0 0
#eval adjacent 0 1
#eval adjacent 1 1
#eval edgeMultiplicity 0 1
#eval edgeMultiplicity 0 0
#eval loopCount
#eval isolatedVertexCount
#eval everyVertexHasDegreeAtLeastTwo
#eval isRegular

-- Local and aggregate degree values.
#eval graph.degree 0
#eval graph.degree 1
#eval graph.maxDegree
#eval graph.minDegree
#eval graph.averageDegree
#eval ∑ v ∈ graph.vertexFinset, graph.degree v

-- These checks make the expected multigraph semantics part of the demo.
example : graph.degree 0 = 4 := by decide
example : graph.degree 1 = 2 := by decide
example : graph.maxDegree = 4 := by decide
example : graph.minDegree = 2 := by decide
example : (∑ v ∈ graph.vertexFinset, graph.degree v) = 6 := by decide

end ComputabilityDemo
