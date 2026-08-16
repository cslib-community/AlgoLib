/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Theory.Matching.Basic
import GraphLib.Weight.Network
import GraphLib.Weight.Walk
import GraphLibTest.Foundation.Basic

/-!
# Attached-data and network foundation tests

Compile-time and semantic fixtures for actual-carrier weights, traversal sums, finite flow
incidence, cuts, and finite matching cardinality.
-/

namespace GraphLibTest.Foundation.WeightNetwork

open GraphLib
open scoped GraphLib
open GraphLibTest.Foundation.Basic

variable {α β γ R W : Type*}

section TypeChecks

variable
  (Gu : Graph α β) (Gs : SimpleGraph α)
  (Gd : DiGraph α β) (Gsd : SimpleDiGraph α)
  (N : Gd.Network R)

example : Gu.VertexWeight W = (α → W) := rfl
example : Gu.EdgeWeight W = (Edge α β → W) := rfl
example : Gu.Cost W = (Edge α β → W) := rfl
example : Gs.EdgeWeight W = (Sym2 α → W) := rfl

example : Gd.VertexWeight W = (α → W) := rfl
example : Gd.EdgeWeight W = (Arc α β → W) := rfl
example : Gd.Cost W = (Arc α β → W) := rfl
example : Gd.Capacity R = (Arc α β → R) := rfl
example : Gsd.Capacity R = ((α × α) → R) := rfl
example : DiGraph.Flow N = (Arc α β → R) := rfl

#check Graph.walkWeight
#check Graph.pathWeight
#check Graph.pathWeight_congr
#check Graph.pathWeight_glue
#check Graph.pathWeight_relabelVertices
#check DiGraph.pathWeight_glue
#check DiGraph.pathWeight_relabelTags
#check SimpleGraph.walkWeight
#check SimpleGraph.pathWeight_glue
#check SimpleGraph.pathWeight_relabelVertices
#check SimpleDiGraph.pathWeight
#check SimpleDiGraph.pathWeight_glue
#check SimpleDiGraph.pathWeight_relabelVertices
#check DiGraph.EdgeWeight.transportReverse_congr
#check DiGraph.Flow.outflow
#check DiGraph.Flow.inflow
#check DiGraph.Flow.flowValue
#check DiGraph.Flow.flowValue_congr
#check DiGraph.Flow.IsFeasible
#check DiGraph.Flow.outflow_transportRelabelVertices
#check DiGraph.Flow.inflow_transportRelabelTags
#check DiGraph.Flow.outflow_transportReverse
#check DiGraph.Flow.flowValue_transportRelabelVertices
#check DiGraph.Flow.isFeasible_transportRelabelVertices
#check DiGraph.Flow.isFeasible_transportRelabelTags
#check DiGraph.Flow.isFeasible_transportReverse
#check DiGraph.cutArcSet
#check DiGraph.Network.cutCapacity

/-- Finite vertices alone are insufficient for flow incidence sums on a general digraph. -/
example (G : DiGraph α β) [Finite V(G)] : True := by
  fail_if_success
    have _h : Finite E(G) := inferInstance
  trivial

end TypeChecks

section ActualCarrierData

/-- Two same-tag edges at different endpoints receive independent values. -/
def reusedEdgeWeight : tagReuseGraph.EdgeWeight Nat := fun e =>
  if e = reusedTagEdgeOne then 3 else if e = reusedTagEdgeTwo then 7 else 0

example : reusedEdgeWeight reusedTagEdgeOne = 3 := by simp [reusedEdgeWeight]
example : reusedEdgeWeight reusedTagEdgeTwo = 7 := by
  simp [reusedEdgeWeight, reusedTagEdgeOne, reusedTagEdgeTwo]

/-- Provenance transport recovers the complete source edge, not merely its reused tag. -/
example :
    Graph.EdgeWeight.transportMapVertices tagReuseGraph (fun _ => ()) reusedEdgeWeight
      (Edge.mapVertices (fun _ => ()) reusedTagEdgeTwo) = 7 := by
  simp [reusedEdgeWeight, reusedTagEdgeOne, reusedTagEdgeTwo]

example (G : Graph α β) (f : α ≃ γ) (weight : G.EdgeWeight W) (e : Edge α β) :
    Graph.EdgeWeight.transportRelabelVertices G f weight (Edge.relabelVertices f e) = weight e :=
  by simp

def reverseArc : Arc Nat Unit := ⟨(), (0, 1)⟩

def reverseArcWeight : (⊤ : DiGraph Nat Unit).EdgeWeight Nat := fun a =>
  if a = reverseArc then 11 else 0

example :
    DiGraph.EdgeWeight.transportReverse (⊤ : DiGraph Nat Unit) reverseArcWeight
      reverseArc.reverse = 11 := by
  simp [reverseArcWeight]

end ActualCarrierData

section TraversalWeights

def firstStep : Edge Nat Unit := ⟨(), s(0, 1)⟩
def secondStep : Edge Nat Unit := ⟨(), s(1, 2)⟩
def thirdStep : Edge Nat Unit := ⟨(), s(2, 3)⟩

def stepWeight : (⊤ : Graph Nat Unit).EdgeWeight Nat := fun e =>
  if e = firstStep then 2 else if e = secondStep then 5 else if e = thirdStep then 7 else 0

def reusedTagWalk : Walk Nat Unit := ((Walk.singleton 0).cons 1 ()).cons 2 ()

example : (⊤ : Graph Nat Unit).walkWeight stepWeight reusedTagWalk = 7 := by
  decide

example : (⊤ : Graph Nat Unit).walkWeight stepWeight reusedTagWalk.reverse = 7 := by
  rw [Graph.walkWeight_reverse]
  decide

def leftWalk : Walk Nat Unit := (Walk.singleton 0).cons 1 ()
def rightWalk : Walk Nat Unit := (Walk.singleton 2).cons 3 ()

example : (⊤ : Graph Nat Unit).walkWeight stepWeight (leftWalk.append rightWalk ()) = 14 := by
  decide

end TraversalWeights

section Networks

def loopArc : Arc Bool Bool := ⟨false, (false, false)⟩
def parallelArcOne : Arc Bool Bool := ⟨false, (false, true)⟩
def parallelArcTwo : Arc Bool Bool := ⟨true, (false, true)⟩
def antiparallelArc : Arc Bool Bool := ⟨false, (true, false)⟩

/-- A finite directed graph with a loop, parallel arcs, and an antiparallel arc. -/
def flowGraph : DiGraph Bool Bool where
  vertexSet := Set.univ
  edgeSet := {loopArc, parallelArcOne, parallelArcTwo, antiparallelArc}
  source_mem := by simp
  target_mem := by simp

local instance : Finite E(flowGraph) := by
  apply Set.Finite.to_subtype
  change ({loopArc, parallelArcOne, parallelArcTwo, antiparallelArc} :
    Set (Arc Bool Bool)).Finite
  exact ((Set.finite_singleton antiparallelArc).insert parallelArcTwo).insert parallelArcOne
    |>.insert loopArc

def capacity : flowGraph.Capacity Nat := fun a =>
  if a = loopArc then 5 else if a = parallelArcOne then 2 else
    if a = parallelArcTwo then 3 else if a = antiparallelArc then 7 else 0

def network : flowGraph.Network Nat where
  source := false
  sink := true
  source_mem := by simp [flowGraph]
  sink_mem := by simp [flowGraph]
  source_ne_sink := by decide
  capacity := capacity

def flow : DiGraph.Flow network := capacity

example : capacity loopArc = 5 := by simp [capacity]
example : capacity parallelArcOne = 2 := by decide
example : capacity parallelArcTwo = 3 := by decide
example : capacity antiparallelArc = 7 := by decide

/-- The loop occurs once in outflow, and the two parallel arcs contribute separately. -/
example : DiGraph.Flow.outflow network flow false = 10 := by
  classical
  change (flowGraph.outIncidenceFinset false).sum flow = 10
  have hout : flowGraph.outIncidenceFinset false = {loopArc, parallelArcOne, parallelArcTwo} := by
    ext a
    rcases a with ⟨tag, u, v⟩
    cases tag <;> cases u <;> cases v <;>
      simp [flowGraph, loopArc, parallelArcOne, parallelArcTwo, antiparallelArc]
  rw [hout]
  simp [flow, capacity, loopArc, parallelArcOne, parallelArcTwo, antiparallelArc]

/-- The same loop occurs once in inflow, together with the antiparallel arc. -/
example : DiGraph.Flow.inflow network flow false = 12 := by
  classical
  change (flowGraph.inIncidenceFinset false).sum flow = 12
  have hin : flowGraph.inIncidenceFinset false = {loopArc, antiparallelArc} := by
    ext a
    rcases a with ⟨tag, u, v⟩
    cases tag <;> cases u <;> cases v <;>
      simp [flowGraph, loopArc, parallelArcOne, parallelArcTwo, antiparallelArc]
  rw [hin]
  simp [flow, capacity, loopArc, parallelArcOne, parallelArcTwo, antiparallelArc]

example : network.IsCut {false} := by
  simp [DiGraph.Network.IsCut, network, flowGraph]

example : parallelArcOne ∈ flowGraph.cutArcSet {false} := by
  simp [flowGraph, parallelArcOne]

example : loopArc ∉ flowGraph.cutArcSet {false} := by
  simp [flowGraph, loopArc]

example : network.cutCapacity {false} = 5 := by
  classical
  rw [DiGraph.Network.cutCapacity_eq_sum_cutArcFinset]
  have hcut : flowGraph.cutArcFinset {false} = {parallelArcOne, parallelArcTwo} := by
    ext a
    rcases a with ⟨tag, u, v⟩
    cases tag <;> cases u <;> cases v <;>
      simp [flowGraph, loopArc, parallelArcOne, parallelArcTwo, antiparallelArc]
  rw [hcut]
  simp [network, capacity, loopArc, parallelArcOne, parallelArcTwo, antiparallelArc]

example : DiGraph.Flow.IsFeasible network (0 : DiGraph.Flow network) := by
  apply DiGraph.Flow.zero_isFeasible
  intro a ha
  simp [network, capacity]

example :
    (DiGraph.Flow.transportReverse network flow) loopArc.reverse = flow loopArc := by simp

example :
    DiGraph.Flow.outflow network.reverse (DiGraph.Flow.transportReverse network flow) false =
      DiGraph.Flow.inflow network flow false := by simp

example :
    DiGraph.Flow.inflow network.reverse (DiGraph.Flow.transportReverse network flow) true =
      DiGraph.Flow.outflow network flow true := by simp

example : DiGraph.Flow.IsFeasible network.reverse
    (DiGraph.Flow.transportReverse network (0 : DiGraph.Flow network)) := by
  apply (DiGraph.Flow.isFeasible_transportReverse network _).2
  apply DiGraph.Flow.zero_isFeasible
  intro a ha
  simp [network, capacity]

end Networks

section Matching

local instance : Finite E(tagReuseGraph) := by
  apply Set.Finite.to_subtype
  change ({reusedTagEdgeOne, reusedTagEdgeTwo} : Set (Edge Nat Unit)).Finite
  exact (Set.finite_singleton reusedTagEdgeTwo).insert reusedTagEdgeOne

/-- A matching may contain two distinct edges that reuse one tag at disjoint endpoints. -/
def reusedTagMatching : Matching tagReuseGraph where
  edgeSet := {reusedTagEdgeOne, reusedTagEdgeTwo}
  edgeSet_subset := fun _ he => he
  disjoint := by
    intro e he f hf hne v hve
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact False.elim (hne rfl)
    · simp [reusedTagEdgeOne, reusedTagEdgeTwo] at hve ⊢
      omega
    · simp [reusedTagEdgeOne, reusedTagEdgeTwo] at hve ⊢
      omega
    · exact False.elim (hne rfl)

example : reusedTagMatching.edgeSet = {reusedTagEdgeOne, reusedTagEdgeTwo} := rfl

example : reusedTagMatching.size = 2 := by
  rw [Matching.size_eq_ncard]
  change ({reusedTagEdgeOne, reusedTagEdgeTwo} : Set (Edge Nat Unit)).ncard = 2
  rw [Set.ncard_pair (by decide)]

end Matching

end GraphLibTest.Foundation.WeightNetwork
