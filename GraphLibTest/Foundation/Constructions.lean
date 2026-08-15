/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Constructions

/-!
# Foundation tests: graph constructions

Compile-time and semantic fixtures for the selected Phase 9 constructor library.
-/

namespace GraphLibTest.Foundation.Constructions

open GraphLib
open scoped GraphLib

def reusedTagEdge₁ : Edge Nat Bool := ⟨true, s(0, 1)⟩
def reusedTagEdge₂ : Edge Nat Bool := ⟨true, s(2, 3)⟩

def generatedGraph : Graph Nat Bool :=
  Graph.ofEdgeSet {reusedTagEdge₁, reusedTagEdge₂}

example : reusedTagEdge₁ ∈ E(generatedGraph) := by simp [generatedGraph]
example : reusedTagEdge₂ ∈ E(generatedGraph) := by simp [generatedGraph]
example : reusedTagEdge₁ ≠ reusedTagEdge₂ := by decide
example : 0 ∈ V(generatedGraph) := by simp [generatedGraph, reusedTagEdge₁]
example : 3 ∈ V(generatedGraph) := by simp [generatedGraph, reusedTagEdge₂]
example : generatedGraph.Adj 0 1 := by simp [generatedGraph, reusedTagEdge₁]
example : generatedGraph.Adj 2 3 := by simp [generatedGraph, reusedTagEdge₂]

example : Finite V(Graph.ofEdge reusedTagEdge₁) := inferInstance
example : Finite E(Graph.ofEdge reusedTagEdge₁) := inferInstance
example : Finite V(Graph.ofEdgeSet {reusedTagEdge₁, reusedTagEdge₂}) := inferInstance
example : Finite E(Graph.ofEdgeSet {reusedTagEdge₁, reusedTagEdge₂}) := inferInstance

def testArc : Arc Nat Bool := ⟨false, (4, 5)⟩

example : V(DiGraph.ofArc testArc) = ({4, 5} : Set Nat) := by
  ext v
  simp [testArc, eq_comm]

example : E(DiGraph.ofArc testArc) = {testArc} := by
  ext a
  simp

example : (DiGraph.ofArc testArc).Adj 4 5 := by simp [testArc]
example : ¬(DiGraph.ofArc testArc).Adj 5 4 := by simp [testArc]
example : Finite V(DiGraph.ofArc testArc) := inferInstance
example : Finite E(DiGraph.ofArc testArc) := inferInstance

example : (SimpleGraph.singleEdge 0 1 (by decide)).Adj 0 1 := by simp
example : (SimpleGraph.singleEdge 0 1 (by decide)).Adj 1 0 := by simp [Sym2.eq_swap]
example : ¬(SimpleGraph.singleEdge 0 1 (by decide)).Adj 0 2 := by simp

example : (SimpleDiGraph.singleArc 0 1 (by decide)).Adj 0 1 := by simp
example : ¬(SimpleDiGraph.singleArc 0 1 (by decide)).Adj 1 0 := by simp

example : (SimpleGraph.complete ({0, 1, 2} : Set Nat)).Adj 0 2 := by simp
example : ¬(SimpleGraph.complete ({0, 1, 2} : Set Nat)).Adj 1 1 := by simp
example : (SimpleDiGraph.complete ({0, 1, 2} : Set Nat)).Adj 2 0 := by simp
example : ¬(SimpleDiGraph.complete ({0, 1, 2} : Set Nat)).Adj 2 2 := by simp

example : Finite V(SimpleGraph.complete ({0, 1, 2} : Set Nat)) := inferInstance
example : Finite E(SimpleGraph.complete ({0, 1, 2} : Set Nat)) := inferInstance
example : Finite V(SimpleDiGraph.complete ({0, 1, 2} : Set Nat)) := inferInstance
example : Finite E(SimpleDiGraph.complete ({0, 1, 2} : Set Nat)) := inferInstance

example : (Graph.empty : Graph Nat Bool) = Graph.edgeless ∅ := by simp
example : (SimpleGraph.empty : SimpleGraph Nat) = SimpleGraph.edgeless ∅ := by simp
example : (DiGraph.empty : DiGraph Nat Bool) = DiGraph.edgeless ∅ := by simp
example : (SimpleDiGraph.empty : SimpleDiGraph Nat) = SimpleDiGraph.edgeless ∅ := by simp

example : Finite V((Graph.edgeless {0, 1} : Graph Nat Bool)) := inferInstance
example : Finite E((Graph.edgeless Set.univ : Graph Nat Bool)) := inferInstance
example : Finite V((SimpleGraph.empty : SimpleGraph Nat)) := inferInstance
example : Finite E((SimpleDiGraph.empty : SimpleDiGraph Nat)) := inferInstance

end GraphLibTest.Foundation.Constructions
