/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Connectivity

/-!
# Connectivity foundation tests

Compile-time and semantic checks for Phase 7 reachability, components, strong connectivity,
acyclicity, forests, and trees.
-/

namespace GraphLibTest.Foundation.Connectivity

open GraphLib
open scoped GraphLib

variable {α β : Type*}

section TypeChecks

variable
  (Gu : Graph α β) (Gs : SimpleGraph α)
  (Gd : DiGraph α β) (Gsd : SimpleDiGraph α)

#check Gs.Reachable
#check Gsd.Reachable
#check Gu.Reachable
#check Gd.Reachable

#check Gs.Preconnected
#check Gs.Connected
#check Gs.connectedComponentSet
#check Gu.Preconnected
#check Gu.Connected
#check Gu.connectedComponentSet

#check Gsd.StronglyConnected
#check Gsd.IsStronglyConnected
#check Gsd.stronglyConnectedComponentSet
#check Gd.StronglyConnected
#check Gd.IsStronglyConnected
#check Gd.stronglyConnectedComponentSet

#check Gs.IsAcyclic
#check Gsd.IsAcyclic
#check Gu.IsAcyclic
#check Gd.IsAcyclic
#check Gs.IsForest
#check Gs.IsTree
#check Gu.IsForest
#check Gu.IsTree

end TypeChecks

section Reachability

/-- Reachability reflexivity is deliberately restricted to graph vertices. -/
example : ¬ (⊥ : SimpleGraph Nat).Reachable 0 0 := by
  intro h
  simpa using h.left_mem

example {G : SimpleGraph α} {u v : α} (h : G.Adj u v) : G.Reachable u v :=
  h.reachable

example {G : SimpleGraph α} {u v w : α}
    (huv : G.Reachable u v) (hvw : G.Reachable v w) : G.Reachable u w :=
  huv.trans hvw

example {G : SimpleGraph α} {u v : α} (h : G.Reachable u v) : G.Reachable v u :=
  h.symm

example {G : DiGraph α β} {u v : α} (h : G.Reachable u v) :
    G.reverse.Reachable v u :=
  h.reverse

example {G H : SimpleGraph α} {u v : α} (h : G.Reachable u v) (hGH : G ≤ H) :
    H.Reachable u v :=
  h.mono hGH

example {γ : Type*} {G : Graph α β} {u v : α} (h : G.Reachable u v)
    (f : α ≃ γ) : (G.relabelVertices f).Reachable (f u) (f v) :=
  h.relabelVertices f

example {G : Graph α β} {u v : α} (h : G.Reachable u v) :
    u ∈ V(G) ∧ v ∈ V(G) :=
  ⟨h.left_mem, h.right_mem⟩

end Reachability

section Components

/-- The empty graph is preconnected under the vacuous convention. -/
example : (⊥ : SimpleGraph Nat).Preconnected := by simp

/-- Connectedness additionally requires nonemptiness. -/
example : ¬ (⊥ : SimpleGraph Nat).Connected := by simp

example {G : SimpleGraph α} {u v : α} (h : G.Reachable u v) :
    G.connectedComponentSet u = G.connectedComponentSet v :=
  SimpleGraph.connectedComponentSet_eq_of_reachable h

example (G : Graph α β) (u v : α) :
    G.connectedComponentSet u = G.connectedComponentSet v ∨
      Disjoint (G.connectedComponentSet u) (G.connectedComponentSet v) :=
  G.connectedComponentSet_eq_or_disjoint u v

example (G : SimpleDiGraph α) (v : α) :
    G.reverse.stronglyConnectedComponentSet v = G.stronglyConnectedComponentSet v := by
  simp

example (G : DiGraph α β) :
    G.reverse.IsStronglyConnected ↔ G.IsStronglyConnected := by
  simp

example (G : SimpleDiGraph α) (u v : α) :
    G.StronglyConnected u v ↔ G.Reachable u v ∧ G.Reachable v u :=
  G.stronglyConnected_iff u v

end Components

section Cycles

private def loopWalk : Walk Nat Unit :=
  (Walk.singleton 0).cons 0 ()

private def loopCycle : Cycle Nat Unit := ⟨loopWalk, by
  simp [loopWalk, Walk.closed, Walk.dropTail, Walk.edges]⟩

/-- A general loop is a cycle of length one and witnesses cyclicity. -/
example : loopCycle.length = 1 := rfl

example : loopCycle.val.toGraph.HasCycle := by
  exact ⟨loopCycle,
    (Graph.IsWalkIn.iff_toGraph_le loopCycle.val.toGraph loopCycle.val).2 le_rfl⟩

private def parallelTwoWalk : Walk Nat Bool :=
  ((Walk.singleton 0).cons 1 false).cons 0 true

private def parallelTwoCycle : Cycle Nat Bool := ⟨parallelTwoWalk, by
  simp [parallelTwoWalk, Walk.closed, Walk.dropTail, Walk.vertices, Walk.edges]⟩

/-- Two distinct parallel actual edges form a general undirected two-cycle. -/
example : parallelTwoCycle.length = 2 := rfl

example : parallelTwoCycle.val.toGraph.HasCycle := by
  exact ⟨parallelTwoCycle,
    (Graph.IsWalkIn.iff_toGraph_le parallelTwoCycle.val.toGraph parallelTwoCycle.val).2 le_rfl⟩

/-- Undirected simple cycles keep the conventional minimum length three. -/
example (c : SimpleCycle α) : 3 ≤ c.length := c.property.1

/-- Directed simple cycles admit length two but exclude length one. -/
example (c : SimpleDiCycle α) : 2 ≤ c.length := c.two_le_length

example : (⊥ : SimpleGraph Nat).IsAcyclic := by
  exact SimpleGraph.isAcyclic_of_no_edges _ rfl

example : (⊥ : Graph Nat Bool).IsAcyclic := by
  exact Graph.isAcyclic_of_no_edges _ rfl

example {G H : Graph α β} (hHG : H ≤ G) (hG : G.IsAcyclic) : H.IsAcyclic :=
  Graph.isAcyclic_of_subgraph G H hHG hG

example (G : SimpleDiGraph α) : G.reverse.IsAcyclic ↔ G.IsAcyclic := by simp

example (G : DiGraph α β) : G.reverse.IsAcyclic ↔ G.IsAcyclic := by simp

end Cycles

end GraphLibTest.Foundation.Connectivity
