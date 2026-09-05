/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Specification
import AlgoLib.Theory.Graph.Connectivity.Basic

/-!
# Agreement with the repository's walk-based connectivity definitions

The general-graph specification specializes exactly to the existing
`SimpleGraph.Reachable` and `SimpleGraph.IsConnected`, rather than introducing
a second, incompatible notion of connectivity.
-/
namespace AlgoLib.Experimental.RAM.BFS

@[simp] theorem link_toGraph (G : SimpleGraph Nat) (u v : Nat) :
    Link G.toGraph u v ↔ G.Adj u v := by
  simp [Link, SimpleGraph.toGraph, SimpleGraph.Adj]

theorem reachable_toGraph (G : SimpleGraph Nat) (u v : Nat) :
    Reachable G.toGraph u v ↔ G.Reachable u v := by
  constructor
  · intro h
    induction h with
    | refl h => exact .refl G h
    | step _ he ih => exact ih.trans ((link_toGraph G _ _).mp he).reachable
  · rintro ⟨w, hw, rfl, rfl⟩
    suffices ∀ {p : VertexSeq Nat}, G.IsVertexSeqIn p → Reachable G.toGraph p.head p.tail from
      this hw
    intro p hp
    induction hp with
    | singleton x hx => exact .refl hx
    | cons p x hp hadj ih =>
      exact .step ih ((link_toGraph G _ _).mpr hadj)

@[simp] theorem connected_toGraph (G : SimpleGraph Nat) : Connected G.toGraph ↔ G.IsConnected := by
  simp only [Connected, SimpleGraph.IsConnected, SimpleGraph.IsPreconnected, reachable_toGraph]
  rfl

end AlgoLib.Experimental.RAM.BFS
