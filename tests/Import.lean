/-
Copyright (c) 2026 AlgoLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import AlgoLib

/-! Check that a module-system consumer can use the public graph and tree APIs. -/

example : Type := AlgoLib.Graph Nat Unit

example : Type := AlgoLib.SimpleGraph Nat

example (G : AlgoLib.SimpleDiGraph Nat) [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (s : Nat) : Finset Nat :=
  G.bfsReachableFinset s

example (t : BinaryTree Nat) (q : Nat) : (SplayTree.splay t q).num_nodes = t.num_nodes :=
  SplayTree.num_nodes_splay t q
