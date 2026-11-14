/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Fable 5.1)
-/
module

public import AlgoLib.Algorithms.Graph.Traversal.BFS

/-!
# `AlgoLib.Algorithms.Graph.Traversal`

Graph traversal algorithms: systematic exploration of the vertices reachable from a
source. This file defines nothing itself: it is an *umbrella* module that re-exports the
development, which is split across `AlgoLib/Algorithms/Graph/Traversal/`:

* `BFS` — breadth-first search on a `SimpleDiGraph`, layer by layer, with the proofs
  that it computes reachability (`SimpleDiGraph.mem_bfsReachableFinset_iff`) and the
  distance (`SimpleDiGraph.bfsDist_eq_dist`), and that its layers are the spheres around
  the source (`SimpleDiGraph.mem_bfsLayer_iff_dist_eq`).

Undirected graphs are traversed through their symmetric orientation
`SimpleGraph.toSimpleDiGraph`; the undirected wrappers `SimpleGraph.reachableFinset` and
`SimpleGraph.computeDist` live in `AlgoLib.Algorithms.Graph.Connectivity.Basic`, together
with the rest of the executable connectivity layer.

Depth-first search is not yet implemented.
-/
