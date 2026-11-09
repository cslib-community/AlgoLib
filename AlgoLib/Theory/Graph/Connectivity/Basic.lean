/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5), Basil Rohner, Sorrachai Yingchareonthawornchai
-/
module

public import AlgoLib.Theory.Graph.Connectivity.Reachable
public import AlgoLib.Theory.Graph.Connectivity.Directed
public import AlgoLib.Theory.Graph.Connectivity.Components
public import AlgoLib.Theory.Graph.Connectivity.Cuts
public import AlgoLib.Theory.Graph.Connectivity.Connectivity

/-!
# `AlgoLib.Theory.Graph.Connectivity`

Connectedness, connected components, cuts, separators, and the connectivity numbers
`κ(G)` and `κ'(G)` for the simple graphs of `AlgoLib.Graph.Basic`.

This file defines nothing itself: it is an *umbrella* module that re-exports the
development, which is split across `AlgoLib/Theory/Connectivity/`:

* `Reachable` — `SimpleGraph.Reachable`, its equivalence properties, the path witness,
  and `IsPreconnected` / `IsConnected`.
* `Directed` — `SimpleDiGraph.Reachable` and the distance `SimpleDiGraph.dist`, the
  undirected distance `SimpleGraph.dist` defined through the symmetric orientation
  `SimpleGraph.toSimpleDiGraph`, and the transfer lemmas between the two.
* `Components` — `componentOf`, `components`, `numComponents`, and the facts that make
  "more than one component" usable.
* `Cuts` — the edge boundary `∂(G, S)`, vertex and edge cuts, cut vertices and cut
  edges, and separators between vertices and between sets of vertices.
* `Connectivity` — `κ(G)` and `κ'(G)`, with the `girth`-style infimum API.

The *executable* layer — the reachability closure `reachableFinset` and distance
`computeDist` by breadth-first search, the connected components as a `Finset`, the four
connectivity numbers as executable definitions, and the `Decidable` instances for
reachability, connectedness, cuts and separating sets — lives in
`AlgoLib.Algorithms.Graph.Connectivity.Basic`. It depends on the search algorithm of
`AlgoLib.Algorithms.Graph.Traversal.BFS`, which is why it is not part of this theory
umbrella: `AlgoLib.Theory` never imports `AlgoLib.Algorithms`.

Downstream files should import this umbrella; the split is internal. The submodules form
the acyclic spine `Reachable ← Components ← Cuts ← Connectivity`, on top of the deletion
operations in `AlgoLib.Graph.Delete` and the walk development in
`AlgoLib.Theory.Structures.InSimpleGraph`; `Directed` sits beside `Reachable`.

## Main definitions

Definitions based on lecture note "Graph Theory ETH 2026" by Benny Sudakov

* `SimpleGraph.Reachable G u v` — some simple walk realized in `G` runs from `u` to `v`.
* `SimpleGraph.IsPreconnected G`, `SimpleGraph.IsConnected G` — Definition 1.35.
* `SimpleGraph.componentOf G v`, `SimpleGraph.components G`,
  `SimpleGraph.IsConnectedComponent G C`, `SimpleGraph.numComponents G`.
* `SimpleGraph.edgeBoundary G S`, written `∂(G, S)`.
* `SimpleGraph.IsVertexCut G S` — Definition 3.1.(i); `SimpleGraph.IsCutVertex G v` —
  Definition 3.1.(ii); `SimpleGraph.IsEdgeCut G F`; `SimpleGraph.IsCutEdge G e` —
  Definition 2.5.
* `SimpleGraph.IsVertexSeparator`, `SimpleGraph.IsEdgeSeparator` — separators between
  two vertices; `SimpleGraph.IsSTVertexCut`, `SimpleGraph.IsSTEdgeCut` — between two
  sets of vertices.
* `SimpleGraph.vertexConnectivity G`, `SimpleGraph.edgeConnectivity G`, written `κ(G)`
  and `κ'(G)`.
* `SimpleDiGraph.Reachable G u v`, `SimpleDiGraph.dist G u v`, `SimpleGraph.dist G u v` —
  directed reachability and the distance, the undirected one through
  `SimpleGraph.toSimpleDiGraph`.
* The computable counterparts `SimpleGraph.reachableFinset G u` (of `componentOf`),
  `SimpleGraph.computeDist G u v` (of `dist`) and `SimpleGraph.computeVertexConnectivity G`
  (of `κ(G)`) are in `AlgoLib.Algorithms.Graph.Connectivity.Basic`.

## Notation

All notation is `scoped` to `AlgoLib`, so `open scoped AlgoLib` brings it into scope
alongside `V(G)` and `E(G)`.

* `∂(G, S)` — the edge boundary of `S` in `G`.
* `κ(G)` — the vertex connectivity of `G`.
* `κ'(G)` — the edge connectivity of `G`.

## Design choices

Each submodule documents its own choices; the three that shape the whole development are:

* **Reachability is stated with walks, not paths**, so that reflexivity, symmetry and
  transitivity fall straight out of `IsSimplePathIn.singleton`, `IsSimpleWalkIn.reverse`
  and `IsSimpleWalkIn.glue`. The path version is a theorem
  (`Reachable.exists_isSimplePathIn`), which keeps `[DecidableEq α]` out of the `Prop`.
* **Components are `Set α`, not a quotient.** `vertexSet` is a subset of `α` rather than
  a type, so a `Quot`-based component type would push subtype coercions through the whole
  set-based library.
* **Cardinalities use `Set.encard`, never `Set.ncard`.** `ncard` returns the junk value
  `0` on infinite sets, which silently falsifies statements such as "a disconnected graph
  has more than one component" on infinite graphs.

## Strong connectivity

There is deliberately no `stronglyConnectedComponent` here. In an undirected graph
`Reachable` is symmetric (`SimpleGraph.Reachable.symm`), so strong components coincide
with connected components and a separate API would be pure duplication. Strong
connectivity is a genuinely directed notion; its home is `SimpleDiGraph`, where
`SimpleDiGraph.IsSimpleWalkIn` and its closure lemmas are already available in
`AlgoLib.Theory.Structures.InSimpleDiGraph`.
-/
