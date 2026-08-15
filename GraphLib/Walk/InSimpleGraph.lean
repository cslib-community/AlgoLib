/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Walk.InSimpleGraph.VertexSeq
import GraphLib.Walk.InSimpleGraph.Walk
import GraphLib.Walk.InSimpleGraph.Path
import GraphLib.Walk.InSimpleGraph.Cycle

/-!
# Vertex sequences, walks, paths and cycles realized in a simple graph

A `VertexSeq α` is a purely combinatorial object: it knows nothing about any
graph. This development connects vertex sequences to a `SimpleGraph` through the
predicate `SimpleGraph.IsVertexSeqIn`, which says that the sequence is *realized*
in `G`: its first vertex is a vertex of `G` and every consecutive pair is an edge
of `G` (phrased through `SimpleGraph.Adj`).

This file defines nothing itself: it is an *umbrella* module that merely
re-exports (imports) the `InSimpleGraph` development, which is split across
`GraphLib/Walk/InSimpleGraph/`:

* `VertexSeq` — `IsVertexSeqIn`, its constructor characterizations, vertex and
  edge membership, closure under the `VertexSeq` operations, and the edge-set
  characterization.
* `Walk` — `IsSimpleWalkIn`, the bridge to `IsVertexSeqIn`, the generated-subgraph
  characterization, and closure under the walk operations (`append`, `glue`, …).
* `Path` — `IsSimplePathIn`, extension by a fresh adjacent vertex, and the
  vertex-count bound.
* `Cycle` — `IsSimpleCycleIn`, `HasSimpleCycle`, `IsAcyclic`, and the
  path-to-cycle construction lemmas.

Downstream files should keep importing this umbrella; the split is internal. The
submodules form the acyclic spine `VertexSeq ← Walk ← Path ← Cycle`.

## Main definitions

* `SimpleGraph.IsVertexSeqIn G w` — `w` is realized in `G`.
* `SimpleGraph.IsSimpleWalkIn G w` — a `SimpleWalk` is realized in `G` through its
  underlying vertex sequence.
* `SimpleGraph.IsSimplePathIn G p` — a `SimplePath` is realized in `G`.
* `SimpleGraph.IsSimpleCycleIn G c` — a `SimpleCycle` is realized in `G`.
* `SimpleGraph.HasSimpleCycle G` — `G` contains a simple cycle.
* `SimpleGraph.IsAcyclic G` — `G` contains no simple cycle.

## Design choices

* **Adjacency, not edge sets.** The `cons` step is stated with `G.Adj w.tail u`
  rather than `s(w.tail, u) ∈ E(G)`. The two are definitionally equal, but `Adj`
  is the intended primitive and carries the reusable `symm`/`ne`/`left_mem`/
  `right_mem` API.
-/
