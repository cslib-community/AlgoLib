/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Theory.MooreBound.Counting
import GraphLib.Theory.MooreBound.Core
import GraphLib.Theory.MooreBound.RootedLayers
import GraphLib.Theory.MooreBound.HalfLayers
import GraphLib.Theory.MooreBound.Bounds

/-!
# Moore bounds for simple graphs

This module states the odd-girth and even-girth Moore bounds for finite simple
graphs. The proofs count the vertices in the breadth-first layers around a root
vertex, respectively around a central edge.

This file defines nothing itself: it is an *umbrella* module that merely
re-exports (imports) the Moore development, which is split across
`GraphLib/Theory/MooreBound/`:

* `Counting` — the two purely set-theoretic counting lemmas (`GraphLib.Set`).
* `Core` — fresh neighbours of a path\'s tail, the short cycle a chord would
  create, and the two lemmas that both layer families consume.
* `RootedLayers` — `IsRootedPath` / `rootLayer`: the layers around a root vertex.
* `HalfLayers` — `IsAvoidingRootedPath` / `halfLayer`: the layers around one end
  of a central edge.
* `Bounds` — the two theorems.

The submodules form the acyclic spine
`Counting ← Core ← RootedLayers ← HalfLayers ← Bounds`.

## Main results

* `SimpleGraph.mooreBound_odd` — if `girth G ≥ 2 * r + 1` and every vertex has
  degree at least `δ`, then
  `1 + δ * ∑ i ∈ range r, (δ - 1)^i ≤ |V(G)|`.
* `SimpleGraph.mooreBound_even` — if `girth G ≥ 2 * r` and every vertex has
  degree at least `δ`, then
  `2 * ∑ i ∈ range r, (δ - 1)^i ≤ |V(G)|`.

Everything else is implementation detail and lives in the `SimpleGraph.MooreBound`
namespace: the layer families, the paths that witness them, and the counting
lemmas that make them grow. Only the two theorems above are public API.

## Implementation notes

Both statements include a nonempty vertex-set hypothesis. Without it, the lower
degree hypothesis is vacuous on the empty graph, while the odd bound with
`r = 0` asserts `1 ≤ |V(G)|`.

The odd bound does not require `2 ≤ δ`: its rooted construction starts from the
given nonempty vertex set. The even bound retains this hypothesis because it is
needed to obtain the central edge from which the two half-trees grow.

The finite-local `SimpleGraph.neighborSet` / `SimpleGraph.degree` API is provided
by `GraphLib.Graph.Degree`. The Moore statements carry `[Finite V(G)]`, which
supplies the local neighborhood finiteness needed to elaborate every degree.
-/
