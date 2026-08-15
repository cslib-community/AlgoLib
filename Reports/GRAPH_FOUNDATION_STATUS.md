# GraphLib foundation status

**Updated:** 2026-08-15

**Current phase:** Phase 6 — `COMPLETE`

**Exit condition satisfied:** Yes

## Completed

- Added canonical adjacency-fiber neighborhoods for all four graph types in
  `Graph/Neighborhood.lean`, with membership, containment, outside-vertex emptiness, symmetry or
  reversal, subgraph monotonicity, and transformation formulas.
- Rebuilt `Graph/Finite.lean` around mathematical `Set` finiteness and genuine noncomputable
  `Finset` views. General vertex and actual-edge finiteness remain independent; only simple graph
  types derive finite edges from finite vertices. Added membership, coercion, subset, and `ncard`
  bridges for vertex, edge, neighborhood, incidence, and loop finsets.
- Recreated `Graph/Degree.lean` with finite-local degree. General undirected loops count twice and
  parallel actual edges separately; directed loops count once in each direction. Added cardinal
  characterizations, bounds, subgraph and transformation monotonicity, extrema with comparison and
  attainment, and the two Moore helper lemmas.
- Added `Graph/DegreeSum.lean` with both undirected handshaking identities, directed in/out degree
  sums over actual arcs, equality of directed sums, and rational average-degree formulas.
- Migrated Girth and every MooreBound layer to the canonical neighborhood orientation and
  instance-bearing finite-local degree boundary. Removed local duplicate degree/neighborhood
  definitions, moved the Moore helpers, and applied the locked girth top/non-top theorem names.
- Added `GraphLibTest/Foundation/FiniteDegree.lean`, covering finite vertices with infinite general
  edges, locally finite degree in an infinite graph, neighborhood loop/parallel semantics, two
  parallel edges, two loops contributing degree four, directed loop degrees and sums, simple
  handshake, and compile-time API checks. Updated `GraphLib/All.lean` with the new modules.

## Deviations and deferred items

- No required Phase 6 item was deferred, no earlier-phase repair was needed, and no semantic
  redesign was made.
- Only plan-permitted advanced degree inequalities, parity/density theory, executable refinement
  contracts, and extended-degree/regularity/complement APIs remain deferred.
- Existing unrelated linter warnings and the two pre-existing
  `DataStructures/InverseAckermann/Nivasch.lean` `sorry` declarations remain. Phase 6 added no
  production `sorry`.

## Validation

- Incremental builds of `Neighborhood`, `Finite`, `Degree`, `DegreeSum`, the new foundation test,
  Girth, and every MooreBound leaf succeeded.
- `lake build GraphLib.Graph.Neighborhood GraphLib.Graph.Finite GraphLib.Graph.Degree
  GraphLib.Graph.DegreeSum GraphLibTest.Foundation.FiniteDegree GraphLib.Theory.Girth
  GraphLib.Theory.MooreBound.Counting GraphLib.Theory.MooreBound.Core
  GraphLib.Theory.MooreBound.RootedLayers GraphLib.Theory.MooreBound.HalfLayers
  GraphLib.Theory.MooreBound.Bounds GraphLib.Theory.MooreBound
  GraphLib.Walk.InSimpleGraph GraphLib.Walk.InSimpleDiGraph
  GraphLibTest.Foundation.Walk GraphLib GraphLib.All GraphLibTest.ImportAll`: success (1184 jobs).
- Searches found no Phase 6 production `sorry`, stale girth theorem names, duplicate degree or
  neighborhood definitions, deprecated `compute*Finset`/`finMaxDegree`/`avgDegree` API, or
  wrong-returning `*Finset` declaration. `git diff --check` passes.

## Next action

Begin Phase 7 only: implement connectivity and graph structure at the Phase 7 boundary.
