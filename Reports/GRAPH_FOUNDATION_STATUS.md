# GraphLib foundation status

**Updated:** 2026-08-15

**Current phase:** Phase 3 — `COMPLETE`

**Exit condition satisfied:** Yes

## Completed

- Added `Graph/Delete.lean` with same-ambient edge and vertex deletion on all four graph
  families, including singleton and endpoint-wide operations. The routine API covers V/E and
  membership formulas, link/arc/incidence/adjacency characterizations, subgraph and no-op facts,
  repeated/commuting/idempotent deletion, source/deleted-set monotonicity, and edge/vertex
  deletion commutation. Endpoint-wide laws quantify over actual bundled values, so they remove
  every matching parallel edge or arc.
- Added `Graph/Map.lean` with provenance-bearing arbitrary vertex maps for general graphs. The
  complete source `Edge`/`Arc` is the target tag, making the actual-value map injective even for
  constant vertex functions. Added the documented lossy simple maps, equivalence-based vertex
  and tag relabeling, relation/order/identity/composition/inverse laws, and commutation with
  induce/restrict/delete.
- Added explicit `underlyingSimple` and `forgetDirection` conversions. Their V/E and adjacency
  formulas expose loop/parallel loss, while general direction-forgetting retains the full source
  arc as provenance.
- Added `Graph/Reverse.lean` with arc and directed-graph reversal, computations, involution and
  equivalence laws, relation transport, reflection/preservation of `≤`, `≤s`, and `≤i`, and
  commutation with induce, restriction, every deletion, relabeling, and provenance mapping.
- Added the three transformation leaves to `GraphLib/All.lean` and extended
  `GraphLibTest/Foundation/Transformations.lean` with all required Phase 3 type checks and
  semantic fixtures: parallel delete-one/delete-between, constant-map provenance, simple loop
  dropping, relabel identity/composition/inverse, reverse endpoint/involution behavior, parallel
  collapse in `underlyingSimple`, and antiparallel merge in simple `forgetDirection`.

## Deviations and deferred items

- No Phase 3 deviation and no required Phase 3 item was deferred.
- As authorized by the plan, general graph-level arbitrary `mapTags`, repeated-provenance
  flattening, and a `Hom`/`Embedding`/`Iso` hierarchy remain deferred.
- Connectivity consequences, residual construction, and SCC/reachability reversal theorems
  remain in their later phases.
- Existing unrelated warnings remain in `Graph/Finite.lean` and the pre-Phase-3 walk modules;
  the two existing `InverseAckermann/Nivasch.lean` `sorry` declarations also remain. Phase 3
  added no production `sorry`.

## Validation

- Independent builds of `GraphLib.Graph.Delete`, `GraphLib.Graph.Map`, and
  `GraphLib.Graph.Reverse`, plus the focused transformation tests: success.
- `lake build GraphLib GraphLib.All GraphLibTest.ImportAll GraphLibTest.Foundation.Basic
  GraphLibTest.Foundation.Transformations GraphLib.Theory.Structures.VertexSeq
  GraphLib.Theory.Structures.SimpleWalk GraphLib.Theory.Structures.SimplePath
  GraphLib.Theory.Structures.SimpleCycle GraphLib.Theory.Structures.InSimpleGraph
  GraphLib.Theory.Structures.InSimpleDiGraph
  GraphLib.Theory.Structures.SimpleGraph_only.Girth
  GraphLib.Theory.Structures.SimpleGraph_only.MooreBound`: success (1168 jobs).
- Final read-only review found no false statements, identity/provenance violations, namespace
  collisions, or accidental later-phase APIs; its routine-API completeness findings were fixed.
- Guards found no `sorry`, forbidden foundation names, contraction API, or misleading general
  `mapVertices_id` in the Phase 3 files. Trailing-whitespace and `git diff --check` checks passed.

## Next action

Begin Phase 4 only: mechanically relocate the validated simple spine to its final module paths,
preserving the Girth/Moore regression chain, then stop at the Phase 4 exit condition.
