# GraphLib foundation status

**Updated:** 2026-08-15

**Current phase:** Phase 5 — `COMPLETE`

**Exit condition satisfied:** Yes

## Completed

- Finalized graph-independent general `Walk` data in `GraphLib/Walk/Walk.lean`, including raw
  tags, reconstructed actual `Edge`/`Arc` lists, append/glue, reversal, subsequences, erasure,
  maps/folds, `GetElem`, vertex-sequence commutation, and generated general graphs/digraphs.
- Added the direction-correct general hierarchy: `Trail`/`DiTrail`, `Path`,
  `Circuit`/`DiCircuit`, and `Cycle`/`DiCycle`. Safe coercions retain semantics; in particular,
  cycles coerce through circuits and never to paths. Added `Walk.toPath` through cycle erasure.
- Added general undirected and directed realization layers with constructor and actual-step list
  views, operation/reversal closure, generated-graph `≤` equivalences, graph transformation and
  relabel transport, thin carrier predicates, and ambient vertex/edge-set congruence.
- Split `InSimpleDiGraph` into independently compiling `VertexSeq`, `Walk`, `Path`, and `Cycle`
  leaves with a declaration-free umbrella. Added directed simple cycles and completed
  induce/restrict/delete/relabel realization transport for both simple realization families.
- Replaced the legacy raw-walk, trail, path, cycle, realization, Eulerian, and Hamiltonian drafts
  with temporary declaration-free forwarders to the final modules. The final coverage API now
  includes realization and direction-correct full edge/arc or vertex coverage for all four graph
  kinds, with projections and ambient extensionality lemmas.
- Extended `GraphLibTest/Foundation/Walk.lean` with tag reuse/full-bundle coverage, undirected
  versus directed trail behavior, loop and parallel-edge cycles, the simple undirected/directed
  length conventions, generated-graph realization, directed reversal, and rejection of coverage
  data that is not realized.

## Deviations and deferred items

- No required Phase 5 item was deferred and no semantic redesign was made.
- `HasSimpleCycle`/`IsAcyclic` remain in their current realization layer as previously scheduled
  for Phase 7. The temporary legacy forwarding modules remain scheduled for Phase 9 removal;
  the final `GraphLib/Walk.lean` umbrella is likewise left to Phase 9.
- Existing unrelated warnings remain in `Graph/Finite.lean`, and the two pre-existing
  `InverseAckermann/Nivasch.lean` `sorry` declarations remain. Phase 5 added no production
  `sorry`.

## Validation

- Independently built every new general carrier/realization/coverage module and all four split
  `InSimpleDiGraph` leaves: success.
- `lake build GraphLib GraphLib.All GraphLibTest.ImportAll
  GraphLibTest.Foundation.Basic GraphLibTest.Foundation.Transformations
  GraphLibTest.Foundation.Walk GraphLib.Walk.Walk GraphLib.Walk.Trail
  GraphLib.Walk.Path GraphLib.Walk.Circuit GraphLib.Walk.Cycle
  GraphLib.Walk.SimpleDiCycle GraphLib.Walk.InGraph GraphLib.Walk.InDiGraph
  GraphLib.Walk.InSimpleGraph GraphLib.Walk.InSimpleDiGraph.VertexSeq
  GraphLib.Walk.InSimpleDiGraph.Walk GraphLib.Walk.InSimpleDiGraph.Path
  GraphLib.Walk.InSimpleDiGraph.Cycle GraphLib.Walk.InSimpleDiGraph
  GraphLib.Walk.Coverage GraphLib.Theory.Girth GraphLib.Theory.MooreBound
  GraphLib.Theory.MooreBound.Bounds`: success (1182 jobs).
- Searches found no production `sorry` in Phase 5 files, stale identity-sensitive raw-tag API,
  accidental contraction API, or unsafe cycle-to-path coercion. `git diff --check` passes.

## Next action

Begin Phase 6 only: complete neighborhood, mathematical finiteness, degree, and counting, then
stop at the Phase 6 exit condition.
