# GraphLib foundation status

**Updated:** 2026-08-15

**Current phase:** Phase 4 — `COMPLETE`

**Exit condition satisfied:** Yes

## Completed

- Relocated the validated graph-independent spine to `GraphLib/Walk`: the eight
  `VertexSeq` leaves and umbrella, `SimpleWalk`, `SimplePath`, and `SimpleCycle`. Their
  declarations now live under `GraphLib`, with the existing representations, theorem bodies,
  constructor orientation, and definitional equalities preserved.
- Moved the common-prefix helper to `GraphLib/Util/List.lean` as
  `GraphLib.List.commonPrefix` and moved the Moore counting helpers from root `Set` to
  `GraphLib.Set`.
- Relocated the simple-graph realization leaves and umbrella, the existing simple directed
  realization module, Bipartite, Girth, and every Moore-bound leaf to their final concept-based
  module paths. Updated production imports and immediate legacy clients to use the final paths.
- Replaced all 27 old module paths with declaration-free forwarding imports. Every forwarder is
  explicitly marked as temporary and scheduled for Phase 9 removal.
- Added the isolated `SimplePath.extendTail` constructor with vertex/head/tail/length/edge/arc
  computations and `SimpleGraph.IsSimplePathIn.extendTail`; the frozen existential extension
  lemma now delegates to the concrete constructor without changing its signature.
- Added `GraphLibTest/Foundation/Walk.lean` with checks for every frozen Phase 4 declaration,
  Girth and both Moore bounds, plus definitional-equality fixtures for singleton and tail
  extension.

## Deviations and deferred items

- No required Phase 4 item was deferred and no semantic redesign was made.
- As required by phase discipline, `SimpleDiCycle`, the split/completion of
  `InSimpleDiGraph`, and general walk realization remain Phase 5 work.
- The temporary Girth-local neighborhood/degree API remains until Phase 6.
  `HasSimpleCycle`/`IsAcyclic` remain in the relocated realization layer until Phase 7.
- The forwarding modules remain until their planned Phase 9 removal.
- Existing unrelated warnings remain in `Graph/Finite.lean` and the pre-Phase-5 raw-walk
  modules; the two existing `InverseAckermann/Nivasch.lean` `sorry` declarations also remain.
  Phase 4 added no production `sorry`.

## Validation

- Independently built every final `Util.List`, `Walk.VertexSeq.*`, simple-spine,
  `Walk.InSimpleGraph.*`, `Walk.InSimpleDiGraph`, Bipartite, Girth, and Moore-bound leaf:
  success.
- Rebuilt all 27 legacy forwarding modules directly: success (1121 jobs).
- `lake build GraphLib GraphLib.All GraphLibTest.ImportAll
  GraphLibTest.Foundation.Basic GraphLibTest.Foundation.Transformations
  GraphLibTest.Foundation.Walk GraphLib.Walk.InSimpleGraph
  GraphLib.Walk.InSimpleDiGraph GraphLib.Theory.Girth GraphLib.Theory.MooreBound
  GraphLib.Theory.MooreBound.Bounds`: success (1169 jobs).
- Frozen `#check` signatures and constructor/projection reduction tests pass. Searches found no
  old-path imports in production clients, production `sorry` in the Phase 4 files, accidental
  contraction API, or Phase 5 directed-cycle additions. Final read-only review found no API,
  namespace, import-DAG, or theorem regressions. `git diff --check` passes.

## Next action

Begin Phase 5 only: complete raw/general walks and direction-correct realization at the final
walk module paths, then stop at the Phase 5 exit condition.
