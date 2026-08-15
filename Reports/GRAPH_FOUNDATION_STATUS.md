# GraphLib foundation status

**Updated:** 2026-08-15

**Current phase:** Phase 8 — `COMPLETE`

**Exit condition satisfied:** Yes

## Completed

- Added `Weight/Basic.lean` with vertex weights and actual-edge weights/costs for all four graph
  types, actual-arc capacities for directed graphs, active-carrier `EqOn`, explicit equivalence
  transport algebra, and relabel/reverse/provenance-map application and congruence laws. General
  graph data is indexed by complete `Edge` or `Arc` values, never by tags alone.
- Added `Weight/Walk.lean` with graph-independent walk/path sums over reconstructed actual edges or
  arcs. Its routine API includes singleton/one-step, append/glue, path/walk compatibility,
  active-carrier congruence under realization, undirected reversal, transported directed reversal,
  and relabel laws.
- Added `Weight/Network.lean` with actual-arc `Network` and `Flow`, finite-incidence outflow/inflow,
  flow value, feasibility, cuts and cut capacity, active-carrier extensionality, zero-flow
  feasibility, conservation rewriting, and relabel/reverse transports with source/sink swap.
- Migrated `Theory/Matching/Basic.lean` from `edges` to actual-carrier `edgeSet`, with
  `edgeSet_subset : edgeSet ⊆ E(G)` and genuinely finite `edgeFinset`/`size` APIs.
- Added `Foundation/WeightNetwork.lean`, covering same-tag distinct-edge weights, provenance,
  relabel/reverse transport, reused-tag traversal sums, actual-arc capacity/flow domains,
  loop/parallel/antiparallel incidence contributions, cuts, the finite-vertices negative instance,
  zero flow, and finite matching size. Added the three Phase 8 leaves directly to `GraphLib.All`.

## Deviations and deferred items

- No earlier-phase repair or Phase 8 deviation was needed. Same-carrier induce/restrict/delete
  operations reuse attached functions directly, so no duplicate transport API was added for them.
- Plan-permitted bundled attached-data wrappers, vertex-visit weights, distance/shortest-path
  theory, residual networks, max-flow/min-cut theory, and flow algorithms remain deferred.
- The Phase 9 `Weight.lean` umbrella was intentionally not created; Phase 8 leaves are direct
  `GraphLib.All` imports until final umbrella cleanup.
- Existing unrelated linter warnings and the two pre-existing
  `DataStructures/InverseAckermann/Nivasch.lean` `sorry` declarations remain. Phase 8 added no
  production `sorry`.

## Validation

- Incremental builds of `GraphLib.Weight.Basic`, `GraphLib.Weight.Walk`,
  `GraphLib.Weight.Network`, and `GraphLibTest.Foundation.WeightNetwork` succeeded.
- `lake build GraphLib GraphLib.All GraphLibTest.ImportAll GraphLib.Walk.InSimpleGraph
  GraphLib.Walk.InSimpleDiGraph GraphLib.Theory.Girth GraphLib.Theory.MooreBound
  GraphLibTest.Foundation.Basic GraphLibTest.Foundation.Transformations
  GraphLibTest.Foundation.Walk GraphLibTest.Foundation.FiniteDegree
  GraphLibTest.Foundation.Connectivity GraphLibTest.Foundation.WeightNetwork`: success (1196 jobs).
- Searches found no Phase 8 production `sorry`, forbidden weighted/capacitated graph type,
  tag-keyed general attached data, residual/contraction API, speculative finite view, stale matching
  field use, or premature `Weight.lean` umbrella. `git diff --check` passes.

## Next action

Begin Phase 9 only: add the selected constructors, finalize truthful umbrellas and test targets,
and remove the temporary forwarding modules described by the final plan.
