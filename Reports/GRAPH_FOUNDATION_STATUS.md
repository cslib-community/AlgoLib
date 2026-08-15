# GraphLib foundation status

**Updated:** 2026-08-15

**Current phase:** Phase 7 — `COMPLETE`

**Exit condition satisfied:** Yes

## Completed

- Added `Connectivity/Reachability.lean` for all four graph types. Reachability uses the appropriate
  path carrier and has path/walk equivalences, endpoint membership, vertex-restricted reflexivity,
  transitivity, undirected symmetry, directed reversal, subgraph monotonicity, adjacency closure,
  and vertex/tag relabel transport.
- Added `Connectivity/Connected.lean` with vacuous `Preconnected`, nonempty `Connected`, literal
  component sets, component membership/subset/equality/equal-or-disjoint laws, one-component
  connectedness, empty-graph conventions, and relabel transport.
- Added `Connectivity/StronglyConnected.lean` with mutual reachability, nonempty whole-graph strong
  connectedness, SCC sets and their partition laws, directed reversal, and relabel transport.
- Added `Connectivity/Acyclic.lean` with direction- and identity-correct cycle absence for all four
  graph types. Added subgraph/no-edge, reversal, and relabel laws, plus undirected `IsForest :=
  IsAcyclic` and `IsTree := Connected ∧ IsAcyclic` for simple and general graphs.
- Moved `SimpleGraph.HasSimpleCycle`/`IsAcyclic` out of the realization layer. Replaced the obsolete
  connectivity, Forest, and Tree drafts with declaration-free Phase 9 forwarders; removed
  `SimpleGraph.Contains` and `SimpleGraph.IsConnected`; repaired Girth and forwarding imports; and
  added the declaration-free `GraphLib.Connectivity` umbrella to `GraphLib.All`.
- Added `GraphLibTest/Foundation/Connectivity.lean`, covering all public carrier types, empty-graph
  semantics, reachability endpoints/transitivity/symmetry/reversal, component partition laws, SCC
  reversal, general loop and parallel-edge cycles, simple cycle length conventions, no-edge
  acyclicity, and subgraph monotonicity.

## Deviations and deferred items

- Repaired a blocking Phase 5 omission: cycle erasure now preserves both endpoints and realization
  for general walks; `Walk.toPath` exposes both endpoint laws; and simple-walk glue/map endpoint
  projections are available. These are the smallest earlier-spine repairs needed to prove Phase 7
  reachability transitivity and the walk/path equivalences.
- Cycle-carrier relabel construction remains private to `Connectivity/Acyclic.lean`; Phase 7 exposes
  the required graph-level existence and acyclicity invariance without expanding the earlier raw
  carrier API.
- No required Phase 7 item was deferred. Plan-permitted quotient/executable component enumeration,
  condensation algorithms, unique-path tree theory, topological ordering, feedback sets, and
  advanced cycle theory remain deferred.
- Existing unrelated linter warnings and the two pre-existing
  `DataStructures/InverseAckermann/Nivasch.lean` `sorry` declarations remain. Phase 7 added no
  production `sorry`.

## Validation

- Incremental builds of every new connectivity leaf, migration forwarder, Girth, and the Phase 7
  foundation test succeeded.
- `lake build GraphLib GraphLib.All GraphLibTest.ImportAll GraphLib.Walk.InSimpleGraph
  GraphLib.Walk.InSimpleDiGraph GraphLib.Theory.Girth GraphLib.Theory.MooreBound
  GraphLibTest.Foundation.Walk GraphLibTest.Foundation.Connectivity`: success (1186 jobs).
- Searches found no Phase 7 production `sorry`, `SimpleGraph.Contains`, `SimpleGraph.IsConnected`,
  or connectivity/acyclicity definitions outside the canonical `Connectivity` modules.
  `git diff --check` passes.

## Next action

Begin Phase 8 only: implement attached data, traversal weights, networks, and the matching stress
test at the Phase 8 boundary.
