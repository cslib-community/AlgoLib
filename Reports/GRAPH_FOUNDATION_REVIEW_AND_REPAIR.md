# GraphLib foundation review and repair report

- **Date:** 2026-08-16
- **Final status:** `CONVERGED_WITH_DEFERRED_ITEMS`

## 1. Executive summary

GraphLib's graph foundation is mathematically sound, coherently layered, and ready for a real
algorithm integration test. Two independent review rounds found no S0 correctness defect. The
locked semantics for actual edge identity, tag reuse, loops, parallel edges, antiparallel arcs,
graph transformations, reversal, walks and cycles, finiteness, degree, connectivity, and attached
weights all survived adversarial examples and the final regression suite.

The review did find API and architecture friction worth repairing before integration. The largest
repairs were one-way finite transport through graph operations; public path/cycle realization,
glue, relabel, projection, and algebra laws; reverse incidence/degree transport; induce/restrict/
delete algebra; and flow aggregate/feasibility transport. Three unnecessarily broad imports were
narrowed. Naming and simp corrections brought the new surface back into the documented grammar.
Round 2 found no new S0/S1 issue; its three accepted S2 items and one S3 rename were local
post-repair consistency gaps and are fixed.

The remaining work is deliberately nonblocking: existing linter/documentation debt and executable
enumeration or algorithm-specific structures. Those should be driven by a real BFS, SCC,
shortest-path, MST, or flow development rather than speculative foundation growth. No consequential
human design decision is outstanding.

|                  | S0 | S1 | S2 | S3 |
| ---------------- | -: | -: | -: | -: |
| Round 1 found    |  0 |  3 | 16 |  2 |
| Round 1 accepted |  0 |  2 | 13 |  2 |
| Round 2 found    |  0 |  0 |  4 |  2 |
| Round 2 accepted |  0 |  0 |  3 |  1 |
| Fixed            |  0 |  2 | 16 |  1 |
| Deferred         |  0 |  0 |  0 |  2 |

Raw “found” counts retain overlaps between reviewers. Accepted and disposition counts are
deduplicated. Final disposition: **19 fixed, 2 deferred, 2 rejected, 0 human decisions**.

## 2. Human decisions / manual inspection

No consequential mathematical or public-API decision needs human resolution. The alternatives
raised during review either had concrete minimal repairs, were cleanup-only, or lacked enough
evidence to justify public-surface growth.

## 3. Architecture after review

The folder and namespace organization remains coherent; no file move, merge, or split was
warranted. The final production import graph contains 69 modules and 161 internal edges. It is a
DAG, and the audit found no upward import from `Graph` into walk/connectivity/weight/theory, from
`Walk` into connectivity/weight/theory, or from `Connectivity` into weight/theory.

```text
Graph primitives
  -> graph operations / finite / map / reverse / degree
  -> Walk carriers
       -> graph-family realization modules
       -> Connectivity
            -> Theory (Girth, MooreBound, ...)
  -> Weight.Basic
       -> Weight.Walk
       -> Weight.Network
Umbrellas: GraphLib.All and GraphLibTest.ImportAll
```

Three leaf imports were narrowed:

- `Walk.Path`: `Trail` to `Walk`;
- `SimpleDiCycle`: `SimpleCycle` to `SimplePath`;
- `Weight.Walk`: broad simple-realization imports to concrete path leaves.

Carrier operations now live with their carriers, realization preservation with `Walk/In*`, weight
identities with `Weight/Walk`, and network consequences with `Weight/Network`. `Connectivity/Acyclic`
uses the public cycle relabel API instead of maintaining a private reconstruction block. The broad
finite-instance family remains in the intended `Graph.Finite` layer and showed no synthesis cycle.
No suspicious dependency edge remains.

## 4. Semantic invariant audit

| Invariant | Final result |
| --------- | ------------ |
| Actual general edge/arc identity | Preserved as tag plus unordered/ordered endpoints; no tag-only collapse. |
| Tag reuse and parallelism | Same tags at different endpoints and parallel actual edges remain distinct. Deleting one parallel edge leaves the other. |
| Loops | General graphs retain loops; simple conversions reject/drop them as specified. Undirected degree counts each loop twice; directed loops count once in both in- and out-degree. |
| Antiparallel arcs | Remain distinct in directed graphs; direction-forgetting merges only their endpoint image where appropriate. |
| Endpoint-image loss | General map operations retain source provenance in tags; simple images enforce looplessness explicitly. |
| Induce/restrict/delete | Membership, monotonicity, and commutation laws agree across all four graph families. |
| Reverse | Arc identity, incidence, degree, realization, weights, and double reversal are correct. R2-B01 fixed nested restrict/delete simp normalization. |
| Walk data | Raw tags reconstruct actual bundled edges/arcs from adjacent vertices; tag reuse stress cases distinguish the reconstructed objects. |
| Trail/path/circuit/cycle conventions | Trails forbid repeated actual edges/arcs; paths forbid repeated vertices; general cycles admit loops, undirected two-cycles require distinct actual edges, and directed simple cycles admit length two but not one. |
| Finite vertices versus finite edges | Kept independent for general graphs. Transformation instances are one-way and do not infer finite edges from finite vertices. |
| Reachability/connectivity/SCC | Reachability is path-based on graph vertices; preconnectedness is vacuous on the empty graph, while connectedness and strong connectedness require nonemptiness. Reverse/relabel laws pass. |
| Weights/capacities/flows | Functions are indexed by actual edges/arcs. Parallel arcs and loops aggregate correctly; loops cancel in internal conservation; transport and feasibility laws pass. |

The empty graph, a single loop, multiple loops, parallel edges, reused tags, antiparallel arcs,
nested operations, double reversal, finite-vertex/infinite-edge separation, and nonzero loop-bearing
flows were all exercised. No failed invariant remains.

## 5. Public API audit

The final public surface covers the routine bridge layer needed by clients without requiring them
to unfold graph or walk representations.

| Area | Graph | DiGraph | SimpleGraph | SimpleDiGraph |
| ---- | :---: | :-----: | :---------: | :-----------: |
| Membership/extensionality | Yes | Yes | Yes | Yes |
| Induce/restrict/delete algebra | Yes | Yes | Yes | Yes |
| Finite transformation transport | Yes | Yes | Yes | Yes |
| Path realization and relabel | Yes | Yes | Yes | Yes |
| Path glue and weight glue | Yes | Yes | Yes | Yes |
| Cycle realization/relabel | Yes | Yes | Yes | Yes |
| Reverse incidence/degree | N/A | Yes | N/A | Yes |
| Aggregate flow transport | N/A | Yes | N/A | N/A |

Important additions include exact path gluing; path/cycle vertex/tag relabeling with projection and
identity/composition/inverse laws; realization wrappers for operations, relabeling, and glue;
reverse incidence images and degree swaps; and weight/flow transport. Operation-specific degree
theorems no longer require redundant target-finiteness hypotheses when source finiteness safely
synthesizes them.

Intentionally thin areas are executable adjacency/incidence enumeration, residual-network
construction, queues/heaps/union-find integration, and algorithm state structures. These belong to
real clients, not the mathematical foundation.

## 6. Naming, redundancy, and public-surface audit

The repaired declarations follow `NAMING.md`:

- directed endpoint APIs use source/target vocabulary;
- zip projection names are descriptive;
- transformed membership theorems use `mem_edgeSet_<operation>`;
- relabel algebra uses `_id`, `_comp`, and `_inverse`;
- `mem_edgeSet_forgetDirection` now has the shortest canonical membership name.

The private cycle relabel reconstruction in `Acyclic` was deleted in favor of public carrier
operations. No alias-only theorem family or speculative blanket carrier map was added. The proposed
wholesale deletion/rewrite of 241 existing `simpNF` declarations (R1-C02) was rejected: the debt is
real, but review found no loop, instability, or client failure that justified widening this task.

## 7. Simp, typeclass, and automation hygiene

Two undirected commutativity equalities were removed from `[simp]`, avoiding orientation-sensitive
normalization. Round 2 added involution lemmas for double images under arc reversal and ordered-pair
swap, so nested reverse/restrict/delete expressions now normalize. Path/cycle projection and relabel
algebra lemmas remove the need to expose `.val` in ordinary client proofs.

The new finite instances transport only from source facts to transformed objects. Low-heartbeat
nested induce/restrict/delete/reverse probes found no loop or ambiguity, and negative probes confirm
that finite vertices still do not synthesize finite general edges. `simpComm`, impossible-instance,
and non-class-instance checks showed no new regression.

R2-D02 proposed operation-specific degree bridge simp lemmas after reverse/delete normalization.
It was rejected as redundant S3 surface: the canonical reverse-degree theorem works with
`simpa only`, while a bridge family for every operation would duplicate existing algebra. Stable
`grind`, unused-simp-argument, flexible-tactic, and documentation warnings remain candidates for a
separate cleanup/proof-compression pass.

## 8. Downstream client simulation

| Client | Exercised | Result and remaining boundary |
| ------ | --------- | ----------------------------- |
| BFS / reachability | Finite vertex sets, neighbor frontiers, reachability, induce/delete/relabel | Mathematical skeletons elaborate. Executable enumeration and queue state remain client-driven. |
| SCC | Directed reachability, reverse, relabel, strong components | Reverse/relabel skeletons elaborate. Concrete SCC traversal state is algorithm infrastructure. |
| Weighted shortest path | Path realization, glue, relabel, weight additivity | Triggered path glue/relabel/projection and weight repairs. The final client no longer needs `.val` workarounds. Heap/distance-map choices remain deferred. |
| MST | Actual-edge weights, finite subgraph edge sets, simple graph paths/cycles | Candidate-edge and weighting skeletons elaborate. Union-find and exchange-proof organization are client choices. |
| Flow / augmenting paths | Arc incidence, capacities, path weights, aggregates, reverse, feasibility | Triggered aggregate/feasibility transport repairs. Residual networks and augmenting algorithms remain intentionally absent. |

The review distinguishes those executable boundaries from foundation deficiencies. No current
client skeleton requires a representation change.

## 9. Round 1 findings and repairs

| ID | Severity | Area | Disposition | Repair / reason |
| -- | -------- | ---- | ----------- | --------------- |
| R1-A01 | S2 | Import DAG | Fixed | `Walk.Path` now imports `Walk.Walk`. |
| R1-A02 | S2 | Import DAG | Fixed | `SimpleDiCycle` now imports `SimplePath`. |
| R1-A03 | S2 | Import DAG | Fixed | `Weight.Walk` uses concrete realization leaves. |
| R1-D01/B01/C03 | S1 | Finiteness | Fixed | Added safe one-way finite transport and local incidence helpers. |
| R1-D02 | S2 | Paths | Fixed | Added injective map and vertex/tag relabel APIs with transport. |
| R1-D03 | S2 | Paths/weights | Fixed | Added exact path glue, realization, and additive weight laws. |
| R1-D04/B06 | S2 | Flows | Fixed | Added relabel/reverse aggregates, flow value, and feasibility transport. |
| R1-B02 | S1 | Cycle boundary | Fixed | Added scoped public relabel carriers and removed private reconstruction. |
| R1-B03 | S2 | Realization | Fixed | Added compact path/cycle operation and relabel wrappers. |
| R1-B04 | S2 | Reverse/degree | Fixed | Added reverse incidence images and in/out-degree swaps. |
| R1-B05 | S2 | Operation algebra | Fixed | Added induce/restrict/delete commutation across all families. |
| R1-C01 | S2 | Simp | Fixed | Removed simp attributes from two commutativity equalities. |
| R1-C04 | S2 | Naming | Fixed | Canonicalized directed and zip vocabulary. |
| R1-C05 | S2 | Naming | Fixed | Canonicalized transformed edge-set membership names. |
| R1-C06 | S2 | Naming | Fixed | Canonicalized relabel algebra suffixes. |
| R1-D05 | S3 | Diagnostics | Deferred | Stable build/linter noise belongs to a cleanup pass. |
| R1-C07 | S3 | Documentation | Deferred | Public-doc lint debt belongs to a focused documentation pass. |

R1-C02, a proposed broad simp-layer rewrite, was rejected for insufficient concrete evidence.

## 10. Round 2 findings and repairs

| ID | Severity | Area | Disposition | Repair / reason |
| -- | -------- | ---- | ----------- | --------------- |
| R2-C01 | S2 | Cross-family path API | Fixed | Added simple-family path glue realization, weight glue, and relabel-weight wrappers. |
| R2-C02 | S3 | Naming | Fixed | Renamed to `mem_edgeSet_forgetDirection`. |
| R2-B01 | S2 | Reverse simp algebra | Fixed | Added double reverse-image normalization for arcs and ordered pairs, with tests. |
| R2-B02/D01 | S2 | Wrapper abstraction | Fixed | Added path/cycle projections and relabel id/comp/inverse laws, with client regressions. |
| R2-D02 | S3 | Degree simp convenience | Rejected | Existing direct theorem is stable; a bridge family would be redundant. |

Round 2 discovered no S0 or S1 issue. Its accepted findings were local completeness and
normalization gaps introduced or exposed by the Round 1 repair, and all are closed.

## 11. Deferred issues

### Deferred S2

None.

### Deferred S3

- R1-D05: stable `grind` suggestions and routine linter warnings.
- R1-C07: missing public documentation, concentrated around walk accessors and predicates.

### Client-driven deferred work

- executable adjacency/incidence enumeration and concrete finite containers;
- traversal queues/stacks, priority queues, and distance/predecessor maps;
- SCC algorithm state;
- MST union-find and certificate structures;
- residual networks and augmenting-flow state.

## 12. Build and regression evidence

The final requested build succeeded with 1182 jobs:

```text
lake build GraphLib GraphLib.All GraphLibTest GraphLibTest.ImportAll \
  GraphLib.Walk.InSimpleGraph GraphLib.Walk.InSimpleDiGraph \
  GraphLib.Theory.Girth GraphLib.Theory.MooreBound \
  GraphLib.Graph.Basic GraphLib.Graph.Adjacency GraphLib.Graph.Finite \
  GraphLib.Graph.Constructions GraphLib.Weight.Basic GraphLib.Weight.Walk \
  GraphLib.Weight.Network
```

Each locked semantic file also succeeded independently:

```text
GraphLibTest/Foundation/Basic.lean
GraphLibTest/Foundation/Transformations.lean
GraphLibTest/Foundation/FiniteDegree.lean
GraphLibTest/Foundation/Walk.lean
GraphLibTest/Foundation/Connectivity.lean
GraphLibTest/Foundation/WeightNetwork.lean
```

Focused cycle/Acyclic, realization, reverse/degree, path-weight, and network builds succeeded.
`git diff --check` is clean. Forbidden legacy names are absent. The patch adds no `sorry` or
`admit`; all remaining `sorry`s are pre-existing in the excluded Union-Find and Inverse-Ackermann
scaffolds. The build emits stable linter and `grind` suggestions but no error, timeout, suspicious
instance search, or import-performance regression.

## 13. Readiness for algorithm integration

**`READY_WITH_CAVEATS`**

GraphLib is suitable for a nontrivial graph algorithm formalization with correctness and runtime
analysis. Its mathematical representations and proof-facing APIs are stable enough to begin. The
likely client-driven adjustment points are:

1. executable adjacency/incidence enumeration;
2. finite carrier/container bridges;
3. algorithm state and data-structure interfaces;
4. residual-network operations for flow;
5. a small number of theorem orientations discovered by actual invariant proofs.

These are expected integration discoveries, not current foundation blockers.

## 14. Recommended next steps

1. Formalize one real algorithm end to end, preferably one that exercises finite enumeration and a
   nontrivial invariant.
2. Make only evidence-backed, client-driven foundation adjustments.
3. Freeze the public graph-foundation API after that integration.
4. Run a separate documentation and proof-compression/`simp`/`grind` cleanup pass.
