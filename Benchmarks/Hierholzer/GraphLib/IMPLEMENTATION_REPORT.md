# GraphLib Hierholzer blind-first-attempt implementation report

## Scope, provenance, and freeze evidence

This report covers only the GraphLib-side implementation. No counterpart benchmark source,
worktree, history, report, or generated artifact was inspected.

- Protocol-recorded repository commit: `d4dbdf45b2420750e55eb7caf529265a2bfff11f`.
- Common infrastructure commit / implementation base: `1b5c9f94e7cc660df254626555463ab8b2da791c`
  (`Freeze Hierholzer Common benchmark infrastructure`), parent
  `3a842eeb02c32af5ba6e45ba1a5ced7e9778bcfa`.
- Branch: `benchmark/hierholzer-graphlib`.
- GraphLib frozen source-manifest digest recomputed at the implementation base:
  `3ec806b9b96ce6b079c12fbeb930556937b36c1a6e21d92a70d190bf5d80c894`.
- `Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256`: all four entries verified `OK`
  before substantive work and again before review.
- Lean/toolchain and dependencies are those recorded by `COMMON_FREEZE_REPORT.md`: Lean
  `4.30.0-rc2`, Mathlib `d802ffd29db1f5dc5a29206b1a8af62bfcc234a3`, and CSLib
  `608cbe1b629a276abd3f2081f9b42dc766d8fd78`.
- The preserved first-green commit is recorded in the final handoff and in the post-freeze
  metadata update to this report. The commit being described is the first snapshot containing
  all mandatory source, stress evaluations, this report, and the four-reviewer disposition.

The representation was compiled and frozen before `Algorithm.lean` existed. Its manifest is:

| frozen input | SHA-256 |
| --- | --- |
| `Adapter.lean` | `baabf138983737c4d2ce06b52dfad5566f67060fc4075b9a39d8c16717a6d52d` |
| `Representation.lean` | `b350baeea2d3608f4640b91cba77100d0c11e3fbb99f8ffe130cf076b106a665` |
| `REPRESENTATION_FREEZE.md` | `fe9d85850a6702285f4cc217cdd189a5f6e08ed241f3d1be1474c395f3df42f7` |

No representation attempt was abandoned before that freeze. The pre-core hashes of
`Representation.lean` and the freeze record were respectively
`76c14a…083` and `b4f399…fa7f`. Reviewer A found that the frozen footprint counted both
top-level array headers but not their two structure-field pointers. The one allowed repair round
changed only `repWords`/`r0` and its documentation, producing the current hashes above. No
executable field, representation law, access primitive, or storage-to-counter mapping changed.

## Delivered files

- `Adapter.lean`: exact frozen semantics and GraphLib bridges.
- `Representation.lean`: certified dense incidence layout, footprint, counting bridges, and total
  existence theorem.
- `REPRESENTATION_FREEZE.md` and `REPRESENTATION_MANIFEST.sha256`: pre-core schema and digest.
- `Algorithm.lean`: the timed standard stack/backtracking implementation.
- `Correctness.lean`: invariants, semantic proof, and mandatory corollaries.
- `Resource.lean`: all fourteen component bounds and scalar theorems.
- `Stress.lean`: seven explicit supplied representations, exact results, exact cost vectors,
  decoded certificates, and concrete bounds.
- `Audit.lean`: reproducible `#print axioms` commands.
- `IMPLEMENTATION_REPORT.md`: this report.
- `Benchmarks/Hierholzer/GraphLib.lean`: side-specific umbrella.

No existing file in `GraphLib/`, Common, Mathlib, CSLib, or project configuration was modified.

## Mathematical adapter

The local meanings are literal implementations of the frozen contract:

- `Vertex G := {v // v ∈ V(G)}` and `ActualEdge G := {e // e ∈ E(G)}`;
- `Link G e x y := G.IsLink e.1 x.1 y.1`;
- `Inc := ∃ y, Link`, `Loop e x := Link e x x`;
- `degree := ncard incident actual edges + ncard loops`;
- `Step := ∃ actual edge, Link`, with `Reachable := Relation.ReflTransGen Step`;
- `vertexCount := Set.ncard V(G)` and `edgeCount := Set.ncard E(G)`.

Actual edge identity is the complete bundled GraphLib `Edge`, not its tag. The public correctness
theorem has only `[Finite V(G)]`, `[Finite E(G)]`, the supplied representation and start, plus the
two frozen explicit assumptions `heven` and `hconn`; there is no ambient `Fintype`, `DecidableEq`,
hashing, or stronger connectivity premise.

Material GraphLib APIs reused were `Graph.IsLink` and its symmetry/endpoints/incidence lemmas,
`Graph.inc_iff_exists_isLink`, `incidenceSet`, `loopSet`, native `degree`, `vertexFinset`,
`edgeFinset`, `ncard_incidenceSet_add_ncard_loopSet_eq_degree`, `ncard_edgeSet`, and especially
`sum_degrees_eq_twice_card_edges`. The bridge `degree_eq_graphDegree` proves the frozen
loop-corrected adapter degree equals the native degree. `degreeSum_eq_twice_edgeCount` transports
the native handshaking theorem to subtype-indexed benchmark sizes.

No blocking GraphLib API defect was found. Missing conveniences were a ready dense enumeration of
the vertex/actual-edge subtypes and a native predicate/theory matching “every non-isolated vertex
is reachable from this start” rather than full `Graph.Connected`; local generic finite-choice and
reachability induction were used. A native circuit result was optional and was not implemented.

## Certified executable representation

`IncidenceEnumeration n m` contains exactly:

- `endpoints : Vector (Fin n × Fin n) m`;
- `buckets : Vector (Array (Fin m × Bool)) n`.

A Boolean is an endpoint role, so `(e,false)` and `(e,true)` remain distinct even for a loop and
occur together in the loop vertex's bucket. `CertifiedIncidenceRepresentation` adds the two dense
sizes, equivalences onto all mathematical vertices and full actual edges, the refinement proof,
and equalities to official `ncard` sizes. Proofs/equivalences are logical certification, not hot
payload. Bucket order is arbitrary, and the theorem suite quantifies over every certified `R`.

The five normalized representation obligations are: endpoint soundness; bucket duplicate freedom;
exact canonical dart membership/no junk; a bijection onto every actual vertex including isolated
ones with the correct cardinal; and a bijection onto every full actual edge with the correct
cardinal. Exact membership derives two darts per edge, including two roles in one bucket for a
loop. There is no start, used flag, cursor, parity/connectivity proof, tour, or traversal schedule
in `R`.

The logical footprint is definitionally

```text
repWords R = 6 + 2*n + 2*m + 2*I
r0 = 6, rV = 2, rE = 2, rI = 2.
```

The six constant words are two supplied sizes plus a structure pointer and container header for
each top-level array; each vertex contributes an outer pointer and inner-array header; each endpoint
pair two words; each dart an edge ID and role. Using `I = 2m`, this reduces to `6 + 2n + 6m`.

`representation_exists` is total for every finite mathematical input. It noncomputably chooses
dense equivalences and an orientation of each unordered bundled edge, then constructs every bucket
as the filtered finite set of canonical darts. This is option 3 in the protocol: only a
noncomputable general construction/existence theorem, with no preprocessing-cost theorem. The
stress fixtures separately supply a small computable constructor from explicit endpoint data; it
is test infrastructure, not the primary general constructor.

`encodeVertex := decodeVertex.symm` is outside the clock. For an explicitly supplied computable
equivalence it can execute, but the mandatory general existence path selects its equivalence
noncomputably. No lookup cost is proved, and it is not presented as an end-to-end executable entry
point.

Alternative layouts considered were CSR and per-vertex lists. CSR would reduce headers but require
an offset vector and more indexing proof; lists make constant-time cursor advancement awkward in
the purely threaded state. Arrays-of-arrays give the simplest honest pointer/length/dart ledger.
No hash table, ambient-value comparison, matrix, cached endpoint reconstruction, or deletion-based
graph state is used.

## Algorithm and semantic proof

The core is standard linear Hierholzer. It initializes one used Boolean per actual edge, one cursor
per vertex, and a root frame. Each nonempty iteration peeks the top vertex, advances its persistent
bucket cursor past already-used darts, and either marks one actual edge used and pushes its other
endpoint, or pops an exhausted frame. A non-root pop conses `(incomingEdge,destination)` onto the
output. Backtracking order plus front-cons yields traversal order directly, so no uncharged reverse,
append, copy, endpoint reconstruction, validation, or decoded-output materialization follows the
clock. The public return is exactly `IndexedTour n m`.

The ten normalized persistent algorithm-state obligations are three cursor obligations (every
cursor is in bounds; global remaining-dart fuel equals the sum of bucket suffix lengths; every
scanned prefix dart is used) and seven core obligations (rooted linked stack shape; the empty-stack
closed walk; the nonempty live walk; used flag iff membership in output-plus-stack chain; no
duplicate chain edge IDs; every emitted destination is exhausted; and start exhaustion on final
empty stack). `ScanCorrect` additionally packages local preservation of used flags, cursor
monotonicity, stack/output identity, and the exact `some`/`none` outcome.

Termination/correctness uses
`corePotential = 2*(m - chain.length) + stack.length`. A push and either pop reduce it exactly by
one. The initial value is `2m+1`; the repaired public step fuel is exactly `2m+1`, and the proof
uses `corePotential ≤ stepFuel`, observing directly that zero potential forces an empty stack.
Parity is used exactly when an exhausted vertex is popped: the loop-corrected used degree and a
dense walk endpoint parity lemma force closure under `heven`. `hconn` is used only afterward to
propagate cursor exhaustion from the start to all non-isolated vertices and hence prove coverage.

`hierholzer_correct` proves the exact Common `ValidEulerTour` with all six fields: length relation,
head `s`, last `s`, positional actual-edge links, decoded edge `Nodup`, and coverage of every
bundled mathematical edge. The mandatory corollaries are `hierholzer_edgeless`,
`hierholzer_exact_length`, and `hierholzer_positive_edge_circuit`.

## Bridge and helper inventory

Representation/semantic bridges (category C unless noted) are:

- Adapter: `inc_iff_graphInc`, `loop_iff_graphIsLink`, `degree_eq_graphDegree`,
  `natCard_vertex`, `natCard_actualEdge`, and `degreeSum_eq_twice_edgeCount`.
- Representation: `endpoint_sound`, `bucket_nodup`, `dart_mem_bucket_iff`, `dart_link`,
  `bucket_size_eq_filter_card`, `incidenceCount_eq_twice_edgeCount`,
  `incidenceCount_eq_sum_degree`, `exists_link_endpoints`, `chosenEndpoints_spec`, and
  `representation_exists`.
- Correctness graph/representation bridges: `link_inc_iff`, `link_loop_iff`,
  `edgeWeight_of_link`, `DenseLink.left_eq_of_right`, `degree_eq_sum_edgeWeight`,
  `usedDegree_eq_degree_of_incident_complete`, `incident_has_bucket_dart`,
  `used_of_cursor_exhausted`, `CoreInvariant.reachable_exhausted`,
  `CoreInvariant.edges_complete`, and `DenseWalkSteps.decoded_links`.

Auxiliary generic/list/finite lemmas introduced locally are `DenseWalkSteps.append`, `snoc_iff`,
`length_vertices`, `usedDegree_even_iff_endpoints`, `ncard_predicate_eq_sum_ite`,
`walk_closes_at_even_exhausted`, the `Vector` get/set/init lemmas, the `remainingDarts` summation
lemmas, the four `StackShape`/`stackSteps` lemmas, three potential-drop lemmas,
`DenseWalkSteps.property_of_incident_mem`, `vertices_getLast`, and `length_eq_fin_card`. They remain
side-local and are charged here. The remaining correctness declarations are algorithm invariant
definitions or preservation/main theorems, not additional foundation bridges.

Primary friction labels are: A for parity closure, stack rotation, and coverage; B for dependent
`Vector`/`Fin` indexing and list/sum normalization; C for full bundled-edge dense equivalence,
endpoint orientation, and decoder correspondence; D for the missing weak non-isolated
connectivity convenience; and E for manual event instrumentation, two structural fuels, and
fourteen-field recurrence algebra. A/B/E are not attributed to GraphLib.

## Complete primitive/tick audit

Only Common `Event` wrappers introduce nonzero cost. `Algorithm.lean` contains no `TimeM.tick`,
`✓`, manually constructed nonzero `TimeM`, `Finset`, `filter`, `fold`, `map`, `append`, or `reverse`
in the timed transitive call graph.

| timed function/path | exact charged operations |
| --- | --- |
| `initVectorLoop` | one `initWrite` per initialized logical word; capacity is reserved before the linearly threaded pushes |
| `initializeState` | `m+n` initialization writes, then one stack push with three payload writes |
| `scanBucket`, fuel zero | none |
| `scanBucket`, bounds failure | one `indexLt`; returns the original fuel word without arithmetic |
| each inspected dart | one `indexLt`; two incidence reads (edge ID and role); one `indexSucc`; one cursor write; one used read |
| `nextIncident` | one outer bucket-pointer incidence read, one cached inner length/header incidence read, one cursor read, then `scanBucket` |
| every nonempty `runLoop` iteration | stack check; three-word stack peek; one `nextIncident` |
| unused-dart/push branch | one used write; two endpoint reads; stack push plus three payload writes |
| exhausted non-root/pop branch | stack pop plus three payload reads; output emit plus two payload writes |
| exhausted root branch | stack pop plus three payload reads, no output |
| fuel-zero completion | no final redundant empty-stack check; zero potential proves the stack is empty |
| `hierholzer` wrapper | one `indexAdd` for dart fuel `2m`, one `indexAdd` for step fuel `2m+1`, and one output write for returned start |

The returned `steps` list is already ordered and shared from the final state; `outputRead = 0` is
therefore exact. Mathematical decoding is a proof-only pointwise view. Eulerian validation and
representation construction are excluded exactly as allowed by the protocol.

Primitive assumptions: bounded `Fin`/`Nat` comparisons, increments, and additions are word-RAM
operations; array/Vector reads are constant time; persistent array writes receive the protocol's
unit-write assumption and are plausibly in-place because state is linearly threaded; preallocated
`Array.push` does not reallocate; list cons/head/tail are constant-time structural operations.
Allocation headers are free for runtime initialization exactly where the frozen table says so.
The word width assumption is `w ≥ max 1 (ceil(log2(n+I+1)))`. A supplied start implies `n≥1`;
therefore the largest structural guard `I+1` is strictly below `n+I+1`, while IDs, cursors and
ordinary one-past-end sentinels are no larger. Charging each word operation logarithmically
gives the immediate conservative bit-cost robustness estimate
`O((n+m+1) log(n+m+1))` after `I=2m`.

## Resource theorems

`hierholzer_component_bounds` is unconditional in every certified representation and start. In
the frozen fourteen-field order its bounds are:

```text
initWrite    ≤ n + m
incidenceRead≤ 2I + 4m + 4
endpointRead ≤ 4m + 4
usedRead     ≤ I
usedWrite    ≤ 2m + 2
cursorRead   ≤ 2m + 2
cursorWrite  ≤ I
indexOp      ≤ 2I + 2m + 4
stackControl ≤ 6m + 7
stackRead    ≤ 12m + 12
stackWrite   ≤ 6m + 9
outputControl≤ 2m + 2
outputRead   = 0
outputWrite  ≤ 4m + 5
```

Summation gives the fully reduced primary inequality

```text
total time ≤ 51 + 1*n + 45*m + 6*I
c0 = 51, cV = 1, cE = 45, cI = 6.
```

The representation laws prove `I = 2m` by summing exact dart fibers over buckets. Independently,
the adapter/native handshaking bridge proves `I = degreeSum G = Σ_v degree_G(v)`. Substitution
gives `total time ≤ 51 + n + 57m`; `C = 57`, and `C_eq_protocol_max` proves
`C = max c0 (max cV (cE+2*cI))`. Hence the proved pointwise result is
`total time ≤ 57*(n+m+1)`, also rewritten to official `vertexCount G` and `edgeCount G`.

## Representation and auxiliary space

The representation bound is proved as above. No machine-checked peak auxiliary-space theorem was
added. The following is the normalized conservative logical-word estimate, explicitly not a
theorem: `m` used flags, `n` cursors, two vector headers, a four-field state, at most `m+1`
three-word stack frames plus list-spine pointers, and at most `m` two-word output steps plus
list-spine pointers. Since non-root stack frames plus emitted steps never exceed `m`, charging the
larger four-word stack-cell price gives at most `n + 5m + 10` live algorithm-owned words, or
`n + 5m + 12` while forming the two-word `IndexedTour`. Including `R` gives at most
`18 + 3n + 11m` at the return boundary after `I=2m`. The output list is shared, not copied. These
space estimates deliberately include headers/pointers but remain unproved normalized evidence.

## Mandatory supplied-representation stress results

Each row is backed in `Stress.lean` by: an explicit `Represents` theorem; an exact returned
`IndexedTour` equality; a decoded six-clause `ValidEulerTour`; an exact full `Cost` equality; and an
exact scalar total conjoined with the concrete `C*(n+m+1)` bound.

Cost vectors below use `(init,inc,end,usedR,usedW,cursorR,cursorW,index,stackC,stackR,stackW,outC,outR,outW)`.

| case `(n,m)` | traversal-ordered `(start; steps)` | full cost vector | total / concrete bound |
| --- | --- | --- | --- |
| one vertex, no edges `(1,0)` | `0; []` | `(1,2,0,0,0,1,0,2,4,6,3,0,0,1)` | `20 ≤ 114` |
| one loop `(1,1)` | `0; [(0,0)]` | `(2,10,2,2,1,3,2,6,10,15,6,1,0,3)` | `63 ≤ 171` |
| two distinct loops `(1,2)` | `0; [(0,0),(1,0)]` | `(3,18,4,4,2,5,4,10,16,24,9,2,0,5)` | `106 ≤ 228` |
| two parallel actual edges `(2,2)` | `0; [(0,1),(1,0)]` | `(4,18,4,4,2,5,4,10,16,24,9,2,0,5)` | `107 ≤ 285` |
| two-edge component plus isolate `(3,2)` | `0; [(0,1),(1,0)]` | `(5,18,4,4,2,5,4,10,16,24,9,2,0,5)` | `108 ≤ 342` |
| triangle `(3,3)` | `0; [(0,1),(1,2),(2,0)]` | `(6,26,6,6,3,7,6,14,22,33,12,3,0,7)` | `151 ≤ 399` |
| triangle with all tags `Unit` `(3,3)` | same ordered steps | same vector | `151 ≤ 399` |

The last fixture proves the bundled edges remain injective solely because their endpoint pairs
differ while every tag is identical. Thus tag values are demonstrably not dense edge identity.

## Computability, assumptions, automation, and axioms

The timed core is computable and uses only dense IDs; it has no classical choice or ambient
equality constraint. Noncomputable specification definitions are `degree`, `vertexCount`,
`edgeCount`, `degreeSum`, `edgeWeight`, and `usedDegree`. The latter two are proof-only parity
devices. Construction-path noncomputability is confined to `denseEquiv`, `chosenEndpoints`, and
the proof of `representation_exists`. Proof-local `Fintype.ofFinite` instances and classical finite
sums/sets appear in adapter, representation, and correctness arguments only.

Stress construction assumes `DecidableEq tagType` only to turn an injective explicit edge map into
an equivalence with its range. The public representation/core/theorems need no such instance.

`simp` is used heavily for executable reduction and transport, `omega` for natural arithmetic,
`aesop` only in two small GraphLib set extensionality subgoals, and `decide` for finite explicit
fixtures. No `native_decide`, custom axiom, `sorry`, or `admit` is present. Harmless refactors of
dependent `Vector` expressions were the most brittle part; named local equalities were more stable
than large `change` calls.

The independent `Audit.lean` output is identical for every audited principal theorem:

```text
[propext, Classical.choice, Quot.sound]
```

Audited names are `representation_exists`, `hierholzer_correct`, `hierholzer_edgeless`,
`hierholzer_exact_length`, `hierholzer_positive_edge_circuit`,
`hierholzer_component_bounds`, `hierholzer_total_affine`, and
`hierholzer_total_linear_mathematical`. These are standard Lean/Mathlib logical axioms; there are no
benchmark-local axioms.

## Engineering burden and LOC

There are 2,825 physical Lean lines and 2,382 nonblank, non-comment Lean lines. Markdown and
generated artifacts are excluded. Per-file code LOC are: Adapter 88, Representation 165,
Algorithm 157, Correctness 1,271, Resource 311, Stress 378, Audit 11, umbrella 1. There are 133
explicit theorem declarations and 483 theorem-statement LOC under the published rule “from each
`theorem`/`private theorem` line through its first `:=` line.” Common is shared-neutral and excluded;
its frozen report records 827 physical lines.

Every delivered code line is classified once by an explicit file/range rule:

| category | nonblank/non-comment LOC | rule |
| --- | ---: | --- |
| 1 executable representation and constructor | 113 | `Representation.lean` 1–109 and 182–244 |
| 2 representation correspondence/bridge | 52 | `Representation.lean` 110–181 |
| 3 algorithm core | 157 | all of `Algorithm.lean` |
| 4 functional correctness | 1,271 | all of `Correctness.lean` |
| 5 time analysis | 311 | all of `Resource.lean` |
| 6 generic data-structure support | 0 | helpers are charged to their owning proof files |
| 7 graph-specific helpers | 88 | all of `Adapter.lean` |
| 8 tests/examples | 390 | Stress 378 + Audit 11 + umbrella 1 |

The conceptual counts are five representation invariants, ten persistent algorithm-state
invariants, 27 named semantic/representation bridge lemmas listed above, 18 normalized auxiliary
generic lemma groups, and no new axioms. The public correctness theorem has two typeclass premises,
four ordinary explicit objects (`R`, `s`, `heven`, `hconn`; `G` is implicit), and exactly the two
Eulerian property premises. This normalization avoids inflating counts by record fields or aliases.

Major implementation difficulty was correctness, not execution: the parity proof had to count a
loop twice while edge uniqueness still counted it once; backtracking rotates an edge from the end
of the live stack path to the front of emitted output; and connectivity-to-coverage required an
induction over the frozen edge-forgetting reachability. Time analysis was comparatively mechanical
but verbose because every recurrence carries fourteen fields.

No exploratory source survives. Minor failed elaboration approaches were a direct dependent
`change` across the supplied fixture's endpoint vector (replaced by a named `vectorGet` equality),
dependent numeral literals before reducing `rep.n/rep.m` (replaced by concrete expected-tour
types), and `rfl` for nonempty computed tours (replaced by kernel `decide`). Approximate discarded
source was under 40 lines; no algorithm or representation redesign was abandoned. Explicit local
`.olean` generation was needed because the benchmark tree is not a Lake target.

The first-green staged diff against base `1b5c9f9…791c` was 11 new files, 3,353 insertions and no
deletions. Its raw file breakdown was: umbrella 3; Adapter 131; Algorithm 210; Audit 20;
Correctness 1,399; report 446; representation freeze record 79; representation manifest 3;
Representation 244; Resource 357; Stress 461. The Lean-only physical/code LOC metrics above
exclude the Markdown report and manifests as required.

## Independent review and one repair round

Exactly four independent read-only reviews were commissioned after the first complete source build:
A representation/architecture, B correctness, C timing/ticks, and D optimization/maintainability.
They did not edit files and did not inspect a counterpart implementation.

- A found one representation-accounting defect: the formula counted top-level array headers but
  omitted the two pointers from `IncidenceEnumeration` to those arrays. Accepted and repaired by
  changing `r0` from 4 to 6 and updating the freeze record/manifest. A independently confirmed the
  schema is standard, contains no traversal advice, represents loops as two roles of one edge ID,
  preserves parallel/reused-tag identities, and has no materially simpler required layout. Its
  optional two-word sentinel frame optimization was rejected for this snapshot because the honest
  three-word frame is simpler and changing it would cause a large correctness/accounting rewrite.
- B found no correctness defect after adversarially checking loops, parallel identity, pop
  rotation, exact coverage, edgeless behavior, and the exact uses of `heven` and `hconn`. B's optional
  suggestion to instantiate the universal theorem through concrete `heven/hconn` in a stress case
  was not adopted: every fixture already has an independent six-clause decoded certificate and the
  universal implication itself is kernel-checked; this would add test proof duplication.
- C found two timed-call-graph under-ticks. First, step fuel `2m+2` was formed by raw additions even
  though dart fuel `2m` had been charged. Accepted: a second `Event.indexAdd` now forms step fuel.
  The repair also tightened it to the exact potential `2m+1`, changed the termination premise from
  strict to non-strict, and thereby stays below the frozen word bound and avoids the old final
  redundant empty-stack check. The net fixture totals are unchanged: `indexOp` rises by one and
  `stackControl` falls by one. Second, the bounds-false scan branch reconstructed `dartFuel+1`
  without a tick. Accepted: `scanBucket` retains the original `fuel` argument and returns that word
  unchanged. C otherwise confirmed every incidence/endpoint/cursor/used/stack/output event, the
  global `I` scan bound, all coefficient algebra, order independence, and absence of hidden
  traversals. The public conservative bound changes only `indexOp ... +3` to `... +4`, hence
  `c0=51`; `C=57` remains.
- D found no high-severity issue. D identified the repeated spelling of push/pop record transitions
  across algorithm, correctness, and resource files as the main maintenance risk and suggested
  future pure transition helpers or a proof-only stack-state refactor. Rejected for this one repair
  round because it would broadly perturb stable proofs without changing the frozen result. Accepted
  the low-risk suggestion that `Audit.lean` import `Correctness` and `Resource` directly instead of
  the entire stress suite. Suggestions to add a post-freeze semantic-bridge file, deduplicate all
  fixture proofs, and remove unused convenience lemmas were deferred as nonessential cleanup.

Finding classification: the pointer omission is a representation-accounting defect (C); both raw
fuel arithmetic sites are resource-accounting defects (E); repeated transitions and fixture
boilerplate are maintainability findings (B); no correctness defect, foundation defect, or
blindness/protocol-scope violation remained after repair. This was the only repair/optimization
round.

## Reproduction and final status

Commands used (from the worktree root) are:

```sh
shasum -a 256 -c Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256
find GraphLib -type f -name '*.lean' -print0 | sort -z \
  | xargs -0 shasum -a 256 | shasum -a 256
shasum -a 256 -c Benchmarks/Hierholzer/GraphLib/REPRESENTATION_MANIFEST.sha256
lake env lean Benchmarks/Hierholzer/GraphLib/Adapter.lean
lake env lean Benchmarks/Hierholzer/GraphLib/Representation.lean
lake env lean Benchmarks/Hierholzer/GraphLib/Algorithm.lean
lake env lean Benchmarks/Hierholzer/GraphLib/Correctness.lean
lake env lean Benchmarks/Hierholzer/GraphLib/Resource.lean
lake env lean Benchmarks/Hierholzer/GraphLib/Stress.lean
lake env lean Benchmarks/Hierholzer/GraphLib.lean
lake env lean Benchmarks/Hierholzer/GraphLib/Audit.lean
git diff --check
rg -n -w -g '*.lean' 'sorry|admit' Benchmarks/Hierholzer/GraphLib Benchmarks/Hierholzer/GraphLib.lean
rg -n -g '*.lean' 'TimeM\.tick|✓' Benchmarks/Hierholzer/GraphLib Benchmarks/Hierholzer/GraphLib.lean
rg -n -g '*.lean' 'Mathlib\.Combinatorics\.(Graph|SimpleGraph)' Benchmarks/Hierholzer/GraphLib \
  Benchmarks/Hierholzer/GraphLib.lean
```

All Lean modules and stress evaluations passed. Manifest checks passed. The three forbidden-source
audits and `git diff --check` returned no findings. A clean isolated-artifact rebuild compiled
Common, all seven GraphLib modules, the umbrella, and the audit in dependency order under
`/private/tmp/hierholzer-graphlib-final.PKjaqX`; it passed with linter warnings only. Final
commit/diff statistics are recorded with the preserved first-green snapshot.
