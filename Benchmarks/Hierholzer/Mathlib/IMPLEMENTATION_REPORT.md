# Mathlib-side blind Hierholzer implementation report

## Status and frozen inputs

This is the blind Mathlib-side first attempt. It was developed without reading or searching the
GraphLib source tree, the other benchmark side, its worktree, history, artifacts, or report.

- Frozen repository/base commit used for this worktree:
  `1b5c9f94e7cc660df254626555463ab8b2da791c`.
- Frozen Mathlib commit from the protocol: `d802ffd29db1f5dc5a29206b1a8af62bfcc234a3`.
- Frozen CSLib commit from the protocol: `608cbe1b629a276abd3f2081f9b42dc766d8fd78`.
- Lean: `4.30.0-rc2`, protocol commit
  `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- The Common manifest was checked with
  `shasum -a 256 -c Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256`; every entry was `OK`.
- The first-green source commit is the commit containing this report. A Git object cannot contain
  its own hash; the exact resulting object ID is recorded in the run handoff immediately after the
  commit is created.

## Delivered files

- `Benchmarks/Hierholzer/Mathlib.lean`: public umbrella.
- `Mathlib/Adapter.lean`: frozen semantic adapter.
- `Mathlib/Representation.lean`: frozen certified representation, footprint, and existence.
- `Mathlib/REPRESENTATION_FREEZE.md` and `REPRESENTATION_MANIFEST.sha256`: pre-core freeze.
- `Mathlib/Core.lean`: timed executable Hierholzer core.
- `Mathlib/Counting.lean`: exact two-dart counting.
- `Mathlib/Dense.lean`: dense/mathematical semantic and degree bridges.
- `Mathlib/Trail.lean`: dense trails and parity lemmas.
- `Mathlib/Correctness.lean`: state invariant and executable-loop proof.
- `Mathlib/Certificate.lean`: common certificate and public theorems.
- `Mathlib/Resource.lean`: fourteen-component and scalar time bounds.
- `Mathlib/Space.lean`: logical auxiliary-space theorem.
- `Mathlib/Word.lean`: bounded-word and sentinel obligations.
- `Mathlib/Stress.lean`: seven supplied-representation executable stress cases.

No foundation, Common, package, or project-configuration file was changed.

## Mathematical adapter

For `G : Graph α ε`, the adapter is literal:

- `Vertex G := {x // x ∈ V(G)}` and `Edge G := {e // e ∈ E(G)}`;
- `Link G e x y := G.IsLink e.1 x.1 y.1`;
- `Inc G e x := ∃ y, Link G e x y`;
- `Loop G e x := Link G e x x`;
- `degree G x := ncard {e | Inc G e x} + ncard {e | Loop G e x}`;
- `Step G x y := ∃ e, Link G e x y`;
- `Reachable G := Relation.ReflTransGen (Step G)`.

Thus loops contribute two and parallel mathematical edge values remain distinct. The adapter adds
no ambient `Fintype`, `DecidableEq`, `BEq`, or hashing assumption.

## Certified representation and construction

`CertifiedIncidenceRepresentation G` stores `n`, `m`, equivalences
`Fin n ≃ Vertex G` and `Fin m ≃ Edge G`, an `m`-entry endpoint vector, and an `n`-entry vector of
incidence arrays. A `Dart m` stores an edge ID and a Boolean endpoint role. Its laws are:

1. both decode maps are bijections, covering isolated vertices and every actual edge;
2. each endpoint pair decodes to a mathematical `Link`;
3. every bucket has no duplicate dart value;
4. membership is exactly `Dart.vertex ends d = x`;
5. consequently every edge has exactly its role-0 and role-1 darts and no others;
6. the two role values remain distinct for a loop in one bucket.

The order of a bucket is unconstrained, and no start, parity/reachability proof, successor schedule,
used-edge order, splice schedule, or output advice is stored.

The mandatory theorem is:

```lean
theorem representation_exists
    (G : Graph α ε) [Finite (Vertex G)] [Finite (Edge G)] :
    Nonempty (CertifiedIncidenceRepresentation G)
```

`RepresentationConstruction.build` is total but noncomputable. It chooses finite equivalences and
one endpoint pair per mathematical edge, then filters all canonical darts into each bucket. It is
not claimed as executable or linear preprocessing and has no cost theorem. `Stress.supplied` is a
computable constructor from explicit endpoint vectors and buckets once the certification proofs are
supplied; it is used by all smoke tests.

The mathematical-start lookup is `R.decodeVertex.symm`, exposed as noncomputable `encodeVertex`.
It is outside the primary runtime, has no lookup-cost theorem, and is not presented as an
end-to-end executable entry point. The timed entry point takes the dense start ID directly.

### Frozen representation hash and footprint

The post-freeze hashes still validate:

```text
799a74de2530156dfc47d3e8531a69494182caedaa872aa47a51a9c00f23843a  Representation.lean
67f137cd2e691dbe36b3f0b38fab0009f3eaf1e41fd5a3da2350010e2b58bee7  Adapter.lean
```

The logical footprint is defined and proved as

```text
repWords R = 5 + 2*n + 2*m + 2*I
repWords R ≤ repR0 + repRV*n + repRE*m + repRI*I
(repR0, repRV, repRE, repRI) = (5, 2, 2, 2).
```

The constant covers one top-level record word, the two sizes, and one embedded top-level container
handle/header word each for `ends` and `buckets`; `2n` covers a bucket-vector slot/reference plus
one separately allocated inner-array header per vertex, `2m` the endpoint pairs, and `2I` the
two-word darts. This is the frozen logical layout, not a claim about arbitrary Lean closure/object
layout. Proofs and mathematical decode equivalences are excluded explicitly by the protocol and
are not used by the timed core. Using `I = 2m`, this is exactly `5 + 2n + 6m`.

Arrays-of-arrays were chosen over CSR because they need no offset table or preprocessing theorem,
and over lists because a cursor into a list would require repeated traversal. A dense matrix was
rejected as superlinear. Executing directly on `Graph` was rejected because the frozen multigraph
API has no executable finite incidence enumeration and endpoint choice is noncomputable.

## Algorithm

`hierholzer R start : TimeM Cost (IndexedTour R.n R.m)` is the standard stack/backtracking
algorithm. State consists of one used flag per actual edge, one cursor per vertex bucket, a stack of
two-word `(incoming edge?, vertex)` frames, and a list of two-word canonical output steps.

At a stack top it scans the next dart. A previously used actual edge advances only the cursor. A new
edge marks its single edge flag, reads its endpoints, and pushes the opposite endpoint. When a
bucket is exhausted, it pops; a non-bottom frame is consed to output. Pop order plus cons produces
traversal order directly, so there is no untimed reverse, append, copied output buffer, endpoint
reconstruction, or post-clock traversal. The fuel values are `2m` scans and `m+1` pops, and the
representation theorem proves `2m = I`.

The central `RunInvariant` has eleven normalized atomic obligations: cursor bounds; scanned-prefix
usedness; stack-path shape; splice decomposition; edge-ID nodup across stack and output; exact
used-flag correspondence; output-vertex exhaustion; empty-stack start exhaustion; empty-stack
closed trail; scan balance; and pop balance. The even-degree trail-parity lemma proves that an
exhausted top can be popped at the current splice anchor. Connectivity is used only after the loop,
to show every actual edge lies at a reached/exhausted vertex and is therefore present in output.

## Correctness and bridge route

The exact public theorem is:

```lean
theorem CertifiedIncidenceRepresentation.hierholzer_correct
    [Finite (Vertex G)] [Finite (Edge G)]
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (heven : ∀ x : Vertex G, Even (degree G x))
    (hconn : ∀ x : Vertex G,
      (∃ e : Edge G, Inc G e x) → Reachable G s x) :
    ValidEulerTour (Link G) s
      (R.decodeTour (hierholzer R (R.encodeVertex s)).ret)
```

It proves all six Common fields: length relation, start, finish, positional links, actual-edge
`Nodup`, and complete coverage. It is accompanied by `hierholzer_edgeless`,
`hierholzer_exact_lengths`, and `hierholzer_positive_edge_circuit` with exactly the frozen
assumptions.

The main representation/graph bridges are `link_decode_iff`, `inc_decode_iff`, `loop_decode_iff`,
`degree_decode_eq_bucket_size`, `incidenceCount_eq_sum_degree`, and
`sum_degree_eq_two_mul_edgeCount`. Counting bridges are `bucket_size_eq_dartFiber_card`,
`fintype_card_dart`, and `incidenceCount_eq_two_mul_m`; cardinality bridges are
`n_eq_vertexCount` and `m_eq_edgeCount`. Output bridges are `DenseTrail.decodedLinks`,
`validEulerTour_of_dense`, `reachable_dense`, and `RunInvariant.final_edge_complete`.

Under the blind-run normalization, there are six conceptual representation obligations, eleven
algorithm-state invariant obligations, fifteen principal representation/output bridge lemmas,
eight graph-specific adapter/counting lemmas, and the remaining support lemmas are generic dense
array/list/trail or algorithm-specific facts. These counts describe concepts rather than exploiting
declaration splitting; the common Step-4 codebook may refine line attribution later.

Mathlib APIs that materially helped were multigraph `Graph.IsLink` symmetry and endpoint facts,
edge-membership-to-link existence, `Finite.equivFin`, `Nat.card_congr`, `Set.ncard`, finite-set
cardinality identities, `Relation.ReflTransGen`, and generic `Vector`, `Array`, `List`, and `Finset`
lemmas. The frozen multigraph namespace supplied no reusable finite incidence view, loop-corrected
degree, handshaking theorem, edge-aware walk/trail/circuit, reachability, or Euler theorem. Those
gaps required benchmark-local declarations; no `SimpleGraph` API was used.

## Time model and complete tick audit

The transitive timed call graph is `hierholzer → initState/chargeInitWords → run`, plus only frozen
Common event wrappers.

- `chargeInitWords`: one `initWrite` per initialized flag/cursor word.
- `initState`: `m+n` initialization events and one two-word bottom-frame push.
- `hierholzer`: one `indexAdd` for `2m`, one `indexSucc` for `m+1`, the loop, then one
  `outputStoreStart`.
- Every `run` call: one stack availability check.
- Nonempty stack: one two-word peek, one outer bucket-slot read, one bucket-length read, one cursor
  read, and one index comparison.
- Present dart: two incidence reads for edge ID and role; one cursor increment and one cursor write;
  one used read. A new edge additionally has one used write, two endpoint reads, and one two-word
  stack push. A used edge has no endpoint or push event.
- Exhausted bucket: one two-word pop. A non-bottom frame additionally emits one output cell and two
  output payload words.
- The final indexed start costs one output word. No output step is read or copied and no reverse is
  performed.

No side-specific timed function directly calls `TimeM.tick`, uses `✓`, or constructs nonzero
`TimeM`. Dense `Vector`/`Array` access and linearly threaded `Vector.set` are assumed constant-time
word-RAM primitives. Lean persistent-array copying under arbitrary sharing is not verified; the
state is used linearly. List cons is the fixed output/stack allocation primitive, never a resizable
buffer. Ambient mathematical equality/hashing and `Finset` operations are absent from the hot loop.

The complete frozen primitive table used by that audit is:

| Primitive | Counter and price |
| --- | --- |
| initialize one algorithm word | `initWrite += 1` |
| read one incidence/offset word | `incidenceRead += 1` |
| read one endpoint ID | `endpointRead += 1` |
| read/write one used flag | `usedRead += 1` / `usedWrite += 1` |
| read/write one cursor | `cursorRead += 1` / `cursorWrite += 1` |
| bounded compare/increment/add | `indexOp += 1` |
| stack check/push/peek/pop request | `stackControl += 1` |
| read/write one stack payload word | `stackRead += 1` / `stackWrite += 1` |
| emit/visit one output cell | `outputControl += 1` |
| read/write one output payload word | `outputRead += 1` / `outputWrite += 1` |
| function call, projection, pattern dispatch, proof-only decode | zero |

At `Core.run`'s bucket access, the returned Boolean from `Event.indexLt cursor bucketSize` is not
used as a control value; its one `indexOp` is the explicit abstract charge for the bounds test
performed by the immediately following `bucket[cursor]?`. The actual option branch and the charge
therefore correspond one-for-one, although the frozen manual ledger does not enforce that
correspondence structurally. Fuel `Nat` pattern dispatch is zero-cost under the last table row.

The unconditional fourteen-field theorem `hierholzer_bounds` is, in field order:

```text
initWrite      ≤ n + m
incidenceRead  ≤ 4I + 2m + 4
endpointRead   ≤ 2I
usedRead       ≤ I
usedWrite      ≤ I
cursorRead     ≤ I + m + 2
cursorWrite    ≤ I
indexOp        ≤ 2I + m + 4
stackControl   ≤ 3I + 3m + 6
stackRead      ≤ 2I + 4m + 6
stackWrite     ≤ 2I + 2
outputControl  ≤ m + 1
outputRead      = 0
outputWrite    ≤ 2m + 3.
```

The concrete scalar constants are

```text
(c0, cV, cE, cI) = (28, 1, 15, 19)
total time ≤ 28 + n + 15m + 19I.
```

`incidenceCount_eq_two_mul_m` partitions all canonical darts by their unique bucket and uses
`Dart m ≃ Fin m × Bool`; hence `I = 2m`. `degree_decode_eq_bucket_size` separately transports the
adapter's incidence-plus-loop cardinality to the same buckets, giving
`I = Σ_v degree_G(v) = 2m`. Substitution yields

```text
total time ≤ 28 + n + 53m
total time ≤ 53 * (n + m + 1),    linearC = 53.
```

The word-width assumption is
`w ≥ max 1 (ceil(log2(n + I + 1)))`. Replacing each word operation by its conservative bit cost
immediately gives `O((n+m+1) log(n+m+1))`; this is secondary to the proved unit-cost theorem.
`Word.lean` formalizes the missing arithmetic side: `wordCapacity = n + I + 1`, the optional
incoming-edge encoding uses IDs `0,...,m-1` and sentinel `m`, and theorems prove that every vertex
ID, edge ID/sentinel, initial fuel, invariant scan/pop fuel, and invariant cursor lies strictly
below `wordCapacity`. `lt_two_pow_of_lt_wordCapacity` transports each result through the protocol
assumption `wordCapacity ≤ 2^w`.

## Space accounting

`auxiliaryWords` counts five current-state/container headers, `m` flags, `n` cursors, three words
per stack list cell (two payload plus one structural word), and three per output cell. For every
state satisfying the executable invariant, `StackPath.stack_length_eq`, global edge `Nodup`, and
the combined-edge cardinality prove

```text
stack.length ≤ m + 1
output.length ≤ m
stack.length + output.length ≤ m + 1
auxiliaryWords state ≤ n + 4m + 8.
```

This is a machine-checked peak logical-state bound for invariant states under the linearly threaded
RAM model. Adding the reduced representation gives `13 + 3n + 10m`; adding two conservative words
for the transient indexed-result header/start gives the clearly labeled normalized combined peak
estimate `15 + 3n + 10m`. The latter combined estimate is not a separate Lean theorem, and output
steps are shared rather than copied.

## Executable stress results

The tuple order below is the frozen fourteen-field order. Every supplied representation proves its
bucket laws, its expected incidence count, the returned indexed result, a decoded
`ValidEulerTour`, and the concrete componentwise bound. All seven bound evaluations printed
`true`.

| Case | Traversal-ordered steps `(edge,destination)` | Cost vector |
| --- | --- | --- |
| one vertex, no edges | `[]` | `(1,2,0,0,0,1,0,3,5,4,2,0,0,1)` |
| one loop | `[(0,0)]` | `(2,12,2,2,1,4,2,8,13,12,4,1,0,3)` |
| two distinct loops | `[(0,0),(1,0)]` | `(3,22,4,4,2,7,4,13,21,20,6,2,0,5)` |
| two parallel actual edges | `[(0,1),(1,0)]` | `(4,22,4,4,2,7,4,13,21,20,6,2,0,5)` |
| parallel component plus isolate | `[(0,1),(1,0)]` | `(5,22,4,4,2,7,4,13,21,20,6,2,0,5)` |
| triangle | `[(0,1),(1,2),(2,0)]` | `(6,32,6,6,3,10,6,18,29,28,8,3,0,7)` |
| four distinct parallel identities | `[(0,1),(1,0),(2,1),(3,0)]` | `(6,42,8,8,4,13,8,23,37,36,10,4,0,9)` |

The last case uses four different Mathlib edge values with identical endpoints, so endpoint
adjacency cannot accidentally stand in for edge identity. Loop cases have two darts per loop but
one used flag and one output occurrence.

## Noncomputability, assumptions, and axioms

Noncomputability occurs in adapter `degree` (`Set.ncard`), official cardinalities, inverse
mathematical-to-dense lookup, and the total representation construction (finite enumeration,
endpoint choice, and bucket filtering). It is construction/specification/proof-side only. The core,
explicit supplied constructor, dense operations, tests, and cost evaluation are computable.

The public theorem has two typeclass premises, exactly `[Finite (Vertex G)]` and
`[Finite (Edge G)]`, plus the explicit representation, start, evenness, and edge-bearing
connectivity premises. No ambient equality or hashing premise is added. Dense `Fin`/`Bool` equality
is used internally and in tests.

`#print axioms` for `representation_exists`, `incidenceCount_eq_sum_degree`,
`incidenceCount_eq_two_mul_m`, `hierholzer_correct`, `hierholzer_bounds`,
`hierholzer_linear_math`, and `RunInvariant.auxiliaryWords_le` uniformly reported only:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorry` or `admit`.

## Engineering observations and failed approaches

- A proof directly mirroring the large timed recursion produced expensive proof terms. The final
  architecture proves the semantic recursion and reconnects it to the identically branching timed
  implementation with `run_ret_eq_logicalRun`. That bridge requires unlimited heartbeats locally
  and a clean compile of `Correctness.lean` took roughly four minutes in this run. This is generic
  recursive-proof/compiler friction, not algorithm runtime.
- Whole-certificate `native_decide` on decoded stress tours selected a noncomputable unrelated
  instance through imported Mathlib and could not compile. The tests now compute the exact indexed
  output, construct a dense trail with explicit edge identities, and invoke
  `validEulerTour_of_dense`. No semantic requirement was weakened.
- Named `Fin` constants were needed in closed tests because numeral instance synthesis did not
  unfold representation-size definitions early enough. This is test elaboration only.
- No representation attempt was abandoned after the pre-core freeze, and no executable field was
  added after it.

Proofs use `simp`, `omega`, `aesop`, finite cardinality automation, and `native_decide` for closed
computable examples. The invariant proof is the most refactor-sensitive part; changes to the exact
recursive branch shape require updating both semantic and timed value bridges.

## Friction classification

| Label | Primary items |
| --- | --- |
| A — unavoidable algorithm/graph theory | stack/splice invariant, parity-at-pop, coverage from connectivity, edge identity and loop reasoning |
| B — generic Lean/data structures | vector update/get lemmas, list decomposition, finite-cardinality transports, recursive value-bridge elaboration, closed `Fin` constants |
| C — mathematical/executable bridge | endpoint/link, incidence, loop, degree-to-bucket, dense reachability, and decoded-tour correspondence |
| D — missing graph API | no general-multigraph finite incidence view, loop-corrected degree/handshaking, reachability, or edge-aware walk/trail/circuit API |
| E — time framework | manual wrapper audit, fourteen-field recurrences, fuel-to-incidence rewrite, word-RAM/persistent-array trust statement |

The categories are primary attributions: A, B, and E are not attributed to the graph foundation.
No foundation change or upstream patch was made or proposed during this first attempt.

## Source metrics

At the complete post-review green state the delivered Lean files contain 2,594 raw physical lines.
A disclosed simple block/line-comment and blank-line filter counts 2,159 nonblank, non-comment
physical lines; a theorem-header-through-`:=` scan counts 340 theorem-statement lines. The dominant
declaration attribution is: executable representation/construction 120; representation bridges
218; algorithm core 133; functional correctness 1,092; time analysis 160; generic data/space and
word/umbrella support 143; graph-specific adapter 43; tests/examples 250. These sum to 2,159. This is the
blind-run classification; Step 4 may reclassify declarations with its common published codebook,
but moving declarations between files will not change the total.

The preserved-scope staged diff/stat was recorded before commit: 16 new files, 3,108 inserted
physical lines, and zero deletions. Per-file additions were: umbrella 9, Adapter 68, Certificate
264, Core 172, Correctness 804, Counting 69, Dense 168, this report 437,
REPRESENTATION_FREEZE 75, representation manifest 2, Representation 222, Resource 188, Space 79,
Stress 281, Trail 157, and Word 113. Only these Mathlib-side benchmark paths are staged.

## Review and repair disposition

Exactly four independent read-only reviews were run after the first complete implementation built.
All were instructed not to inspect the other benchmark side.

- **A, representation/architecture:** confirmed the exact dart laws, loop/parallel identity,
  absence of traversal advice, standard asymptotically optimal architecture, and unchanged freeze
  hashes. It questioned excluding the stored `Equiv` closures from footprint; this was rejected
  because the frozen protocol expressly excludes mathematical decode equivalences and the timed
  executable projection never accesses them. It also proposed a physical object-graph convention
  with two more top-level pointer words. The frozen logical convention embeds each top-level
  container handle/header in its record field but counts separately referenced inner arrays; the
  report now states that convention explicitly. No representation source or hash changed.
- **B, correctness:** adversarially checked loops, parallel identity, cursor/used invariants,
  even-degree pop closure, fuel fallback impossibility, connectivity-driven final coverage, all six
  certificate fields, and all corollaries. It tried loop, parallel, isolate, odd-path, and disconnected
  even-component counterexamples and found no correctness defect.
- **C, time/ticks:** independently reproduced every component, `(28,1,15,19)`, `I=2m`, reduced
  `53m`, and `C=53`, with no hidden traversal or order dependence. Its `indexLt/get?` audit note is
  now explicit. Its bounded-word finding was accepted by adding `Word.lean`; its space tightening
  was accepted and proved; its request for the complete primitive table was accepted above.
- **D, optimization/maintainability:** identified the duplicated branch structure of timed `run`
  and semantic `logicalRun` as the main proof-stability cost, plus broad tactic imports, repeated
  fourteen-field ledgers, positional record proofs, one duplicate dense-link induction, and public
  test-fixture exposure. These are valid future refactor opportunities but were deliberately not
  adopted in the single repair round: extracting a shared step interpreter or changing imports
  would rewrite the most sensitive verified core for no correctness/accounting gain. The risks and
  four-minute clean proof compile are already disclosed rather than hidden.

Accepted findings were classified as time-framework/accounting robustness and meaningful space
optimization. There were no accepted correctness or representation defects and no protocol
violation. This concludes the one permitted review/repair round.

## Build and audit commands

The benchmark uses explicit Lean compilation and never bare `lake build`. Principal commands are:

```sh
shasum -a 256 -c Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256
shasum -a 256 -c Benchmarks/Hierholzer/Mathlib/REPRESENTATION_MANIFEST.sha256
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Representation.olean Benchmarks/Hierholzer/Mathlib/Representation.lean
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Core.olean Benchmarks/Hierholzer/Mathlib/Core.lean
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Correctness.olean Benchmarks/Hierholzer/Mathlib/Correctness.lean
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Certificate.olean Benchmarks/Hierholzer/Mathlib/Certificate.lean
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Resource.olean Benchmarks/Hierholzer/Mathlib/Resource.lean
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Space.olean Benchmarks/Hierholzer/Mathlib/Space.lean
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Word.olean Benchmarks/Hierholzer/Mathlib/Word.lean
lake env lean -o .lake/build/lib/lean/Benchmarks/Hierholzer/Mathlib/Stress.olean Benchmarks/Hierholzer/Mathlib/Stress.lean
lake env lean Benchmarks/Hierholzer/Mathlib.lean
git diff --check -- Benchmarks/Hierholzer/Mathlib Benchmarks/Hierholzer/Mathlib.lean
rg -n -g '*.lean' '\b(sorry|admit)\b|TimeM\.tick|✓' Benchmarks/Hierholzer/Mathlib Benchmarks/Hierholzer/Mathlib.lean
```

The complete umbrella build and all seven executable tests are green. A final clean ordered compile,
hash/audit pass, diff/stat, LOC capture, and local first-green commit follow this report update.
