# Frozen benchmark protocol: Hierholzer formalization

- **Status:** frozen for Steps 2 and 3
- **Freeze date:** 2026-08-16
- **Benchmark:** finite undirected multigraphs, with loops and parallel edges
- **Compared foundations:** the current GraphLib working tree and the pinned Mathlib `Graph`

## 1. Executive summary

This benchmark asks whether GraphLib's algorithm-oriented mathematical graph foundation reduces
the representation and proof burden of a verified linear-time Hierholzer development relative to
Mathlib's current multigraph foundation. It does **not** assume that an efficient algorithm should
execute directly on either mathematical graph object.

The protocol freezes the following choices.

1. Both sides use finite undirected multigraphs with actual edge identity. Loops and parallel edges
   are mandatory.
2. Both sides prove the same semantic result: a closed edge-aware tour starting at a supplied
   vertex, using every actual edge exactly once. The primary certificate permits the unique
   zero-edge tour `[s]`. Native-library adapters are optional secondary results and cannot change
   the primary score.
3. Both sides may use their best benchmark-local executable representation. The primary runtime
   starts from a certified dense, edge-indexed incidence representation. Every mathematical edge
   has exactly two incidence occurrences ("darts"), including two occurrences of a loop.
4. Construction of that representation is outside the primary algorithm time on both sides. Its
   computability, proof burden, code size, and any proved construction cost are reported separately.
5. Runtime is an explicitly annotated **abstract RAM resource theorem**, not a theorem about Lean's
   evaluator or generated native code. `Cslib.Algorithms.Lean.TimeM` is used with a small vector of
   primitive-operation counters and a scalar projection. Ticks remain manual and therefore require
   a mandatory tick audit.
6. The primary concrete theorem exposes the constants and the total incidence size. A second
   theorem uses the incidence/degree sum `I = 2m` to obtain an explicit pointwise linear bound in
   `n + m`. Bare `IsBigO` claims are not sufficient.
7. Neither graph foundation may be modified during the first implementation attempt. Local bridge
   lemmas are allowed and measured. Missing foundation APIs are recorded rather than silently
   upstreamed.

The protocol is deliberately neutral. A win may consist of fewer bridge invariants, better native
walk/degree support, a more executable mathematical representation, or simply a smaller and more
stable development. Noncomputability and raw line count are not wins by themselves.

## 2. Scientific/design question

The controlled question is:

> Once both mathematical graph specifications are allowed the same standard executable incidence
> representation, how much graph-specific representation and proof burden remains in a complete
> Hierholzer correctness and abstract-RAM linear-time development?

This separates two claims that are often conflated in the discussion around
[CSLib PR #503](https://github.com/leanprover/cslib/pull/503):

- an algorithm need not execute directly on a mathematical graph specification; and
- an algorithm-oriented specification may still reduce the work needed to construct, relate, and
  reason about the executable representation and its output.

[PR #804](https://github.com/leanprover/cslib/pull/804) and
[PR #805](https://github.com/leanprover/cslib/pull/805) establish viable separation patterns for
DFS. They are evidence, not benchmark prescriptions. Their adjacency-only correspondence is too
weak for this benchmark: Hierholzer must preserve mathematical edge identity and must pair the two
incidence occurrences belonging to one undirected edge.

## 3. Non-goals

Steps 2 and 3 need not:

- prove the converse Euler characterization or a full iff theorem;
- implement graph construction from every mathematical `Set` presentation;
- prove a cost semantics for Lean bytecode, C code, garbage collection, or cache behavior;
- optimize constant factors for a particular machine;
- develop a general-purpose graph algorithm framework;
- extend either underlying graph foundation;
- eliminate classical reasoning from specification-only proofs;
- benchmark `SimpleGraph`, directed graphs, or loopless graphs as substitutes;
- use mathematical graph deletion as the hot executable state; or
- prove preprocessing is linear unless the chosen constructor and its assumptions make that claim
  meaningful.

No Hierholzer implementation belongs in this protocol task.

The later timed core must nevertheless be recognizably Hierholzer: it grows a trail through unused
incident actual edges and performs the standard stack backtracking or equivalent closed-tour
splicing. A search over candidate edge permutations, an invocation of a nonconstructive existence
theorem, or an unrelated Euler-tour algorithm is not an admissible implementation even if it meets
the extensional output predicate.

## 4. Frozen versions and repository state

Later tasks must use the following state unless a blocking bug forces a documented, symmetric
restart.

| Item | Frozen value |
| --- | --- |
| Repository | `yzll0/GraphAlgorithms_wx`, branch `upstream-main` |
| Repository `HEAD` | `d4dbdf45b2420750e55eb7caf529265a2bfff11f` |
| GraphLib state | dirty working-tree GraphLib snapshot described below |
| GraphLib source-manifest SHA-256 | `3ec806b9b96ce6b079c12fbeb930556937b36c1a6e21d92a70d190bf5d80c894` |
| GraphLib binary diff SHA-256 vs `HEAD` | `be871015f591989cd345d9e67dbe83fbe6b5daf485d9fdd82079d38ddaedefec` |
| Mathlib commit | `d802ffd29db1f5dc5a29206b1a8af62bfcc234a3` |
| CSLib commit | `608cbe1b629a276abd3f2081f9b42dc766d8fd78` |
| Lean | `4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` |
| `TimeM.lean` SHA-256 | `b58d42bb8ba3345c5ab52701f8f4d77dae557b096b79d326ccda4fa4ffd3dcf6` |
| `MergeSort.lean` SHA-256 | `3cfa73d2da202625935d3a15391cf548d1466b8b2b231443dcbee38f60e9a72a` |
| CSLib PR #503 head at freeze | `e0a79a4796fb066153f9864c529c3f6331312bbb` |
| CSLib PR #804 head at freeze | `85accb059257afb668c7aa5dc0664a64c1c5c328` |
| CSLib PR #805 head at freeze | `2e1ef82e19663c44250b400289c3d3c48c3d5a7c` |

The GraphLib snapshot is intentionally newer than `HEAD`: 24 tracked `GraphLib/**/*.lean` files
have working-tree changes. To verify the source-manifest digest, from the repository root run:

```sh
find GraphLib -type f -name '*.lean' -print0 | sort -z \
  | xargs -0 shasum -a 256 | shasum -a 256
```

The binary-diff digest is from:

```sh
git diff --binary HEAD -- GraphLib | shasum -a 256
```

The current Mathlib and CSLib package checkouts are clean. If the GraphLib worktree is committed
before Step 2, the implementation report must record the new commit and confirm that the manifest
digest above is unchanged. Any changed digest invalidates the frozen comparison unless both sides
restart on the same documented protocol revision.

## 5. Exact graph class and common semantic adapter

The GraphLib mathematical input is:

```lean
G : GraphLib.Graph α β
```

Its actual edges are values of `GraphLib.Edge α β`, and `E(G)` is a set of those full bundled
values. A tag alone is never an edge identity.

The Mathlib mathematical input is:

```lean
G : Graph α ε
```

Its actual edges are the values of `ε` in `E(G)`, and `G.IsLink e u v` supplies incidence.

For the shared contract, each side defines a thin benchmark-local semantic adapter with the
following meanings:

- `V_G := {v // v ∈ V(G)}`;
- `E_G := {e // e ∈ E(G)}`;
- `Link_G (e : E_G) (u v : V_G)` is the library's actual-edge link relation;
- `Inc_G e v := ∃ w, Link_G e v w`;
- `Loop_G e v := Link_G e v v`;
- `degree_G v := ncard {e : E_G | Inc_G e v} + ncard {e : E_G | Loop_G e v}`;
- `Step_G u v := ∃ e : E_G, Link_G e u v`; and
- `Reachable_G := Relation.ReflTransGen Step_G`.

The two `ncard` terms intentionally make a loop contribute two and a nonloop incident edge one.
Parallel actual edges are separate subtype values and are counted separately. GraphLib may prove
this adapter degree equal to `Graph.degree`; Mathlib must define the corresponding local degree
because the frozen multigraph API has no degree module.

The finiteness assumptions are exactly:

```lean
[Finite V_G] [Finite E_G]
```

Finite vertices do not imply finite edges. No ambient `[Fintype α]`, `[Fintype β]`, or
`[Fintype ε]` assumption may be added to the primary theorem. An executable representation may
carry dense enumerations, as specified below.

The official benchmark sizes are literally the same quantities on both sides:

```text
n := Set.ncard V(G)
m := Set.ncard E(G)
```

A local classical or representation-supplied `Fintype` may be used in proofs, but its cardinality
must be proved equal to these `n` and `m`; that equality is not part of the definition of the
benchmark sizes. Likewise, the sizes of `R`'s dense `Fin` index types must be proved equal to
`n` and `m`.

For GraphLib, `m` counts bundled `Edge α β` values, never tags and never the lossy endpoint-pair
image. For Mathlib, it counts members of the mathematical edge set, never adjacency-list entries.

## 6. Exact input and output specification

### Mathematical and executable input

The public correctness theorem takes:

- a mathematical graph `G` of the appropriate side;
- a certified executable representation `R` representing exactly `G`;
- a starting mathematical vertex `s : V_G`; and
- the Eulerian hypotheses in Section 7.

The timed core takes `R` and the dense index `R.encodeVertex s`. The correctness theorem decodes
the returned indexed data through `R`. Computing `encodeVertex s` is outside the core clock, just
like representation construction. Each report must state whether that lookup is executable, its
data-structure assumptions, and any proved or measured cost; a noncomputable lookup may not be
presented as an end-to-end executable entry point.

The transitive timed core must be computable: it may not contain `Classical.choose`, `Quot.out`, an
opaque noncomputable endpoint selection, or a noncomputable finite enumeration. Classical reasoning
is permitted in representation existence/bridge proofs and in proof-only decoding.

### Common output certificate

Both sides expose the same logical certificate shape, called `TourData` here:

```lean
structure TourData (V E : Type*) where
  vertices : List V
  edges    : List E
```

The executable core has one canonical indexed result shape:

```lean
structure IndexedTour (n m : Nat) where
  start : Fin n
  steps : List (Fin m × Fin n)
```

Its public executable type is exactly
`hierholzer (R : CertifiedIncidenceRepresentation G) (start : Fin n) :
TimeM Cost (IndexedTour n m)`. Internal state may be threaded through helpers, but a certified
public input does not return `Option` or an error sum.

A step `(e,v)` means “traverse edge `e` to next vertex `v`.” The list is already in traversal
order. `R.decodeTour` is fixed extensionally: its vertex list is `decodeVertex start` followed by
the pointwise `decodeVertex` image of the step destinations, and its edge list is the pointwise
`decodeEdge` image of the step edge IDs. It may perform no search, reordering, reversal, append,
unzipping into an executable second buffer, or endpoint reconstruction. These maps may remain
logical views in the correctness theorem; any executable materialization is charged under
Section 12.

The exact primary predicate `ValidEulerTour Link_G s t` is the conjunction of:

1. `t.vertices.length = t.edges.length + 1`;
2. `t.vertices.head? = some s`;
3. `t.vertices.getLast? = some s`;
4. for every `i < t.edges.length`,
   `Link_G t.edges[i] t.vertices[i] t.vertices[i+1]`;
5. `t.edges.Nodup`; and
6. `∀ e : E_G, e ∈ t.edges`.

Because vertices and edges are subtypes of the mathematical sets, no outside vertex or edge can
appear. Conditions 5 and 6 say that every actual edge occurs exactly once. Conditions 1 and 4
preserve edge identity and its position in the walk rather than merely comparing endpoint pairs.

The Lean spelling may use `get`, `getElem`, `List.Pairwise`, a zipped list, or an equivalent
`Forall₂` formulation. The six semantic clauses above may not be weakened.

The executable result remains indexed in the canonical shape above. Its decoder yields
`TourData V_G E_G` by pointwise relabeling only; decoding may be a logical map rather than a
separately allocated runtime value. Any executable materialization of decoded output is governed
by Section 12.

## 7. Exact Eulerian preconditions

For every input, both implementations assume exactly:

```text
Hstart : s is an actual vertex (enforced by s : V_G)
Heven  : ∀ v : V_G, Even (degree_G v)
Hconn  : ∀ v : V_G, (∃ e : E_G, Inc_G e v) → Reachable_G s v
```

`Hconn` says that every non-isolated vertex is in the component of `s`. It deliberately does not
require isolated vertices to be mutually reachable. It is therefore weaker and more textbook-like
than GraphLib's current `Graph.Connected`, which requires every graph vertex to be connected.

No nonempty-edge assumption is made. If `m > 0`, `Hconn` implies that `s` is in the unique
edge-bearing component. If `m = 0`, any supplied `s : V_G` is valid. A graph with an empty vertex
set has no possible start and is outside this start-indexed function's domain.

Later implementations may prove stronger intermediate lemmas, but the public theorem may not
replace `Hconn` with full connectedness or replace loop-counting degree with incidence-set cardinality
alone.

## 8. Exact correctness theorem target

Each side must prove a theorem with the following schema, modulo namespaces and its graph type:

```lean
theorem hierholzer_correct
    (G) [Finite V_G] [Finite E_G]
    (R : CertifiedIncidenceRepresentation G)
    (s : V_G)
    (heven : ∀ v : V_G, Even (degree_G v))
    (hconn : ∀ v : V_G, (∃ e : E_G, Inc_G e v) → Reachable_G s v) :
    ValidEulerTour Link_G s (R.decodeTour (hierholzer R (R.encodeVertex s)).ret)
```

The theorem is over a certified `R`, so returning an unchecked failure case or weakening the result
to a partial correctness statement is not acceptable.

The following corollaries are mandatory:

1. **Edgeless:** if `m = 0`, the decoded edge list is `[]` and the decoded vertex list is `[s]`.
2. **Length:** the decoded tour has exactly `m` edges and `m + 1` vertices.
3. **Positive-edge circuit:** if `0 < m`, the result is a positive-length closed trail using every
   actual edge exactly once.

GraphLib may additionally construct `c : GraphLib.Circuit α β` when `0 < m` and prove
`G.IsEulerianCircuitIn c`; this is a useful native-API demonstration but is not mandatory and its
LOC is reported separately from the primary score. The frozen Mathlib multigraph `Graph` API has no
native walk/trail/circuit type, so the common edge-aware certificate is its natural
benchmark-local target. Mathlib's mature `SimpleGraph.Walk` API may not be used: it removes loops
and collapses parallel edge identity.

Thus neither side owes a stronger theorem merely because its foundation exposes more native API.
The six common clauses are the primary comparison target on both sides.

## 9. Executable representation policy

### Required semantic interface

Each side may choose its layout, but `R` must expose or refine the following standard incidence
interface:

- dense vertex IDs equivalent to `Fin n` and a bijection `decodeVertex : Fin n ≃ V_G`;
- dense edge IDs equivalent to `Fin m` and a bijection `decodeEdge : Fin m ≃ E_G`;
- `ends : Fin m → Fin n × Fin n`;
- finite incidence buckets indexed by `Fin n`; and
- a dart containing an edge ID and one of its two endpoint roles.

The representation laws are mandatory:

1. **Endpoint soundness:** if `ends e = (u,v)`, then
   `Link_G (decodeEdge e) (decodeVertex u) (decodeVertex v)`.
2. **Exactly two darts:** edge `e` has precisely the role-0 dart in `u`'s bucket and the role-1
   dart in `v`'s bucket, and no other occurrences.
3. **Loops:** when `u = v`, both distinct roles occur in that same bucket. A loop is still one edge
   ID and has one used flag.
4. **No junk:** every bucket entry is one of those canonical darts for its vertex.
5. **No omission/duplication:** the decode maps are bijections onto all actual mathematical
   vertices and edges, including isolated vertices.
6. **Constant-time refinement:** the hot-loop operations listed in Section 11 are provided by the
   chosen layout with the stated abstract costs.

For every finite mathematical input, each side must also prove a total, possibly noncomputable
existence theorem:

```lean
theorem representation_exists (G) [Finite V_G] [Finite E_G] :
    Nonempty (CertifiedIncidenceRepresentation G)
```

This prevents the main theorem from being conditional on a representation that might not exist.
The theorem includes all six laws, not only endpoint adjacency. A computable constructor is a
separate, stronger result.

Consequently, with

```text
I(R) := sum over all vertex buckets of their lengths,
```

both sides must prove:

```text
I(R) = sum over v : V_G of degree_G(v) = 2m.
```

For GraphLib, actual edge IDs are full `Edge α β` bundles. A tag-only enumeration is invalid.
For Mathlib, two independently created adjacency occurrences are not two mathematical edges; they
must share one edge ID. In particular, the `AdjList.toGraph` occurrence convention in PR #804 is
not a sufficient identity bridge for this benchmark.

### Layout freedom

Allowed layouts include arrays of arrays, CSR/flat incidence arrays with offsets, lists with
per-vertex cursors, or an extension with cached endpoints and mutable flags. Both sides may use
linearly threaded or persistent arrays under the abstract RAM assumption, or a proof-oriented pure
model. The primary timed implementation may not use `ST`: the frozen `TimeM` has no costed state
transformer, and no common `ST` cost/refinement layer is part of this protocol.

The representation may contain additional redundant fields only when they are ordinary
graph-encoding or graph-access accelerators, are independent of the chosen start and Eulerian
hypothesis proofs, and all consistency invariants and costs are reported. Correctness and runtime
theorems quantify over **every** certified `R`, not a specially chosen adjacency ordering.

No representation field or law may provide solution-specific advice: a cached Euler tour, successor
or splice schedule, per-start traversal order, computational reachability/parity certificate,
precomputed used-edge order, or any equivalent encoding of an admissible output is forbidden.
Additional executable fields and their intended primitive operations must be declared and
content-hashed before the corresponding blind implementation begins its algorithm core; Step 4
rejects a late field that moves Hierholzer work across the untimed boundary.

The primary executable payload of `R` must itself be linear-sized. Each side defines a logical
word count `repWords R` and proves, with concrete numeral constants,

```text
repWords R ≤ r0 + rV*n + rE*m + rI*I.
```

Every stored dense ID, flag, role, cursor, offset, length, pointer, and payload component is one
logical word; pairs and records contribute the sum of their components, and all redundant
executable fields count. Erased proofs and the mathematical decode equivalences do not count.
Container headers and structural pointers do count under one common Step-4 counting script/codebook.
A superlinear matrix, all-pairs table, or other superlinear accelerator is allowed only as a
separately reported secondary experiment and cannot establish the primary result.

The hot loop should normally use dense IDs, used-edge Boolean storage, per-vertex cursors, a stack,
and an output buffer. It must not rely on equality or hashing of ambient mathematical vertex/edge
values unless those costs and assumptions are explicitly included.

Stack elements may be fixed-size records containing dense IDs, but charging is per logical payload
word plus a stack-control event; packing a multiword record does not make it one event. The
canonical output step contains exactly two logical words, one edge ID and one next-vertex ID. A
pair of unbounded lists or another size-dependent payload is never one primitive item.

GraphLib declaration names must follow `GraphLib/NAMING.md`: use names such as
`IncidenceEnumeration`, a genuine `AdjacencyList`, and `...Represents G`; do not introduce the
rejected speculative `FiniteView`/`FiniteGraphView` vocabulary.

### Construction freedom and obligations

`R` may be:

- supplied as part of the executable input;
- built computably from stronger concrete input data;
- extracted noncomputably from finite mathematical sets; or
- accompanied by both a noncomputable existence constructor and a computable constructor from a
  concrete graph representation.

All are valid for the primary runtime theorem. The implementation report must state which exists.
No side receives credit merely because a definition lacks the `noncomputable` keyword. Measured
credit comes from smaller bridge burden, weaker construction assumptions, an executable constructor,
or a proved construction-cost theorem.

Option 4 does not waive `representation_exists`; it means only that no executable constructor is
delivered beyond the mandatory existence proof.

## 10. Chosen time-cost methodology

### Primary method

Use the frozen CSLib `Cslib.Algorithms.Lean.TimeM` behind a closed benchmark-local primitive-wrapper
API. Its cost type is a product of natural-number counters rather than a single undifferentiated
natural. The common `Cost` record has **exactly** these fields, in this order, all of type `Nat`:

```text
initWrite; incidenceRead; endpointRead; usedRead; usedWrite; cursorRead; cursorWrite;
indexOp; stackControl; stackRead; stackWrite; outputControl; outputRead; outputWrite.
```

No side may add, split, merge, or omit a field. Addition and zero are componentwise. The fixed
`total` projection sums these fourteen fields with unit weight. The common module exposes one
unit-basis event wrapper per field and no arbitrary-cost wrapper; `indexEq`, `indexLt`,
`indexSucc`, and `indexAdd` are the only public specializations of `indexOp`. Composite stack and
output helpers are built from `stackControl`/`stackRead`/`stackWrite` and
`outputControl`/`outputRead`/`outputWrite` as prescribed by Section 11. Both sides use the same
record, event wrappers, composite helpers, and projection.

This neutral common scaffold must be written, compiled, and content-hashed before either blind
algorithm core begins. Its exact source hash appears in both reports. Changing a field, wrapper,
or composite price is a protocol amendment applied to both sides, not a side-specific refinement.
The scaffold is reported once and excluded from adjusted side-specific totals; raw totals include
it.

Every timed function returns `TimeM Cost α`. The correctness theorem is about `.ret`; resource
theorems are about the cost vector and `total .time`.

Algorithm code may not call `TimeM.tick`, use `✓`, or construct a nonzero `TimeM` cost directly.
Only the frozen wrappers may do that. The wrappers centralize declared prices, but they do not
structurally prevent a concrete access or expensive pure computation from bypassing them. Fidelity
therefore remains a source-audit obligation; wrapped `TimeM` is a practical pinned abstract-event
ledger, not an execution-cost semantics.

This is a **manual abstract-resource annotation**. `TimeM` itself explicitly says its annotations
are trusted. The theorem therefore means:

> Under the frozen RAM primitive table, the instrumented program performs at most the proved
> number of abstract primitive events.

It does not mean that Lean's kernel checked each tick against evaluator steps, that persistent
array updates are physically constant-time in all sharing contexts, or that wall-clock execution
is bounded by the theorem.

### Why this method is primary

`TimeM` is already pinned, small, used by the CSLib MergeSort development, and used in the PR
#804/#805 DFS demonstrations. It supports correctness/time separation and exact recurrence or
accounting theorems. A closed wrapper vocabulary, a cost vector, and a syntactic raw-tick
prohibition reduce the main weakness of a plain writer counter: silent changes in what one
natural-number tick denotes. They do not eliminate the need to trust and audit that all relevant
computation passes through the wrappers. AlgoLean is structurally stronger on this point and
`complexitylib` is semantically stronger; their current version mismatch and encoding/refinement
overhead would likely dominate the graph-foundation comparison, which is why neither is primary.

The alternatives are not primary for this frozen run:

| Candidate | Meaning and issue | Decision |
| --- | --- | --- |
| Plain `TimeM ℕ` | Exact sum of manual annotations; `.ret` is the instrumented program, but arbitrary unticked work and arbitrary costs are trusted | Replaced by wrapped vector-valued `TimeM` |
| AlgoLean-style `Prog`/query DSL | Structural query cost centralizes models and supports interpreters; still trusts query costs and can hide expensive pure work. The surveyed version is early-stage and pins a different Lean/CSLib version | Strong future replication; not imported into this frozen run |
| `complexitylib` RAM semantics | Cost follows RAM instruction execution rather than ticks and supports logarithmic cost/space; graph/data encodings and low-level refinement would dominate this library comparison | High-assurance reference, not the primary vehicle |
| Mathlib transition/Turing semantics | Counts chosen transitions or machine steps without ticks; arbitrary transition granularity can hide work, while a full tape encoding is prohibitively remote from the target comparison | Not primary |
| Abstract costed data-structure typeclasses | Good modularity if implementations and refinements are verified; easy to hide unjustified axioms and not currently standardized in the project | Allowed only behind the same primitive ledger |
| Direct operational semantics of Lean | Could connect to evaluator steps, allocation, and copying; no mature pinned framework here covers the required arrays and amortization | Out of scope |
| Wall-clock benchmarking | Measures the compiler/runtime/machine and is useful as a smoke test, but is noisy and is not a proof | Optional secondary metric only |
| Informal textbook analysis only | Cannot satisfy the requested machine-checked resource result | Rejected |

### Mandatory secondary evidence

Each side must also provide:

- a line-by-line tick audit for the timed transitive call graph;
- the operation-count vector, not just `total`;
- the primitive assumptions used by every data structure;
- executable evaluations of every mandatory supplied-`R` stress case, checking the returned
  `IndexedTour`, its cost vector, and the concrete bound;
- an optional identical-machine wall-clock table, clearly labeled non-theorem evidence;
- any preprocessing cost or lack of such a theorem; and
- a bounded-word trust statement and logarithmic-cost robustness estimate as described below.

## 11. Primitive-operation cost model

The following table is frozen. One listed primitive adds one unit to its named counter unless a
row explicitly says otherwise.

| Operation | Abstract cost | Required treatment |
| --- | ---: | --- |
| Initialize one algorithm-owned logical word | 1 `initWrite` | Initializing `n` cursor words or `m` flag words costs `n` or `m`; allocation headers are free |
| Read one incidence/offset logical word | 1 `incidenceRead` | An edge ID and a separately stored role are two words and hence two events |
| Read one endpoint-ID logical word | 1 `endpointRead` | Reading a stored endpoint pair costs two; a proved packed encoding is allowed only if it fits one frozen-width word |
| Read one used-edge flag word | 1 `usedRead` | Bit packing is not primary; one Boolean flag occupies one modeled word |
| Write one used-edge flag word | 1 `usedWrite` | An edge changes from unused to used at most once |
| Read one cursor word | 1 `cursorRead` | Includes reading the current per-vertex position |
| Write one cursor word | 1 `cursorWrite` | Includes storing an advanced position |
| Compare, increment, or add bounded word indices | 1 `indexOp` | Charge each bounds/loop test and each cursor/index arithmetic operation |
| Check stack emptiness/top availability, push, pop, or request a peek | 1 `stackControl` | Each distinct stack action costs one before payload accesses |
| Read one stack payload word | 1 `stackRead` | A `k`-word frame returned by peek/pop costs `k` reads |
| Write one stack payload word | 1 `stackWrite` | Pushing a `k`-word frame costs `k` writes in addition to stack control |
| Allocate/visit one logical output step | 1 `outputControl` | Charge once per emitted step and once per step visited by reverse/copy |
| Read one output payload word | 1 `outputRead` | Canonical steps have two payload words, so a full step read costs two |
| Write one output payload word | 1 `outputWrite` | Emitting or copying a canonical step costs two writes; storing the result start costs one |
| Function call, constructor projection, proof field, pattern dispatch | 0 | Standard abstract-RAM administrative convention |
| Decode an ID only inside a proposition/proof | 0 | Erased specification work, not executable materialization |

An operation is charged once by its lowest-level row. Conversely, a composite helper such as
`nextIncident` must tick all incidence reads, cursor operations, comparisons, and increments it
performs. A stack push of a two-word frame costs one `stackControl` plus two `stackWrite`; a pop
returning that frame costs one `stackControl` plus two `stackRead`; an empty check still costs one
`stackControl`. A single `pop?` may combine its emptiness test and pop into that one control event;
if code first peeks/checks and later pops, those are two distinct control events. Emitting the
canonical two-word step costs one `outputControl` plus two
`outputWrite`; visiting and copying it costs one `outputControl`, two `outputRead`, and two
`outputWrite`. A representation that uses a different fixed-size frame must prove its word
encoding and pay for every word. Every storage-class-to-counter assignment must appear in the
common pre-core source manifest before either blind algorithm core begins. An unlisted storage
class is ineligible for the first run unless a symmetric protocol amendment is applied and both
sides restart. No bundled Lean record gets a one-event price merely because it is one value.

The following restrictions prevent unrealistic unit costs:

- `Finset`/list membership, insertion, deletion, and search are **not** unit-cost. Their traversed
  comparisons must be counted, or a proved data-structure bound must be supplied.
- No size-dependent pure `map`, `fold`, `filter`, `append`, `reverse`, repeated `length`, bulk array
  operation, or recursive traversal may occur unticked in the timed transitive call graph. It must
  be expanded into costed primitives or covered by a proved cost lemma.
- `Graph.deleteEdge`, set difference, finite-set extraction, and theorem-level `ncard` are not
  executable O(1) updates.
- Persistent `Array.set` receives the abstract unit write cost only as an explicit RAM assumption;
  the report must say whether linear threading makes that assumption plausible for execution.
- `Array.push` or another resizable buffer is not silently worst-case O(1). Use preallocation, list
  cons, or state and prove an aggregate/amortized bound.
- Hash-table lookup may be reported only as expected/amortized under explicit lawful
  `BEq`/`Hashable` assumptions. It cannot replace the primary deterministic dense-index theorem.
- Equality of ambient `α`, `β`, or `ε` is not assumed O(1). The primary hot loop uses dense IDs.
- A whole Lean expression cannot receive one tick merely because it calls one library function.
  Its relevant primitive operations must be exposed by wrappers or proved cost lemmas.

Both sides must use the same benchmark-local primitive wrappers. No timed primitive may be called
outside those wrappers in the transitive timed core.

The unit-cost result assumes a word-RAM whose word width `w` satisfies
`w ≥ max 1 (ceil(log2 (n + I + 1)))`, and every sentinel or packed encoding must be proved to lie
below `2^w`. Since `I = 2m`, this covers vertex IDs, edge IDs, offsets/cursors that may reach `I`,
and the ordinary one-past-end sentinels. Arithmetic in the timed core must be bounded accordingly.
Each report must also give the immediate conservative bit/log-cost estimate obtained by charging a
word operation `O(log(n+I+1))`; normally the linear operation bound becomes
`O((n+m+1) log(n+m+1))`. This robustness estimate is secondary and does not replace the textbook
word-RAM theorem.

## 12. Runtime boundary and preprocessing policy

### Included in primary algorithm runtime

The clock starts with a certified `R` and a start ID already supplied. It includes:

- initialization of all algorithm-owned cursors, flags, stacks, and output state;
- all incidence scans, including skipped darts of already-used edges;
- used-edge tests and updates;
- endpoint/other-end lookups performed by the core;
- stack operations and output assembly;
- final reversal/copy required to return the traversal-ordered `IndexedTour`; and
- any validation the implementation actually performs at runtime.

The primary theorem may trust `R`'s proof fields and need not recheck them at runtime. It may not
trust unproved executable invariants.

### Excluded symmetrically

The following are outside the primary Hierholzer clock on both sides:

- constructing dense vertex/edge enumerations from mathematical sets;
- choosing or computing endpoints from the mathematical graph;
- building incidence buckets and proofs that they represent `G`;
- checking the Eulerian preconditions; and
- proof-only decoding into mathematical subtype values.

This is the usual adjacency-representation-as-input boundary. Exclusion from runtime does **not**
exclude the code or proofs from representation/bridge metrics.

### Output boundary

Returning the canonical `IndexedTour` and any reverse/copy needed to put `steps` in traversal order
is included. The output must contain one `(edge ID, next vertex ID)` pair per mathematical edge;
returning only a residual stack, predecessor map, splice forest, or other representation that still
needs a traversal is not permitted. A logical pointwise `List.map` used only in the correctness
statement to relabel IDs is excluded as erased specification work. If the program allocates the
two `TourData` lists of mathematical values or a GraphLib `Walk` as its executable return value,
all lookup and allocation work for that materialization is included in the primary time or in a
separately stated conversion theorem. The implementation may not perform it and describe it as
free.

### Separate construction result

Each report must give one of:

1. a proved construction theorem with an explicit cost and assumptions;
2. executable construction code without a proved cost;
3. only a noncomputable existence/construction theorem; or
4. a supplied-representation-only executable interface, with no executable constructor beyond the
   mandatory proof of representation existence.

These are ordered facts, not an automatic winner ranking. Any optional construction-time theorem
must use the same primitive table or clearly state a separate table.

In every case the mandatory `representation_exists` theorem and its proof/LOC remain part of the
representation burden. Failing to deliver an executable constructor is recorded as missing
capability, not as zero construction LOC or reduced construction burden, and can never count as a
construction win.

## 13. Concrete resource theorem target

Let:

```text
n = number of actual mathematical vertices
m = number of actual mathematical edges
I = total number of representation darts
```

First prove componentwise bounds for the cost vector. Each field must be bounded by an explicit
affine expression in `1`, `n`, `m`, and `I`, or by an exact identity. Then prove a scalar theorem:

```text
total (hierholzer R start).time
  ≤ c0 + cV * n + cE * m + cI * I
```

This resource theorem is unconditional: it holds for every certified representation `R` and every
valid dense start ID, whether or not the mathematical graph satisfies `Heven` or `Hconn`. Those
hypotheses occur only in correctness/coverage theorems. Resource constants may not depend on
Eulerian proofs, a favorable adjacency order, or a specially constructed `R`.

Requirements on this theorem:

- `c0`, `cV`, `cE`, and `cI` are named definitions whose right-hand sides are concrete numerals;
- they are not existentially quantified and are not hidden inside asymptotic notation;
- zero coefficients are allowed only when the componentwise ledger demonstrates that the
  corresponding work is absent;
- every helper in the timed transitive call graph is covered; and
- the report prints the fully reduced numeric inequality.

An exact accounting identity is preferred where natural. A tighter bound is welcome, but it must
also be presented in the common affine form so the two results are structurally comparable.

Separately prove the representation/counting bridge:

```text
I = ∑ v : V_G, degree_G v
I = 2 * m
```

GraphLib may reuse its `Graph.sum_degrees_eq_twice_card_edges` after proving adapter equivalence.
Mathlib may prove a benchmark-local handshaking lemma. These proof differences are part of the
measured graph-foundation burden.

## 14. Textbook linear-time theorem target

Substitute `I = 2m` into the concrete theorem and expose:

```text
total time ≤ c0 + cV*n + (cE + 2*cI)*m.
```

Define the concrete numeral:

```text
C := max c0 (max cV (cE + 2*cI)).
```

The mandatory Level-2 theorem is the stronger pointwise statement:

```text
total time ≤ C * (n + m + 1).
```

This is the official `O(n+m)` result. An `Asymptotics.IsBigO` corollary over a suitably defined
family may be added, but is not a substitute: creating a worst-case envelope solely to display
`IsBigO` would add unrelated infrastructure. Both reports must compare the concrete coefficients
and operation-vector bounds before mentioning asymptotics.

## 15. Allowed dependencies

### GraphLib side

May use:

- the frozen GraphLib snapshot;
- generic Mathlib and generic CSLib modules;
- frozen `TimeM` and the neutral benchmark cost scaffold; and
- generic arrays, lists, finite types, arithmetic, and proof automation.

Must not use Mathlib `Graph`, `SimpleGraph`, graph walks, graph connectivity, graph degree, or other
Mathlib graph-specific facts as substitutes for GraphLib. Incidental transitive imports do not
invalidate the run, but direct graph-specific imports and declaration references do.

### Mathlib side

May use:

- Mathlib's frozen multigraph `Graph` infrastructure, including Basic/Subgraph/Delete/Lattice/Maps;
- other Mathlib graph modules when they apply without changing the graph class;
- generic Mathlib and CSLib;
- frozen `TimeM` and the neutral benchmark cost scaffold; and
- the same categories of generic data structures and automation.

Must not import or refer to GraphLib. It must not translate the input to `SimpleGraph` in a way that
removes loops or parallel identities.

### Shared code

Only graph-agnostic code fixed by this protocol may be shared: the `Cost` record, tick wrappers,
generic `TourData`, generic dense-ID utilities, and generic list/array lemmas. A shared declaration
must not import or mention either graph library. Shared code is reported once and excluded equally
from adjusted side-specific totals; raw totals must still show it.

Every shared-neutral Lean source file—not only the cost scaffold—must be written from this frozen
specification before either blind algorithm core begins. Publish a path-to-SHA-256 manifest covering
the cost scaffold, `TourData`/`IndexedTour`, dense-ID utilities, and every shared generic list/array
lemma. A shared file absent from that manifest is charged to the side introducing it unless a
symmetric protocol amendment is applied and both sides restart. If one physical common tree cannot
be arranged, each blind implementation duplicates the manifested files before its core begins and
Step 4 verifies the copies are semantically identical before excluding them.

Any new shared helper proposed after one implementation has been inspected requires either a
protocol amendment and rerun of both sides or must be charged to the side that introduced it.

## 16. Foundation-modification policy

During the first implementation attempt:

- do not modify any existing file under `GraphLib/`;
- do not modify `.lake/packages/mathlib` or `.lake/packages/cslib`;
- put neutral code under `Benchmarks/Hierholzer/Common/`, GraphLib code under
  `Benchmarks/Hierholzer/GraphLib/`, and Mathlib code under `Benchmarks/Hierholzer/Mathlib/`; and
- keep tiny feasibility probes disposable and outside the delivered source.

Classification is frozen as follows.

- **Foundation modification:** any edit to existing GraphLib graph/walk/connectivity/degree files,
  to Mathlib graph files, or to their public declarations.
- **Benchmark-local bridge code:** a new definition or theorem that relates the executable
  representation/output to the chosen mathematical graph, or adapts common semantics to a library.
- **Graph-specific helper:** a new declaration whose statement mentions a graph-specific type,
  relation, or operation but is not part of the representation correspondence.
- **Generic data-structure code:** imports neither graph foundation and states no graph-specific
  theorem.
- **Proposed upstream improvement:** an unimplemented recommendation or a separately recorded patch
  after the first attempt.

If a blocking defect makes a tiny foundation repair unavoidable, stop the side's first attempt and
record the exact blocker. The same category of repair must be offered to the other side. Apply it
only through a protocol revision; then rebuild or rerun both sides as necessary. Report results
before and after the repair separately.

## 17. Required implementation reports

Each side must deliver `IMPLEMENTATION_REPORT.md` next to its code. The report must include:

- frozen versions and final source commit/digest;
- exact build and test commands and final status;
- the mandatory representation-existence theorem and whether any executable constructor exists;
- chosen mathematical adapter and theorem statements;
- chosen executable layout;
- executable representation word-count formula and its concrete linear bound;
- alternative layouts considered and why they were rejected;
- every representation invariant;
- every bridge lemma, classified as representation, graph-specific, or generic;
- APIs that materially helped and APIs that were missing;
- all typeclass, decidable equality, `BEq`, hashing, and finiteness assumptions;
- noncomputable definitions and whether they are proof-only or on a construction path;
- computability and cost status of the mathematical-start-to-dense-ID lookup;
- preprocessing code, runtime boundary, and any preprocessing theorem;
- the complete primitive-cost table and tick audit;
- componentwise, concrete affine, and final linear-time bounds;
- results of all mandatory executable supplied-representation stress cases, including cost vectors;
- primitive assumptions behind arrays, mutation, allocation, and amortization;
- auxiliary-space bound or an explicit statement that none was proved;
- generic data-structure difficulties separate from graph-library difficulties;
- correctness and time-analysis difficulties separate from one another;
- major failed or abandoned approaches, with time/LOC when known;
- reviewer-suggested optimizations and whether they were adopted;
- every foundation change or proposed upstream change; and
- the metrics and friction classifications in Section 18.

Informative failures must not be deleted from the narrative merely because a later approach works.
Do not count exploratory files in final LOC, but do report their existence and approximate size.

## 18. Final comparison metrics

### Code size

Report physical nonblank, non-comment Lean source lines, using one common counting script in Step 4.
Classify every delivered declaration exactly once:

1. executable representation and constructor;
2. representation correspondence/bridge theorems;
3. algorithm core;
4. functional correctness proof;
5. time-analysis proof;
6. generic data-structure support;
7. graph-specific helpers; and
8. tests/examples.

Also report raw file LOC, theorem-statement LOC, and shared-neutral LOC. Generated code, copied logs,
and Markdown do not count as Lean LOC. Moving a helper to another file does not change its category.

### Logical/proof burden

Report:

- number of algorithm-state invariants;
- number of representation invariants;
- number of bridge lemmas;
- number of new graph-specific lemmas;
- number of auxiliary generic lemmas;
- number of explicit theorem premises and typeclass premises in the public correctness theorem;
- dependence on choice/noncomputability, split into construction and proof-only uses;
- count and identity of axioms shown by `#print axioms` for main theorems;
- theorem-statement LOC and any required adapter equivalences; and
- whether native walk, trail, circuit, degree, connectivity, delete/restrict, and handshaking APIs
  were reusable.

Invariant and lemma counts use atomic conceptual obligations, not the number of record fields or
theorem declarations. Combining obligations into a conjunction/structure theorem, splitting one
proof into aliases, or renaming a theorem does not change the count. Step 4 applies one published
normalization codebook to both reports and records any judgment calls.

### Algorithmic result

Report:

- the full operation-count vector;
- the reduced `c0`, `cV`, `cE`, `cI` values;
- the reduced coefficient of `m` after substituting `I = 2m`;
- final `C` in `C*(n+m+1)`;
- whether initialization, decoding, reversal, allocation, and validation are included;
- preprocessing status and any preprocessing cost;
- primitive-operation assumptions; and
- the explicit `r0`, `rV`, `rE`, `rI` representation-footprint constants and reduced `repWords`
  inequality;
- peak algorithm-owned auxiliary words; and
- peak combined executable words, including `R`, live algorithm state, and indexed output, if
  proved, otherwise the same normalized logical-word estimate clearly labeled unproved.

### Engineering burden

Report:

- clean-build and incremental-build status;
- proof brittleness observed after harmless refactors;
- reliance on heavy automation (`aesop`, `grind`, `simp`, `omega`, `native_decide`, etc.);
- timeouts, recursion/fuel issues, and compiler workarounds;
- major failed approaches;
- foundation modifications or requested APIs; and
- executable smoke-test status.

Automation use is not intrinsically negative; the report records whether it hides fragility or
substantially reduces maintainable proof burden.

### Friction classification

Every significant difficulty and every new nontrivial helper receives exactly one primary label:

- **A:** unavoidable Hierholzer or graph-theory complexity;
- **B:** generic Lean or data-structure complexity;
- **C:** mathematical-graph/executable-representation friction;
- **D:** missing graph-library API; or
- **E:** time-complexity framework friction.

Secondary labels may be noted, but final attribution uses the primary label. Categories A, B, and
E must not be credited to or blamed on either graph library.

For the C/D boundary, **C** means correspondence between a chosen executable representation or
output and the mathematical graph. **D** means a reusable mathematical graph theorem/API that is
missing independently of that chosen representation. Merely mentioning a graph type does not make
a helper D: the report must state the proposed reusable foundation declaration and why its statement
does not depend on `R`. Step 4 resolves disputed labels under the same rule for both sides.

Raw LOC is never the sole ranking. The final comparison presents a dimension-by-dimension result
and may conclude GraphLib wins, Mathlib wins, the results are equivalent, or the tradeoff is mixed.

## 19. Fairness and anti-gaming rules

1. **Blind first attempts.** The Step 2 and Step 3 implementers receive this protocol and the frozen
   foundation, but not the other side's implementation or report until both first attempts are
   declared complete.
2. **Same representation freedom.** Neither side must execute on its mathematical graph. Both may
   refine or extend the standard incidence interface.
3. **Same runtime boundary.** Representation construction and precondition checking are excluded
   from both primary clocks and measured separately for both.
4. **Same edge semantics.** `m` is mathematical actual-edge cardinality. Darts, adjacency entries,
   tags, and endpoint pairs are not edges.
5. **Same loop convention.** A loop is one edge, two darts, and degree contribution two.
6. **Same theorem strength.** Both prove all six common certificate clauses from exactly `Heven`
   and `Hconn`, including the edgeless case.
7. **No hidden validation.** A side may trust certified representation proofs, but any executable
   validation it performs is timed.
8. **No hidden output work.** Both sides return the same traversal-ordered canonical `IndexedTour`.
   Materializing decoded or native graph objects must be timed or separately reported on both.
9. **No tag shortcut.** GraphLib tags may be reused at different endpoints; all identity-sensitive
   state and coverage use full actual edges or dense IDs bijective with them.
10. **No adjacency shortcut.** Mathlib occurrence positions may not replace actual edge identity
    without a bijective bridge and pairing of the two darts.
11. **No unit-cost `Finset` fiction.** Linear scans and persistent rebuilding are expanded or proved.
12. **No under-ticking.** A missing tick for a frozen primitive is a correctness defect in the
    resource theorem, not an optimization. A tick with no corresponding primitive is reported too.
13. **No free amortization.** Dynamic buffers/maps require preallocation, aggregate analysis, or
    explicit expected/amortized assumptions.
14. **No foundation growth by stealth.** Local lemmas remain local and are measured. Moving them
    upstream does not erase their benchmark cost.
15. **No common-code laundering.** Graph-specific code cannot be labeled generic. New shared code
    after viewing one side triggers the rule in Section 15.
16. **No noncomputability erasure.** Noncomputable construction is permitted but recorded. It cannot
    be presented as executable preprocessing or omitted from bridge metrics.
17. **Same optimization opportunity.** After unblinding, each side gets one documented review pass
    and may adopt analogous optimizations. Preserve first-attempt and final metrics.
18. **Concrete before asymptotic.** No result may be summarized as simply `O(n+m)`; constants,
    incidence counts, exclusions, and assumptions accompany it.
19. **No packing or footprint trick.** Multiword endpoint, dart, stack, and output records pay per
    modeled word. Every executable representation field contributes to `repWords`, and the primary
    representation has the concrete linear footprint required by Section 9.
20. **Unconditional resource bound.** Runtime bounds range over every certified `R` and start, not
    only Eulerian inputs or a constructor-selected adjacency order.
21. **Matched implementation conditions.** The two blind first attempts use the same implementation
    prompt, model class, tool/network access, and nominal time/token budget. Preserve the first-attempt
    source commit and report before unblinding. “First attempt complete” means the first preserved
    source snapshot at which the mandatory representation, core, common correctness theorem,
    unconditional concrete and linear resource theorems, and all stress evaluations build together,
    with its report frozen; later cleanup does not replace that snapshot. If the run conditions
    cannot be matched, elapsed time, failed-attempt counts, and reviewer-intervention burden are
    descriptive only and are excluded from winner claims.

## 20. Known limitations

- The primary resource theorem depends on manual instrumentation. The tick audit and vector counter
  make the claim inspectable but do not derive it from Lean execution semantics.
- The unit-cost abstract RAM array model is a textbook abstraction. Persistent Lean arrays may copy
  under sharing, and native runtime details are not verified.
- Supplying the incidence representation as input deliberately moves graph conversion outside the
  primary time. The benchmark still measures its fields, invariants, bridges, constructors, and
  proofs, but a noncomputable constructor may have no meaningful runtime.
- A common dense incidence interface narrows the execution design space. This is intentional for a
  controlled runtime comparison, but it does not compare every possible graph representation.
- GraphLib has native general multigraph walks/circuits while the frozen Mathlib `Graph` does not.
  The common certificate equalizes theorem strength, but adapter LOC can still expose this intrinsic
  difference.
- `Circuit` in GraphLib requires positive length, whereas the standard edgeless Euler tour is a
  zero-edge closed walk. The common certificate and the mandatory two-case corollaries make this
  convention explicit.
- Wall-clock and memory measurements, if included, are secondary and machine-dependent.
- Results apply to the frozen pre-release Lean/Mathlib/CSLib state and may change as their graph and
  complexity APIs evolve.

## 21. Unresolved questions

There is no unresolved question that changes the meaning of Steps 2 or 3.

The only optional choices are implementation layout, whether to prove a preprocessing theorem,
whether to materialize a native output at runtime, and whether to add wall-clock or `IsBigO`
corollaries. The mandatory semantic contract, runtime boundary, primitive costs, concrete theorem,
and metrics are fixed regardless of those choices.

## Appendix A. Frozen API observations

These observations explain the protocol; later agents must verify declaration names against the
frozen source rather than treating this appendix as a substitute for source inspection.

### GraphLib

- `GraphLib.Edge` stores a tag and `Sym2` endpoints; the whole bundle is actual identity.
- `GraphLib.Graph.edgeSet` contains actual bundled edges.
- `Graph.IsLink`, `Graph.Inc`, `incidenceSet`, and `loopSet` are present.
- `Graph.degree` counts incidence plus a loop correction, and
  `Graph.sum_degrees_eq_twice_card_edges` is present.
- finite vertex, edge, and incidence `Finset` views exist but are noncomputable.
- `Walk.edges` reconstructs actual bundled edges, `Trail` requires `Nodup`, `Circuit` is a positive
  closed trail, and `Graph.IsEulerianCircuitIn` requires exact actual-edge coverage.
- restrict/delete operations preserve actual edge identity and are specification tools, not an
  executable constant-time state.
- the foundation review explicitly leaves executable incidence enumeration and algorithm state to
  clients.

Relevant local sources include `GraphLib/Graph/Basic.lean`, `Incidence.lean`, `Finite.lean`,
`Degree.lean`, `DegreeSum.lean`, `Delete.lean`, `GraphLib/Walk/Walk.lean`, `Trail.lean`,
`Circuit.lean`, `InGraph.lean`, and `Coverage.lean`, plus
`Reports/GRAPH_FOUNDATION_REVIEW_AND_REPAIR.md` and `GraphLib/NAMING.md`.

### Mathlib

- frozen `Mathlib.Combinatorics.Graph.Basic` defines `Graph α ε` with an actual edge set and
  `IsLink`; loops and parallel edge identities are supported.
- `Graph.Inc.other` is noncomputable witness extraction.
- restrict, edge deletion, vertex deletion, subgraph orders, maps, and lattice files exist.
- the frozen multigraph directory has no finite, degree, degree-sum, walk, trail, circuit,
  reachability, or Eulerian module.
- Mathlib's separate `SimpleGraph` walk/Eulerian theory is not a replacement for this multigraph
  benchmark.

### PR #804/#805 lessons

- Supplying or constructing an adjacency representation separately from the mathematical graph is
  viable.
- Noncomputable construction does not prevent proving a timed theorem about the subsequent core.
- A DFS adjacency-membership bridge is materially weaker than the edge-bijective representation
  required here.
- Scanning all graph edges for each vertex during construction may be acceptable outside the
  primary clock, but must be reported and cannot be called linear preprocessing.
- Plain manual `TimeM` ticks count the model chosen by the author, not Lean execution steps.

## Appendix B. Mandatory semantic stress cases

Both sides must instantiate supplied certified executable representations and evaluate the same
abstract examples:

1. one vertex and no edges: result `[s]` with no edges;
2. one vertex and one loop: the loop is traversed once although represented by two darts;
3. one vertex and two distinct loops;
4. two vertices with two parallel actual edges;
5. an Eulerian edge-bearing component plus at least one isolated vertex;
6. a triangle or another loopless cycle; and
7. on GraphLib, reused tags at different endpoint pairs, confirming tags are not IDs.

Mathlib examples use distinct actual edge values for the analogous identity tests. Each example
must check representation validity, the traversal-ordered `IndexedTour`, the decoded
`ValidEulerTour`, the full cost vector, and the concrete resource bound; tests of only endpoint
adjacency are insufficient. A noncomputable mathematical-graph-to-representation constructor is
exempt from evaluation, but the timed core on the explicit supplied `R` is not.

## Appendix C. Final review checklist

Before Step 4 compares the results, answer all of the following with evidence:

- Is either side forced into an unnatural mathematical or executable representation?
- Is either side charged for preprocessing, output conversion, or validation that the other gets
  free?
- Are all six correctness clauses and the three hypotheses literally equivalent?
- Are loops one edge/two darts/degree two on both sides?
- Is `m` the cardinality of the actual mathematical edge set on both sides?
- Does every unit-cost operation match Section 11?
- Can either side hide work before the clock or after indexed output?
- Is noncomputable construction visible in the report and metrics?
- Are generic data-structure and time-framework difficulties excluded from graph-library credit?
- Are the first-attempt results preserved before cross-side optimization?

A negative answer is blocking until repaired or documented through a protocol revision applied to
both sides.

## Appendix D. Freeze-review disposition

The independent adversarial review found no blocking defect after repair. The repaired blocking or
serious issues were: solution advice hidden in `R`; superlinear untimed representation footprint;
post-clock output reconstruction; conditional or constructor-specific time bounds; non-isomorphic
cost ledgers; record packing; missing stack observations; insufficient word width; an unfrozen `ST`
path; and laundering noncomputability or absent constructors as reduced burden.

The final should-fix items were also incorporated: all shared-neutral files and storage-to-counter
mappings are frozen in a pre-core hash manifest; start-ID encoding is reported; stress evaluation
is mandatory; invariant counts and the C/D friction boundary use common normalization rules; blind
run conditions and the first-green snapshot are defined.

The following limitations were classified acceptable but mandatory to document: `TimeM` remains a
manually audited event ledger; persistent-array unit writes remain a RAM assumption; preprocessing
is excluded symmetrically but separately scored; the common dense incidence interface narrows the
design space; mandatory representation existence adds symmetric proof burden; GraphLib naming
policy is intrinsic repository governance; and native GraphLib circuit conversion remains an
optional secondary result because it cannot express the zero-edge case.
