# Task: Blind GraphLib-side Hierholzer benchmark

Use **1 main agent + exactly 4 subagents**.

This is the **GraphLib-side blind first attempt** of a controlled benchmark comparing two graph foundations.

Your task is to produce, under the frozen protocol:

1. a certified executable representation of a finite undirected multigraph;
2. an efficient implementation of Hierholzer's algorithm;
3. the mandatory functional correctness theorem and corollaries;
4. the mandatory abstract-RAM resource analysis;
5. all mandatory stress tests;
6. `IMPLEMENTATION_REPORT.md`;
7. a preserved first-green git snapshot.

Your goal is **not** to make GraphLib look good.

Your goal is to produce the cleanest, most efficient, most maintainable solution you can under the frozen benchmark protocol.

If GraphLib still benefits from a separate executable adjacency/incidence representation, use one. Do not force the mathematical `Graph` object to serve directly as hot executable state.

---

# 0. Single source of truth

Read in full:

```text
HIERHOLZER_BENCHMARK_PROTOCOL.md
```

Also verify the frozen shared scaffold:

```text
Benchmarks/Hierholzer/Common/
Benchmarks/Hierholzer/Common.lean
```

and:

```text
Benchmarks/Hierholzer/Common/COMMON_FREEZE_REPORT.md
Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256
```

Before doing substantive work, run:

```sh
shasum -a 256 -c Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256
```

The frozen protocol overrides this prompt if there is any accidental discrepancy.

Do not modify Common.

Do not modify the benchmark protocol.

---

# 1. Blindness requirement

This is a blind first attempt.

You MUST NOT:

* inspect another Hierholzer implementation;
* inspect `Benchmarks/Hierholzer/Mathlib/`;
* inspect another worktree containing the Mathlib-side experiment;
* inspect another benchmark branch's commits, diffs, logs, reports, or generated artifacts;
* ask any subagent to do so;
* search Git history for the other side's experiment;
* use results produced by the concurrent Mathlib experiment.

For repository searches, explicitly scope searches so they do not enter a counterpart benchmark tree or another worktree.

You MAY inspect the frozen benchmark protocol and frozen Common scaffold.

---

# 2. Allowed graph foundation

The assigned mathematical foundation is the current frozen **GraphLib**.

You MAY inspect and use:

* `GraphLib/`;
* GraphLib architecture/naming documentation;
* generic Mathlib;
* generic CSLib;
* generic data structures;
* frozen `TimeM`;
* frozen Common infrastructure.

You MUST NOT use Mathlib's graph foundation as a substitute.

In particular, do not directly import or use declarations from:

```text
Mathlib.Combinatorics.Graph
Mathlib.Combinatorics.SimpleGraph
```

or Mathlib graph-specific walk/connectivity/degree/Eulerian infrastructure.

Incidental transitive imports do not invalidate the experiment, but direct graph-specific dependency does.

Do not inspect Mathlib graph source for implementation inspiration during this blind run.

---

# 3. Filesystem scope

All new GraphLib-side benchmark code must live under:

```text
Benchmarks/Hierholzer/GraphLib/
```

You may add a side-specific umbrella such as:

```text
Benchmarks/Hierholzer/GraphLib.lean
```

if useful.

Do NOT modify:

```text
GraphLib/
Benchmarks/Hierholzer/Common/
.lake/packages/mathlib/
.lake/packages/cslib/
```

or existing project/foundation files.

Benchmark-local bridge lemmas are allowed and must remain local.

If you discover a genuine blocking foundation defect, do not silently repair GraphLib. Record the blocker according to the protocol.

---

# 4. Main scientific requirement

Implement standard linear-time **Hierholzer's algorithm** for finite undirected multigraphs with:

* actual edge identity;
* parallel edges;
* loops;
* isolated vertices.

The timed core must recognizably be Hierholzer: it grows a trail through unused incident actual edges and uses standard stack backtracking / equivalent tour-splicing behavior.

Do not substitute:

* exhaustive edge permutation search;
* a nonconstructive existence proof;
* a different Euler-tour algorithm;
* precomputed traversal advice hidden in the representation.

---

# 5. Mathematical input

Use the frozen GraphLib mathematical graph:

```lean
G : GraphLib.Graph α β
```

Actual mathematical edges are full bundled GraphLib edge values in `E(G)`.

A tag alone is **not** an edge identity.

The benchmark-local semantic adapter must implement the frozen common meanings:

```text
V_G
E_G
Link_G
Inc_G
Loop_G
degree_G
Step_G
Reachable_G
```

exactly as specified by the protocol.

Where GraphLib already has suitable native theory, reuse it when doing so genuinely simplifies the development.

In particular, investigate whether adapter degree can be related cleanly to GraphLib's native degree and whether the native degree-sum theorem can prove the frozen `I = 2m` bridge.

Do not weaken the common semantics to make existing API easier to use.

---

# 6. Certified executable representation

Both graph foundations are allowed an external executable representation.

Design the best GraphLib-side benchmark-local representation refining the frozen standard interface.

It must support:

* dense vertex IDs equivalent to `Fin n`;
* dense actual-edge IDs equivalent to `Fin m`;
* endpoint IDs;
* exactly two darts per mathematical edge;
* two distinct dart roles for a loop in the same bucket;
* no missing or duplicate dart occurrences;
* all isolated vertices;
* constant-time abstract hot-loop access under the frozen RAM model;
* a linear-sized executable payload.

Correctness and resource theorems must quantify over **every** certified representation satisfying the frozen interface, not only one favorable constructor/order.

A representation-specific proof may exploit GraphLib's bundled endpoint information, but the executable core must still obey the frozen dense-ID abstraction and cost model.

---

# 7. Representation freeze before algorithm core

This requirement is important.

Before implementing the Hierholzer core:

1. design the executable representation;
2. implement and compile its carrier/interface;
3. declare every executable field;
4. declare the intended primitive storage access for every field;
5. establish the representation-footprint accounting strategy;
6. create a side-local representation freeze record containing the representation schema and storage-to-counter mapping;
7. hash the frozen representation source/schema and record the hash.

After the algorithm core begins, do not add a new executable field, cached traversal schedule, accelerator, or primitive-operation category.

If the representation is clearly wrong, record it as an abandoned pre-core attempt and redesign **before** beginning the timed core.

Do not hide Hierholzer work in untimed representation construction.

---

# 8. Representation existence

Prove the mandatory total existence theorem for every finite mathematical input:

```lean
theorem representation_exists
    (G) [Finite V_G] [Finite E_G] :
    Nonempty (CertifiedIncidenceRepresentation G)
```

or the exact equivalent under the final side-specific names.

All frozen representation laws must be included.

A noncomputable existence proof is allowed.

If you can additionally provide an executable constructor from suitable concrete data without distorting the benchmark, you may do so, but this is secondary and must be reported separately.

Do not let constructor work enter or disappear from the primary timed theorem inconsistently with the protocol.

---

# 9. Canonical executable result

The public timed core must return the frozen Common result shape:

```lean
IndexedTour n m
```

with:

```text
start : Fin n
steps : List (Fin m × Fin n)
```

already in traversal order.

Do not return an internal splice forest, residual stack, reverse traversal, or other object requiring uncharged postprocessing.

Use Common's graph-neutral decoder for the public semantic theorem.

---

# 10. Correctness theorem

Prove the exact frozen theorem contract.

Under:

```text
Heven
Hconn
```

the decoded result must satisfy the common:

```text
ValidEulerTour
```

with all six clauses:

1. vertex/edge length relation;
2. starts at `s`;
3. ends at `s`;
4. every edge occurrence links the corresponding consecutive vertices;
5. actual edge list is `Nodup`;
6. every actual mathematical edge occurs.

Parallel edges must remain distinct actual edges.

Loops must be traversed once as an edge even though represented by two darts.

Do not strengthen the public assumptions merely for convenience.

---

# 11. Mandatory correctness corollaries

Also prove:

### Edgeless case

If `m = 0`:

```text
decoded edges = []
decoded vertices = [s]
```

### Exact length

The decoded tour contains exactly:

```text
m edges
m + 1 vertices
```

### Positive-edge circuit

If `0 < m`, the result is a positive-length closed trail using every actual edge exactly once.

GraphLib may additionally expose a native `GraphLib.Circuit` /
`Graph.IsEulerianCircuitIn` result if useful.

This native adapter is optional secondary evidence and must remain separately measured from the common primary theorem.

---

# 12. Timed core and Cost discipline

Use only the frozen Common cost infrastructure.

Every timed function returns:

```lean
TimeM Cost α
```

Side-specific algorithm code MUST NOT directly use:

```text
TimeM.tick
✓
```

or manually construct a nonzero `TimeM`.

Only the frozen Common event wrappers may introduce cost.

Audit the entire transitive timed call graph.

Do not hide:

* list traversal;
* `Finset` lookup;
* repeated length;
* array traversal;
* `map`;
* `filter`;
* `fold`;
* `append`;
* `reverse`;
* bulk copying;
* endpoint reconstruction;
* output reconstruction;

inside an unticked pure expression.

Follow the exact frozen primitive table.

---

# 13. Required running-time theorem

Let:

```text
n = mathematical number of vertices
m = mathematical number of actual edges
I = total dart count
```

The resource theorem must be unconditional over every certified representation and dense start ID.

First prove explicit componentwise bounds for all fourteen cost fields.

Then prove:

```text
total (hierholzer R start).time
  ≤ c0 + cV*n + cE*m + cI*I
```

where the four coefficients are concrete numeral definitions.

Then prove:

```text
I = Σ_v degree_G(v)
I = 2*m
```

and derive:

```text
total time
  ≤ c0 + cV*n + (cE + 2*cI)*m
```

and finally the frozen pointwise textbook result:

```text
total time ≤ C * (n + m + 1)
```

with concrete numeral `C`.

Do not substitute an `IsBigO` theorem for this result.

A tighter or exact accounting theorem is welcome in addition.

---

# 14. Representation-space accounting

Define the protocol's logical:

```text
repWords R
```

and prove a concrete bound:

```text
repWords R ≤ r0 + rV*n + rE*m + rI*I
```

with concrete numeral constants.

Count every executable logical word according to the frozen protocol.

Do not exploit Lean record packing to count a multiword payload as one abstract word.

Also report algorithm-owned auxiliary-space usage, whether proved or only normalized-estimated.

---

# 15. Mandatory stress cases

Instantiate explicit supplied certified representations and evaluate at least the protocol's mandatory cases:

1. one vertex, no edges;
2. one vertex, one loop;
3. one vertex, two distinct loops;
4. two vertices, two parallel actual edges;
5. an Eulerian edge-bearing component plus an isolated vertex;
6. a triangle or another loopless cycle;
7. GraphLib-specific reused edge tags at different endpoint pairs.

For each, check:

* representation validity;
* returned traversal-ordered `IndexedTour`;
* decoded `ValidEulerTour`;
* full cost vector;
* concrete resource bound.

The reused-tag case must confirm that tags are not treated as edge IDs.

---

# 16. Subagent roles

Spawn exactly four subagents.

## Subagent A — Representation and algorithm architecture reviewer

Review:

* executable representation;
* whether it is standard and efficient;
* whether redundant state can be removed;
* whether work has been hidden in `R`;
* whether loops/parallel edges are represented cleanly;
* whether `repWords` is honest;
* whether a materially simpler GraphLib-side design exists.

Do not implement an independent competing solution.

## Subagent B — Correctness reviewer

Adversarially review:

* algorithm-state invariants;
* loop handling;
* parallel-edge identity;
* exact edge coverage;
* no duplicate traversal;
* edgeless case;
* stack/backtracking correctness;
* use of `Heven`;
* use of `Hconn`;
* all common certificate clauses.

Try to find counterexamples.

## Subagent C — Time-analysis and tick auditor

Audit the entire timed transitive call graph.

Look specifically for:

* missing ticks;
* extra ticks;
* hidden traversals;
* unrealistic `Finset`/List costs;
* output reconstruction outside the clock;
* incorrect initialization costs;
* cursor scans that could revisit darts superlinearly;
* incorrect componentwise bounds;
* incorrect `I = 2m` use;
* dependence on favorable adjacency order.

Recompute final coefficients independently.

## Subagent D — Optimization and maintainability reviewer

Assume the current solution is correct and ask:

> Can it be substantially shorter, more idiomatic, more stable, or easier to maintain without changing the frozen benchmark?

Review:

* representation choice;
* invariant organization;
* theorem decomposition;
* duplicate bridge lemmas;
* unnecessary use of native GraphLib infrastructure;
* missed useful GraphLib APIs;
* proof brittleness.

The goal is optimization, not advocacy for GraphLib.

---

# 17. Main-agent development process

The main agent owns the integrated implementation.

Use this workflow:

### Phase 1 — reconnaissance

Read:

* frozen protocol;
* frozen Common;
* relevant GraphLib source/API;
* generic data-structure facilities.

Do not inspect the Mathlib graph implementation.

### Phase 2 — representation

Design, implement, compile, and freeze the representation schema before writing the algorithm core.

### Phase 3 — first complete implementation

Implement:

* semantic adapter;
* representation existence;
* Hierholzer core;
* correctness;
* mandatory corollaries;
* resource theorem;
* space accounting;
* stress cases.

Keep working until all mandatory deliverables build together.

### Phase 4 — independent review

Have all four subagents review independently.

Classify findings:

* correctness defect;
* resource-accounting defect;
* representation defect;
* maintainability/optimization;
* protocol violation.

Verify findings rather than blindly accepting them.

### Phase 5 — one repair/optimization round

Repair all accepted correctness, accounting, representation, and meaningful maintainability findings.

Do not endlessly polish.

### Phase 6 — final blind freeze

Run all builds/tests/audits.

Freeze the first complete green blind result before seeing any Mathlib-side implementation.

---

# 18. `IMPLEMENTATION_REPORT.md`

Create:

```text
Benchmarks/Hierholzer/GraphLib/IMPLEMENTATION_REPORT.md
```

Follow every reporting requirement from the frozen protocol.

In particular include:

* exact frozen commit;
* Common manifest verification;
* all files created;
* representation schema/hash;
* representation existence theorem;
* executable constructor status;
* representation invariants;
* representation footprint constants;
* semantic adapter;
* algorithm structure;
* algorithm-state invariants;
* exact correctness theorem;
* mandatory corollaries;
* all bridge lemmas;
* reused GraphLib APIs;
* missing GraphLib APIs;
* every noncomputable use;
* complete tick audit;
* full fourteen-component bounds;
* `c0,cV,cE,cI`;
* final `C`;
* `I = 2m` proof route;
* stress-test results;
* auxiliary-space result;
* failed/abandoned approaches;
* subagent findings and dispositions;
* generic vs graph-specific friction;
* friction labels A/B/C/D/E;
* build commands;
* final build result;
* `#print axioms` for main theorems where appropriate.

Do not compare against Mathlib.

Do not speculate about the concurrent Mathlib result.

This report describes this side only.

---

# 19. First-attempt preservation

The protocol requires preservation of the blind first attempt.

“First attempt complete” means the first source state at which all mandatory items build together:

* certified representation;
* representation existence;
* timed Hierholzer core;
* common correctness theorem;
* mandatory correctness corollaries;
* unconditional concrete resource theorem;
* final linear theorem;
* stress evaluations;
* implementation report.

When this first complete green state is reached:

1. record the full git diff/stat;
2. record the current source LOC metrics;
3. record the exact HEAD/base commit;
4. create a local git commit preserving it.

Suggested commit message:

```text
benchmark: freeze GraphLib Hierholzer blind first attempt
```

Do not inspect or merge anything from the Mathlib-side experiment before this commit exists.

Do not push/merge another side's work.

---

# 20. Build discipline

Use the existing frozen toolchain.

Do not change Lean, Mathlib, CSLib, Common, or project configuration merely to simplify this benchmark.

Use explicit `lake env lean` compilation if the Benchmark tree is not a Lake target, as Common did.

Run:

```text
git diff --check
```

and audit for:

```text
sorry
admit
TimeM.tick
✓
```

outside the frozen Common implementation.

The delivered benchmark must contain no `sorry` or `admit`.

---

# 21. Stopping condition

Stop after the blind GraphLib implementation, review/repair round, report, and first-green commit are complete.

Do NOT:

* open the Mathlib-side worktree;
* inspect its report;
* compare results;
* perform cross-side optimization;
* write the final comparison report.

Those are later tasks.

At the end, report concisely:

* whether the mandatory benchmark is fully green;
* first-attempt commit hash;
* main files created;
* final concrete time bound;
* final `C`;
* representation footprint bound;
* build/test status;
* any unresolved blocker.

If a mandatory result cannot be completed, preserve the best honest partial state and explain the exact blocker instead of weakening the frozen protocol.
