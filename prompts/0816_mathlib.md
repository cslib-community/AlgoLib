# Task: Blind Mathlib-side Hierholzer benchmark

Use **1 main agent + exactly 4 subagents**.

This is the **Mathlib-side blind first attempt** of a controlled benchmark comparing two graph foundations.

Your task is to produce, under the frozen protocol:

1. a certified executable representation of a finite undirected multigraph;
2. an efficient implementation of Hierholzer's algorithm;
3. the mandatory functional correctness theorem and corollaries;
4. the mandatory abstract-RAM resource analysis;
5. all mandatory stress tests;
6. `IMPLEMENTATION_REPORT.md`;
7. a preserved first-green git snapshot.

Your goal is **not** to make Mathlib look good.

Your goal is to produce the cleanest, most efficient, most maintainable solution you can under the frozen benchmark protocol.

If the cleanest architecture separates Mathlib's mathematical `Graph` specification from an executable adjacency/incidence representation, do so freely. Do not force the mathematical `Graph` object to serve directly as hot executable state.

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

* read, inspect, search, grep, or open files under `GraphLib/`;
* inspect GraphLib architecture/review reports for design inspiration;
* inspect `Benchmarks/Hierholzer/GraphLib/`;
* inspect another worktree containing the GraphLib-side experiment;
* inspect another benchmark branch's commits, diffs, logs, reports, or generated artifacts;
* ask any subagent to do any of the above;
* search Git history for the other side's experiment;
* use results produced by the concurrent GraphLib experiment.

When using repository-wide search tools, explicitly scope searches so they cannot enter `GraphLib/`, a counterpart benchmark tree, or another worktree.

Design the best Mathlib-side solution independently from:

* the frozen protocol;
* the frozen Common scaffold;
* the assigned Mathlib foundation;
* generic Lean/Mathlib/CSLib infrastructure.

---

# 2. Allowed graph foundation

The assigned mathematical foundation is the frozen Mathlib **multigraph `Graph`**.

You MAY inspect and use:

* the frozen Mathlib multigraph graph infrastructure;
* applicable Mathlib multigraph modules;
* generic Mathlib;
* generic CSLib;
* generic data structures;
* frozen `TimeM`;
* frozen Common infrastructure.

You MUST NOT:

* use GraphLib;
* inspect GraphLib source;
* use `SimpleGraph` as a replacement that removes loops or parallel-edge identity.

The mathematical benchmark graph must remain the frozen general multigraph `Graph`.

Do not simplify the benchmark to a simple graph.

---

# 3. Filesystem scope

All new Mathlib-side benchmark code must live under:

```text
Benchmarks/Hierholzer/Mathlib/
```

You may add a side-specific umbrella such as:

```text
Benchmarks/Hierholzer/Mathlib.lean
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

If you discover a genuine blocking Mathlib foundation defect, do not silently patch Mathlib. Record the blocker according to the protocol.

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

Use the frozen Mathlib mathematical graph:

```lean
G : Graph α ε
```

Actual mathematical edges are values of `ε` belonging to `E(G)`.

Adjacency occurrences are not mathematical edge identities.

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

Use Mathlib's existing multigraph API where genuinely helpful.

Do not use `SimpleGraph.Walk` or SimpleGraph Eulerian theory to evade the multigraph representation problem.

The local degree definition must follow the frozen loop-counting convention unless the frozen Mathlib API supplies an exactly equivalent multigraph notion.

---

# 6. Certified executable representation

Both graph foundations are allowed an external executable representation.

Design the best Mathlib-side benchmark-local representation refining the frozen standard interface.

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

You are explicitly allowed to separate the mathematical Mathlib graph specification from the executable representation.

Endpoint choices, dense enumerations, and representation existence may use classical/noncomputable reasoning outside the timed core, exactly as allowed by the frozen protocol.

Correctness and resource theorems must quantify over **every** certified representation satisfying the frozen interface, not only one favorable constructor/order.

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

A noncomputable existence proof is fully allowed.

You may choose endpoints/finite enumerations classically in this proof.

If you can additionally provide an executable constructor from suitable concrete data without distorting the benchmark, you may do so, but this is secondary and must be reported separately.

Do not count the noncomputable representation construction as part of the primary Hierholzer clock.

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

Parallel mathematical edges must remain distinct actual edge values.

Loops must be traversed once as a mathematical edge even though represented by two darts.

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

If `0 < m`, the result is a positive-length closed trail using every actual edge exactly once under the common certificate.

Do not introduce a stronger obligation merely because another graph library might possess a native circuit type.

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
7. an additional actual-edge identity stress case analogous to GraphLib's reused-tag test, using distinct Mathlib edge values.

For each, check:

* representation validity;
* returned traversal-ordered `IndexedTour`;
* decoded `ValidEulerTour`;
* full cost vector;
* concrete resource bound.

Tests of endpoint adjacency alone are insufficient.

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
* whether a materially simpler Mathlib-side design exists.

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
* unnecessary Mathlib-specific machinery;
* missed useful Mathlib multigraph APIs;
* proof brittleness.

The goal is optimization, not advocacy for Mathlib.

---

# 17. Main-agent development process

The main agent owns the integrated implementation.

Use this workflow:

### Phase 1 — reconnaissance

Read:

* frozen protocol;
* frozen Common;
* relevant Mathlib multigraph source/API;
* generic data-structure facilities.

Do not inspect GraphLib.

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

Freeze the first complete green blind result before seeing any GraphLib-side implementation.

---

# 18. `IMPLEMENTATION_REPORT.md`

Create:

```text
Benchmarks/Hierholzer/Mathlib/IMPLEMENTATION_REPORT.md
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
* reused Mathlib APIs;
* missing Mathlib APIs;
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

Do not compare against GraphLib.

Do not speculate about the concurrent GraphLib result.

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
benchmark: freeze Mathlib Hierholzer blind first attempt
```

Do not inspect or merge anything from the GraphLib-side experiment before this commit exists.

Do not push/merge another side's work.

---

# 20. Build discipline

Use the existing frozen toolchain.

Do not change Lean, Mathlib, CSLib, Common, or project configuration merely to simplify this benchmark.

Do not run bare `lake build`; the repository default target is GraphLib.

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

Stop after the blind Mathlib implementation, review/repair round, report, and first-green commit are complete.

Do NOT:

* open the GraphLib-side worktree;
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
