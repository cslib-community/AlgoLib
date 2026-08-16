# GraphLib foundation review + repair

Perform a whole-library review-and-repair pass on the completed GraphLib graph foundation.

This is not a line-by-line style review. The goal is to determine whether the resulting library is mathematically correct, architecturally coherent, internally consistent, pleasant for downstream formalization, and free of substantial redundancy or API debt.

Use **one main agent + up to four subagents**.

The **main agent is the only writer**. Subagents review, test, challenge findings, and simulate clients; they should not edit repository files.

Run **at most two complete review rounds**.

Do not continue iterating indefinitely.

---

## 1. Read the project sources first

Before reviewing, read:

1. `GraphLib/NAMING.md`
2. `Reports/2026-08-14_GRAPHLIB_EDGE_REPRESENTATION_DECISION.md`
3. `Reports/2026-08-14_GRAPHLIB_FOUNDATION_IMPLEMENTATION_PLAN.md`
4. `Reports/GRAPH_FOUNDATION_STATUS.md`

Also inspect the actual current repository rather than assuming the implementation followed the plan exactly.

Initialize:

```text
Reports/GRAPH_FOUNDATION_REVIEW_STATUS.md
```

Maintain it throughout this task.

The final report will be:

```text
Reports/GRAPH_FOUNDATION_REVIEW_AND_REPAIR.md
```

If context is compacted or earlier reasoning becomes unclear, reread the status file and authoritative project documents instead of relying on conversation memory.

---

# 2. Severity and evidence standard

Every finding must be classified:

* **S0 — correctness / semantic bug**

  * mathematically incorrect behavior;
  * violation of a locked representation invariant;
  * incorrect loop/parallel-edge/direction/finite semantics;
  * theorem statement that is false or materially misleading.

* **S1 — architectural / public API flaw**

  * likely to cause downstream redesign or repeated proof friction;
  * bad dependency direction;
  * wrong abstraction boundary;
  * important missing API forcing implementation leakage;
  * inconsistent public semantics across graph families.

* **S2 — important quality issue**

  * naming violation;
  * meaningful redundancy;
  * unnecessarily strong assumptions;
  * poor theorem orientation;
  * missing routine theorem;
  * bad simp/typeclass behavior;
  * awkward but locally repairable API.

* **S3 — cleanup**

  * proof style;
  * minor documentation;
  * cosmetic organization;
  * harmless local duplication.

A finding is not accepted merely because a reviewer prefers another design.

For S0/S1, require concrete evidence whenever possible:

* a counterexample;
* a Lean test;
* a violated locked invariant;
* a real downstream client;
* repeated unfolding/private-field access;
* a dependency path;
* an actual compilation/elaboration problem.

Every finding must include:

```text
ID
Severity
Confidence
Files / declarations
Problem
Evidence
Why it matters
Proposed repair
```

---

# 3. Round 1 — four independent reviews

The four reviewers should work **independently**. Do not show them the other reviewers' findings before they report.

## Reviewer A — architecture and dependency structure

Audit:

* folder structure;
* module responsibilities;
* namespace structure;
* import/dependency DAG;
* layer violations;
* unnecessary dependencies;
* overly heavy foundation imports;
* truthful umbrella modules;
* declarations located in the wrong conceptual module;
* files that are too broad or artificially fragmented;
* public/private implementation boundaries.

Generate the actual GraphLib import DAG or enough structured dependency information to identify suspicious edges.

Do not redesign modules merely for aesthetic symmetry.

---

## Reviewer B — semantic correctness and API completeness

Act as the adversarial mathematical/API reviewer.

Audit:

* all locked representation invariants;
* actual `Edge` / `Arc` identity;
* tag reuse;
* parallel edges;
* loops;
* antiparallel arcs;
* induced/restricted/deleted graphs;
* reverse;
* walk realization;
* trail/path/circuit/cycle conventions;
* finite-vertex versus finite-edge assumptions;
* degree semantics;
* reachability/connectivity/SCC conventions;
* weights/capacities on actual edges;
* consistency among all four graph families.

Also review public API completeness:

* membership characterizations;
* extensionality;
* monotonicity;
* operation algebra;
* transformation transport;
* routine bridge lemmas.

Look specifically for downstream proofs that must unnecessarily:

* unfold foundation definitions;
* access structure fields directly;
* reconstruct membership manually;
* perform avoidable casts/transports.

Actively construct small stress cases including:

```text
empty graph
one loop
multiple loops
parallel edges
same tag at different endpoints
antiparallel arcs
finite vertices + infinitely many general edges
delete one parallel edge
reverse twice
nested induce/delete/restrict
```

Try to falsify suspicious statements instead of merely inspecting them.

---

## Reviewer C — naming, redundancy, theorem quality, automation hygiene

Audit the entire public surface against `GraphLib/NAMING.md`.

Check:

* declaration naming;
* namespace placement;
* Set/Finset suffix discipline;
* theorem-name orientation;
* source/target directed terminology;
* duplicate and near-duplicate declarations;
* aliases with no independent value;
* dead speculative API;
* public helpers that should be private;
* overly specialized theorem variants;
* unnecessarily strong assumptions;
* weak theorem conclusions where a canonical iff/equality would be better.

Also audit:

* `[simp]` declarations and orientation;
* typeclass instances;
* unnecessary `classical`;
* unnecessary `DecidableEq`, `Finite`, or `Fintype` assumptions;
* potential simp loops;
* suspicious instance search;
* places where later proof automation could be improved.


Only report proof-style issues as S3 unless they expose a deeper API or automation problem.

---

## Reviewer D — downstream client and usability simulation

Review the library by trying to use it.

Perform small, bounded prototype/skeleton formalizations for several representative clients, for example:

```text
BFS / reachability
SCC
weighted shortest path
MST
flow / augmenting paths
```

Do not implement complete algorithms.

The goal is to discover:

* missing foundation lemmas;
* excessive unfolding;
* awkward signatures;
* bad executable/mathematical boundaries;
* unnecessary casts or transports;
* inability to express natural invariants;
* API asymmetries that matter in practice.

Also inspect build/elaboration usability:

* suspiciously expensive imports;
* slow files;
* fragile simp/typeclass behavior;
* accidental dependence on umbrellas.

Report concrete client friction rather than hypothetical preferences.

---

# 4. Main-agent Round 1 triage

After all four reports return:

1. independently verify important findings;
2. deduplicate overlapping findings;
3. reject unsupported aesthetic suggestions;
4. classify each accepted finding S0/S1/S2/S3;
5. update `GRAPH_FOUNDATION_REVIEW_STATUS.md`.

## Adversarial verification rule

For any **S0 or S1 finding that remains uncertain**:

```text
reviewer finds issue
→ main agent verifies independently
→ if still uncertain, ask another subagent to challenge the finding
→ repair only if the finding survives the challenge
```

The challenger should explicitly attempt to show that the current design is correct or justified.

Do not ask the challenger merely to confirm the first reviewer.

## High-impact changes

Require especially strong evidence before:

* changing a public carrier type;
* changing graph representation;
* changing a mathematical convention;
* introducing a new abstraction/typeclass hierarchy;
* moving large directory families;
* merging/splitting major conceptual modules;
* contradicting locked design documents.

If such a change is plausible but fundamentally a design-choice/taste question, record it under **Human decisions** instead of changing it automatically.

---

# 5. Round 1 repair

The main agent now repairs accepted:

* all S0;
* all S1 that have sufficient evidence and do not require unresolved human design judgment;
* high-confidence S2 issues whose repair is local and clearly improves the library.

S3 findings are normally deferred to the later cleanup/proof-compression pass.

Do not opportunistically redesign unrelated areas.

After repair:

* compile incrementally;
* run import-all/root builds;
* run Girth/Moore regression;
* run relevant semantic stress tests;
* check for new `sorry`;
* update the review status file.

Record each accepted finding as:

```text
OPEN
FIXED
DEFERRED
REJECTED
HUMAN_DECISION
```

with a short reason.

---

# 6. Round 2 — independent re-review

Run one final review round. Do not simply ask reviewers whether Round 1 was good.

Use the four agents differently.

## Reviewer A — architecture regression

Check whether Round 1 repairs introduced:

* new dependency inversions;
* namespace/folder inconsistencies;
* misplaced declarations;
* import inflation;
* unnecessary public surface.

Also verify important Round 1 architecture fixes.

## Reviewer B — semantic red team

Independently search again for S0/S1 semantic bugs.

Do not anchor on the Round 1 findings.

Repeat adversarial stress testing of:

```text
loops
parallel edges
same-tag distinct edges
antiparallel arcs
finite-V/infinite-E
reverse
delete/induce/restrict compositions
walk realization
degree
connectivity
weights/capacities
```

The objective is to find bugs missed in Round 1 or introduced by repairs.

## Reviewer C — API minimality and consistency

Inspect the repaired public API for:

* redundant helpers created during repair;
* duplicate theorem families;
* unnecessary aliases;
* leaked implementation details;
* remaining naming inconsistencies;
* routine missing bridges;
* overly strong hypotheses.

Focus on whether the API is now both sufficient and minimal.

## Reviewer D — client simulation and regression

Repeat bounded downstream use cases against the repaired library.

Focus on whether previously awkward operations now work naturally.

Run relevant builds/regressions and report remaining client friction.

---

# 7. Round 2 triage and repair

The main agent again verifies and deduplicates findings.

Use the same adversarial verification rule for uncertain S0/S1 findings.

Repair:

* every verified S0;
* verified S1 that can be repaired without unresolved design judgment;
* important high-confidence S2 regressions or omissions.

Do not start a third full review round.

After repairs, run the final regression/test suite.

If serious S0/S1 issues remain, stop and mark the review **NON_CONVERGED** rather than continuing indefinitely.

---

# 8. Convergence criteria

The task is **CONVERGED** when:

* no verified S0 remains;
* no verified actionable S1 remains;
* remaining S2 issues are local/nonblocking or explicitly deferred;
* build/import-all is green;
* Girth/Moore regression is green;
* locked semantic stress tests are green;
* no new production `sorry` remains;
* the dependency DAG has no serious layering violation;
* second-round client simulations no longer reveal repeated foundation-level friction;
* newly discovered findings are predominantly S3/local cleanup.

Possible final statuses:

```text
CONVERGED
CONVERGED_WITH_DEFERRED_ITEMS
NON_CONVERGED
```

Stop after Round 2 regardless.

---

# 9. Status-file discipline

Continuously maintain:

```text
Reports/GRAPH_FOUNDATION_REVIEW_STATUS.md
```

Update it at least after:

1. initialization;
2. completion of each Round 1 reviewer;
3. Round 1 triage;
4. Round 1 repair + regression;
5. completion of each Round 2 reviewer;
6. Round 2 triage;
7. final repair + regression.

Keep it concise enough that a fresh main agent can resume from it after context compaction.

Do not paste large compiler logs or reviewer transcripts.

---

# 10. Final report

At the end, write into:

```text
Reports/GRAPH_FOUNDATION_REVIEW_AND_REPAIR.md
```

following the report structure specified in the project review template.

The most important section for the human maintainer is:

```text
Human decisions / items worth manual inspection
```

Keep this focused. Prefer roughly 5–15 items, and fewer if there are genuinely fewer consequential choices.

Do not force the human maintainer to read the complete finding inventory to understand whether the library is healthy.

---

# 11. Final response

Return only a concise summary:

* convergence status;
* Round 1 and Round 2 S0/S1/S2/S3 counts;
* number fixed / deferred / rejected / human-decision;
* major categories of repair;
* final build/regression status;
* number of human decisions requiring attention;
* paths to the review status and final report.
