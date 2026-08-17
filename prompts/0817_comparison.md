# Task: Produce the final blind-first-attempt comparison report for the Hierholzer graph-foundation benchmark

Use **1 main agent + exactly 4 subagents**.

The two blind Hierholzer experiments are now complete:

1. a GraphLib-side implementation;
2. a Mathlib-side implementation.

Both were developed independently from the same frozen benchmark protocol and the same frozen Common infrastructure.

Your job is now to **unblind**, inspect both developments in full, independently verify their important claims and metrics, reconstruct the relevant CSLib graph-design debate, and write a rigorous comparison report.

This is an **analysis/reporting task only**.

Do NOT modify either implementation.

Do NOT optimize either implementation.

Do NOT merge the two benchmark branches.

Do NOT repair code in either worktree.

Do NOT change GraphLib, Mathlib, CSLib, Common, or the benchmark protocol.

The primary evidence must remain the preserved blind first-attempt results.

---

# 0. Main deliverable

Create:

```text
Benchmarks/Hierholzer/COMPARISON_REPORT.md
```

in the main repository/worktree, not in either side-specific experimental worktree.

The report should answer two different questions separately:

### Benchmark question

> Under the frozen Hierholzer protocol, how did the GraphLib and Mathlib foundations compare in executable-representation burden, bridge/proof burden, correctness development, resource analysis, and engineering complexity?

### Broader CSLib design question

> What does this experiment actually tell us about the ongoing disagreement over whether CSLib should maintain a separate graph foundation rather than build graph algorithms on top of Mathlib's graph definitions?

Do **not** collapse these into the simplistic question:

> Which library won?

A mixed result is entirely acceptable.

---

# 1. Sources of truth

Read the following first.

## Frozen benchmark documents

```text
HIERHOLZER_BENCHMARK_PROTOCOL.md
Benchmarks/Hierholzer/Common/COMMON_FREEZE_REPORT.md
Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256
```

The protocol is authoritative for:

* theorem strength;
* runtime boundary;
* cost model;
* representation freedom;
* metrics;
* fairness rules;
* friction classification.

## GraphLib experiment

Discover the GraphLib benchmark worktree/branch with:

```sh
git worktree list --porcelain
```

Read all files under:

```text
Benchmarks/Hierholzer/GraphLib/
```

including:

```text
IMPLEMENTATION_REPORT.md
```

and identify the preserved blind first-attempt commit.

Read the actual Lean source, not only the report.

## Mathlib experiment

Likewise read all files under:

```text
Benchmarks/Hierholzer/Mathlib/
```

including:

```text
IMPLEMENTATION_REPORT.md
```

and identify its preserved blind first-attempt commit.

Read the actual Lean source, not only the report.

## Relevant graph foundations

Now that the experiment is unblinded, inspect the relevant parts of both:

```text
GraphLib/
```

and the pinned Mathlib multigraph infrastructure.

Only inspect what is necessary to understand:

* which APIs were reused;
* which APIs were missing;
* why bridge obligations arose;
* which differences are representation-level;
* which differences are merely differences in API maturity.

---

# 2. Reconstruct the CSLib design debate

Read the current discussion around at least:

* https://github.com/leanprover/cslib/pull/503
* https://github.com/leanprover/cslib/pull/804
* https://github.com/leanprover/cslib/pull/805

Read the full technically relevant conversation, including the most recent comments available at the time of this report.

Follow linked Zulip discussion when needed to understand a technical claim, but do not let the report turn into a social-history narrative.

Focus on the strongest technical versions of the arguments.

Do not caricature either side.

Do not infer someone's position merely from one isolated sentence when later comments refine it.

Use precise GitHub comment links in the final report when attributing an argument.

Quote sparingly; mostly paraphrase.

---

# 3. The dispute must be decomposed into separate claims

The report must explicitly distinguish at least the following claims.

Assign stable IDs such as `C1`, `C2`, etc.

## C1 — Feasibility of algorithms on Mathlib Graph

A strong form sometimes motivating a separate foundation would be:

> Mathlib's graph representation makes graph-algorithm verification impractical or impossible without replacing the graph definition.

Evaluate this separately from all ergonomic claims.

PR #804/#805 already provide DFS evidence relevant to this question; Hierholzer is intended as a substantially stronger multigraph/edge-identity test.

---

## C2 — Necessity of a computable mathematical graph specification

One disputed idea is:

> For graph algorithms, the mathematical graph specification itself needs computable endpoint access.

The opposing architecture is:

```text
mathematical graph specification
        ↓ correspondence
executable adjacency/incidence representation
        ↓
algorithm
```

Under that view, the executable representation is the algorithmic input and representation construction may be outside the primary algorithm clock.

Use the actual benchmark results to assess:

* whether either implementation needed direct executable access to the mathematical graph;
* whether GraphLib's computable bundled endpoints materially simplified anything downstream;
* whether Mathlib's noncomputable endpoint extraction was confined to representation construction/proof;
* whether it affected the timed core at all.

Do not award "computable specification" as a win by itself.

Only award measurable downstream consequences.

---

## C3 — Bundled endpoints reduce bridge burden

GraphLib stores endpoints as data in its actual edge object.

Mathlib's multigraph edges are opaque edge values related to endpoints through `IsLink`.

The empirical question is:

> Did GraphLib's bundled endpoint data substantially reduce the definitions, invariants, bridge theorems, or proof complexity needed to obtain and reason about the certified dense incidence representation?

This is one of the most important benchmark questions.

Measure it rather than assuming the answer.

---

## C4 — External executable representation neutralizes the specification difference

The opposing claim is:

> Once both sides use a standard executable edge-indexed incidence representation, the difference between the mathematical graph specifications largely disappears from the algorithm itself.

Evaluate this using:

* algorithm-core similarity;
* representation layers;
* timed-state similarity;
* correctness invariants;
* resource proofs.

It is possible that the core algorithms become almost identical while the bridge layers differ substantially.

Report those separately.

---

## C5 — Actual edge identity and endpoint-label semantics

GraphLib's actual general edge identity is the full bundled edge value, not merely its `endpointsLabel`.

Thus distinct edges may reuse the same label at different endpoint pairs.

Recent CSLib discussion has explicitly questioned whether permitting this is desirable.

The benchmark includes a reused-tag stress case precisely to ensure tags are not accidentally treated as identities.

Analyze:

* whether this semantic choice caused implementation/proof burden;
* whether it enabled anything useful;
* whether the experiment provides evidence for or against the design;
* whether the result merely shows internal consistency rather than practical necessity.

Do not claim that passing the stress test proves that reusable labels are the best API design.

---

## C6 — Richer graph-theory API

GraphLib currently has substantially more benchmark-relevant theory around some combination of:

* degree;
* handshaking;
* walks/trails/circuits;
* reachability/connectivity;
* edge identity;
* deletion/restriction;
* finite views.

Mathlib's frozen general multigraph API may lack some of these while its SimpleGraph API is much richer.

Determine exactly which existing GraphLib results saved work.

But separate:

> benefit of the underlying graph representation

from:

> benefit of already having more downstream API implemented.

This distinction is mandatory.

If GraphLib saves 300 lines because the handshaking lemma already exists, that is a real current-library advantage, but it is not automatically evidence that Mathlib's underlying `Graph` definition is inferior.

Conversely, if the missing theorem would be easy and natural to add upstream to Mathlib, say so.

---

## C7 — Duplication / ecosystem-fragmentation cost

A major objection in the CSLib discussion is not that GraphLib cannot work, but that duplicating graph foundations:

* fractures the formalization ecosystem;
* duplicates theorem/API development;
* raises long-term maintenance cost;
* makes interoperability harder;
* may conflict with active Mathlib graph refactoring.

This benchmark cannot directly measure years of ecosystem cost.

Therefore distinguish:

### directly measured benefit

from

### policy judgment about whether that benefit is large enough to justify a separate foundation.

Do not pretend one Hierholzer experiment resolves the ecosystem question.

However, use the measured magnitude of any GraphLib advantage to inform the discussion.

For example:

* a tiny local convenience difference would provide weak evidence for maintaining a duplicate foundation;
* a large systematic bridge/proof reduction would provide stronger evidence that there is a genuine design gap worth addressing somewhere.

Possible responses include more than:

> keep GraphLib forever

or

> delete GraphLib immediately.

Also consider:

* upstreaming missing abstractions to Mathlib;
* adding alternative constructors/views to Mathlib;
* making GraphLib a temporary experimental layer;
* migrating GraphLib theory once Mathlib's graph hierarchy stabilizes;
* keeping only genuinely algorithm-specific infrastructure downstream.

---

## C8 — Waiting for / collaborating with Mathlib refactoring

Another dispute concerns whether CSLib should:

* wait for active Mathlib graph refactoring;
* contribute required abstractions upstream now;
* or develop independently and reconcile later.

The benchmark is frozen to one particular Mathlib commit.

Therefore it can show:

> what the cost is today on the frozen version,

but cannot determine:

> what Mathlib will look like after ongoing refactors.

Treat this as a major limitation.

If a benchmark difficulty is obviously addressable by a small upstream theorem or constructor, identify that.

---

## C9 — Is separate GraphLib necessary, or merely useful?

This distinction is critical.

Possible conclusions include:

* Mathlib is sufficient, but GraphLib is significantly more convenient;
* Mathlib is sufficient and the convenience difference is small;
* GraphLib provides a qualitatively different abstraction that matters in this benchmark;
* differences come almost entirely from API maturity rather than core representation;
* results are mixed.

Never equate:

```text
GraphLib is more convenient
```

with:

```text
a separate GraphLib foundation is necessary.
```

Likewise never equate:

```text
Mathlib can implement Hierholzer
```

with:

```text
there is no possible ergonomic/design advantage to GraphLib.
```

---

## C10 — `TimeM` / writer-monad concerns

The benchmark uses the frozen manually instrumented abstract RAM ledger based on `TimeM`.

The CSLib discussion around #804 notes reservations about directly using writer monads for algorithm costs.

This issue is orthogonal to the graph-foundation comparison.

The report must state clearly:

* what the resource theorem proves;
* what remains manually trusted;
* why the common frozen instrumentation makes the two implementations comparable;
* why the result is not a theorem about Lean evaluator/native wall-clock runtime.

Do not count `TimeM` friction against either graph foundation.

---

# 4. Subagent assignments

Spawn exactly four subagents.

They work independently first.

---

## Subagent A — Evidence and metrics auditor

Your job is to establish the factual benchmark record.

Inspect both preserved blind first-attempt commits and both implementation reports.

Independently verify rather than trusting reported metrics.

Check at least:

* exact base commit;
* exact first-attempt commit for each side;
* Common manifest equality;
* files created;
* build success;
* mandatory theorem existence;
* mandatory stress cases;
* presence/absence of `sorry` / `admit`;
* raw tick policy;
* representation schema;
* representation existence;
* computable-constructor status;
* concrete resource constants;
* `I = 2m`;
* final `C`;
* representation-footprint constants;
* noncomputable declarations;
* main axioms;
* LOC categories from the frozen protocol.

Re-run builds/tests where practical without modifying source.

If a reported metric is wrong, use the independently verified value and flag the discrepancy.

Produce a normalized side-by-side metric table.

Do not interpret which architecture is better beyond obvious factual observations.

---

## Subagent B — Technical architecture comparison

Ignore the CSLib politics initially.

Read the actual implementations closely and compare:

1. mathematical semantic adapters;
2. certified incidence representations;
3. representation-existence proofs;
4. endpoint bridging;
5. edge-identity handling;
6. loop handling;
7. parallel-edge handling;
8. algorithm state;
9. Hierholzer core;
10. correctness invariants;
11. output reconstruction;
12. handshaking/degree reasoning;
13. resource proof;
14. space accounting.

For every material difference, determine its primary cause:

* underlying graph representation;
* existing graph API maturity;
* generic Lean/data-structure issue;
* different local implementation choice;
* benchmark/time-framework issue.

Use the frozen A/B/C/D/E friction taxonomy.

Identify where the implementations are essentially isomorphic despite different foundations.

Identify where they genuinely diverge.

Produce a technical comparison without knowing or caring which result is politically convenient.

---

## Subagent C — CSLib debate reconstruction and claim mapping

Read the relevant portions of #503, #804, #805 and linked technical discussions.

Construct the strongest fair versions of the competing positions.

Build a claim matrix using `C1`–`C10`.

For each claim, record:

* who/what discussion motivates the claim;
* exact source link(s);
* whether the Hierholzer benchmark directly tests it;
* what evidence would support or weaken it;
* whether it is primarily technical, ergonomic, or ecosystem-policy.

Do not use rhetoric such as "obviously", "meaningless", or "they proved them wrong."

Do not adjudicate based on tone.

Separate:

```text
technical claim
```

from:

```text
project-governance preference
```

and:

```text
future-looking prediction.
```

---

## Subagent D — Adversarial referee / threats-to-validity reviewer

Assume the preliminary comparison is wrong and try to break it.

Look for:

* unequal implementation quality;
* unequal human intervention;
* one agent choosing a clearly inferior representation;
* hidden preprocessing;
* hidden output work;
* noncomparable theorem strength;
* different runtime boundaries;
* different cost assumptions;
* different LOC categorization;
* GraphLib getting credit for generic API maturity;
* Mathlib getting credit for pushing complexity into noncomputable preprocessing;
* GraphLib getting penalized for stronger optional native results;
* code-generation artifacts contaminating LOC;
* differences caused by agent luck rather than foundation design;
* benchmark overfitting;
* conclusions that generalize beyond what one Hierholzer experiment supports.

Explicitly assess whether either side's implementation appears sufficiently suboptimal that winner claims should be weakened.

Do NOT repair the implementations.

If you identify an obvious symmetric follow-up optimization experiment, describe it as future work only.

Produce a referee-style validity report.

---

# 5. Main-agent evidence discipline

The main agent must synthesize all four reports and inspect the key evidence independently.

Every important conclusion in the final report should be distinguishable as one of:

### OBSERVED

Directly verified from source/build/metrics.

### REPORTED

Claimed by an implementation report but not independently reproduced.

Use this category sparingly.

### INFERENCE

A reasoned interpretation of observed facts.

### EXTERNAL CONTEXT

A claim or argument from CSLib GitHub/Zulip discussion.

### NOT TESTED

A broader question the benchmark does not resolve.

You do not need to prefix every sentence mechanically, but the report must make these epistemic boundaries obvious.

Do not turn inference into fact.

---

# 6. Preserve the blind-first-attempt evidence

Before comparing:

1. identify each side's preserved blind first-attempt commit;
2. verify neither one includes cross-side information;
3. use those snapshots as the primary comparison objects.

If either branch has later commits, distinguish:

```text
blind first-attempt result
```

from any later same-side cleanup.

Do not let later unblinded changes replace the primary evidence.

This task itself must not modify the two experimental implementations.

---

# 7. Normalize LOC and metrics

Use one common script/rule on both sides.

Follow Section 18 of the frozen protocol.

At minimum report:

| Metric                                | GraphLib | Mathlib |
| ------------------------------------- | -------: | ------: |
| Executable representation LOC         |          |         |
| Representation/bridge theorem LOC     |          |         |
| Algorithm-core LOC                    |          |         |
| Correctness-proof LOC                 |          |         |
| Time-analysis LOC                     |          |         |
| Generic DS support LOC                |          |         |
| Graph-specific helper LOC             |          |         |
| Tests LOC                             |          |         |
| Total adjusted side-specific Lean LOC |          |         |
| Representation invariants             |          |         |
| Algorithm-state invariants            |          |         |
| Bridge lemmas                         |          |         |
| Graph-specific helper obligations     |          |         |
| Noncomputable construction uses       |          |         |
| Executable constructor available?     |          |         |
| `c0`                                  |          |         |
| `cV`                                  |          |         |
| `cE`                                  |          |         |
| `cI`                                  |          |         |
| coefficient of `m` after `I=2m`       |          |         |
| final `C`                             |          |         |
| `r0`                                  |          |         |
| `rV`                                  |          |         |
| `rE`                                  |          |         |
| `rI`                                  |          |         |
| main theorem axioms                   |          |         |
| mandatory stress cases passing        |          |         |

Do not use raw LOC as the main conclusion.

For disputed classification decisions, explain them.

---

# 8. Compare three layers separately

This is one of the most important report requirements.

## Layer 1 — Mathematical specification / bridge

Compare everything required to move from:

```text
mathematical graph
```

to:

```text
certified executable incidence representation
```

This is where the GraphLib-vs-Mathlib representation debate is most directly tested.

Include:

* endpoint access;
* edge identity;
* finite enumeration;
* representation existence;
* degree correspondence;
* incidence correctness;
* noncomputability;
* bridge invariants.

---

## Layer 2 — Executable Hierholzer core

Once both sides have their certified dense incidence representation, compare:

* representation payload;
* timed core;
* state;
* stack;
* cursors;
* used flags;
* output.

Ask:

> After crossing the representation boundary, how much of the foundation difference remains?

If the cores are effectively the same, say so explicitly.

That would be evidence about the separation-of-specification-and-implementation thesis.

---

## Layer 3 — Mathematical correctness/resource proof back to graph theory

Compare the work needed to prove:

* link validity;
* exact actual-edge coverage;
* Eulerian consequences;
* connectivity usage;
* degree/handshaking;
* `I = 2m`;
* optional native circuit adapters.

This layer may expose differences in existing theorem API rather than executable representation.

Label that distinction carefully.

---

# 9. Counterfactual analysis

For every substantial advantage, ask:

> Would this advantage survive a small, natural upstream addition to the other library?

Examples:

* missing degree definition;
* missing handshaking lemma;
* endpoint constructor/view;
* finite incidence enumeration;
* a walk/trail abstraction.

Classify advantages roughly as:

### Structural

Would require changing the core graph representation or its fundamental semantics.

### API-level

Could plausibly be repaired by adding ordinary reusable theorems/constructors/views on top of the existing representation.

### Maturity-level

Exists simply because one library has much more downstream theory implemented today.

This section is essential for interpreting whether a separate foundation is justified.

---

# 10. Special analysis: computability

Write a dedicated section answering:

> What did "computable mathematical graph specification" buy in this actual benchmark?

Do not answer abstractly.

Trace the actual code.

For GraphLib:

* where were bundled endpoints used?
* were they used in executable code, bridge construction, proofs, or all three?
* did the timed Hierholzer core directly benefit?
* did GraphLib nevertheless need a dense incidence representation?

For Mathlib:

* where was `Classical.choose` / noncomputability used?
* was it confined to representation existence/construction?
* did any noncomputability enter the timed transitive call graph?
* what proof obligations resulted?

Then state the strongest conclusion supported by the experiment.

Possible examples of acceptable conclusions:

> Specification computability was not required for the linear-time core, but reduced representation-construction proof burden by X.

or:

> Once a certified incidence representation was supplied, specification computability had no measurable effect on the algorithm core, and the bridge difference was small.

or another result supported by evidence.

Do not force a predetermined answer.

---

# 11. Special analysis: edge identity and reused labels

GraphLib treats a full bundled `Edge α β` as actual edge identity.

Its `endpointsLabel` is only one component, and the benchmark deliberately tests reused labels at different endpoints.

Mathlib uses mathematical edge values whose endpoint relation is constrained by `IsLink`.

Explain precisely:

* how each benchmark representation enumerates actual edges;
* whether reused GraphLib labels create any ambiguity;
* what obligations were needed to avoid treating labels as IDs;
* whether the semantic difference mattered to Hierholzer;
* what, if anything, this says about the recent CSLib question of whether label reuse across endpoint pairs should be allowed.

Do not overgeneralize from one algorithm.

---

# 12. Special analysis: current API versus foundational representation

Construct a table like:

| Observed advantage | Size | Cause | Structural/API/Maturity | Plausible upstream fix? |
| ------------------ | ---: | ----- | ----------------------- | ----------------------- |
| ...                |  ... | ...   | ...                     | ...                     |

This is necessary because otherwise a mature GraphLib module may be credited as evidence for its underlying representation when the same theorem could simply be added to Mathlib.

Likewise, do not dismiss a current API advantage merely because it *could* be upstreamed: it is still a real current engineering advantage.

Report both facts.

---

# 13. Map benchmark evidence to CSLib claims

Create a claim-evidence table.

Use conservative statuses:

* **Supported in this benchmark**
* **Partially supported**
* **Weakened**
* **Contradicted by this benchmark**
* **Not tested**
* **Mixed / depends on interpretation**

Avoid the unqualified word `refuted` unless the claim is literally universal and this benchmark supplies a counterexample.

Example structure:

| Claim                                              | Benchmark relevance | Evidence | Status | Scope                       |
| -------------------------------------------------- | ------------------- | -------- | ------ | --------------------------- |
| Mathlib Graph cannot support verified algorithms   | direct              | ...      | ...    | Hierholzer / frozen version |
| computable spec is necessary for algorithm runtime | direct              | ...      | ...    | ...                         |
| bundled endpoints reduce bridge burden             | direct              | ...      | ...    | ...                         |
| thin executable representation is sufficient       | direct              | ...      | ...    | ...                         |
| separate GraphLib is worth ecosystem duplication   | indirect            | ...      | ...    | policy not resolved         |
| ...                                                |                     |          |        |                             |

This should be one of the report's central sections.

---

# 14. Discuss PR #804/#805 fairly

Explain what those PRs established and what they did not establish.

They are DFS demonstrations intended as evidence that:

```text
Mathlib graph specification
+
separate executable adjacency representation
```

can support algorithm correctness and time analysis.

This Hierholzer benchmark is a stronger stress test because it requires:

* actual edge identity;
* two paired darts per undirected edge;
* loops;
* parallel edges;
* edge-used state;
* endpoint correspondence;
* exact Eulerian edge coverage.

Assess whether the Hierholzer results reinforce, qualify, or weaken the lesson of #804/#805.

Do not portray #804/#805 as endorsed production architecture merely because the code exists.

Read their actual PR descriptions and context.

---

# 15. Ecosystem-cost interpretation

Write a careful section titled approximately:

## Does the measured advantage justify a separate CSLib graph foundation?

This must not pretend to compute an objective answer.

Instead discuss:

### Evidence from this benchmark

What measurable GraphLib advantage/disadvantage exists?

### Costs not measured here

* duplicated theorem development;
* interoperability;
* contributor confusion;
* future Mathlib evolution;
* maintenance;
* migration;
* cross-library conversions.

### Possible architectural responses

Depending on the observed results, discuss options such as:

1. keep GraphLib as an independent foundation;
2. keep developing GraphLib temporarily but design for later migration;
3. upstream specific missing API/constructors to Mathlib;
4. use Mathlib as specification and keep only executable algorithm representations in CSLib;
5. use a compatibility layer;
6. run additional discriminating benchmarks before deciding.

Do not recommend a drastic repository decision from weak evidence.

---

# 16. Identify the next best discriminating experiment

Regardless of outcome, propose 1–3 next experiments that would most reduce remaining uncertainty.

Do not just propose another arbitrary graph algorithm.

Choose based on what this benchmark failed to distinguish.

For example, depending on the results:

* an algorithm involving repeated graph modification;
* contraction;
* residual-network edge reversal;
* directed multigraphs;
* weighted shortest paths;
* MST;
* an algorithm whose correctness deeply uses native walk/path theory.

For each proposed experiment explain:

> Which unresolved architecture claim would this test?

Do not implement it.

---

# 17. Threats to validity

Include a substantial section on limitations.

At minimum:

* one algorithm;
* one frozen Mathlib commit;
* one frozen GraphLib snapshot;
* AI-generated implementations;
* stochastic agent quality;
* possible differences in implementation ingenuity;
* manual `TimeM` ledger;
* preprocessing excluded from primary time;
* common dense incidence interface narrows the design space;
* richer GraphLib current API;
* ongoing Mathlib refactoring;
* raw LOC ambiguity;
* noncomputability not equivalent to runtime inefficiency;
* no long-term maintenance-cost measurement.

Explicitly say which conclusions remain robust despite these limitations.

---

# 18. Report structure

Use approximately this structure.

# Hierholzer Graph-Foundation Benchmark: GraphLib vs Mathlib

## 1. Executive summary

Give the main outcome in no more than ~10–15 bullets or compact paragraphs.

State:

* what clearly differed;
* what did not differ;
* strongest evidence for GraphLib;
* strongest evidence for Mathlib architecture;
* what the benchmark does not decide.

Do not bury the conclusion.

## 2. Experimental setup and provenance

* protocol;
* Common;
* frozen commits;
* blind-development procedure;
* first-attempt commits;
* build verification.

## 3. Implementation overview

### GraphLib

### Mathlib

Describe each without evaluation first.

## 4. Normalized quantitative comparison

Tables from Section 7.

## 5. Mathematical specification and representation bridge

## 6. Executable Hierholzer core

## 7. Functional correctness proof

## 8. Time and space analysis

## 9. Computability and preprocessing

## 10. Edge identity, loops, parallel edges, and reused labels

## 11. Existing API reuse versus foundational design

Include structural/API/maturity classification.

## 12. Engineering experience and failed approaches

## 13. Mapping the results to the CSLib #503/#804/#805 debate

Include the C1–C10 claim matrix.

## 14. Does this justify a separate CSLib graph foundation?

Careful evidence-based discussion.

## 15. Threats to validity

## 16. Recommended next steps / discriminating experiments

## 17. Bottom-line conclusions

Use three subsections:

### What this benchmark establishes

### What it suggests but does not establish

### What it does not test

## Appendix A. Exact source/commit/build provenance

## Appendix B. Metric normalization rules

## Appendix C. Detailed friction classification

## Appendix D. Relevant CSLib discussion references

---

# 19. Writing style

The report is intended to be useful to technically sophisticated Lean/CSLib/Mathlib contributors.

Write in a neutral technical style.

Avoid:

* advocacy language;
* "we won";
* "X was right all along";
* reading motives into contributors;
* comments on interpersonal tone;
* rhetorical exaggeration.

Prefer formulations such as:

> In this benchmark...

> The experiment provides evidence that...

> This does not by itself imply...

> The observed difference is primarily attributable to...

> A small upstream API addition would remove this particular gap...

Be willing to conclude that an argument previously used to motivate GraphLib is not supported by the benchmark.

Be equally willing to identify real GraphLib advantages if the evidence shows them.

The value of the report comes from being credible to someone who entered the discussion disagreeing with its eventual conclusion.

---

# 20. Verification before writing conclusions

Before finalizing:

1. Subagent A verifies every number in the headline comparison table.
2. Subagent B verifies every claimed technical cause.
3. Subagent C verifies that every CSLib position is represented fairly and linked to source.
4. Subagent D attacks the draft conclusions and lists overclaims.
5. Main agent repairs all substantiated issues.

For each major headline conclusion, ask:

> Could a skeptical maintainer point to the source and say this is factually wrong or causally unsupported?

If yes, weaken or repair it.

---

# 21. No cross-side optimization in this task

Do not change either implementation after unblinding.

If one side appears to have made a clearly avoidable poor design choice, do three things:

1. document the issue;
2. estimate how much it might affect the comparison;
3. propose a symmetric follow-up optimization run.

Do NOT silently improve that side and then compare its modified code against the other's blind result.

The primary purpose of this report is to preserve and analyze the controlled blind experiment.

---

# 22. Final deliverables and stopping condition

Deliver:

```text
Benchmarks/Hierholzer/COMPARISON_REPORT.md
```

Optionally create a small graph-neutral metrics extraction script only if necessary to reproducibly compute normalized LOC/metrics.

If such a script is created:

* keep it outside either side-specific implementation;
* document it;
* make it symmetric;
* do not modify either experiment.

At the end of the task report:

* comparison report path;
* GraphLib first-attempt commit;
* Mathlib first-attempt commit;
* whether both independently rebuilt;
* whether any reported metric was corrected;
* one-sentence benchmark conclusion;
* one-sentence statement of what remains unresolved.

Do not modify or merge either side's implementation.

Do not begin the next algorithm benchmark.
