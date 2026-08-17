# Hierholzer Graph-Foundation Benchmark: GraphLib vs Mathlib

Report date: 2026-08-17

This report compares the preserved blind first attempts, not subsequently optimized variants. Evidence labels have the following meanings:

- **OBSERVED** — independently checked in source, Git history, manifests, or a fresh build.
- **REPORTED** — stated in a side's implementation report but not independently recoverable.
- **INFERENCE** — an interpretation of observed evidence.
- **EXTERNAL CONTEXT** — a technical position or fact from the CSLib discussion.
- **NOT TESTED** — outside what this experiment can establish.

## 1. Executive summary

1. **OBSERVED:** Both sides implement the same six-clause Common.ValidEulerTour theorem, including actual-edge identity, loops, parallel edges, exact edge coverage, and closure. Both deliver the mandatory corollary content: GraphLib uses the official mathematical edge count, while Mathlib uses R.m, propositionally equal through m_eq_edgeCount. Both independently rebuilt, contain no sorry or admit, and audit to the same standard axioms: propext, Classical.choice, and Quot.sound.

2. **OBSERVED:** Mathlib's frozen general multigraph definition is sufficient for this stronger-than-DFS benchmark. It supports a verified Hierholzer algorithm through a certified executable incidence representation without changing the mathematical graph definition. This is a counterexample to the benchmark's hypothetical universal impossibility form, not a contradiction of a verbatim contributor claim; it does not show that both foundations are equally ergonomic.

3. **OBSERVED:** After the mathematical graph is converted to the supplied certified representation, the designs are substantially isomorphic: a dense endpoint vector, a vector of incidence arrays, two role-distinguished darts per edge, one used flag per actual edge, persistent cursors, a stack, and pop-time output consing. Neither timed core calls the mathematical graph's endpoint relation.

4. **OBSERVED:** GraphLib's bundled endpoints did not yield a general executable preprocessor in this attempt. GraphLib still uses choice to orient Sym2 endpoints; Mathlib uses choice to obtain an IsLink witness. Both general constructors choose dense equivalences, filter darts into buckets, are noncomputable, have no construction-cost theorem, and are outside the primary clock.

5. **OBSERVED:** The clearest current GraphLib API asymmetry is that it reuses pre-existing loop-corrected degree and handshaking results. Mathlib's frozen general-multigraph API lacks those declarations, so the Mathlib attempt develops local representation-relative degree/bucket and degree-sum results. The blind implementations do not isolate a net proof-burden saving, and GraphLib's walk, circuit, deletion, and connectivity libraries did not materially shorten the mandatory result.

6. **OBSERVED:** Adjusted side-specific Lean LOC are 2,382 for GraphLib and 2,093 for Mathlib. The Mathlib implementation report's 2,159 is wrong under the frozen noncomment rule: it includes exactly 66 one-line documentation comments. Category LOC and lemma counts remain secondary evidence because the two proof organizations place comparable work in different files.

7. **OBSERVED:** The proved affine totals are 51 + n + 45m + 6I for GraphLib and 28 + n + 15m + 19I for Mathlib. After each proves I = 2m, their published constants are C = 57 and C = 53. This is not evidence that Mathlib's foundation gives the faster core: on the six matched fixtures, GraphLib's exact/evaluated total is lower on every nonempty case.

8. **INFERENCE:** Resource differences are explained by local choices and an accounting asymmetry. GraphLib retains bucket context while skipping used darts and charges its Option-valued frame as three words. Mathlib re-enters its main loop for each dart and charges the same executable Option-plus-vertex shape as two words by appealing to a separate edge/sentinel encoding that is not used by, or refinement-connected to, the core. None of this depends on bundled endpoints versus relational IsLink edges.

9. **OBSERVED + INFERENCE:** Source theorems state representation constants (r0,rV,rE,rI) = (6,2,2,2) for GraphLib and (5,2,2,2) for Mathlib, but the reports count top-level containers differently. A comparison-only flattened-schema audit that counts two sizes and a pointer plus header for each top-level vector gives (6,2,2,2) for both. That reconstruction is not a Mathlib theorem; the robust result is equal variable coefficients and no demonstrated foundation-level one-word advantage.

10. **OBSERVED:** GraphLib's actual edge identity is the full bundled value (tag,endpoints), not the tag. Reusing one tag at different endpoint pairs is unambiguous and passes its stress case. The case establishes internal consistency, not the practical desirability of reusable labels; GraphLib cannot use equal tag and equal endpoints to distinguish parallel actual edges, whereas Mathlib permits distinct edge-carrier values with the same endpoints.

11. **INFERENCE:** The benchmark supports the separation architecture “mathematical graph specification → certified executable representation → algorithm” for this task. It also records a real present-day GraphLib API advantage. It does not produce a global winner.

12. **NOT TESTED:** One blind Hierholzer experiment cannot measure ecosystem fragmentation, maintenance, contributor coordination, future Mathlib refactoring, or migration cost. It therefore does not decide whether CSLib should permanently maintain a separate graph foundation.

## 2. Experimental setup and provenance

### Frozen contract

The authoritative contract is HIERHOLZER_BENCHMARK_PROTOCOL.md together with the frozen Common directory and its freeze report. It fixes:

- the mathematical adapter predicates and loop-corrected degree;
- weak connectivity through non-isolated vertices;
- all six fields of ValidEulerTour;
- the supplied certified representation boundary;
- the exclusion of general representation construction from the primary clock;
- the 14-component manually instrumented TimeM ledger;
- I = 2m normalization, affine bounds, final C, footprint rules, stress cases, and LOC rules.

The Common manifest object is byte-identical in the base and both experiments (SHA-256 624489ddf4f8b69e31c434fdef1bab44a6447ace777670f9b62fae54020f1910), and all four manifest entries validate in both worktrees. The frozen environment records Lean 4.30.0-rc2, Mathlib commit d802ffd29db1f5dc5a29206b1a8af62bfcc234a3, and CSLib commit 608cbe1b629a276abd3f2081f9b42dc766d8fd78.

### Preserved blind snapshots

| Item | GraphLib | Mathlib |
| --- | --- | --- |
| Common/base parent | 1b5c9f94e7cc660df254626555463ab8b2da791c | same |
| Primary blind first-attempt commit | b2fa1486db00eebf6a909395bbd303033647e107 | 3f0c77b495ccad5376a57293e70cc8b13eeea4a3 |
| Later same-side commit | 0617620b1ce498f8a5737bb2cedb5a3321b1b2f9 | none |
| Later change | report only: records the source commit hash | — |
| Source used here | b2fa148 source; 0617620 report clarification | 3f0c77b |

**OBSERVED:** Each first-attempt commit has the exact same parent. Path-scoped commit diffs add only the corresponding benchmark directory. Repository searches find no cross-side import or reference. GraphLib source at 0617620 is byte-identical to b2fa148; its later commit changes only eight Markdown diff lines. The present Mathlib worktree contains unrelated uncommitted GraphLib deletions; their origin is immaterial because this report uses the preserved commit and path-scoped diffs, never a whole-worktree diff.

The final representation schemas contain no traversal advice. **REPORTED:** each side says its representation was frozen before core work and that four same-side reviews followed the first green build. The squashed commits do not independently preserve a pre-core timeline, and Mathlib's representation manifest hashes Adapter.lean and Representation.lean but not REPRESENTATION_FREEZE.md. Temporal blindness/freeze claims therefore remain process evidence. No cross-side reference or artifact appears in the final source; that does not independently prove what an agent inspected.

### Independent verification

Every Common and side-specific Lean module, each umbrella, GraphLib's checked-in axiom audit, and both stress suites were recompiled from isolated outputs. Both builds passed. The Mathlib correctness module independently reproduced the report's unusually long clean compilation, about five minutes in the audit environment. A temporary read-only Mathlib axiom audit reproduced the same axiom set as GraphLib.

Source audits found:

- no sorry or admit;
- no side-local raw TimeM.tick or raw tick notation;
- mandatory theorem and corollary declarations on both sides;
- all seven mandatory stress families operationally passing;
- valid Common and representation manifests;
- no changes to Common, GraphLib, Mathlib, CSLib, or the protocol.

## 3. Implementation overview

### GraphLib

GraphLib's adapter maps the frozen notions to GraphLib.Graph. An actual edge is the complete GraphLib.Edge value containing a tag and Sym2 endpoints. The adapter reuses native finite views, loop-corrected degree, and a degree-sum theorem.

Its IncidenceEnumeration stores:

- endpoints : Vector (Fin n × Fin n) m;
- buckets : Vector (Array (Fin m × Bool)) n.

CertifiedIncidenceRepresentation additionally stores the dense vertex/actual-edge equivalences, representation proof, and official-cardinality equalities.

The noncomputable existence proof chooses dense equivalences and an orientation for each bundled Sym2 endpoint pair, then forms each bucket by filtering all canonical darts.

The core owns used flags, vertex cursors, a stack whose incoming edge is Option-valued, and an output list. A nested bucket scanner retains bucket context while it skips used darts. Popping conses an edge/destination step directly into traversal order; there is no timed reverse or output-copy pass.

Correctness is proved directly around the timed loop. Its central obligations relate scanned prefixes to used flags, describe a rooted linked stack and closed output trail, maintain duplicate freedom and an exact used-edge partition, prove parity closure when popping, and use reachability plus exhaustion to obtain global coverage.

### Mathlib

Mathlib's adapter implements the same frozen semantics over Mathlib.Combinatorics.Graph.Graph. Its edge carrier is arbitrary and need not store endpoints; IsLink relates edge values to endpoint pairs. Clients may nevertheless choose a bundled edge carrier. Endpoint symmetry, endpoint uniqueness, and existence for members of edgeSet are reused.

Its Representation has the same hot payload:

- an endpoint Vector indexed by dense edge ID;
- a Vector of incidence Arrays indexed by dense vertex ID;
- a Dart structure containing a dense edge ID and Boolean role;
- dense equivalences and the same endpoint, duplicate-freedom, and exact-membership laws.

The noncomputable constructor chooses dense vertex and edge equivalences, chooses one IsLink endpoint witness per edge, and filters all canonical darts into buckets.

The timed state is again used flags, cursors, stack, and output. Its executable frame, like GraphLib's, stores Option (Fin m) plus Fin n. The Mathlib accounting treats this as two words using a separate edge/sentinel encoding, but that encoder is not used by or refinement-connected to Core.run. A single recursive run function returns to its top-level branch after each inspected dart rather than retaining bucket context in a nested scanner. It also emits output by pop-time consing.

Correctness first proves a proof-only logicalRun with the same branching structure, then proves equality with the timed return value. The invariant packages cursor prefixes, stack/trail shape, edge uniqueness, used correspondence, splice relationships, and scan/pop fuel balances. A dense-certificate layer decodes the final result to Common.ValidEulerTour.

## 4. Normalized quantitative comparison

### Code and proof metrics

The same nested-block-comment-aware scanner was applied to both preserved source trees. It excludes blanks, line comments, all block comments including one-line documentation comments, Markdown, manifests, generated artifacts, and frozen Common. Totals are symmetrically comment-normalized. Category boundaries retain each implementation's dominant-purpose organization; they are not a declaration-by-declaration causal normalization. Mathlib's total also includes its stronger optional machine-checked space result, and no mandatory-only matched total is available.

| Metric | GraphLib | Mathlib |
| --- | ---: | ---: |
| Executable representation/constructor LOC | 113 | 108 |
| Representation/bridge theorem LOC | 52 | 211 |
| Algorithm-core LOC | 157 | 123 |
| Correctness-proof LOC | 1,271 | 1,078 |
| Time-analysis LOC | 311 | 152 |
| Generic DS/space/word/umbrella LOC | 0 | 137 |
| Graph-specific adapter/helper LOC | 88 | 35 |
| Tests/audit/examples LOC | 390 | 249 |
| **Total adjusted side-specific Lean LOC** | **2,382** | **2,093** |
| Raw physical Lean LOC | 2,825 | 2,594 |
| Theorem-statement LOC | 483 | 340 |
| Explicit theorem declarations | 133 | 99 |

The Mathlib report's adjusted total 2,159 and category vector are corrected here. The discrepancy is exactly 65 one-line /-- … -/ comments plus one umbrella /-! … -/ comment. GraphLib's reported 2,382 already follows the frozen rule.

These categories are descriptive, not causal. GraphLib puts generic, representation, degree, reachability, and output-decoding helpers inside one 1,271-line Correctness file and reports zero standalone generic support. Mathlib separates comparable work into Dense, Counting, Trail, Certificate, Space, and Word. Consequently, neither the 159-line bridge delta nor the 193-line correctness delta can be attributed directly to the graph foundation.

### Logical, construction, theorem, and test metrics

| Metric | GraphLib | Mathlib | Normalization note |
| --- | ---: | ---: | --- |
| Representation invariants | 5 | 5 | Mathlib's reported sixth role-distinctness fact is a derived Dart/Bool fact; GraphLib has the same fact definitionally |
| Algorithm-state invariants | 10 | 11 | Conceptual fields; packaging-sensitive |
| Principal representation/output bridge lemmas | 21 | 15 | GraphLib's report total 27 includes six adapter bridges |
| Graph-specific helper obligations | 6 | 8 | Mathlib includes adapter/counting obligations; boundary with “bridge” is judgment-dependent |
| Named noncomputable construction helpers | 2 | 8 | Syntactic count only; both perform the same categories of choice/filter construction |
| All explicit side-local noncomputable definitions | 8 | 13 | Includes definitions outside the constructor path |
| General executable constructor available? | No | No | Both provide computable closed fixtures |
| Public theorem premises | 2 typeclasses + R,s,heven,hconn | same | Same two Eulerian property premises |
| Main theorem axioms | propext, Classical.choice, Quot.sound | same | Independently reproduced |
| Mandatory stress families passing | 7/7 | 7/7 | Mathlib cost/bound checks have weaker assertion form; see below |

The bridge/helper counts are a transparent disjoint reading of the reports' inventories, not a theorem-complexity scale. Splitting one theorem into several declarations changes the count without changing the proof.

### Resource and footprint metrics

| Metric | GraphLib | Mathlib |
| --- | ---: | ---: |
| c0 | 51 | 28 |
| cV | 1 | 1 |
| cE | 45 | 15 |
| cI | 6 | 19 |
| Proves I = 2m | yes | yes |
| m coefficient after I = 2m | 57 | 53 |
| Final C | 57 | 53 |
| Source-proved (r0,rV,rE,rI) | (6,2,2,2) | (5,2,2,2) |
| Comparison-only flattened-schema audit | (6,2,2,2) | (6,2,2,2) |
| Flattened-schema estimate after I = 2m | 6 + 2n + 6m | 6 + 2n + 6m |
| Auxiliary-space result | reported estimate n + 5m + 10 | proved, for invariant states, ≤ n + 4m + 8 |

Both executable cores store the same Option (Fin m) plus vertex frame. GraphLib charges it as three logical payload words. Mathlib charges it as two by appealing to a separate edge/sentinel encoding whose range bound is proved, but which is not used by or refinement-connected to the executable frame. The resulting auxiliary-space difference is therefore partly an instrumentation/accounting comparability caveat, alongside unequal proof investment: GraphLib does not machine-check its estimate, while Mathlib proves its published one. Neither difference comes from the mathematical graph foundation.

## 5. Mathematical specification and representation bridge

### What is shared

Both sides must bridge from a finite mathematical graph to an edge-indexed executable representation. In both cases the mandatory work includes:

1. dense equivalences for actual vertices and actual edges;
2. an ordered endpoint pair for every dense edge;
3. endpoint soundness under decoding;
4. exactly two role-distinguished canonical darts per edge;
5. bucket duplicate freedom and exact membership, including two roles in one bucket for a loop;
6. cardinality equalities n = vertexCount and m = edgeCount;
7. incidence-count and degree correspondence;
8. a decoder from indexed output back to actual-edge steps.

The hot schemas and their five normalized certification obligations are effectively identical. Neither side was given or discovered a graph-foundation-native dense incidence view.

### Genuine foundational differences

GraphLib.Edge bundles tag and Sym2 endpoints as data. Equality of the full record is actual-edge identity. Mathlib Graph accepts arbitrary edge values, does not require endpoint data in the carrier, and constrains their endpoint pair through the propositional IsLink relation and uniqueness laws. A Mathlib client may itself choose a bundled edge carrier.

This changes the source of endpoint evidence:

- GraphLib projects e.endpoints, proves the vertices belong to the graph, then chooses an orientation of Sym2.
- Mathlib obtains an IsLink witness for an edgeSet member, then chooses its ordered endpoints.

GraphLib therefore has a direct, self-describing endpoint source. Mathlib's implementation chose a purely endpoint-equality dense relation and exposes explicit decode-iff lemmas. GraphLib chose decoded mathematical Link as its dense relation and later proves incidence/loop characterizations. This visible declaration difference is primarily local proof organization, not a demonstrated structural requirement of Mathlib.Graph.

**OBSERVED:** both representation constructors use Classical.choose and construct the same executable endpoint/bucket schema. **INFERENCE:** after accounting for differently placed endpoint/incidence/loop lemmas, the source does not demonstrate a large systematic bridge reduction attributable to bundled endpoints.

### Degree and handshaking

GraphLib reuses Graph.degree with loop correction and sum_degrees_eq_twice_card_edges, after adapter transport. Mathlib's pinned general-multigraph directory has no corresponding degree module, so the benchmark locally proves the representation-relative degree/bucket identities and degree-sum result needed here.

GraphLib is the only side to reuse a pre-existing general-multigraph degree and handshaking API. This is a genuine **API/maturity-level availability advantage**, because analogous declarations can naturally be stated over Mathlib's existing IsLink interface without changing Graph. The blind implementations do not isolate a net proof-burden saving: GraphLib pays adapter-transport cost, Mathlib proves only representation-relative identities rather than a new reusable standalone handshaking theorem, and both sides independently prove I = 2m.

GraphLib's native finite vertex, edge, incidence, and loop views also support adapter/cardinality transport. They are noncomputable specification views, not the executable dense incidence representation. Mathlib instead reuses IsLink symmetry/uniqueness, endpoint existence, generic finite equivalences, and Set cardinality infrastructure.

### Three-layer conclusion

| Layer | Result | Primary attribution |
| --- | --- | --- |
| Mathematical specification → certified representation | Same executable payload; different endpoint proof source and proof organization; Mathlib has more separately visible local dense/counting work | Structural endpoint model, local organization, and current API maturity |
| Certified representation → timed core | Substantially isomorphic; no mathematical graph access | Local implementation and frozen time framework |
| Core result → mathematical Euler tour/resource theorems | Same proof skeleton and theorem strength; GraphLib reuses degree/handshaking | Hierholzer mathematics, generic Lean work, and API maturity |

## 6. Executable Hierholzer core

Both cores implement the textbook edge-aware stack algorithm over dense IDs:

1. inspect the current stack vertex;
2. advance its persistent bucket cursor;
3. skip a dart whose edge is already used;
4. otherwise mark its actual edge used, choose the opposite endpoint by role, and push;
5. when the bucket is exhausted, pop and emit the incoming edge/destination step;
6. return the stored start ID with the output.

Usedness is per edge ID rather than per dart, so a loop's two roles and parallel edges behave correctly. Both outputs are already in traversal order. Neither timed program executes a final reverse/copy, graph-value materialization, or certificate check. Mathematical decoding occurs only as the protocol-permitted erased pointwise view in the correctness theorem.

The material local differences are:

- GraphLib's scanBucket retains the current bucket pointer, length, and cursor while skipping already-used darts.
- Mathlib's run re-enters the main stack/bucket branch for every inspected dart.
- GraphLib drives a nested scan fuel plus a 2m+1 structural-step potential.
- Mathlib uses 2m scan fuel and m+1 pop fuel in one recursive function.
- Both executable frames store Option (Fin m) plus Fin n.
- GraphLib charges that frame as three logical payload words; Mathlib charges it as two through a separately proved edge/sentinel encoder that is not used by or refinement-connected to run.
- GraphLib proves the timed recursion directly; Mathlib duplicates the branch structure in logicalRun and reconnects return values.

**INFERENCE:** These choices explain the observed cost, space, and proof-organization differences more directly than either mathematical graph definition. They are exactly the sort of differences that a symmetric optimized rerun could reverse without touching GraphLib.Graph or Mathlib.Graph.

## 7. Functional correctness proof

Both main theorems establish all six frozen certificate fields:

1. the vertex list has one more element than the edge list;
2. the tour begins at the requested start;
3. it finishes at the start;
4. every positional edge links consecutive vertices;
5. decoded actual edges are duplicate-free;
6. every actual edge is covered.

Both also deliver the mandatory edgeless, exact-length, and positive-edge-circuit content. GraphLib states the mathematical length bounds using the protocol's official edgeCount G; Mathlib states all three wrappers using R.m. Its proved m_eq_edgeCount makes the statements propositionally equivalent, but the official-spelling wrappers are absent. This is a minor presentation/protocol-form deviation, not weaker mathematics.

Their proof skeletons are also close:

- scanned cursor prefixes contain only used edges;
- the stack is an edge-aware dense walk rooted at the start;
- used flags correspond to stack edges plus emitted output;
- that combined edge sequence is duplicate-free;
- when an exhausted vertex is popped, even degree forces the live walk segment to close there;
- reachability from the start propagates exhaustion;
- exhaustion plus incidence implies every edge is used;
- the edge equivalence and endpoint soundness decode the dense certificate.

Loops cause the same mathematical difficulty on both sides: degree counts a loop twice while exact edge coverage counts it once. GraphLib develops edgeWeight/usedDegree lemmas over decoded incidence; Mathlib develops edgeDegree/degreeOn/fullDenseDegree over the endpoint vector. This is core Hierholzer mathematics, not evidence about one foundation.

GraphLib performs connectivity-to-coverage through the frozen Reachable predicate and encodeVertex. Mathlib's local proof organization first exposes a dense-reachability lift and then performs the same propagation. That lift has a representation-bridge component, but GraphLib still carries equivalence-mediated reachability reasoning; the source does not show that the separate declaration is an unavoidable consequence of Mathlib.Graph.

GraphLib's richer walk/trail/circuit modules were not reused. Its benchmark-local PositiveEdgeCircuit is simply the frozen conjunction, not an optional native GraphLib.Circuit adapter. No credit or penalty is assigned for the unimplemented optional adapter.

The correctness LOC difference is not interpretable as proof difficulty without reauthoring both proofs to one architecture. Mathlib's 1,078-line correctness category includes a proof-only recursion and value bridge; GraphLib's 1,271-line monolithic category embeds generic, degree, incidence, reachability, and decoder helpers that Mathlib places elsewhere.

## 8. Time and space analysis

### What the time theorem proves

Each side proves an unconditional componentwise upper bound on the manually recorded 14-event Cost for every supplied certified representation and start ID. Summing the fields gives:

- GraphLib: total ≤ 51 + n + 45m + 6I.
- Mathlib: total ≤ 28 + n + 15m + 19I.

Both prove from canonical dart membership that I = 2m, yielding:

- GraphLib: total ≤ 51 + n + 57m and final C = 57.
- Mathlib: total ≤ 28 + n + 53m and final linearC = 53.

Both Lean theorems are valid for the event traces each side instrumented, but the stack payloads use inconsistent local charges for the same Option-valued executable frame. Stack-related totals, auxiliary-space coefficients, and final C are therefore preserved blind outputs rather than a fully normalized head-to-head frame comparison.

The smaller published Mathlib C does not establish a faster implementation. It is an upper-bound coefficient obtained from different component estimates. Matched stress totals are:

| Fixture | GraphLib | Mathlib |
| --- | ---: | ---: |
| Empty | 20 | 19 |
| One loop | 63 | 66 |
| Two loops | 106 | 113 |
| Two parallel edges | 107 | 114 |
| Isolated vertex plus Eulerian component | 108 | 115 |
| Triangle | 151 | 162 |

On these fixtures GraphLib totals fit 19 + n + 43m, while Mathlib totals fit 18 + n + 47m. The unmatched seventh stress cases exercise different identity concerns: GraphLib's reused-tag triangle totals 151; Mathlib's four-edge identity case totals 208.

These affine fits describe only the six small matched fixtures; neither is a general exact-cost theorem. Their reversal relative to C is nevertheless a strong warning against a runtime “winner.” GraphLib's scanner avoids repeated context events but its general proof uses looser bounds and a three-word frame charge; Mathlib has tighter final algebra and a two-word charge for the same executable Option-valued frame but repeats main-loop context work.

GraphLib asserts exact fixture results, costs, and concrete bounds as named theorems. Mathlib proves exact tours as local facts inside seven ValidEulerTour examples, but its cost vectors and concrete withinBound values are #eval outputs rather than expected-value equalities. The independent rebuild reproduced every vector and seven true checks. The general Mathlib bound theorem is machine-checked; only the fixture regression artifact is weaker than its report suggests.

### What remains trusted

TimeM proves the sum of manually inserted abstract events. The wrappers are value-preserving and the common frozen codebook makes the two ledgers comparable, but Lean does not prove that:

- every semantically relevant machine operation received the intended tick;
- every charged operation is constant-time on a particular backend;
- persistent array writes are in-place;
- bulk initialization has the asserted per-word behavior;
- the 14 counters predict interpreter, compiler, native, cache, or wall-clock time.

Source audit and the shared protocol mitigate inconsistent instrumentation; they do not turn the result into a runtime theorem about Lean execution. TimeM, fuel arithmetic, word-width, and recurrence friction are common category E and are not charged to either foundation.

### Space

Both representations store the same variable payload: two words per vertex-level bucket slot/header contribution, two endpoint words per edge, and two words per incidence dart. Their source r0 formulas use inconsistent top-level-container conventions. Under the explicitly selected comparison-only flattened pointer-plus-header convention, the normalized logical estimate is:

> repWords = 6 + 2n + 2m + 2I = 6 + 2n + 6m.

Mathlib additionally proves auxiliaryWords ≤ n + 4m + 8 for invariant states. GraphLib reports but does not prove n + 5m + 10. The published coefficient difference partly follows from the sides' different logical charges for the same Option-valued executable frame. It is an accounting/comparability and result-strength difference, not a specification result.

## 9. Computability and preprocessing

### GraphLib trace

Bundled endpoints are used in the representation-construction and bridge proofs. For each actual edge, GraphLib reads the Sym2 endpoint value, invokes Sym2.mk_surjective, and uses Classical.choose to select an ordered pair. It also noncomputably chooses finite equivalences. The definition builds one bucket per vertex by filtering the canonical dart collection; it supplies no construction-cost theorem or meaningful executable runtime claim.

The timed Algorithm module reads only the supplied representation's endpoints and buckets. It does not project GraphLib.Edge.endpoints, enumerate GraphLib sets, or call a mathematical graph endpoint operation. GraphLib therefore still needs the dense representation and does not supply a general executable mathematical-graph-to-representation constructor.

### Mathlib trace

Mathlib uses endpoint existence from edgeSet membership and Classical.choose to select an IsLink witness, then chooses dense equivalences and builds the same endpoint/bucket arrays. Its definition likewise builds one bucket per vertex by filtering canonical darts. The explicit constructor path has more named noncomputable helper definitions, but that syntactic count does not imply greater runtime burden; no construction-cost theorem or meaningful executable runtime claim is supplied. Mathlib.Graph.Inc.other is not in the benchmark call graph.

The timed Core module sees only the supplied representation. No noncomputable definition occurs in either timed transitive call graph. The lookup from a mathematical start to a dense ID is outside the clock on both sides.

### Strongest supported conclusion

**OBSERVED:** Computable endpoint data in GraphLib was not required for the linear-time core and had no measured timed consequence once a certified representation was supplied. It provided a direct endpoint proof source, but did not eliminate other uses of choice or dense representation construction. Both definitions syntactically form each vertex bucket by filtering canonical darts; neither has a proved executable construction cost. Mathlib's noncomputability was confined to untimed construction/lookup and proof.

This does not show that preprocessing is free or that bundled endpoints can never enable a better constructor. Preprocessing was deliberately excluded, and neither side implemented the matched executable constructor that would test that claim.

## 10. Edge identity, loops, parallel edges, and reused labels

GraphLib enumerates ActualEdge G, whose elements are full bundled Edge values. Its tag field is never used as a dense identity. Equal tags at different endpoint pairs produce unequal full edge values, so the reused-Unit-tag triangle is unambiguous. The fixture's injectivity proof relies on differing endpoint bundles.

At the same endpoint pair, however, two GraphLib Edge values with the same tag are equal and cannot denote two distinct parallel actual edges. Parallel edges at fixed endpoints require different tags. Mathlib instead enumerates arbitrary edge values in edgeSet, so distinct carrier values may share the same endpoint relation; those values may be opaque IDs or may themselves be bundled.

After dense enumeration the distinction disappears from Hierholzer:

- every actual edge has one Fin m identity and one used flag;
- every edge has two Boolean-role darts;
- a loop's two darts occur in the same bucket but share one used flag;
- parallel edge IDs do not collapse;
- output decoding is through the full actual-edge equivalence.

The reused-tag stress case confirms that this GraphLib implementation never confuses tags with actual edges. It did not add material algorithm-core burden and shows the semantics are internally consistent. It does not establish that label reuse is useful, necessary, or the best user-facing API. The most recent [PR #503 question about reused endpoint labels](https://github.com/leanprover/cslib/pull/503#issuecomment-5309869675) therefore remains a design question rather than a benchmark result.

## 11. Existing API reuse versus foundational design

| Observed advantage or difference | Measured size/effect | Primary cause | Classification | Plausible upstream or local response |
| --- | --- | --- | --- | --- |
| GraphLib native loop-corrected degree and handshaking | Pre-existing general theorem materially reused; net proof saving not isolated | Existing downstream theory | API/maturity | Add general-multigraph degree and degree-sum declarations to Mathlib |
| GraphLib edge carries Sym2 endpoints | Direct endpoint proof source, but both choose orientation and build the same R | Core edge semantics | Structural | Add an endpoint view/constructor to Mathlib to improve ergonomics without replacing Graph |
| Opaque Mathlib edge identity | Allows distinct values with identical endpoints; no timed-core penalty | Core edge semantics | Structural | Optional bundled edge type Graph α (Edge α γ), view, or compatibility layer |
| Mathlib explicit dense link/incidence/loop declarations | Separately visible work; GraphLib places analogous characterizations elsewhere; no reliable raw-LOC causal delta | Local dense-relation choice plus representation boundary | Local/API bridge | Reusable certified incidence view and decode lemmas |
| GraphLib walk/trail/circuit/deletion theory | No measured mandatory saving in this attempt | Maturity | Maturity | Test an algorithm whose proof deeply consumes these APIs |
| Both lack a ready certified dense incidence representation | Both implement benchmark-local R and noncomputable existence | Missing algorithm-facing API | API-level | Share a graph-neutral certified incidence interface/construction theorem |
| GraphLib C = 57 vs Mathlib C = 53 | Bound coefficients; fixture ordering reverses | Scanner, frame, fuel, proof tightness | Local/time framework | Symmetric optimized core/accounting rerun |
| Source r0 = 6 vs 5 | Becomes 6 vs 6 under a common convention | Header/record codebook | Local accounting | Publish one physical/logical storage convention |
| Mathlib published smaller auxiliary bound | n + 4m + 8 versus unproved n + 5m + 10 estimate | Different charges for the same Option-valued frame plus proof investment | Accounting/local | Use one executable frame/refinement and one charge, then prove both bounds |
| Mathlib lower adjusted total LOC | 289 lines, but categories and architectures differ | Mixed local proof organization | Descriptive only | A shared graph-neutral core would isolate adapter burden |

The degree/handshaking API-availability advantage is real today even if it is repairable upstream; its net quantitative saving is not isolated. Conversely, the structural endpoint/identity difference is real even though this benchmark largely neutralizes it after certification. “Could be upstreamed” does not erase current availability, while “exists today” does not prove the underlying representation is superior.

## 12. Engineering experience and failed approaches

**REPORTED:** Both sides say one representation was retained through the freeze, four read-only same-side reviews were run, and one permitted repair round followed. These process claims cannot be converted into contributor-hours or foundation difficulty.

GraphLib reports:

- correctness, especially loop parity, pop-time rotation, and reachability-to-coverage, as the dominant difficulty;
- brittle dependent Vector elaboration handled with named equalities;
- less than 40 lines of discarded elaboration attempts and no abandoned core/schema;
- reviewer correction of r0 from 4 to 6;
- two under-ticked fuel arithmetic sites repaired without changing fixture totals or C;
- a deliberately retained three-word logical charge for its Option-valued frame to avoid a broad blind-result rewrite.

Mathlib reports:

- an initial direct timed-recursion proof producing expensive proof terms;
- the final logicalRun/return-value bridge, with a local unlimited-heartbeats setting;
- an unsuccessful native_decide route for whole decoded certificates because of an unrelated noncomputable instance;
- explicit Fin constants needed in closed fixtures;
- a review-added bounded-word argument and proved space theorem;
- duplicated semantic/timed branching as the principal refactor risk.

**OBSERVED:** the final Mathlib Correctness build is materially slower than the other modules, and the final source contains the stated logical/timed split. **INFERENCE:** these experiences mainly measure independent proof architecture, generic dependent programming, and the frozen TimeM method. There is no controlled human-effort log, pre-repair source pair, token accounting, or same-author crossover, so no engineering-speed winner is defensible.

## 13. Mapping the results to the CSLib #503/#804/#805 debate

### Strongest fair versions of the positions

The case for the separate GraphLib design is stronger than “algorithms are impossible in Mathlib.” It emphasizes an edge object with embedded endpoints, set-like operations that preserve one graph type, a uniform hierarchy across graph families, existing walk/manipulation theory, and the cost of waiting for an upstream refactor. See the early [embedded-set and uniform-hierarchy rationale](https://github.com/leanprover/cslib/pull/503#issuecomment-4390252539) and the [independent-progress argument](https://github.com/leanprover/cslib/pull/503#issuecomment-5245240336). The endpoint-computability claim is distinct from efficient Lean execution: an [opposing comment](https://github.com/leanprover/cslib/pull/503#issuecomment-4387006723) notes that the PR's Set/Sym2 structures are not array- or vector-based executable adjacency structures.

The case against a duplicate foundation does not reject algorithm-specific executable structures. Its stronger architecture keeps mathematical graph theory on Mathlib's abstraction while allowing adjacency/incidence structures with correspondence theorems for algorithms. It also emphasizes duplicated theorem development, interoperability, maintenance, and the opportunity to collaborate with active upstream work. See the [ecosystem-fragmentation concern](https://github.com/leanprover/cslib/pull/503#issuecomment-5245385361), [collaborate during refactoring](https://github.com/leanprover/cslib/pull/503#issuecomment-5245469032), [maintenance prediction](https://github.com/leanprover/cslib/pull/503#issuecomment-5245652391), and the Zulip statement that [custom executable representations are compatible with an abstract mathematical graph theory](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587788293).

No precise technical comment located in the discussion states the strongest C1 sentence below verbatim. It is treated as a benchmark hypothesis/strong form, not attributed as a quotation.

### Claim-evidence matrix

| ID | Claim | Discussion motivation / source | Kind | Directness | Benchmark evidence and status | Scope |
| --- | --- | --- | --- | --- | --- | --- |
| C1 | Mathlib Graph makes verified graph algorithms impractical or impossible without replacing the definition | [#503 rationale](https://github.com/leanprover/cslib/pull/503), [duplication/feasibility response](https://github.com/leanprover/cslib/pull/503#issuecomment-5245385361), [#804](https://github.com/leanprover/cslib/pull/804) | Technical feasibility | Direct for feasibility; weak for broad practicality | **Contradicted by this benchmark in the literal impossibility form; otherwise weakened.** A complete edge-identity-sensitive Hierholzer theorem and time bound build on frozen Mathlib Graph. One AI-generated attempt does not settle general ergonomics. | This theorem, frozen Mathlib |
| C2 | The mathematical graph specification itself must provide computable endpoint access for the algorithm | [computable-endpoint case](https://github.com/leanprover/cslib/pull/503#issuecomment-5301523196), [two-layer response](https://github.com/leanprover/cslib/pull/503#issuecomment-5301836877), [specification-layer reply](https://github.com/leanprover/cslib/pull/503#issuecomment-5306438445) | Technical architecture | Direct | **Contradicted only in the narrow necessity-for-the-timed-core form; broader specification-level desirability is not decided.** Both timed cores consume only R; Mathlib endpoint choice remains outside the timed call graph, while GraphLib's benchmark also uses choice during dense-view construction and supplies no general executable dense constructor. | Runtime boundary fixed by protocol |
| C3 | Bundled endpoints substantially reduce bridge burden | [structural endpoint argument](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/586401138), [alternative constructor](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587760147) | Technical/ergonomic | Direct | **Mixed / weakened.** GraphLib has a direct endpoint source and self-describing edges; nevertheless the certified schemas, normalized obligations, constructor pattern, and proof skeleton are close. Raw bridge LOC are not causally comparable. | Dense-incidence Hierholzer |
| C4 | An external certified executable representation largely neutralizes the mathematical specification difference | [#804](https://github.com/leanprover/cslib/pull/804), [#805](https://github.com/leanprover/cslib/pull/805), [custom executable structure distinction](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587788293) | Technical architecture | Direct | **Supported in this benchmark.** Hot payload, state, core, output, invariants, and resource theorem shape are substantially isomorphic; differences remain in construction/decoding and API availability. | After crossing R boundary |
| C5 | Permitting the same endpointsLabel at different endpoint pairs is a coherent and desirable semantic choice | [local label semantics](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/588464019), [latest desirability question](https://github.com/leanprover/cslib/pull/503#issuecomment-5309869675) | Technical semantics/API ergonomics | Direct for coherence, limited for usefulness | **Coherence supported; usefulness not tested.** The fixture proves that tags are not identities. It supplies no evidence that reusable labels are practically useful or preferable; the same-tag/same-endpoint limitation remains. | Identity semantics in this algorithm |
| C6 | GraphLib's richer graph API materially reduces work | [GraphLib uniform API case](https://github.com/leanprover/cslib/pull/503#issuecomment-4390252539), [Mathlib API-coherence case](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/586397555) | API/maturity | Direct for current API | **Partially supported.** Degree/handshaking are materially reused, but the net saving is not isolated. Walk/trail/circuit/deletion theory was not materially reused. This is API/maturity evidence, not representation necessity. | Frozen library snapshots |
| C7 | A separate foundation's benefits justify duplication and ecosystem fragmentation | [fragmentation review](https://github.com/leanprover/cslib/pull/503#pullrequestreview-4899883219), [independent-progress response](https://github.com/leanprover/cslib/pull/503#issuecomment-5245240336) | Ecosystem policy | Indirect | **Not tested.** The measured API benefit informs proportionality but years of duplicated maintenance, conversions, and contributor burden were not measured. | Ecosystem policy |
| C8 | CSLib should wait for, contribute to, or proceed independently of Mathlib refactoring | [collaborate during refactor](https://github.com/leanprover/cslib/pull/503#issuecomment-5245469032), [proceed then reconcile](https://github.com/leanprover/cslib/pull/503#issuecomment-5245240336) | Governance/future prediction | Indirect/future | **Not tested.** The experiment records today's frozen cost only. Missing degree/handshaking and certified views look plausibly upstreamable. | Future governance |
| C9 | Separate GraphLib is necessary, or at least useful | [#804's necessity claim](https://github.com/leanprover/cslib/pull/804), [computable-specification distinction](https://github.com/leanprover/cslib/pull/503#issuecomment-5306438445) | Technical/ergonomic/policy | Direct for necessity; indirect for repository policy | **Necessary: weakened/unsupported for this benchmark. Useful: partially supported by current API. Overall mixed.** Mathlib suffices for this frozen Hierholzer benchmark; GraphLib remains a coherent foundation with some present convenience. | Hierholzer versus permanent policy |
| C10 | Manual TimeM/writer-ledger results should not be equated with real Lean runtime | [writer-monad reservation](https://github.com/leanprover/cslib/pull/503#issuecomment-5304682206), [execution-model caution](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587807781) | Technical, orthogonal | Direct but orthogonal | **Supported as a limitation shared by both.** The frozen ledger makes the attempts comparable; tick completeness, operation costs, code generation, and wall-clock behavior remain trusted/unmeasured. | Abstract ledger only |

### What PR #804 and #805 establish

[PR #804](https://github.com/leanprover/cslib/pull/804) and [PR #805](https://github.com/leanprover/cslib/pull/805) are draft demonstrations, explicitly not merge proposals. Their strongest legitimate result is existential: Mathlib Graph can be related to a separate executable adjacency representation for verified DFS/reachability and manually instrumented cost reasoning. PR #805 additionally illustrates noncomputable top-level construction with a separate analyzable core. PR #804's author stated that he [used TimeM despite his reservations about directly using writer monads for algorithms](https://github.com/leanprover/cslib/pull/503#issuecomment-5304682206).

They do not by themselves establish a production architecture. They are AI-generated and unreviewed in the PR record; PR #804 states that its author does not vouch for complete accuracy. More technically, vertex-reachability DFS does not require an actual-edge bijection, paired darts, loop-twice degree accounting, edge-used state, or exact Eulerian edge coverage.

In #804, the displayed round-trip theorem is adjacency equivalence (toGraph_ofGraph_adj), not an actual-edge bijection. That is enough for DFS reachability but not for Hierholzer's exact-edge theorem.

The present Hierholzer result therefore reinforces the architectural feasibility lesson of #804/#805 under a substantially stronger multigraph identity test. It also qualifies that lesson: the bridge is real, construction remains noncomputable/uncosted on both sides, and current graph-theory API maturity can still affect proof work. The later [computable-specification reply](https://github.com/leanprover/cslib/pull/503#issuecomment-5306438445) preserves a separate specification-layer design desideratum; it does not re-establish a claim that Mathlib-based algorithms are infeasible.

## 14. Does this justify a separate CSLib graph foundation?

### Evidence from this benchmark

The experiment finds no qualitative Hierholzer capability available only to GraphLib. Mathlib proves the same main theorem over the same executable boundary. Bundled endpoints remove the need to choose endpoint witnesses, but in this implementation they did not eliminate dense-representation construction, other uses of choice, or the broadly similar correctness skeleton. The clearest GraphLib-specific convenience observed is current degree/handshaking API availability and reuse; the structural identity/endpoints design remains coherent but does not affect the timed core.

This provides stronger evidence for addressing concrete API/view gaps than for claiming that a separate foundation is necessary for graph algorithms. That is an inference about the magnitude and location of the measured differences, not a repository recommendation.

### Costs not measured

The experiment does not measure:

- duplicated theorem and tactic maintenance;
- conversions and interoperability with Mathlib clients;
- contributor discovery/confusion;
- coordination or review latency;
- migration cost in either direction;
- future Mathlib graph-hierarchy changes;
- the value of GraphLib theory for algorithms unlike Hierholzer.

Those are central to the policy argument. A successful local benchmark cannot assign them a numeric weight.

### Plausible architectural responses

The evidence is compatible with several nonbinary choices:

1. keep GraphLib as an independent experimental foundation while documenting the measured current API advantages;
2. design ongoing GraphLib work for later migration or compatibility;
3. upstream general-multigraph degree, handshaking, endpoint views/constructors, and finite certified-view lemmas to Mathlib;
4. use Mathlib as mathematical specification while retaining graph-neutral executable algorithm representations in CSLib;
5. maintain a temporary adapter/compatibility layer;
6. run more discriminating benchmarks before a permanent decision.

The benchmark does not by itself justify either immediate deletion or a permanent commitment to duplication. The open question is whether structural differences matter in workloads that do not collapse to the same certified dense representation, and whether their value outweighs ecosystem costs.

## 15. Threats to validity

### Internal and construct validity

- **One implementation per side:** independent agents made different scanner, frame, recursion, proof, and file-layout choices.
- **AI-generated work:** stochastic agent quality and reviewer luck can dominate LOC, compile time, and proof elegance.
- **Unmatched execution-condition evidence:** the side prompts are closely matched, but preserved logs do not independently establish identical model configuration, token/time consumption, tool use, or human intervention.
- **Blindness/freeze provenance:** final source isolation is observable, but pre-core timing and review chronology are mostly reported.
- **Repairs differ:** GraphLib repaired footprint and two tick-accounting defects; Mathlib added word/space arguments. No matched pre-review snapshot supports intervention comparisons.
- **Common dense interface:** requiring nearly identical arrays-of-arrays representations intentionally narrows the design space and may neutralize foundation differences.
- **Manual TimeM ledger:** theorem-checked arithmetic rests on manually trusted event placement and operational assumptions.
- **Preprocessing excluded:** both noncomputable definitions build one bucket per vertex by filtering canonical darts, but no executable construction cost is proved.
- **Stress assertion asymmetry:** GraphLib asserts exact costs/bounds; Mathlib evaluates them. Independent reproduction reduces but does not eliminate regression-strength asymmetry.
- **Footprint abstraction:** source r constants are logical codebook results, not verified Lean heap-layout theorems; the 6/6 flattened comparison is an audit reconstruction rather than a Mathlib theorem.
- **Corollary presentation:** Mathlib's mandatory corollaries use R.m rather than the official edgeCount spelling, although m_eq_edgeCount proves equivalence.
- **LOC ambiguity:** declaration placement and helper attribution differ; conceptual counts are packaging-sensitive.

### External validity

- only undirected finite multigraph Hierholzer is tested;
- only one frozen GraphLib snapshot and one pinned Mathlib commit are tested;
- Mathlib graph refactoring is ongoing;
- GraphLib currently has more downstream multigraph theory, creating a maturity confound;
- noncomputability does not by itself imply runtime inefficiency, and computability does not imply an efficient representation;
- no graph mutation, contraction, residual reversal, weighted algorithm, or deep native walk/path reuse is tested;
- no long-term maintenance, interoperability, or ecosystem cost is measured.

### Conclusions robust to these threats

Despite those limitations, the following survive:

1. frozen Mathlib Graph is sufficient for the full benchmark theorem;
2. neither timed core requires direct executable mathematical-graph endpoints;
3. the certified representations and post-boundary cores are substantially isomorphic;
4. GraphLib's present degree/handshaking API was materially reused and avoids needing a new general GraphLib handshaking theorem, although net proof savings are not isolated;
5. bundled endpoints did not produce an executable general constructor or timed-core advantage here;
6. the measured constants and LOC do not justify a global winner;
7. the permanent separate-foundation policy remains unresolved.

## 16. Recommended next steps / discriminating experiments

### 1. Shared-core adapter benchmark

Freeze one graph-neutral dense Hierholzer core, correctness proof, cost proof, frame encoding, and scanner policy. Implement only the GraphLib and Mathlib mathematical adapters and certified-representation bridges independently.

This directly tests C3 and the residual part of C4 by removing local core/proof architecture as a confound.

### 2. Preprocessing-inclusive executable benchmark

Require a certified incidence constructor, prove or instrument its cost, and include it in an end-to-end theorem. Preserve the present results unchanged. The protocol must freeze one of two comparison designs:

- supply matched explicit endpoint-access certificates to both sides, which isolates incidence-construction cost but deliberately neutralizes native endpoint access; or
- state the minimum foundation-native executable assumptions separately and count any assumption difference as part of the outcome.

Finite enumerations and decidable equality alone are insufficient to give Mathlib a computable IsLink witness. Making this choice explicit is necessary for a fair C2 test of whether bundled endpoints enable a materially simpler executable preprocessor.

### 3. Mutation/native-theory benchmark

Choose an edge-identity-sensitive algorithm based on repeated graph modification—contraction or residual-network edge reversal is more discriminating than another read-only traversal—and require correctness to reuse native walk/path or deletion/contraction theory where available.

This tests whether GraphLib's uniform embedded-set/deletion/walk architecture supplies a structural advantage that the fixed dense Hierholzer boundary could not reveal. If residual networks are selected, a directed multigraph variant would also probe how each identity model handles reversals and paired residual edges.

Before drawing runtime conclusions, a separate symmetric optimization experiment should give both preserved attempts the same executable frame representation and logical charge—either both explicitly encode/refine a sentinel or both retain and charge Option—plus the same retained-bucket scanner, fuels, and tight total-cost proof. That experiment would test implementation quality, not foundation design.

## 17. Bottom-line conclusions

### What this benchmark establishes

- Both preserved first attempts verify the same strong Euler-tour specification and abstract linear bound; their mandatory corollary content is propositionally matched despite Mathlib's R.m spelling.
- Mathlib's abstract multigraph specification works with a separate certified executable incidence representation for an edge-identity-, loop-, and parallel-edge-sensitive algorithm.
- After the boundary, the mathematical foundation no longer appears in hot operations, and the state/core skeleton is substantially isomorphic; bridge and local proof architectures still differ.
- GraphLib has a real current degree/handshaking API-availability advantage, though its net proof saving is not isolated.
- Both general representation constructors are noncomputable and uncosted; neither timed core accesses the mathematical graph.

### What it suggests but does not establish

- For this class of algorithms, investing in shared executable views and missing Mathlib multigraph API could address the clearest measured API/view gap; this experiment does not quantify how much of GraphLib's broader value would be recovered.
- GraphLib's structural endpoint and identity choices may matter more for mutation-heavy or native-theory-heavy algorithms than they did here.
- The clearest GraphLib-specific convenience observed in this experiment is present API maturity, not a unique executable capability.

### What it does not test

- whether reusable endpoint labels are the best API;
- whether either side has the best possible executable constructor or core;
- native Lean performance;
- future Mathlib graph definitions;
- maintenance, interoperability, migration, or ecosystem cost;
- whether a permanent separate CSLib graph foundation is worth those unmeasured costs.

## Appendix A. Exact source/commit/build provenance

### Commits and paths

- Base/Common parent: 1b5c9f94e7cc660df254626555463ab8b2da791c.
- GraphLib primary source commit: b2fa1486db00eebf6a909395bbd303033647e107.
- GraphLib report-only follow-up: 0617620b1ce498f8a5737bb2cedb5a3321b1b2f9.
- Mathlib primary source commit: 3f0c77b495ccad5376a57293e70cc8b13eeea4a3.
- GraphLib experimental worktree inspected: /Users/yzll/GraphAlgorithms_hierholzer_graphlib.
- Mathlib experimental worktree inspected: /Users/yzll/GraphAlgorithms_hierholzer_mathlib.
- Main deliverable worktree: /Users/yzll/GraphAlgorithms_wx.

GraphLib's commit adds 11 benchmark-side files: umbrella, Adapter, Representation, Algorithm, Correctness, Resource, Stress, Audit, implementation report, representation freeze record, and representation manifest. Mathlib's commit adds 16: umbrella, Adapter, Representation, Dense, Counting, Core, Trail, Correctness, Certificate, Resource, Space, Word, Stress, implementation report, freeze record, and manifest.

### Verification record

- git worktree and git show/diff established commit ancestry and side-only paths.
- sha256sum -c validated Common and representation manifests.
- Direct lake env lean compilation covered Common, every side module, umbrellas, stress, and GraphLib Audit; isolated temporary output directories avoided changing source.
- A temporary Mathlib audit module printed axioms for representation existence, correctness, component bounds, and mathematical linearity.
- Both source trees passed git diff --check in the preserved path scope.
- Symmetric source scans checked comments/LOC, sorry/admit, raw tick use, imports, and cross-side names.

The exact side build commands are documented in each IMPLEMENTATION_REPORT.md. This comparison did not invoke lake build, edit either side, merge branches, or run an optimization.

## Appendix B. Metric normalization rules

### LOC

Code LOC are physical lines with blank lines and all comment text removed by a nested block-comment-aware scanner. Common, Markdown, manifest text, and generated output are excluded. The same rule is applied to both sources. Theorem-statement LOC count from each theorem/private theorem header through the first assignment token line, under the protocol rule.

Category attribution is by dominant declaration purpose:

1. representation schema and general construction;
2. representation/semantic/cardinality bridges;
3. timed algorithm core;
4. functional correctness and certificate proof;
5. resource recurrence/bounds;
6. generic data structure, space, and word support;
7. mathematical graph adapter/helpers;
8. tests, examples, audits, and umbrella.

The categories partition each side but do not normalize proof architecture. Total adjusted LOC are more reproducible than category deltas; neither is a semantic complexity metric.

### Concept counts

Representation invariants count semantic obligations, not derived role facts or record fields. Algorithm-state invariants follow each report's normalized persistent invariant fields. Bridge/helper counts use each report's named inventory, split disjointly where GraphLib's “bridge” total includes adapter results. They are disclosed for protocol completeness but are not used as a ranking.

### Footprint

The source theorems are preserved as reported. For comparison, the common logical rule counts:

- two stored size words;
- a pointer/handle and header word for each of the two top-level vectors;
- 2n for vertex-level bucket contributions;
- 2m for endpoint pairs;
- 2I for edge-ID/role darts;
- no proof fields or mathematical decode equivalences.

Under this explicitly selected flattened comparison convention, the audit estimate is r = (6,2,2,2) on both representations. Other consistent record/container conventions may change constant terms or expose a constant nesting cost. The robust result is equality of the variable coefficients (rV,rE,rI) = (2,2,2) and the absence of a demonstrated foundation-level size advantage.

### Resource ledger

The 14 component order is:

> initWrite, incidenceRead, endpointRead, usedRead, usedWrite, cursorRead, cursorWrite, indexOp, stackControl, stackRead, stackWrite, outputControl, outputRead, outputWrite.

The independently verified component bounds are:

- GraphLib: [n+m, 2I+4m+4, 4m+4, I, 2m+2, 2m+2, I, 2I+2m+4, 6m+7, 12m+12, 6m+9, 2m+2, 0, 4m+5].
- Mathlib: [n+m, 4I+2m+4, 2I, I, I, I+m+2, I, 2I+m+4, 3I+3m+6, 2I+4m+6, 2I+2, m+1, 0, 2m+3].

Summation yields the reported affine tuples and, after I = 2m, final constants.

## Appendix C. Detailed friction classification

| Friction | Shared work | Material asymmetry | Attribution |
| --- | --- | --- | --- |
| A — unavoidable Hierholzer/graph theory | stack/splice correctness, parity at exhausted vertices, loop-twice counting, connectivity-to-coverage, exact edge coverage | Different local parity vocabulary only | Not foundation-specific |
| B — generic Lean/data structures | dependent Vector updates, Fin bounds, list normalization, finite-cardinality transport | Mathlib logical/timed recursion bridge; GraphLib brittle dependent-vector rewrites | Generic/local |
| C — mathematical/executable bridge | dense equivalences, endpoint orientation, endpoint soundness, canonical darts, decode proof | Bundled-edge injectivity/tag semantics versus IsLink endpoint witness/uniqueness | Foundation boundary, partly structural |
| D — missing graph API | no ready certified dense executable view on either side | Mathlib lacks general-multigraph degree/handshaking; GraphLib lacks exact weak-connectivity convenience | Current API/maturity |
| E — time framework | manual wrappers, fuels, 14-field recurrences, word and persistent-array assumptions | Scanner/frame choices change constants | Common framework/local |

## Appendix D. Relevant CSLib discussion references

Primary threads:

- [CSLib PR #503 — new graph definitions](https://github.com/leanprover/cslib/pull/503)
- [CSLib PR #804 — Mathlib-graph DFS demonstration](https://github.com/leanprover/cslib/pull/804)
- [CSLib PR #805 — alternative Mathlib-graph DFS architecture](https://github.com/leanprover/cslib/pull/805)

Technically relevant comments:

- [compatibility and duplicated-definition concern](https://github.com/leanprover/cslib/pull/503#issuecomment-4276922534)
- [bundled mathematical data versus efficient executable arrays](https://github.com/leanprover/cslib/pull/503#issuecomment-4387006723)
- [embedded sets and uniform graph hierarchy](https://github.com/leanprover/cslib/pull/503#issuecomment-4390252539)
- [independent progress while upstream changes](https://github.com/leanprover/cslib/pull/503#issuecomment-5245240336)
- [ecosystem-fragmentation concern](https://github.com/leanprover/cslib/pull/503#issuecomment-5245385361)
- [collaborate with upstream during refactoring](https://github.com/leanprover/cslib/pull/503#issuecomment-5245469032)
- [maintenance-cost prediction](https://github.com/leanprover/cslib/pull/503#issuecomment-5245652391)
- [technical endpoint-computability exchange](https://github.com/leanprover/cslib/pull/503#issuecomment-5301523196)
- [two-layer specification/representation argument](https://github.com/leanprover/cslib/pull/503#issuecomment-5301836877)
- [temporary vendoring/upstream collaboration option](https://github.com/leanprover/cslib/pull/503#issuecomment-5301948145)
- [noncomputable endpoint-extraction exchange](https://github.com/leanprover/cslib/pull/503#issuecomment-5304284675)
- [response disputing that noncomputability is itself a problem](https://github.com/leanprover/cslib/pull/503#issuecomment-5304367191)
- [PR #804 and TimeM reservation](https://github.com/leanprover/cslib/pull/503#issuecomment-5304682206)
- [computable-specification reply](https://github.com/leanprover/cslib/pull/503#issuecomment-5306438445)
- [distinguishing the #804 and #805 architectures](https://github.com/leanprover/cslib/pull/503#issuecomment-5306638449)
- [latest reused-label question at the report cutoff](https://github.com/leanprover/cslib/pull/503#issuecomment-5309869675)

Relevant Zulip technical points:

- [alternative endpoint constructor](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587760147)
- [favorable response to the alternative-constructor proposal](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587764498)
- [algorithm-specific executable structures with abstract graph theory](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587788293)
- [local semantics of endpoint labels](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/588464019)
- [class-based endpoint function proposal](https://leanprover.zulipchat.com/#narrow/channel/252551-graph-theory/topic/A.20Set-based.20Multigraph.20Definition/near/616705067)
- [external computable-endpoint class interpretation](https://leanprover.zulipchat.com/#narrow/channel/252551-graph-theory/topic/A.20Set-based.20Multigraph.20Definition/near/616707968)
- [two-layer architecture](https://leanprover.zulipchat.com/#narrow/channel/252551-graph-theory/topic/A.20Set-based.20Multigraph.20Definition/near/616710569)
- [opaque-edge carrier can itself be a bundled Edge type](https://leanprover.zulipchat.com/#narrow/channel/252551-graph-theory/topic/A.20Set-based.20Multigraph.20Definition/near/616713652)
- [later conclusion that computable endpoints need not require replacing Graph](https://leanprover.zulipchat.com/#narrow/channel/252551-graph-theory/topic/A.20Set-based.20Multigraph.20Definition/near/616806111)
- [stated TimeM goal](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/588460680)
- [execution-model caution](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/New.20graph.20definitions/near/587807781)

## Final handoff

- Comparison report: Benchmarks/Hierholzer/COMPARISON_REPORT.md.
- GraphLib blind first-attempt commit: b2fa1486db00eebf6a909395bbd303033647e107.
- Mathlib blind first-attempt commit: 3f0c77b495ccad5376a57293e70cc8b13eeea4a3.
- Independent rebuild: both sides passed, including all side modules, umbrellas, stress output, and axiom audits.
- Corrected reported metrics: Mathlib adjusted LOC is 2,093 rather than 2,159; its costs/concrete bounds are executable checks rather than asserted expected equalities; source r0 values use noncomparable conventions, and the 6/6 value is only a flattened comparison audit.
- Benchmark conclusion: Mathlib is sufficient for the frozen Hierholzer theorem, the post-representation cores are substantially isomorphic, and GraphLib's clearest present advantage is reusable degree/handshaking API availability rather than a unique executable capability.
- Unresolved: this benchmark does not determine whether GraphLib's structural choices justify the unmeasured ecosystem and maintenance costs of a permanent separate CSLib graph foundation.
