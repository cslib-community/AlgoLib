# Graph Foundation Review Status

## Current state

* Last updated: 2026-08-16
* Review status: CONVERGED_WITH_DEFERRED_ITEMS
* Current round: 2 of at most 2
* Current step: Complete
* Working tree notes: Before this review, `AGENTS.md` was deleted, `prompts/0815_final.md` was modified, and the review prompt/status/report files were untracked. Those user-owned changes remain out of scope and preserved. Only the main agent writes repository files.

## Review counts

| Round            | S0 | S1 | S2 | S3 |
| ---------------- | -: | -: | -: | -: |
| Round 1 found    |  0 |  3 | 16 |  2 |
| Round 1 accepted |  0 |  2 | 13 |  2 |
| Round 2 found    |  0 |  0 |  4 |  2 |
| Round 2 accepted |  0 |  0 |  3 |  1 |

Raw found counts preserve every reviewer report. Accepted counts are deduplicated; corroborating
reviewer IDs receive one final disposition.

## Finding disposition

* OPEN: None.
* FIXED (19): R1-A01, R1-A02, R1-A03; merged R1-D01/R1-B01/R1-C03; R1-D02; R1-D03; merged R1-D04/R1-B06; narrowed R1-B02; narrowed R1-B03; R1-B04; R1-B05; R1-C01; R1-C04; R1-C05; R1-C06; R2-C01; R2-C02; R2-B01; merged R2-B02/R2-D01.
* DEFERRED (2): R1-D05 and R1-C07, both S3.
* REJECTED (2): R1-C02 as a single actionable S2 because no evidence justified a wholesale simp-layer rewrite; R2-D02 as an S3 because operation normalization intentionally rewrites reverse/delete before degree simplification, while the direct reverse-degree theorem remains available and a family of redundant bridge rules would enlarge the simp surface.
* HUMAN_DECISION (0): None.

## Round 1 accepted findings and repair verification

| Canonical ID | Severity | Disposition | Verification |
| ------------ | -------- | ----------- | ------------ |
| R1-A01 | S2 | FIXED | `Path.lean` imports `Walk.Walk`; full build green. |
| R1-A02 | S2 | FIXED | `SimpleDiCycle.lean` imports `SimplePath`; full build green. |
| R1-A03 | S2 | FIXED | `Weight.Walk` imports concrete simple-path realization leaves. |
| R1-D01/B01/C03 | S1 | FIXED | Directed finite transport covers induce/restrict/delete/map/relabel/reverse without reverse-inference loops; transformed degree and flow clients elaborate. |
| R1-D02 | S2 | FIXED | General paths have injective map and vertex/tag relabel operations, projections, realization, and weight transport. |
| R1-D03 | S2 | FIXED | Exact path gluing, realization, and additive weight laws are public and tested. |
| R1-D04/B06 | S2 | FIXED | Relabel/reverse aggregate outflow/inflow, relabel flow value, and feasibility equivalences are public and tested. |
| R1-B02 | S1 | FIXED | Cycle-specific public relabel operations replaced the private Acyclic reconstruction block; speculative blanket carrier maps were not added. |
| R1-B03 | S2 | FIXED | Compact path/cycle realization wrappers cover membership, monotonicity, transformations, relabeling, and path glue. |
| R1-B04 | S2 | FIXED | Reverse incidence-image and in/out-degree swap laws exist for both directed graph families. |
| R1-B05 | S2 | FIXED | Induce commutes canonically with restrict/delete for all four graph families. |
| R1-C01 | S2 | FIXED | Two undirected commutativity equalities are no longer simp rules. |
| R1-C04 | S2 | FIXED | Public arc APIs use source/target and descriptive zip projection vocabulary. |
| R1-C05 | S2 | FIXED | Transformed membership iff lemmas use canonical `mem_edgeSet_*` names. |
| R1-C06 | S2 | FIXED | Edge/arc relabel algebra uses `_id`, `_comp`, and `_inverse`. |

## Human decisions

None identified.

## Deferred S2/S3

* R1-D05 (S3, DEFERRED): successful builds still emit stable `grind` suggestions and routine linter warnings. Leave these for a separate proof-compression/diagnostics pass.
* R1-C07 (S3, DEFERRED): missing public-doc lints, mostly on walk accessors and predicates, belong in a focused documentation pass.

## Repairs completed

* Narrowed three leaf import edges while preserving the acyclic umbrella structure.
* Added one-way finite vertex/edge transport through standard graph operations and local finite-incidence helpers; retained the finite-V/finite-E separation.
* Removed derived target-finiteness hypotheses from degree transformation theorems where synthesis is now safe.
* Added directed reverse incidence and degree laws.
* Added exact general-path glue plus path/cycle relabel carriers, realization wrappers, and weight laws.
* Replaced private Acyclic cycle transport with public carrier operations.
* Added induce/restrict/delete normalization across all graph families.
* Added aggregate flow relabel/reverse laws and feasibility transport.
* Applied the verified naming and simp-attribute corrections.
* Expanded `FiniteDegree`, `Walk`, and `WeightNetwork` foundation regressions.
* Added simple-family path glue, path-weight glue, and relabel-weight symmetry.
* Added public path/cycle accessor normalization and relabel identity/composition/inverse laws.
* Added directed double reverse-image normalization and promoted nested reverse/restrict/delete tests.
* Canonicalized `mem_edgeSet_forgetDirection`.

## Tests currently green

* Full requested root/import-all/leaf build: success, 1182 jobs.
* Six semantic foundation stress files: `Basic`, `Transformations`, `FiniteDegree`, `Walk`, `Connectivity`, and `WeightNetwork` all succeed.
* Focused cycle/Acyclic, realization, degree, weight-walk, and network builds all succeed.
* `git diff --check`: success.
* No forbidden legacy names and no newly added `sorry`/`admit`; remaining `sorry`s are pre-existing in the excluded Union-Find/Inverse-Ackermann scaffolds.

## Tests currently failing

None.

## Structural state

* Dependency DAG: acyclic; no layer inversion found; the three verified broad leaf imports are repaired.
* Namespace/folder layout: coherent; no move/split/merge warranted.
* Semantic invariants: no S0 discovered; locked stress cases remain green.
* Public API: finite transforms, path/cycle transports, reverse-degree laws, operation algebra, and flow transport now cover the concrete client gaps.
* Client boundary: mathematical BFS, SCC, shortest-path, MST, and flow skeletons are expressible; executable enumeration and algorithm-specific data structures remain intentionally client-driven.

## Next action

Review complete. Proceed to one real algorithm integration project, then make only client-driven foundation adjustments before freezing the public API.

---

# Review log

## Round 1

### Reviewer A — architecture

* Completed: 2026-08-16
* Finding IDs: R1-A01, R1-A02, R1-A03
* Result: no S0/S1; three unnecessarily broad leaf imports, all fixed.

### Reviewer B — semantics/API

* Completed: 2026-08-16
* Finding IDs: R1-B01 through R1-B06
* Result: no S0; all six semantic stress files green. Verified finite transport, scoped carrier/realization, reverse-degree, operation-algebra, and flow-transport gaps; all accepted scopes fixed.

### Reviewer C — naming/redundancy/automation

* Completed: 2026-08-16
* Finding IDs: R1-C01 through R1-C07
* Result: verified two simp-commutativity and three naming-family issues, all fixed; broad simp/doc lint debt was rejected or deferred.

### Reviewer D — client simulation

* Completed: 2026-08-16
* Finding IDs: R1-D01 through R1-D05
* Result: BFS/reachability, SCC, shortest-path, MST, and forward-flow skeletons were expressible. Concrete finite, path glue/relabel, and aggregate-flow gaps were fixed; executable enumeration remains intentionally deferred.

### Round 1 repair and regression

* Completed: 2026-08-16
* Full requested build: success, 1182 jobs.
* Locked semantic stress suite: all six files succeed.
* Disposition after repair: 15 fixed, 2 deferred, 1 rejected, 0 human decisions.

## Round 2

### Reviewer A — architecture regression

* Completed: 2026-08-16
* Finding IDs: none
* Raw counts: S0 0, S1 0, S2 0, S3 0.
* Result: clean. The reconstructed 69-module / 161-internal-edge production import graph is acyclic, has no upward layer imports, and contains only the three intended import-narrowing changes. Added finiteness instances remain in `Graph.Finite` and caused no synthesis cycle in the 1182-job build.

### Reviewer C — API minimality, naming, and automation regression

* Completed: 2026-08-16
* Finding IDs: R2-C01, R2-C02
* Raw counts: S0 0, S1 0, S2 1, S3 1.
* Result pending triage: reported missing simple-family path glue/weight wrapper symmetry (S2) and one noncanonical membership theorem suffix (S3). Forbidden legacy names remain absent; simp/typeclass lint baselines did not regress, and bounded nested finiteness synthesis found no loop.

### Reviewer D — downstream client regression

* Completed: 2026-08-16
* Finding IDs: R2-D01, R2-D02
* Raw counts: S0 0, S1 0, S2 1, S3 1.
* Result pending triage: reported incomplete public accessor normalization for new path/cycle glue and relabel operations (S2), plus a transformed reverse-degree `simp` convenience gap (S3). BFS/reachability, SCC, shortest-path, MST, flow, nested finiteness, and aggregate-transport probes otherwise elaborate; the 1182-job build remains green.

### Reviewer B — semantic red team

* Completed: 2026-08-16
* Finding IDs: R2-B01, R2-B02
* Raw counts: S0 0, S1 0, S2 2, S3 0.
* Result pending triage: reported nested directed reverse/restrict/delete `simp` normalization failure (S2) and independently corroborated the path/cycle projection and relabel-algebra gap (S2). Low-heartbeat nested finiteness, negative finite-edge inference, nonzero loop/parallel/antiparallel flow, and locked transformation probes all pass.

### Round 2 triage and targeted repair

* Completed: 2026-08-16
* Accepted, deduplicated counts: S0 0, S1 0, S2 3, S3 1.
* Fixed: R2-C01 (simple-family path realization and weight symmetry), R2-C02 (canonical `mem_edgeSet_forgetDirection` name), R2-B01 (double reverse-image simp normalization), and merged R2-B02/R2-D01 (path/cycle projections and relabel algebra).
* Rejected: R2-D02 (S3), because `simpa only using ...outDegree_reverse` is already stable and operation-specific degree bridge rules would add a redundant simp family.
* Focused builds and promoted semantic regressions pass.

### Final regression and convergence

* Completed: 2026-08-16
* Full requested build: success, 1182 jobs.
* Locked six-file semantic suite: success.
* Source hygiene: `git diff --check` succeeds; forbidden legacy names are absent; no new `sorry` or `admit` was introduced.
* Final disposition: 19 fixed, 2 deferred, 2 rejected, 0 human decisions.
* Final status: `CONVERGED_WITH_DEFERRED_ITEMS`.
