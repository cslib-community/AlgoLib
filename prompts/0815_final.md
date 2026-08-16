# TARGET_PHASE: Phase 9

Implement **TARGET_PHASE only** from the GraphLib foundation implementation plan. Do not continue to the next phase.

First read:

1. `AGENTS.md`
2. `GraphLib/NAMING.md`
3. `Reports/2026-08-14_GRAPHLIB_EDGE_REPRESENTATION_DECISION.md`
4. the TARGET_PHASE section of `Reports/2026-08-14_GRAPHLIB_FOUNDATION_IMPLEMENTATION_PLAN.md`
5. `Reports/GRAPH_FOUNDATION_STATUS.md`

Then inspect the actual repository state, including current definitions, imports, downstream usages, git diff/status, and relevant existing tests.

Do not rely on memory from previous Codex sessions.

## Task

Complete the work assigned to TARGET_PHASE:

* required definitions;
* routine API required by the phase;
* migrations/renames/deletions;
* immediate downstream repairs;
* phase-specific tests and regression targets;
* the phase exit condition.

Do not implement later phases opportunistically.

If an earlier-phase defect blocks the current phase, make the smallest necessary repair and record it in the status file.

After completion, push it to Github. The commit message is "Phase" + the number of TARGET_PHASE.

## Subagents

The main agent should normally be the only writer.

Use up to four subagents only when they materially help. Prefer read-only subagents for:

* preflight dependency/API exploration;
* diff/API/naming review;
* build and regression triage;
* one difficult phase-specific technical question.

Do not use all four by default, and do not run overlapping write-heavy agents.

A good default workflow is:

```text
preflight
→ main implementation
→ review + testing
→ main fixes
```

## Implementation rules

Follow `AGENTS.md` and the final plan rather than redesigning settled architecture.

Search all usages before making breaking public-API changes.

Compile incrementally rather than waiting until the end.

Preserve the validated:

```text
VertexSeq → SimpleWalk → SimplePath → SimpleCycle
→ InSimpleGraph → Girth → MooreBound
```

regression chain whenever required by the phase exit condition.

Do not add production `sorry`, contraction APIs, speculative executable graph representations, implicit lossy coercions, or unrelated cleanup.

For the general noninjective `mapVertices` yellow flag, follow the policy in `AGENTS.md`.

If context is compacted or a decision becomes unclear, reread the relevant repo documents instead of reconstructing it from chat memory.

## Before stopping

Reread the TARGET_PHASE section and its exit condition.

Then:

1. run the required phase tests/builds;
2. fix failures caused by this phase;
3. inspect the final diff for unrelated changes;
4. update `Reports/GRAPH_FOUNDATION_STATUS.md`;
5. mark the phase `COMPLETE`, `PARTIAL`, or `BLOCKED`;
6. stop without beginning the next phase.

In your final response, report concisely:

* phase status;
* major files/API changed;
* deviations or deferred items;
* tests run and results;
* whether the exit condition is satisfied;
* the recommended next action.
