# GraphLib foundation construction

GraphLib is currently undergoing a staged rebuild of its graph foundation. Some existing source files are obsolete, incomplete, or scheduled for migration, so do not infer the intended architecture from the current tree alone.

When writing stuff into empty lean files, let the author be Weixuan Yuan.

## Source of truth

For graph-foundation work, use the following precedence:

1. the current user instruction;
2. this `AGENTS.md`;
3. `GraphLib/NAMING.md`;
4. `Reports/2026-08-14_GRAPHLIB_EDGE_REPRESENTATION_DECISION.md`;
5. `Reports/2026-08-14_GRAPHLIB_FOUNDATION_IMPLEMENTATION_PLAN.md`;
6. `Reports/2026-08-14_GRAPHLIB_ARCHITECTURE_PROPOSAL.md`;
7. current source code.

Before implementing a phase, read:

* this file;
* `GraphLib/NAMING.md`;
* the edge-representation decision;
* the relevant phase of the final implementation plan;
* `GRAPH_FOUNDATION_STATUS.md`;
* the actual source files and downstream usages touched by the phase.

If context has been compacted or an earlier decision is unclear, reopen these files instead of relying on chat memory.


## Phase discipline

The final implementation plan defines the construction phases.

When assigned Phase X:

* implement Phase X only;
* do not continue to Phase X+1;
* complete its required migrations, routine API, tests, and exit condition;
* repair an earlier-phase issue only if it blocks the current phase;
* record any such repair or deviation in `GRAPH_FOUNDATION_STATUS.md`.

Do not opportunistically implement later-phase APIs.

## Locked invariants

Do not reopen these during routine implementation.

### General edges

`Graph α β` and `DiGraph α β` keep bundled:

```lean
Edge α β
Arc α β
```

The whole bundle is actual identity. `β` is only a tag/discriminator and need not be globally unique.

For general graphs, `E(G)` contains actual `Edge` / `Arc` values. Lossy endpoint-pair images use explicit names such as `edgeEndpointPairSet` and `arcEndpointPairSet`.

Identity-sensitive APIs use actual edges/arcs, not unrestricted tags.

### Walks

Preserve the graph-independent spine:

```text
VertexSeq → SimpleWalk → SimplePath → SimpleCycle → G.Is...In
```

General walks are graph-independent as well.

For raw general walks, distinguish:

```text
tags    -- raw tag values
edges   -- reconstructed actual Edge values
arcs    -- reconstructed actual Arc values
```

Identity-sensitive statements use `edges` / `arcs`.

### Transformations

Induce/restrict/delete keep the same ambient vertex/tag types.

Follow the operation meanings and naming rules fixed in `NAMING.md`.

Do not introduce implicit lossy coercions.

### Finiteness and attached data

Do not introduce speculative executable graph representations such as `Finite*View` or `compute*Finset`.

Weights, costs, capacities, and flows are attached data, not new graph types.

For general graphs they are indexed by actual `Edge` / `Arc` values, not merely by `β`.

### Contraction

Contraction is out of scope for this construction round.

Do not add contraction files, carriers, operations, or contraction-specific theory.

## Yellow flag: general `mapVertices`

For noninjective `Graph.mapVertices` / `DiGraph.mapVertices`, try the provenance-bearing design specified in the final implementation plan first.

The locked requirement is:

> A noninjective map must not silently merge distinct actual edges while claiming identity preservation.

The exact provenance carrier is not worth forcing if real Lean/client evidence shows substantial typing or composition friction.

If that happens:

* do not redesign the entire edge representation;
* do not replace it with an unsafe simpler map;
* isolate or defer the exact public API if necessary;
* record the concrete problem and evidence in `GRAPH_FOUNDATION_STATUS.md`;
* leave the phase `PARTIAL` if its exit condition is consequently unmet.

Ordinary proof inconvenience is not enough reason to deviate.

## Implementation discipline

Before changing a public declaration, search its definitions and downstream usages.

Preserve mature existing code where the final plan says to preserve it, especially:

```text
VertexSeq
→ SimpleWalk
→ SimplePath
→ SimpleCycle
→ InSimpleGraph
→ Girth
→ MooreBound
```

At every relevant phase boundary this regression chain must compile.

Follow `NAMING.md` for new public API and docstrings.

Do not:

* add production `sorry`;
* add compatibility aliases for semantically wrong legacy APIs merely to make compilation easier;
* modify unrelated research files;
* upgrade Lean/Mathlib during this construction;
* perform unrelated broad cleanup.

Nontrivial lemmas explicitly allowed to be deferred by the plan may be deferred if the definitions and routine API remain coherent. Record them in the status file.

## Subagents

The main agent is the only writer by default.

Use subagents only when useful, primarily read-only for:

1. dependency/API exploration before editing;
2. reviewing the diff for naming/API/invariant issues;
3. running builds and regression triage;
4. investigating one difficult phase-specific question.

Do not spawn all four merely because four slots are available.

Avoid parallel writers on overlapping Lean files. Prefer:

```text
explore
→ main-agent implementation
→ review + testing
→ main-agent fixes
```

## Status file

`Reports/GRAPH_FOUNDATION_STATUS.md` is the durable handoff between sessions.

Read it before starting and update it before stopping.

Keep it concise and record:

* current/last completed phase;
* implementation completed;
* deviations from the plan;
* deferred or unresolved items;
* meaningful test commands and results;
* whether the phase exit condition is satisfied;
* the next concrete action.

Do not use it as a transcript or paste large compiler logs.

A phase is `COMPLETE` only if its exit condition from the final implementation plan is satisfied. Otherwise mark it `PARTIAL` or `BLOCKED`.

Never silently continue to the next phase.
