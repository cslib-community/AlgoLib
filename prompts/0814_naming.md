We have completed the representation investigation for GraphLib (Reports/2026-08-14_GRAPHLIB_EDGE_REPRESENTATION_DECISION.md). Treat its final representation decisions as fixed input for this task.

Your task is now to design a coherent naming convention for the GraphLib foundation. Output your result as a new markdown file NAMING.md in GraphLib folder.

## Primary goals

In priority order:

1. **Internal consistency across GraphLib.**
2. **Standard graph-theory / TCS terminology.**
3. For basic concepts with the same mathematical meaning, stay reasonably close to established Mathlib terminology and theorem-naming patterns.
4. Do **not** copy Mathlib inconsistencies or representation-specific naming when GraphLib uses a different abstraction.

The result should be a set of rules that future coding agents can apply mechanically with relatively little judgment.

## Important distinction

Treat these as two separate questions:

* **Mathematical vocabulary**: `degree`, `outDegree`, `neighborSet`, `reachable`, `induced`, `subgraph`, `arc`, etc. Standard graph theory and TCS usage should be the main authority.
* **Lean declaration grammar**: patterns such as `mem_*`, `*_iff`, `*_mono`, `map_*`, `coe_*`, `of_*`, namespace placement, theorem orientation, Set/Finset suffixes, etc. Mathlib is an important reference here.

Do not conflate the two.

## Existing code

Survey the current GraphLib thoroughly. Preserve good naming patterns that already have substantial downstream use unless there is a clear gain from changing them.

In particular, pay attention to the already-successful graph-independent chain

```text
VertexSeq
→ SimpleWalk
→ SimplePath
→ SimpleCycle
→ G.Is...In
```

and its use by Girth/Moore-bound code.

## Mathlib

Survey the relevant Mathlib graph APIs and extract useful naming **patterns**, especially for:

* adjacency;
* incidence;
* neighbor sets/finsets;
* degree;
* subgraphs;
* induced graphs;
* deletion;
* maps/relabeling;
* walks/paths/cycles;
* reachability/connectivity;
* finite APIs;
* simp and membership lemmas.

Do not mechanically imitate legacy inconsistencies.

## Finite/executable terminology

Reconsider the previous report's (Reports/2026-08-14_GRAPHLIB_ARCHITECTURE_PROPOSAL.md) names such as:

```lean
FiniteAdjView
FiniteEdgeView
FiniteVertexView
```

These names currently feel nonstandard and awkward.

Investigate both:

1. whether the underlying abstraction belongs in the current foundation at all; and
2. if it does, what its most natural name should be.

Possible terminology may include concepts such as adjacency lists, finite/enumerable graph data, graph representations, executable graph data, or views, but do not assume any of these is correct.

The mathematical Set/Finset API such as

```lean
vertexFinset
edgeFinset
neighborFinset
incidenceFinset
```

should be considered separately from any executable representation.

## Four-subagent split

Use four subagents:

1. **Mathlib naming surveyor**: extract stable naming patterns and identify known inconsistencies that should not be copied.
2. **GraphLib naming auditor**: inspect existing declarations and real downstream usage; identify conventions worth preserving and collisions/inconsistencies to fix.
3. **TCS terminology reviewer**: evaluate public mathematical names against standard graph-theory/TCS vocabulary and algorithmic usage.
4. **Consistency/lint designer**: propose mechanical rules, then stress-test them by naming a broad sample of representative declarations across all four graph types.

The parent agent must synthesize one coherent convention.

## Topics the naming guide must cover

At minimum:

* type and structure names;
* predicates and the use of `Is...`;
* noun vs verb names for graph transformations;
* singular/plural conventions;
* `Set` vs `Finset` naming;
* directed `in` / `out` terminology and word order;
* adjacency/incidence terminology;
* edge vs arc terminology;
* walk/path/trail/cycle terminology;
* general vs simple graph terminology;
* map vs relabel vs transport;
* theorem naming patterns;
* `mem_*`, `*_mem`, `*_iff`, `*_eq`, `*_mono`, `*_comm`, etc.;
* constructors and `of_*` / `mk` conventions;
* namespaces;
* notation;
* file/module names;
* abbreviations that are allowed or forbidden;
* docstring/comment conventions for public definitions versus routine lemmas.

## Stress test

Apply the proposed rules to a representative API sample covering at least:

* adjacency;
* edge/arc membership;
* neighbor sets and finsets;
* incidence;
* degree/in-degree/out-degree;
* subgraph;
* induced restriction;
* deletion;
* reverse;
* relabeling;
* walk realization;
* reachability;
* connectedness/SCC;
* finite enumeration;
* weights/capacities.

Show enough concrete proposed names to reveal awkward rules before they are adopted.

## Output

Produce a naming/style specification suitable for committing as a project design document.

It should contain:

1. core principles;
2. a compact naming grammar;
3. terminology decisions;
4. theorem-name patterns;
5. Set/Finset rules;
6. directed naming rules;
7. namespace/file-name rules;
8. minimal documentation/comment rules;
9. a table of important names to preserve/change from current GraphLib;
10. the resolution of the `Finite*View` terminology question;
11. representative examples;
12. explicit anti-patterns;
13. `LOCKED`, `PROVISIONAL`, and `DEFERRED` decisions.

The goal is not to pre-name every future lemma. The goal is to make routine future names predictable.

Do not write the full construction plan or implement the library yet.
