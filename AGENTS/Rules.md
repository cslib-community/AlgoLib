# GraphLib Construction Rules

Prescriptive rules for anyone (human or agent) editing GraphLib. These are hard
requirements, not suggestions. More rules will be added over time.

## Rule 1 — Prefer `V(G)` / `E(G)` over `G.vertexSet` / `G.edgeSet`

Whenever you refer to the vertex set or edge set of any graph, write the scoped
notation `V(G)` and `E(G)` instead of the structure projections `G.vertexSet`
and `G.edgeSet`. This applies to every graph type (`SimpleGraph`,
`SimpleDiGraph`, `Graph`, `DiGraph`, …) and to any graph-valued expression, e.g.
`V(H)`, `V(w.toSimpleGraph)`.

* The notation is `scoped` in namespace `GraphLib`, so the file needs
  `open scoped GraphLib` in scope. Most graph files already have it.
* `V(G)` unfolds definitionally to `G.vertexSet` (via the `HasVertexSet`
  instance), so this is a surface-syntax change; proofs relying on definitional
  equality keep working, but rebuild to be sure.
* `V(G)` is a single bracketed atom, so postfix projections compose normally:
  `V(G).ncard`, `V(G).Finite`, `V(G).Nonempty`, `S ⊆ V(G)`.

### Exception: simp normal-form / definitional-projection lemmas

Do **not** apply this rule to a lemma whose whole purpose is to state what a
graph's vertex/edge set *is*, when that lemma is a `@[simp]` normal-form anchor.
Those lemmas must keep the `.vertexSet` / `.edgeSet` projection on their
left-hand side so that `simp` can match goals that arise from unfolding other
definitions (for example `SimpleGraph.subgraphOf`), which are phrased with the
projection.

Concretely, the `@[simp]` lemmas in `SimpleWalk.lean` keep the projection:

```
@[simp] lemma mem_vertexSet_toSimpleGraph (w : SimpleWalk α) {v : α} :
    v ∈ w.toSimpleGraph.vertexSet ↔ v ∈ w.support := Iff.rfl
```

Rewriting this LHS to `v ∈ V(w.toSimpleGraph)` breaks downstream `simp` calls
(they can no longer rewrite goals stated with `.vertexSet`). When in doubt, if
the lemma is `@[simp]` and its statement is the *definition* of a generated
graph's vertex/edge set, keep the projection; everywhere else, use `V(G)` /
`E(G)`.

## Rule 2 — The sequence types live in the root namespace, on purpose

`VertexSeq`, `SimpleWalk`, `SimplePath`, `SimpleCycle` (and the legacy `Snoc`
class) are declared in the **root** namespace. The graph types (`SimpleGraph`,
`SimpleDiGraph`, `Graph`, `DiGraph`) and the `V(·)` / `E(·)` notation are
declared inside `namespace GraphLib`.

This asymmetry is a decision, not an oversight. Do not "fix" it by wrapping the
sequence types in `namespace GraphLib`: the rename would touch every file in the
library, and the sequence types are deliberately free of any graph dependency
(they are pure combinatorics — see the module docstring of
`GraphLib/Theory/Structures/VertexSeq.lean`).

Two visible consequences, both expected:

* `SimpleWalk.lean` writes `open GraphLib` *inside* `namespace SimpleWalk`, so
  that `toSimpleGraph` can name `SimpleGraph`. Leave it.
* A realized-in predicate such as `GraphLib.SimpleGraph.IsSimpleWalkIn` lives in
  `GraphLib` but takes an argument whose type does not. That is fine.
