# GraphLib naming and API style

**Status:** prescriptive design document

**Date:** 2026-08-14

**Scope:** the GraphLib foundation and its immediate walk, connectivity, finite, and
edge-data APIs

This document is the naming standard for new GraphLib declarations and for foundation
renames. It is not a catalogue of the current tree. Where current code disagrees with a
`LOCKED` rule below, the code should migrate toward this document.

The representation decisions in
`Reports/2026-08-14_GRAPHLIB_EDGE_REPRESENTATION_DECISION.md` are fixed input. In particular,
general edges remain bundled `Edge` and `Arc` values, and the entire bundle—not its tag—is the
actual edge identity.

## 1. Core principles

Apply these in order.

1. **Give the same concept the same stem everywhere.** The graph namespace and the result type
   should carry routine context; names should not restate it.
2. **Use standard graph-theory and TCS vocabulary.** Say vertex, edge, arc, adjacency,
   incidence, neighbor, degree, path, trail, cycle, reachable, and strongly connected.
3. **Separate vocabulary from Lean grammar.** Mathlib is strong evidence for declaration shapes
   such as `mem_*`, `coe_*`, `*_iff`, and predicate namespaces. It is not authority for a term
   whose mathematical meaning differs in GraphLib.
4. **Preserve validated local APIs.** In particular, keep the graph-independent chain

   ```text
   VertexSeq → SimpleWalk → SimplePath → SimpleCycle → G.Is...In
   ```

   and the names used by Girth and Moore-bound proofs.
5. **Make loss, direction, finiteness, and identity visible.** A name must not make an endpoint
   image sound like an edge set, a tag sound like an identity, a noncomputable `Finset` sound
   executable, or a noninjective map sound like a relabeling.
6. **Prefer a rule that can be linted.** An occasional longer name is better than a short name
   whose meaning requires inspecting its definition.

The quick test is: given the namespace, declaration name, and result type, a reader should be
able to reconstruct the essential mathematical statement without being misled.

## 2. Compact naming grammar

| Declaration kind | Grammar | Examples |
|---|---|---|
| Type, structure, class, inductive, bundled certificate | singular `UpperCamel` noun | `Graph`, `Arc`, `SimplePath`, `Network` |
| Named mathematical property | normally `Is...` | `IsAcyclic`, `IsLink`, `IsArc`, `IsInducedSubgraph` |
| Existential possession property | `Has...` | `HasSimpleCycle` |
| Established relation/property exception | conventional `UpperCamel` name | `Adj`, `Inc`, `Reachable`, `Preconnected`, `Connected`, `StronglyConnected` |
| Function, accessor, operation | `lowerCamel` noun or verb phrase | `vertexSet`, `neighborSet`, `deleteEdges`, `relabelVertices` |
| `Set`-valued collection | singular semantic stem + `Set` | `edgeSet`, `neighborSet`, `incidenceSet` |
| `Finset` counterpart | identical stem + `Finset` | `edgeFinset`, `neighborFinset`, `incidenceFinset` |
| List/sequence projection | plural noun | `vertices`, `tags`, `edges`, `arcs` |
| Theorem | lower-camel atoms separated by `_` | `mem_neighborSet`, `edgeSet_induce`, `induce_adj` |

The lowercase predicates `nodup`, `nonstalling`, and `closed` are preserved. They are local
properties of a sequence-like value, not names of graph-theoretic classes.

### 2.1 `Is`, `Has`, and conventional exceptions

- Use `Is...` for a public proposition classifying an object: `IsAcyclic`, `IsTree`,
  `IsEulerianTrailIn`.
- Use `Has...` when the proposition is explicitly existential: `HasSimpleCycle`.
- Do not add `Is` to the stable relational vocabulary `Adj`, `Inc`, `Reachable`,
  `Preconnected`, `Connected`, or `StronglyConnected`.
- Preserve the realization grammar `G.Is<Object>In x`: `G.IsVertexSeqIn w`,
  `G.IsSimplePathIn p`, and `G.IsWalkIn w`.
- A non-`Prop` declaration must not begin with `Is` or `Has`.

### 2.2 Singular and plural

- Types are singular: `Edge`, `Arc`, `Walk`, `ConnectedComponent`.
- Collections use a singular element stem followed by the carrier suffix:
  `vertexSet`, not `verticesSet`; `edgeFinset`, not `edgesFinset`.
- A transform taking a set uses a plural object: `deleteEdges F`, `deleteVerts S`.
- A singleton wrapper uses a singular object: `deleteEdge e`, `deleteVert v`.
- Plural projections are appropriate for traversals: `w.vertices`, `w.tags`, `w.edges`,
  `w.arcs`.
- Use **vertex**, not **node**, in mathematical graph APIs. `node` remains available for tree or
  implementation data structures.

`Verts` is permitted only in the established transformation family `deleteVerts` and in theorem
fragments that mention that declaration. Elsewhere spell `vertex` or `vertices`.

## 3. Foundation terminology

### 3.1 The four graph types

The public type names are fixed:

```lean
Graph α β
SimpleGraph α
DiGraph α β
SimpleDiGraph α
```

`Graph` and `DiGraph` are the general types; they permit loops and parallel edges. Do not rename
them `MultiGraph`, `PseudoGraph`, `DirectedGraph`, or `Digraph`. `SimpleGraph` and
`SimpleDiGraph` are the loopless, no-parallel-edge types.

The prefix `Simple` on the validated data types `SimpleWalk`, `SimplePath`, and `SimpleCycle` is
also fixed. Do not use those existing names as a precedent for inventing nonstandard terms such
as `SimpleTrail` without a separate mathematical review.

### 3.2 Actual edges, arcs, and tags

- `Edge α β` is an undirected bundled edge.
- `Arc α β` is a directed bundled edge.
- `E(G)` is always the set of actual edge objects:

  | Graph type | Element type of `E(G)` |
  |---|---|
  | `SimpleGraph α` | `Sym2 α` |
  | `SimpleDiGraph α` | `α × α` |
  | `Graph α β` | `Edge α β` |
  | `DiGraph α β` | `Arc α β` |

- The whole `Edge` or `Arc` value is identity. The `β` component is a **tag** or
  **discriminator**, may be reused at different endpoints, and is not an unrestricted edge key.
- Rename `Edge.endpointsLabel` and `Arc.endpointsLabel` to `tag`. Do not retain `label` as a
  synonym.
- Preserve `Edge.endpoints` and `Arc.endpoints`. Add public `Arc.source` and `Arc.target`
  accessors; directed public statements should not expose `.endpoints.1` or `.endpoints.2`.
- If the optional uniqueness predicate is introduced, name it `TagInjective`, not
  `LabelInjective` or `UniqueLabels`.

Use `edgeSet`, `edgeFinset`, `deleteEdges`, and `EdgeWeight` as carrier-generic names on all four
graph types. Use **arc** when direction or ordered endpoints are the point: `Arc`, `IsArc`,
`arcs`, `arcEndpointPairSet`, and `deleteArcsFromTo`.

### 3.3 Endpoint images

The lossy images that forget a general edge's tag have deliberately explicit names:

```lean
Graph.edgeEndpointPairSet : Graph α β → Set (Sym2 α)
DiGraph.arcEndpointPairSet : DiGraph α β → Set (α × α)
```

Use `edgeEndpointPairSet` and `arcEndpointPairSet`, not `edgeEnds`, `arcEnds`, `edgeSet`,
`arcSet`, or `endpointSet`. The word `Pair` distinguishes these sets from a set of individual
endpoint vertices, and `Set` exposes the result carrier.

There is no corresponding alias on the simple graph types: their actual edge objects already
are endpoint pairs, so `E(G)` is the correct API. If a finite endpoint image later has a real
client, use `edgeEndpointPairFinset` or `arcEndpointPairFinset`.

### 3.4 Adjacency and incidence

Use the following relations:

```lean
G.IsLink e u v       -- undirected actual edge e links u and v
G.IsArc a u v        -- directed actual arc a has source u and target v
G.Inc e v            -- e is incident with v
G.Adj u v            -- u and v are adjacent; directed: u → v
```

`IsLink` and `IsArc` are graph-relative predicates even though endpoints project directly from
bundled values: they include actual-edge membership. `Adj` existentially forgets the particular
edge or arc. `Inc` forgets the other endpoint but not the actual edge.

Use proposition namespaces for proof methods:

```lean
IsLink.edge_mem
IsLink.left_mem
IsLink.right_mem
IsArc.edge_mem
IsArc.source_mem
IsArc.target_mem
Inc.edge_mem
Inc.vertex_mem
Adj.symm
Adj.ne
Adj.mono
```

For undirected ordered arguments, `left` and `right` are harmless positional words. For directed
arguments use `source` and `target`, never `left`/`right`, `fst`/`snd`, or `src`/`dst` in public
names.

The current theorems named `Graph.incidence`, `SimpleGraph.incidence`, and their directed
variants do not define incidence; they prove endpoint closure. Replace them with the predicate
API above and its `*_mem` lemmas.

### 3.5 Neighborhood and degree

Use:

```text
neighborSet             neighborFinset             degree
outNeighborSet          outNeighborFinset          outDegree
inNeighborSet           inNeighborFinset           inDegree
incidenceSet            incidenceFinset
outIncidenceSet         outIncidenceFinset
inIncidenceSet          inIncidenceFinset
loopSet                 loopFinset
minDegree               maxDegree                  averageDegree
minOutDegree            maxOutDegree
minInDegree             maxInDegree
```

The direction modifier comes first. An extremal modifier comes before direction:
`maxOutDegree`, not `outMaxDegree`, `degreeOut`, or `maxDegreeOut`.

`neighborSet G v` is the adjacency fiber `{u | G.Adj v u}`. Thus a loop contributes `v` exactly
when `G.Adj v v`. If a self-excluding neighborhood is needed, name it `openNeighborSet`; do not
silently subtract `{v}` inside `neighborSet`.

Names do not determine counting semantics, so public degree docstrings must state them. In a
general undirected graph, parallel edges count with multiplicity and a loop contributes two to
`degree`. In a directed graph, a loop contributes one to each of `inDegree` and `outDegree`.
Natural-valued degree declarations must require the relevant local finiteness; they must not use
`Set.ncard` to turn an infinite degree silently into zero.

Use `averageDegree`, not `avgDegree`; `maxDegree`, not `finMaxDegree`. If extended infinite degree
is introduced later, `eDegree` is provisional and must live beside an explicit type/value
docstring.

### 3.6 Weights, costs, capacities, and flows

Attached data does not change the graph type. Use graph-namespaced nouns such as:

```text
VertexWeight
EdgeWeight
Cost
Capacity
Network
Flow
Flow.IsFeasible
```

`EdgeWeight`, `Cost`, and `Capacity` range over actual elements of `E(G)`. For general graphs
that means `Edge α β` or `Arc α β`, never unrestricted `β → W`. A structure field or supplied
function is singular: `weight`, `cost`, `capacity`, `flow`.

Aggregates name both the object and quantity: `walkWeight`, `pathWeight`, `cutCapacity`, and
`flowValue`. Use operation laws such as `walkWeight_append` and `walkWeight_reverse`. Algebraic,
order, and nonnegativity assumptions belong on the definitions or theorems that need them; do
not encode them by inventing names such as `NonnegativeWeightedGraph`.

Use `transport` only for moving this attached data along a named edge equivalence or
correspondence. Same-carrier operations such as `induce`, `restrictEdges`, and deletion normally
reuse the original function and do not need a renamed copy.

## 4. Walk, path, trail, and cycle terminology

### 4.1 Preserve the graph-independent simple chain

These data types and their namespaces are locked:

```lean
VertexSeq
SimpleWalk
SimplePath
SimpleCycle
```

Preserve their common operations and accessors:

```text
singleton, cons, append, glue, reverse
dropHead, dropTail, prefixUntil, suffixFrom
takeWhile, dropWhile, loopErase, cycleErase
vertices, support, edges, arcs, head, tail, length
nodup, nonstalling, closed
```

`VertexSeq.cons` is a documented historical exception: it extends at the right. It has extensive
pattern-matching and definitional-equality use, so keep it. New sequence types must not copy that
orientation accidentally; use the terminology natural for their constructors.

The graph-relative realization predicates remain:

```lean
G.IsVertexSeqIn w
G.IsSimpleWalkIn w
G.IsSimplePathIn p
G.IsSimpleCycleIn c
```

Their APIs live in predicate namespaces and use short operation names such as `singleton`,
`append`, `reverse`, `dropHead`, `edge_mem`, `iff_edges`, and `mono`.

Preserve the validated constructors `SimpleCycle.ofPathClosing`,
`SimpleCycle.ofInternallyDisjointPaths`, and `SimpleCycle.ofTwoPaths`.

### 4.2 General edge-aware walks

Use the standard hierarchy:

- `Walk`: an alternating vertex/tag traversal datum;
- `Trail`: no repeated actual edge or arc;
- `Path`: no repeated vertex;
- `Circuit`: a nonempty closed trail;
- `Cycle`: a closed path except for the repeated first/last vertex, with the documented general
  graph loop and parallel-edge conventions.

For realization use `G.IsWalkIn`, `G.IsTrailIn`, `G.IsPathIn`, `G.IsCircuitIn`, and
`G.IsCycleIn` as applicable.

Because the current raw `Walk α β` stores step tags, its tag API must say so:

```text
tags             hasTag             mapTags
mapVertices      edges              arcs
toGraph          toDiGraph
```

Do not call tag membership `hasEdge`, do not call tag mapping `mapE`, and do not use `∈ₑ` for tag
membership. `edges` and `arcs` are reserved for reconstructed actual bundled values. Under the
fixed bundled representation, `toGraph` and `toDiGraph` remain structurally meaningful and may
be preserved.

Coverage predicates put the graph first and include realization:

```lean
G.IsEulerianTrailIn t
G.IsEulerianCircuitIn c
G.IsHamiltonianPathIn p
G.IsHamiltonianCycleIn c
```

Do not use `Walk.IsEulerian` or `Walk.IsHamiltonian` for a predicate that also needs an ambient
graph.

## 5. Connectivity terminology

Use:

```lean
G.Reachable u v
G.Preconnected
G.Connected
G.StronglyConnected u v
G.IsStronglyConnected
ConnectedComponent
StronglyConnectedComponent
```

`Reachable`, not `IsReachable`, is the existential path relation. For undirected graphs it is
symmetric. For directed graphs it is directional, and reversal transports it to `G.reverse`.

`StronglyConnected u v` is mutual reachability between two vertices. `IsStronglyConnected` is
the whole directed-graph property. Spell out `StronglyConnectedComponent` in mathematical API;
`SCC` is reserved for algorithm/module names and local prose.

The exact public carrier for connected and strongly connected components remains provisional.
If a function returns a literal `Set α`, use a `Set` suffix, for example
`stronglyConnectedComponentSet`. A bundled or quotient type uses `ConnectedComponent` or
`StronglyConnectedComponent` without a carrier suffix.

## 6. Subgraphs and graph transformations

### 6.1 Subgraphs

The canonical relation is order notation:

```lean
H ≤ G       -- subgraph
H ≤s G      -- spanning subgraph
H ≤i G      -- induced subgraph
```

Use the proposition/structure names `IsSubgraph`, `IsSpanningSubgraph`, and
`IsInducedSubgraph`. Replace `subgraphOf` rather than maintaining two primary spellings.

GraphLib subgraphs remain ordinary graph values in the same ambient vertex and edge types. Do
not copy Mathlib's legacy dependent-simple-subgraph vocabulary such as `G.Subgraph`, `verts`,
`spanningCoe`, `coeInduceIso`, or transport-heavy `Walk.transfer`.

### 6.2 Noun and verb grammar

Use these operation names:

| Meaning | Name |
|---|---|
| vertex-induced restriction | `induce` |
| spanning restriction to actual edges | `restrictEdges` |
| delete a set / one actual edge | `deleteEdges` / `deleteEdge` |
| delete a set / one vertex | `deleteVerts` / `deleteVert` |
| delete every undirected edge with endpoints `u`, `v` | `deleteEdgesBetween` |
| delete every directed arc from `u` to `v` | `deleteArcsFromTo` |
| reverse directed orientation | `reverse` |
| forget directed orientation | `forgetDirection` |
| lossy loop/parallel-edge collapse | `underlyingSimple` |

Use a verb when the declaration acts on a graph and selected data. Do not use
`inducedSubgraph`, `edgeRestriction`, `reversedGraph`, or the bare ambiguous `restrict`.
Established noun-like mathematical constructions such as `complement` and `lineGraph` remain
acceptable.

`SimpleGraph.toGraph` and `SimpleDiGraph.toDiGraph` are explicit canonical conversions and keep
their names. They must not be implicit coercions. A lossy conversion uses a name that exposes the
loss, such as `underlyingSimple`, and is never a coercion.

### 6.3 Map, relabel, and transport

These words have distinct meanings:

```text
mapVertices       arbitrary vertex function
mapTags           arbitrary tag function on an Edge/Arc or explicitly lossy graph operation
relabelVertices   vertex equivalence
relabelTags       tag equivalence
transport         movement of attached data along an explicit equivalence/correspondence
```

Rules:

- `relabelVertices` and `relabelTags` accept equivalences, not arbitrary functions.
- A noninjective `mapVertices` on a general graph must expose provenance/correspondence or state
  that it quotients; it must not silently merge actual edges while claiming identity preservation.
- A graph constructor is never named `transport`.
- `EdgeWeight.transport`, `Capacity.transport`, and similar names are appropriate for attached
  data.
- Use the standard morphism nouns `Hom`, `Embedding`, and `Iso` when such structures are actually
  introduced. Do not add a large morphism hierarchy only to reserve names.

## 7. Set and Finset rules

The mathematical collection API is separate from executable graph data.

1. A public foundation collection whose result is `Set τ` ends in `Set`.
2. Its finite counterpart replaces the terminal `Set` with `Finset` and changes no other stem.
3. A `*Finset` declaration must return `Finset`, never `Set`.
4. Use the same mathematical membership semantics in both versions.
5. `vertexFinset`, `edgeFinset`, `neighborFinset`, and `incidenceFinset` are mathematical views;
   the name alone makes no computability promise.
6. General `Graph` and `DiGraph` need actual-edge finiteness independently of vertex finiteness;
   finite vertices do not rule out infinitely many parallel edges.

Examples:

| Set API | Finset API |
|---|---|
| `vertexSet` | `vertexFinset` |
| `edgeSet` | `edgeFinset` |
| `neighborSet` | `neighborFinset` |
| `outNeighborSet` | `outNeighborFinset` |
| `incidenceSet` | `incidenceFinset` |
| `inIncidenceSet` | `inIncidenceFinset` |
| `edgeEndpointPairSet` | `edgeEndpointPairFinset` if needed |

The closed exception list for suffix-free collection accessors is: established traversal
projections such as `support`, `vertices`, `tags`, `edges`, and `arcs`, plus the scoped `V(G)` and
`E(G)` notation. Do not grow this list casually.

## 8. Theorem-name grammar

### 8.1 Namespace first

Put a theorem in the namespace of the object or proposition whose API it extends, then omit that
context from the short name:

```lean
VertexSeq.head_reverse
SimpleGraph.Adj.symm
SimpleGraph.IsSimpleWalkIn.reverse
DiGraph.IsArc.source_mem
```

The same short name may occur in sibling graph namespaces. Do not write
`simpleGraph_adj_symm` or `vertexSeq_head_reverse`.

### 8.2 Membership and coercion

Use:

```text
mem_<container>        membership characterization
not_mem_<container>    negative membership characterization
coe_<finset>           Finset-to-Set coercion equality
```

Examples:

```lean
mem_neighborSet
mem_outNeighborFinset
mem_edgeEndpointPairSet
not_mem_edgeSet_deleteEdge
coe_vertexFinset
coe_incidenceFinset
```

`mem_neighborSet` may itself be an iff; do not add the redundant suffix `_iff`. Use `*_mem` when
the theorem derives membership of a distinguished constituent from evidence, such as
`head_mem`, `tail_mem`, `source_mem`, `target_mem`, `edge_mem`, or `vertex_mem`.

### 8.3 Observable first, relation transform first

There are two intentional orientations.

When computing a projection, collection, measure, or data accessor of a constructed value, put
the observable first:

```text
<observable>_<operation>
```

Examples:

```lean
vertexSet_induce
edgeSet_deleteEdges
edgeEndpointPairSet_induce
outNeighborSet_reverse
degree_induce
source_reverse
head_reverse
edges_append
length_mapVertices
```

When characterizing a logical graph relation after a transformation, put the transformation
first:

```text
<operation>_<relation>
```

Examples:

```lean
induce_adj
induce_isLink
deleteEdges_isArc
reverse_adj
reverse_isArc
relabelVertices_adj
relabelVertices_reachable
mapVertices_isLink
```

The relation fragments for this rule include `adj`, `inc`, `isLink`, `isArc`, `reachable`, and
the `is...In` realization fragments. Thus use `edgeSet_induce`, not `induce_edgeSet`, but
`induce_adj`, not `adj_induce`.

### 8.4 Standard suffixes and connectors

| Shape | Use | Example |
|---|---|---|
| iff characterization | `*_iff_*` | `reachable_iff_exists_simplePath` |
| equality | `*_eq_*`, `eq_*`, or named computation pattern | `eq_top_iff_isAcyclic` |
| conclusion from substantive cause | `<conclusion>_of_<cause>` | `isAcyclic_of_subgraph` |
| monotone/antitone | `*_mono`, `*_anti` | `induce_mono`, `Reachable.mono` |
| multiple monotone arguments | `*_mono_left`, `*_mono_right` | `restrictEdges_mono_right` |
| symmetry as swapped iff | `*_comm` | `adj_comm`, `isLink_comm` |
| algebraic law | `*_assoc`, `*_left_comm`, `*_id`, `*_comp` | `relabelVertices_comp` |
| injectivity/surjectivity | `*_injective`, `*_surjective` | `toList_injective` |
| subset statement | expose both sides | `incidenceSet_subset_edgeSet` |

Use `_comm` only for a real commutativity equality or a relation invariant under swapping. A
theorem merely allowing two hypotheses to be swapped is not `*_comm`.

Keep `_of_<cause>` when the cause is the mathematical reason the result holds. Omit routine
elaboration guards already visible in the signature. Use the declared predicate fragment,
including `is`/`has`: `eq_top_of_isAcyclic`, not `eq_top_of_acyclic`.

For exact top/bottom statements prefer literal names:

```text
eq_top_iff_isAcyclic
ne_top_iff_hasSimpleCycle
eq_top_of_isAcyclic
ne_top_of_two_le_degree
```

Do not use `infinite` or `finite` when the statement is specifically equality or inequality with
`⊤` and the subject itself is not a set/type.

### 8.5 Cardinality

- Use `card_<finset>_eq_<quantity>`: `card_neighborFinset_eq_degree`.
- Use `ncard_<set>` for a `Set.ncard` equality: `ncard_vertexSet`.
- Do not create both `edgeFinset_card` and `card_edgeFinset` orientations.
- State inequality operands in mathematical reading order:
  `card_edgeFinset_le_card_vertexFinset_choose_two`.

### 8.6 Simp names and attributes

Give canonical membership, coercion, constructor, and projection computations their ordinary
names; attributes do not change naming grammar. Mark a theorem `@[simp]` only when it reduces
expression complexity and has a stable orientation.

Do not mark proof-to-membership lemmas `simp` when simp cannot infer the missing edge or vertex.
For example, `Inc.edge_mem`, `Inc.vertex_mem`, and `IsLink.inc_left` are proof methods, not
unconditional rewrite rules.

## 9. Constructors and conversions

- Use the generated `mk` for raw structure fields. A convenience `mk` is justified only when it
  is the canonical low-level constructor.
- Use lowercase inductive constructors inside the type namespace: `singleton`, `cons`.
- Use `of<Source>` for a mathematical constructor from another object or theorem:
  `ofPathClosing`, `ofTwoPaths`, `of_subgraph`.
- Use `to<Target>` for an explicit canonical conversion or forgetful projection:
  `toList`, `toGraph`, `toDiGraph`.
- Do not use `of_*` merely to hide arbitrary arguments to `mk`.
- Constructor computation theorems use the ordinary observable grammar:
  `head_singleton`, `length_ofTwoPaths`, `edgeSet_toGraph`.
- A lossy conversion must say what is forgotten or collapsed; it is not registered as a
  coercion.

## 10. Directed naming rules

The following rules are mechanical.

1. `G.Adj u v` means from `u` to `v`.
2. Use `source` and `target` for an arc's ordered endpoints.
3. Put `out`/`in` before the semantic noun: `outNeighborSet`, `inDegree`.
4. Put outer modifiers before direction: `minOutDegree`, `maxInDegree`.
5. In API listings and paired definitions, order `out` before `in` unless dependency or a standard
   theorem statement dictates otherwise.
6. Directed reversal is `reverse`; it swaps source and target and is involutive.
7. Reversing a directed walk realizes it in `G.reverse`, not generally in `G`.
8. Residual construction is not reversal. Residual names must expose origin and polarity, such
   as `ResidualArc.forward` and `ResidualArc.backward`.

Avoid `successor`/`predecessor` as synonyms for graph neighborhoods in the mathematical layer.
An executable algorithm may use `successors` only when its access model deliberately adopts
that standard algorithmic term.

## 11. Namespace and module names

### 11.1 Namespaces

- All public declarations live under `GraphLib`.
- Put graph-specific declarations in `Graph`, `SimpleGraph`, `DiGraph`, or `SimpleDiGraph`.
- Put graph-independent data and operations in `VertexSeq`, `SimpleWalk`, `SimplePath`,
  `SimpleCycle`, `Walk`, and the corresponding general type namespaces.
- Put proof methods in predicate namespaces such as `Adj`, `IsLink`, `IsSimplePathIn`, and
  `Reachable`.
- A namespace supplies context; do not repeat it in every declaration name.
- Do not add generic declarations to root `Set` or `List` from a GraphLib theory file unless the
  declaration is intended and suitable for upstream Mathlib. Otherwise use a GraphLib-owned
  utility or theory namespace.

### 11.2 Files and modules

Lean module segments and filenames use `UpperCamel` and are concept-oriented:

```text
Graph/Adjacency.lean
Graph/Incidence.lean
Graph/Neighborhood.lean
Graph/Subgraph.lean
Graph/Delete.lean
Graph/Map.lean
Graph/Reverse.lean
Graph/Finite.lean
Graph/Degree.lean
Graph/DegreeSum.lean
Connectivity/Reachability.lean
Connectivity/Connected.lean
Connectivity/StronglyConnected.lean
```

- Prefer singular concept files: `Map.lean`, not `Maps.lean`; `Subgraph.lean`, not
  `Subgraphs.lean`.
- Plural is acceptable for a conventional family, such as `Constructions.lean`.
- A directory umbrella has the directory's name and primarily imports its children.
- `Basic.lean` must contain the genuine base of a concept or be a deliberate small umbrella. It
  must not be an empty placeholder.
- Do not encode applicability in directory names such as `SimpleGraph_only`. Let imports,
  namespaces, and signatures express applicability.
- Established algorithm acronyms are permitted as module segments: `Algorithms/SCC`,
  `Algorithms/MST`, `BFS`, and `DFS`. Mathematical declarations still spell out the concept.

## 12. Notation

- Preserve the scoped notations `V(G)` and `E(G)`.
- Use the standard subgraph order and, when defined, scoped `≤s` and `≤i`.
- Keep notation scoped unless it is universal Lean syntax.
- Remove/defer `G[S]`; the `GetElem` encoding treats every set index as valid and has no
  downstream use. Write `G.induce S`.
- Do not introduce `N(G,v)`, `N+(G,v)`, `d(G,v)`, `δ(G)`, or `Δ(G)` as primary API. The named
  declarations are clearer, searchable, and type-directed.
- Do not use `∈ₑ` for raw tag membership. Write `t ∈ w.tags` or `w.hasTag t`.
- The `:+` notation and generic root `Snoc` class are provisional. If retained during migration,
  keep them scoped and do not add new instances until a second real client justifies the class.

## 13. Abbreviations

Allowed in public names because they are established Lean or TCS vocabulary:

```text
Adj, Inc, Di, Finset, mem, coe, iff, eq, ne, le, lt,
ncard, card, mono, anti, inj, surj, SCC, MST, BFS, DFS
```

Restrictions:

- `SCC`, `MST`, `BFS`, and `DFS` are for algorithm/module names and local prose. Spell out
  mathematical declarations such as `StronglyConnectedComponent`.
- `inj` and `surj` are acceptable local/theorem fragments when matching Lean conventions;
  type/structure names use `Embedding` and `Equiv`/`Iso` as appropriate.
- Do not use `avg`, `fin`, `nbr`, `neigh`, `vert`, `conn`, `repr`, `src`, `dst`, `fst`, `snd`,
  `mapV`, or `mapE` in new public names.
- A public apostrophe suffix is only for a genuinely primed mathematical object or a short-lived
  compatibility shim, never for “second attempt”. Do not create names such as `map_adj'`.

## 14. Minimal documentation and comment rules

Every public type, structure, class, field, transformation, collection accessor, and named
mathematical predicate gets a docstring. The docstring states the mathematical meaning, not just
the Lean type.

Mention the following whenever relevant:

- whether values are actual edges/arcs or endpoint images;
- that `tag` is not globally unique;
- source/target direction;
- loop and parallel-edge behavior;
- whether degree counts loops twice;
- finite assumptions and whether a definition is noncomputable;
- whether a map may merge or drop edges;
- whether a conversion is lossy.

Routine `mem_*`, `coe_*`, constructor-computation, and direct namespace proof lemmas may omit a
docstring when the name and statement are self-explanatory. Headline theorems and nonobvious
orientation/side-condition lemmas require one.

Use `/-! ... -/` for module and section documentation, `/-- ... -/` for public declarations, and
`--` for a local proof explanation. Comments should explain why a step or convention is needed;
do not narrate tactics or preserve obsolete implementation history.

## 15. The `Finite*View` decision

`FiniteAdjView`, `FiniteEdgeView`, and `FiniteVertexView` are rejected and must not enter the
current foundation.

Reasons:

- `Finite` confuses stored exhaustive data with the logical `Finite` proposition;
- `View` is vague and nonstandard;
- the proposed records have no current algorithm client;
- `AdjacencyList` would be inaccurate for a `Finset`-valued abstract interface;
- the current `computeVertexFinset` and `computeEdgeFinset` declarations are unused outside their
  own correctness lemmas.

The current foundation exposes only the mathematical API:

```text
vertexFinset
edgeFinset
neighborFinset
incidenceFinset
```

These may be noncomputable and are not an algorithm input contract.

When a real client exists, use terminology according to what is actually supplied:

- `AdjacencyEnumeration G` for exhaustive vertex plus neighbor/out-neighbor enumerations;
- `IncidenceEnumeration G` for edge-aware per-vertex incidence/out-arc enumerations;
- `EdgeEnumeration G` only if a client independently needs a global actual-edge enumeration;
- `AdjacencyList` only for a genuinely list/array-backed representation with a stated access and
  cost model;
- `...Represents G` or a namespaced `Represents` predicate for the refinement relation between
  concrete data and the mathematical graph.

The exact record factoring is `DEFERRED` until BFS, MST, or flow supplies the first client. The
rejection of `Finite*View` and the distinction between mathematical finsets, enumeration
contracts, and concrete adjacency lists are `LOCKED`.

## 16. Representative API stress test

Assume `Gu : Graph α β`, `Gs : SimpleGraph α`, `Gd : DiGraph α β`, and
`Gsd : SimpleDiGraph α`.

| Topic | `Graph` | `SimpleGraph` | `DiGraph` | `SimpleDiGraph` |
|---|---|---|---|---|
| Actual carrier | `E(Gu) : Set (Edge α β)` | `E(Gs) : Set (Sym2 α)` | `E(Gd) : Set (Arc α β)` | `E(Gsd) : Set (α × α)` |
| Endpoint relation | `Gu.IsLink e u v` | `Gs.IsLink e u v` | `Gd.IsArc a u v` | `Gsd.IsArc a u v` |
| Adjacency | `Gu.Adj u v` | `Gs.Adj u v` | `Gd.Adj u v` | `Gsd.Adj u v` |
| Lossy endpoint image | `Gu.edgeEndpointPairSet` | use `E(Gs)` | `Gd.arcEndpointPairSet` | use `E(Gsd)` |
| Neighborhood | `neighborSet` | `neighborSet` | `outNeighborSet`, `inNeighborSet` | same |
| Finite neighborhood | `neighborFinset` | `neighborFinset` | `outNeighborFinset`, `inNeighborFinset` | same |
| Incidence collection | `incidenceSet` | `incidenceSet` | `outIncidenceSet`, `inIncidenceSet` | same |
| Finite incidence | `incidenceFinset` | `incidenceFinset` | `outIncidenceFinset`, `inIncidenceFinset` | same |
| Degree | `degree` | `degree` | `outDegree`, `inDegree` | same |
| Subgraph | `H ≤ Gu` | `H ≤ Gs` | `H ≤ Gd` | `H ≤ Gsd` |
| Induced restriction | `induce` | `induce` | `induce` | `induce` |
| Actual-edge deletion | `deleteEdge`, `deleteEdges` | same | same | same |
| Endpoint-wide deletion | `deleteEdgesBetween` | same | `deleteArcsFromTo` | same |
| Reverse | not applicable | not applicable | `reverse` | `reverse` |
| Vertex relabel | `relabelVertices` | same | same | same |
| Tag relabel | `relabelTags` | not applicable | `relabelTags` | not applicable |
| Realization | `IsWalkIn` | `IsSimpleWalkIn` | `IsWalkIn` | `IsSimpleWalkIn` |
| Reachability | `Reachable` | `Reachable` | `Reachable` | `Reachable` |
| Connectedness | `Connected` | `Connected` | `StronglyConnected`, `IsStronglyConnected` | same |
| Mathematical enumeration | `vertexFinset`, `edgeFinset` | same | same | same |
| Weight | `EdgeWeight` | `EdgeWeight` | `EdgeWeight` | `EdgeWeight` |
| Capacity | normally not used | normally not used | `Capacity` | `Capacity` |

Representative theorem names expose the grammar:

```lean
mem_neighborSet
mem_outNeighborFinset
mem_incidenceSet
mem_edgeFinset
coe_edgeFinset
card_neighborFinset_eq_degree

IsLink.edge_mem
IsArc.source_mem
IsArc.target_mem
Inc.vertex_mem
Adj.mono

vertexSet_induce
edgeSet_induce
induce_adj
induce_isArc
edgeSet_deleteEdges
deleteEdges_isLink
deleteVerts_adj

source_reverse
target_reverse
reverse_isArc
reverse_adj
reverse_reverse

relabelVertices_adj
relabelVertices_id
relabelVertices_comp
relabelTags_id
mapVertices_isLink

IsSimpleWalkIn.iff_edges
IsSimpleWalkIn.reverse
IsSimpleWalkIn.mono
IsWalkIn.iff_edges
Reachable.refl
Reachable.trans
Reachable.reverse
reachable_iff_exists_simplePath
stronglyConnected_iff
mem_stronglyConnectedComponentSet

walkWeight_append
walkWeight_reverse
cutCapacity_eq_sum
capacity_transport_relabelTags
```

This sample is intentionally repetitive: a future agent should be able to select a row and
derive the corresponding name without inventing a new local dialect.

## 17. Important current names: preserve or change

| Current name/pattern | Decision | Replacement or clarification |
|---|---|---|
| `Graph`, `SimpleGraph`, `DiGraph`, `SimpleDiGraph` | Preserve | Fixed public type names |
| `Edge`, `Arc` | Preserve | Full bundle is actual identity |
| `vertexSet`, `edgeSet`, `V(G)`, `E(G)` | Preserve names | Repair general `E(G)` to actual bundled values |
| `endpointsLabel` | Change | `tag` |
| `Edge.endpoints`, `Arc.endpoints` | Preserve | Add `Arc.source`, `Arc.target` |
| endpoint-image `E(G)` | Change | `edgeEndpointPairSet`, `arcEndpointPairSet` |
| `Adj`, `Adj.symm`, `Adj.ne`, `adj_comm` | Preserve | Directed endpoint lemmas use source/target |
| `Graph.incidence` closure theorem | Change | `Inc` plus `IsLink.*_mem`, `IsArc.*_mem`, `Inc.vertex_mem` |
| `neighborSet`, `neighborFinset` | Preserve | Fix implementations and finite hypotheses |
| `outNeighborSet`, `inNeighborSet` | Preserve | Direction-first grammar |
| `incidenceSet`, `incidenceFinset` | Preserve names | Every `*Finset` must actually return `Finset` |
| `degree`, `outDegree`, `inDegree` | Preserve | Require correct finiteness/counting semantics |
| `finMaxDegree` | Change | `maxDegree` |
| `avgDegree` | Change | `averageDegree` |
| `subgraphOf` | Change | `IsSubgraph` and `≤` |
| `induce` | Preserve | Remove/defer `G[S]` |
| simple-to-general `Coe` | Remove | Keep explicit `toGraph`, `toDiGraph` |
| `VertexSeq`, `SimpleWalk`, `SimplePath`, `SimpleCycle` | Preserve | Locked validated spine |
| right-extending `VertexSeq.cons` | Preserve exception | Document; do not generalize |
| `G.IsVertexSeqIn`, `G.IsSimpleWalkIn`, `G.IsSimplePathIn`, `G.IsSimpleCycleIn` | Preserve | Locked realization grammar |
| `SimpleCycle.ofPathClosing`, `ofTwoPaths` | Preserve | Validated `of<Source>` constructors |
| `SimpleWalk.toSimpleGraph`, `toSimpleDiGraph` | Preserve | Generated-graph bridge |
| `Walk.toGraph`, `Walk.toDiGraph` | Preserve | Meaningful for bundled reconstruction |
| `Walk.hasEdge`, `toEdgeList`, `mapE` over tags | Change | `hasTag`, `tags`, `mapTags` |
| `Walk.mapV` | Change | `mapVertices` |
| `Walk` `HasSubset` mixing vertices/tags | Remove | No sound actual-edge inclusion meaning |
| `computeVertexFinset`, `computeEdgeFinset` | Remove/defer | No duplicate executable-looking foundation API |
| `FiniteAdjView`, `FiniteEdgeView`, `FiniteVertexView` | Reject | Defer executable contracts; see §15 |
| `SimpleGraph.IsConnected` draft | Change | `Preconnected` / `Connected` |
| `Walk.IsEulerian`, `Walk.IsHamiltonian` drafts | Change | graph-relative `G.Is...In` names |
| girth `infinite_*`, `finite_*` for `= ⊤`, `≠ ⊤` | Change | literal `eq_top_*`, `ne_top_*` names |
| `Graph/Graphs.lean` snake-case placeholders | Reject | implemented constructors in `Constructions.lean` |
| `SimpleGraph_only` module directory | Change | concept-oriented modules/namespaces |

## 18. Explicit anti-patterns

Do not introduce:

- `*Set` returning anything other than `Set`, or `*Finset` returning anything other than
  `Finset`;
- `neighborsSet`, `edgesFinset`, `commonNeighbors : Set _`, or another noncanonical plural;
- `edgeEnds`, `arcEnds`, or any endpoint image exposed as `E(G)`;
- unrestricted general-graph edge data typed as `β → W`;
- public `.endpoints.1` / `.endpoints.2` directed vocabulary;
- `degreeOut`, `outMaxDegree`, `neighborInSet`, `src`, or `dst`;
- `induce_edgeSet`, `adj_induce`, or another reversal of the theorem-orientation rules;
- `deleteEdge` taking a set or `deleteEdges` taking a single value;
- `relabelVertices` accepting a non-equivalence;
- a graph construction named `transport`;
- bare `restrict`, `map`, or `relabel` when the changed component or semantics is ambiguous;
- `IsAdj`, `IsInc`, `IsReachable`, or public mathematical declarations abbreviated `SCC`;
- proof-strategy names, `_lemma`, `_theorem`, `_property`, public `_aux`, or unexplained apostrophe
  variants;
- unscoped graph notation or lossy coercions;
- representation-specific Mathlib names such as `spanningCoe`, `coeInduceIso`, `mapLe`, or
  `Walk.transfer`;
- `Finite*View`, or `AdjacencyList` for a non-list representation;
- a public definition/type without a mathematical docstring.

## 19. Decision register

### `LOCKED`

1. The type names `Graph`, `SimpleGraph`, `DiGraph`, `SimpleDiGraph`, `Edge`, and `Arc`.
2. General graphs retain bundled actual edges; `E(G)` denotes actual edge/arc objects on all four
   graph types.
3. `β` is exposed as `tag`; it is not implicitly unique and is not edge identity.
4. Lossy endpoint images are `edgeEndpointPairSet` and `arcEndpointPairSet`.
5. Core vocabulary: `Adj`, `IsLink`, `IsArc`, `Inc`, neighborhood/incidence families, and
   direction-first `out`/`in` order.
6. The graph-independent `VertexSeq → SimpleWalk → SimplePath → SimpleCycle` chain and
   `G.Is...In` realization grammar.
7. `H ≤ G`, `≤s`, `≤i`; `induce`, `restrictEdges`, deletion, `reverse`, `mapVertices`,
   `relabelVertices`, and `relabelTags` word meanings.
8. Exact `Set`/`Finset` suffix discipline and the theorem-name grammar in §8.
9. Explicit conversions rather than lossy or representation-changing coercions.
10. Rejection of `FiniteAdjView`, `FiniteEdgeView`, `FiniteVertexView`, and `compute*Finset` as
    foundation API.

### `PROVISIONAL`

1. The exact public carrier and API for `ConnectedComponent` and
   `StronglyConnectedComponent`; their spelled-out vocabulary is fixed.
2. The exact provenance-bearing result type and composition laws for noninjective
   `mapVertices`; the name and no-silent-merge rule are fixed.
3. Whether edge weights, costs, and capacities remain namespace aliases/functions or receive a
   small bundled wrapper. `EdgeWeight`, `Capacity`, and actual-edge domains are the default.
4. The generic `Snoc` class and `:+` notation; `VertexSeq.cons` itself remains fixed.
5. The optional `TagInjective` predicate and any extended infinite-degree API.
6. `AdjacencyEnumeration`, `IncidenceEnumeration`, and `EdgeEnumeration` as reserved future
   terms; no structures are authorized by this document.

### `DEFERRED`

1. The executable graph representation and refinement records until a real BFS, MST, or flow
   client determines their fields.
2. Concrete adjacency-list/array/hash representations and their cost models.
3. Contraction result types, provenance normalization, and contraction-specific declaration
   names.
4. A public `GraphLike`, dart, half-edge, or incidence-identity hierarchy.
5. Migration from bundled edges to a separate abstract identity type.
6. Full general Eulerian/Hamiltonian APIs until the realized trail/path/circuit types exist.

## 20. Mathlib patterns adopted and rejected

The pinned Mathlib survey covered `Combinatorics/Graph/{Basic,Subgraph,Delete,Maps}.lean` and the
relevant `Combinatorics/SimpleGraph` basic, finite, maps, walk, path, and connectivity modules.

Adopt:

- `Adj`, `IsLink`, `Inc`, `neighborSet`, `neighborFinset`, `incidenceSet`,
  `incidenceFinset`, `degree`, `minDegree`, `maxDegree`;
- `Reachable`, `Preconnected`, `Connected`, `ConnectedComponent`;
- `Hom`, `Embedding`, `Iso`;
- `H ≤ G`, `IsSpanningSubgraph`, `IsInducedSubgraph`, `≤s`, `≤i`;
- `mem_*`, `coe_*`, proposition namespaces, and standard algebraic suffixes.

Do not copy:

- the legacy dependent `SimpleGraph.Subgraph` carrier and its coercion vocabulary;
- subtype-changing induced graphs;
- graph-indexed walk/path carriers and their proof transport names;
- Mathlib `Digraph`'s thin relation-only vocabulary as a model for explicit arc identity;
- inconsistent names such as suffix-free `commonNeighbors`, mixed `notMem_*`, bare `restrict`,
  apostrophe variants, or competing cardinality orientations.

This is a selective alignment: GraphLib uses Mathlib's stable Lean grammar where the concepts
match and retains GraphLib's representation-appropriate mathematical vocabulary where they do
not.
