# GraphLib graph foundation: final implementation plan

**Date:** 2026-08-14  
**Status:** implementation-ready construction plan; no Lean implementation is included  
**Controlling inputs:** `GraphLib/NAMING.md`, the bundled-edge decision memo, the architecture proposal where not superseded, and the repository audit described below

## 1. Executive summary

This construction round will produce a definition-complete, routine-lemma-nearly-complete mathematical foundation for:

```lean
SimpleGraph α
SimpleDiGraph α
Graph α β
DiGraph α β
```

The general graph types keep their existing bundled actual edges:

```lean
Edge α β     -- tag plus unordered endpoints
Arc α β      -- tag plus ordered endpoints
```

The whole bundle is identity. The tag may be reused at different endpoints. The first breaking repair is therefore:

```lean
E(G) = G.edgeSet : Set (Edge α β)   -- Graph
E(G) = G.edgeSet : Set (Arc α β)    -- DiGraph
```

Lossy endpoint images will be exposed only as `edgeEndpointPairSet` and `arcEndpointPairSet`.

The implementation proceeds bottom-up: actual-edge semantics; incidence and adjacency; subgraphs and same-carrier transformations; the preserved simple-walk spine and a completed general realized-walk layer; mathematical finite views and correct degree; connectivity; attached data and network specifications; and a small constructor library. Every phase ends with a green import-all build, and the validated

```text
VertexSeq → SimpleWalk → SimplePath → SimpleCycle
→ Is...In → Girth → MooreBound
```

chain is a mandatory regression target.

This round deliberately contains no contraction file, carrier, operation, theorem, or implementation phase. It also contains no `Finite*View`, `compute*Finset`, executable graph representation, large `GraphLike` hierarchy, weighted graph type, residual-network algorithm, or contraction-specific transport. `VertexSplit` is deferred because no current foundation client needs it.

### Classification used below

- **MUST DEFINE NOW**: public mathematical data or an operation that later clients must not reinvent.
- **SHOULD PROVE NOW**: routine construction, membership, extensionality, transport, monotonicity, or algebra laws needed for normal rewriting.
- **MAY DEFER**: nontrivial theory or an interface whose correct shape needs a real client.
- **OUT OF SCOPE**: intentionally excluded from this round.

## 2. Fixed inputs and scope

The implementation must obey these decisions without reopening them:

1. `Graph`, `SimpleGraph`, `DiGraph`, `SimpleDiGraph`, `Edge`, and `Arc` keep those names.
2. `Edge α β` and `Arc α β` remain bundled. Rename `endpointsLabel` to `tag`; do not keep `label` or `endpointsLabel` as an alias.
3. `E(G)` always contains actual edges/arcs. For the four graph types its element types are respectively `Edge α β`, `Sym2 α`, `Arc α β`, and `α × α`.
4. General endpoint images are explicitly lossy and named `edgeEndpointPairSet` and `arcEndpointPairSet`.
5. Walk data remains graph-independent. The mature simple chain is preserved, and general realization is expressed by `G.Is...In` predicates.
6. `induce`, restriction, and deletion retain ambient vertex/tag types. Relabeling is bijective; arbitrary `mapVertices` is allowed but must expose provenance rather than silently merge general edges.
7. Mathematical `Set`/`Finset` APIs belong in the foundation. Executable enumeration contracts are deferred.
8. Weights, costs, capacities, and flows are data on actual edges/arcs, not graph structure and never unrestricted functions on a general tag type.
9. Public names, theorem orientation, `Set`/`Finset` suffixes, directed source/target vocabulary, and scoped notation follow `NAMING.md`.
10. Contraction is out of scope. Noninjective `mapVertices` is included because it is independently foundational, not as a contraction implementation.

Two architecture-proposal recommendations are explicitly superseded: do not migrate to an abstract edge-identity relation, and do not add `FiniteAdjView`/`FiniteEdgeView`. The proposal's suggested removal of `Walk.toGraph`/`toDiGraph` is also superseded: bundled reconstruction makes those operations well-defined.

## 3. Current repository audit

### 3.1 What is already sound and should be preserved

- `Graph/Basic.lean` stores general `edgeSet` as `Set (Edge α β)` / `Set (Arc α β)`. Structure equality already makes the whole bundled value the identity.
- The simple structures have explicit vertex sets and endpoint-pair edge sets with looplessness proofs.
- `Graph.induce` and its three siblings already retain ambient types and filter bundled actual values directly.
- `Matching` stores `Set (Edge α β)`, confirming that an identity-sensitive client already expects full bundles.
- General `Walk α β` is real graph-independent code. It stores step tags but reconstructs correct full values in `Walk.edges` and `Walk.arcs`; `toGraph` and `toDiGraph` are structurally meaningful.
- The `VertexSeq` file split is sensible, and `SimpleWalk`, `SimplePath`, `SimpleCycle`, and `InSimpleGraph/*` are mature. `SimpleCycle.ofPathClosing`, `ofInternallyDisjointPaths`, and `ofTwoPaths` have real Girth/Moore clients.
- `InSimpleDiGraph.lean` has a substantive directed vertex-sequence/simple-walk realization API and correctly lacks a same-graph reverse theorem.
- `Graph/Finite.lean` independently compiles and contains useful simple-graph mathematical finsets and cardinal bounds.
- The full Girth/Moore umbrella independently compiles.

### 3.2 Mandatory semantic repairs

The current general `HasEdgeSet` instances return endpoint images:

```lean
Edge.endpoints '' G.edgeSet
Arc.endpoints '' G.edgeSet
```

Consequently current general `E(G)` and general adjacency erase parallel-edge identity, while `subgraphOf`, degree incidence sets, matching, Eulerian drafts, and reconstructed walks use full records. This public/private split is the principal foundation defect.

Other required corrections are:

- `Graph.incidence` and its siblings are endpoint-closure theorems, not an incidence predicate.
- general neighborhoods currently exclude a loop vertex, contrary to the required adjacency-fiber meaning;
- the general undirected degree draft counts a loop once instead of twice;
- natural degrees use `Set.ncard` without finiteness, silently returning zero on infinite local sets;
- six declarations named `*Finset` return `Set`;
- implicit simple-to-general coercions hide a representation change;
- `subgraphOf` has no order instance, and `G[S]` abuses `GetElem` despite having no clients.

### 3.3 Mature, incomplete, and obsolete modules

An independent compile audit found exactly three failing Lean modules:

```text
GraphLib/Graph/Degree.lean
GraphLib/Graph/Graphs.lean
GraphLib/Theory/Structures/Basic.lean
```

`Graph/Degree.lean` has malformed notation, incomplete declarations, `sorry`s, and incorrect semantics. `Graph/Graphs.lean` is sixteen untyped placeholders. `Theory/Structures/Basic.lean` is a 742-line historical draft with mutually incompatible duplicate graph/walk/path representations. They are replacement/deletion targets, not starting points.

`Trail.lean`, `Path.lean`, `Cycle.lean`, and `InGraph.lean` are empty shells; `InDiGraph.lean` is absent. Connectivity, MST, flow, SCC, shortest-path, and most theory `Basic.lean` files are placeholders. `Forest` and `Tree` duplicate realization and connectedness. Eulerian and Hamiltonian drafts omit realization. `Search` and `GraphTraversal` duplicate the same traversal placeholder.

The default `lake build GraphLib` succeeds only because `GraphLib.lean` omits most graph modules, including the three failing files and the mature Girth/Moore chain. It instead imports `UnionFind.Blueprint`, which contains nine unrelated `sorry`s. A truthful import-all target is therefore an early deliverable.

### 3.4 Downstream constraints

- `subgraphOf` has roughly twenty uses concentrated in `InSimpleGraph`, `InSimpleDiGraph`, and Girth. They can be migrated atomically.
- Girth temporarily owns `SimpleGraph.neighborSet` and `degree`; Moore core temporarily owns `neighborSet_subset_vertexSet`, `exists_neighbor_ne_of_two_le_degree`, and `exists_adj_of_nonempty_of_two_le_degree`.
- No current client uses `computeVertexFinset`, `computeEdgeFinset`, a `Finite*View`, general degree, directed degree, or weights/networks.
- No current source client needs the simple-to-general coercions or `G[S]`.
- The dependency declaration is unstable: `lakefile.toml` names `v4.30.0-rc2`, while the manifest records a pinned commit with `inputRev = "master"`. Freeze the dependency state during this migration; upgrade separately.

## 4. Target module tree

Only modules in this construction round are shown. There is deliberately no `Contraction.lean`, `Executable/`, or `VertexSplit.lean`.

```text
GraphLib/
├── Graph.lean                         -- true graph umbrella
├── Graph/
│   ├── Basic.lean
│   ├── Incidence.lean
│   ├── Adjacency.lean
│   ├── Subgraph.lean
│   ├── Delete.lean
│   ├── Map.lean
│   ├── Reverse.lean
│   ├── Neighborhood.lean
│   ├── Finite.lean
│   ├── Degree.lean
│   ├── DegreeSum.lean
│   └── Constructions.lean
├── Util/
│   └── List.lean
├── Walk.lean                          -- true walk umbrella
├── Walk/
│   ├── VertexSeq.lean
│   ├── VertexSeq/
│   │   ├── Basic.lean
│   │   ├── Predicates.lean
│   │   ├── Append.lean
│   │   ├── Subseq.lean
│   │   ├── Erase.lean
│   │   ├── Edges.lean
│   │   ├── MapZip.lean
│   │   └── Index.lean
│   ├── SimpleWalk.lean
│   ├── SimplePath.lean
│   ├── SimpleCycle.lean
│   ├── SimpleDiCycle.lean
│   ├── Walk.lean
│   ├── Trail.lean                     -- Trail and DiTrail
│   ├── Path.lean                      -- shared vertex-simple Path
│   ├── Circuit.lean                   -- Circuit and DiCircuit
│   ├── Cycle.lean                     -- Cycle and DiCycle
│   ├── InSimpleGraph.lean
│   ├── InSimpleGraph/{VertexSeq,Walk,Path,Cycle}.lean
│   ├── InSimpleDiGraph.lean
│   ├── InSimpleDiGraph/{VertexSeq,Walk,Path,Cycle}.lean
│   ├── InGraph.lean
│   ├── InDiGraph.lean
│   └── Coverage.lean                  -- Eulerian/Hamiltonian predicates only
├── Connectivity.lean                  -- true connectivity umbrella
├── Connectivity/
│   ├── Reachability.lean
│   ├── Connected.lean
│   ├── StronglyConnected.lean
│   └── Acyclic.lean
├── Weight.lean                        -- true attached-data umbrella
├── Weight/
│   ├── Basic.lean
│   ├── Walk.lean
│   └── Network.lean
├── Theory/
│   ├── Coloring/Bipartite.lean
│   ├── Girth.lean
│   ├── MooreBound.lean
│   └── MooreBound/{Counting,Core,RootedLayers,HalfLayers,Bounds}.lean
├── All.lean                            -- imports every production module
└── ...                                -- higher theory/algorithms outside this round

GraphLibTest/
├── ImportAll.lean
└── Foundation/{Basic,Transformations,Walk,FiniteDegree,Connectivity,WeightNetwork}.lean
```

`Interop/Mathlib.lean` is deferred until a theorem client exists. If later added, it is a leaf depending on this foundation. `VertexSplit` is likewise optional/client-driven and not a deliverable here.

## 5. Dependency DAG

The implementation order is acyclic if the following boundary rules are enforced:

```text
Mathlib Set / Sym2
  → Graph.Basic
  → Graph.Incidence
  → Graph.Adjacency
  → Graph.Subgraph
  → Graph.Delete
  → Graph.Map
  → Graph.Reverse
  → Graph.Neighborhood
  → Graph.Finite
  → Graph.Degree
  → Graph.DegreeSum

Util.List → Walk.VertexSeq/* → SimpleWalk → SimplePath
                                      ├→ SimpleCycle
                                      └→ SimpleDiCycle

Graph.Basic → Walk.Walk
              ├→ Trail/DiTrail
              ├→ Path
              └→ Circuit/DiCircuit → Cycle/DiCycle

graph transformations + walk carriers
  → InSimpleGraph / InSimpleDiGraph / InGraph / InDiGraph
  → Connectivity.Reachability
      ├→ Connectivity.Connected
      ├→ Connectivity.StronglyConnected
      └→ Connectivity.Acyclic

Graph.Map + Graph.Reverse → Weight.Basic
realized walks + Weight.Basic → Weight.Walk
Graph.Finite + incidence + Weight.Basic → Weight.Network

InSimpleGraph + Graph.Degree → Theory.Girth → Theory.MooreBound
Graph.Basic + Graph.Adjacency + Graph.Finite → Graph.Constructions
```

Rules preventing cycles:

- no `Graph/*` foundation file imports walks, connectivity, weights, or theory;
- walk transport along graph operations lives in realization modules, never in `Graph/Map.lean`;
- weight transport lives in `Weight/Basic.lean`, never in `Graph/Map` or `Reverse`;
- transformation-specific neighborhood laws live in `Neighborhood.lean`, which may import prior transformations;
- leaf modules import concrete children, not umbrellas;
- component and tree definitions consume reachability; reachability never imports them;
- Girth/Moore consume the foundation and do not define foundation vocabulary.

## 6. File-by-file implementation specification

### 6.1 `Graph/Basic.lean`

**Purpose/types/imports.** Minimal carrier definitions for all four graph types; import only the required `Set`/`Sym2` support.

**MUST DEFINE NOW.** Preserve the storage model, with renamed/publicly meaningful fields:

```lean
structure Edge (α β : Type*) where
  tag       : β
  endpoints : Sym2 α

structure Arc (α β : Type*) where
  tag       : β
  endpoints : α × α

def Arc.source (a : Arc α β) : α := a.endpoints.1
def Arc.target (a : Arc α β) : α := a.endpoints.2
```

The four graph structures retain `vertexSet` and `edgeSet`. Replace apostrophe proof fields with `endpoints_mem`, directed `source_mem`/`target_mem`, and simple `loopless`. Keep small `HasVertexSet`/`HasEdgeSet` classes and scoped `V(G)`/`E(G)` notation. The general `HasEdgeSet` instances return the actual bundled fields.

Define only the general lossy views:

```lean
Graph.edgeEndpointPairSet G := Edge.endpoints '' E(G)
DiGraph.arcEndpointPairSet G := Arc.endpoints '' E(G)
```

Preserve explicit `SimpleGraph.toGraph : Graph α (Sym2 α)` and `SimpleDiGraph.toDiGraph : DiGraph α (α × α)`; remove both `Coe` instances.

**SHOULD PROVE NOW.** `Arc.source_mk`, `target_mk`; edge/arc extensionality; four graph extensionality theorems by `V` and actual `E`; `mem_edgeEndpointPairSet`, `mem_arcEndpointPairSet`; `vertexSet_toGraph`, `edgeSet_toGraph`, and directed counterparts; structure proof irrelevance/extensionality simp support. Document tag nonuniqueness and every lossy view.

**MAY DEFER.** `TagInjective`, `GraphLike`, darts/half-edges, direct Mathlib adapters.

**Migration/clients/tests.** Rename `endpointsLabel` without an alias; delete the old closure theorems named `incidence`; update all graph constructors. Immediate clients are every graph file, generated walk graphs, matching, and conversions. Acceptance checks assert the exact four `E(G)` element types and reject `Edge.endpointsLabel` and implicit conversions.

### 6.2 `Graph/Incidence.lean`

**Purpose/types/imports.** Actual-edge endpoint relations for all four types; import only `Graph.Basic`.

**MUST DEFINE NOW.** For both undirected types:

```lean
G.IsLink e u v := e ∈ E(G) ∧ endpoints e = s(u, v)
G.Inc e v      := e ∈ E(G) ∧ v ∈ endpoints e
```

For both directed types:

```lean
G.IsArc a u v := a ∈ E(G) ∧ source a = u ∧ target a = v
G.Inc a v     := a ∈ E(G) ∧ (source a = v ∨ target a = v)
```

For simple graph carriers, `endpoints`, `source`, and `target` in these schemata mean the obvious `Sym2`/pair projections.

Also define Set-valued collections: undirected `incidenceSet` and `loopSet`; directed `outIncidenceSet`, `inIncidenceSet`, and `loopSet`. Every general collection contains full `Edge`/`Arc` values.

**SHOULD PROVE NOW.** `IsLink.edge_mem/endpoints_eq/left_mem/right_mem/symm/inc_left/inc_right`; `isLink_comm`, `isLink_iff`; `IsArc.edge_mem/source_eq/target_eq/source_mem/target_mem/inc_source/inc_target`; `Inc.edge_mem/vertex_mem`; `inc_iff_exists_isLink/isArc`; `mem_incidenceSet`, direction-specific `mem_*IncidenceSet`, `mem_loopSet`; collection subsets of `E(G)`; loop/source/target characterizations. Do not expose directed `.endpoints.1/.2` in public statements.

**MAY DEFER.** Distinguishable loop incidences/darts and executable incidence enumeration.

**Migration/clients/tests.** This replaces `Graph.incidence` and its variants. Immediate clients are adjacency, finite/degree, realized walks, Eulerian specifications, and networks. Tests extract edge and vertex membership through predicate namespaces and verify incidence retains parallel identities.

### 6.3 `Graph/Adjacency.lean`

**Purpose/types/imports.** Vertex adjacency derived from actual link/arc witnesses; import `Graph.Incidence`.

**MUST DEFINE NOW.** Define all four `Adj` relations as `∃ e, G.IsLink e u v` or `∃ a, G.IsArc a u v`. This is definitionally identity-forgetting but not identity-destroying.

**SHOULD PROVE NOW.** `adj_iff_exists_isLink/isArc`; simple direct membership characterizations; undirected `Adj.symm` and `adj_comm`; simple `Adj.ne`; undirected `Adj.left_mem/right_mem`; directed `Adj.source_mem/target_mem`; witness-extraction methods. Preserve the current simple adjacency behavior.

**MAY DEFER.** Generic relation typeclasses.

**Migration/clients/tests.** Rewrite general adjacency away from endpoint-image `E(G)`. Rename directed `Adj.left_mem/right_mem`; update the two current directed-realization uses. Clients are realization, neighborhood, connectivity, coloring, and Moore. Test that parallel edges witness the same adjacency without becoming the edge carrier.

### 6.4 `Graph/Subgraph.lean`

**Purpose/types/imports.** Same-ambient graph order, lattice basics, induced graphs, and spanning actual-edge restriction; import `Graph.Adjacency`.

**MUST DEFINE NOW.** For every graph type define `IsSubgraph H G` as inclusion of `V` and actual `E`, install `LE` and `PartialOrder`, and make `H ≤ G` canonical. Define `IsSpanningSubgraph` (`H ≤ G` and equal vertex sets) and `IsInducedSubgraph` (subgraph plus retention of every ambient actual edge whose endpoints lie in `V(H)`), with scoped `≤s` and `≤i`.

Define `⊥`, `⊓`, and `⊔` for all four same-typed graph families. Bundled identity makes general union/intersection coherent: equal bundled values cannot disagree about endpoints. Define `⊤` as all vertices plus all permitted actual edges (non-diagonal only for simple types). No compatibility predicate is needed.

Preserve:

```lean
G.induce S            -- V = S ∩ V(G), same ambient types
G.restrictEdges F     -- V unchanged, E = E(G) ∩ F
```

where `F` always has the actual edge/arc type.

**SHOULD PROVE NOW.**

- Order/lattice: `IsSubgraph.vertexSet_subset/edgeSet_subset/isLink/isArc/inc/adj`, `Adj.mono`, V/E formulas for bottom/top/inf/sup, and order laws.
- Spanning/induced: reflexivity/transitivity, endpoint-relation congruence on vertices of `H`.
- Induce: `vertexSet_induce`, `edgeSet_induce`, `mem_*_induce`, `induce_le`, inducedness, `induce_le_iff`, left/right monotonicity, empty/univ/vertex-set, nesting/intersection, and `induce_isLink/isArc/inc/adj`.
- Restriction: V/E/membership formulas, subgraph/spanning facts, two-argument monotonicity, empty/univ/edge-set, nesting/intersection, and exact link/arc/incidence/adjacency characterizations. Adjacency after restriction must retain an actual-edge existential so deleting one parallel edge does not imply adjacency disappears.

**MAY DEFER.** `edgeGenerated`, dependent subgraph carriers, and large morphism APIs.

**Migration/clients/tests.** Replace all `subgraphOf` uses atomically; remove all `GetElem` instances for `G[S]`. Immediate clients are every realization layer, deletion, reachability, Girth, matching, and MST specifications. Tests cover relation notation, ambient types, nesting/idempotence, and actual-edge restriction.

### 6.5 `Graph/Delete.lean`

**Purpose/types/imports.** Same-carrier deletions; import `Graph.Subgraph`.

**MUST DEFINE NOW.** On all four graph types implement `deleteEdges`, `deleteEdge`, `deleteVerts`, and `deleteVert`. On undirected types add `deleteEdgesBetween`; on directed types add `deleteArcsFromTo`. Define them through `restrictEdges`/`induce` when that preserves transparent simp behavior.

**SHOULD PROVE NOW.** V/E and membership formulas; `not_mem_edgeSet_deleteEdge`; link/arc/incidence/adjacency characterizations; every deletion is a subgraph; empty/singleton/no-op laws; idempotence; repeated set deletion via union; commutativity of singleton deletion; vertex/edge deletion commutation; monotonicity in the source graph and antitonicity in the deleted set. Endpoint-wide deletion theorems must explicitly remove every matching actual edge/arc.

**MAY DEFER.** Connectivity consequences, dynamic representations, and rewiring.

**Migration/clients/tests.** New module. Immediate clients are later algorithms, cut specifications, and realized-walk restriction lemmas. Test two parallel edges: `deleteEdge e₁` retains `e₂`, while `deleteEdgesBetween u v` removes both.

### 6.6 `Graph/Map.lean`

**Purpose/types/imports.** Arbitrary vertex mapping, bijective relabeling, tag relabeling, and explicit lossy/canonical conversions; import `Graph.Delete`.

**MUST DEFINE NOW.** Use a concrete safe one-step provenance design for arbitrary maps:

```lean
Edge.mapVertices : (α → γ) → Edge α β → Edge γ (Edge α β)
Arc.mapVertices  : (α → γ) → Arc α β  → Arc γ (Arc α β)

Graph.mapVertices   : Graph α β   → (α → γ) → Graph γ (Edge α β)
DiGraph.mapVertices : DiGraph α β → (α → γ) → DiGraph γ (Arc α β)
```

The complete source bundle is the output tag, so the edge map is injective even for a constant vertex map. For simple graph types, `mapVertices : (α → γ) → ... γ` maps endpoints, drops newly created loops, and merges equal endpoint pairs; document that quotienting behavior.

Define equivalence-based relabeling:

```lean
Edge.relabelVertices (f : α ≃ γ) : Edge α β ≃ Edge γ β
Arc.relabelVertices  (f : α ≃ γ) : Arc α β ≃ Arc γ β
Edge.relabelTags     (g : β ≃ δ) : Edge α β ≃ Edge α δ
Arc.relabelTags      (g : β ≃ δ) : Arc α β ≃ Arc α δ
```

and graph-level `relabelVertices` on all four types plus `relabelTags` on general types.

Add explicit conversions:

```lean
Graph.underlyingSimple        : Graph α β → SimpleGraph α
DiGraph.underlyingSimple      : DiGraph α β → SimpleDiGraph α
DiGraph.forgetDirection       : DiGraph α β → Graph α (Arc α β)
SimpleDiGraph.forgetDirection : SimpleDiGraph α → SimpleGraph α
```

The general direction-forgetting conversion uses the full source arc as provenance; the simple conversion is documented as merging antiparallel arcs.

**SHOULD PROVE NOW.** Record tag/endpoint/source/target computations and injectivity; V/E membership formulas; source actual-edge preservation; `mapVertices_isLink/isArc/adj`; simple adjacency preservation with the necessary noncollapse side condition; relabel V/E and link/arc/inc/adj families; relabel identity/composition/inverse; subgraph equivalence; commutation with induce/restrict/delete; conversion V/E and adjacency formulas; explicit loss statements for `underlyingSimple` and simple `forgetDirection`.

**MAY DEFER.** General graph-level arbitrary `mapTags`, repeated-provenance flattening, and a `Hom`/`Embedding`/`Iso` hierarchy. Do not state a misleading `mapVertices_id`: the general result has a provenance-bearing tag type.

**Migration/clients/tests.** New module; remove implicit conversions in Basic. Immediate clients are weight transport, realization transport, and future noninjective transformations. Test same-tag/different-endpoint source edges under a constant map and verify they remain distinct.

### 6.7 `Graph/Reverse.lean`

**Purpose/types/imports.** Directed orientation reversal; import `Graph.Map`.

**MUST DEFINE NOW.** `Arc.reverse`, `DiGraph.reverse`, and `SimpleDiGraph.reverse`. `Arc.reverse` preserves `tag` and swaps endpoints; because identity is the full bundle, a nonloop arc changes actual value.

**SHOULD PROVE NOW.** `tag_reverse`, `source_reverse`, `target_reverse`, `endpoints_reverse`, record involution/injectivity/equivalence; graph V/E formulas; `reverse_isArc/inc/adj`; graph involution; order reflection/preservation for `≤`, `≤s`, `≤i`; commutation with induce, restriction, every deletion, vertex/tag relabeling, and provenance-aware mapping (up to the necessary tag relabeling).

**MAY DEFER.** Residual construction and SCC theorems; reversal is not residual polarity.

**Migration/clients/tests.** New module. Immediate clients are directed realization, reachability/SCC, and attached-data transport. Tests check source/target swap, actual-arc set image, and `reverse_reverse`.

### 6.8 `Graph/Neighborhood.lean`

**Purpose/types/imports.** Adjacency fibers; import `Graph.Reverse` so transformation laws can live here without reversing core dependencies.

**MUST DEFINE NOW.** `neighborSet` for both undirected types and `outNeighborSet`/`inNeighborSet` for both directed types, exactly as adjacency fibers. A loop therefore puts `v` in its own neighborhood; parallel edges do not increase the set.

**SHOULD PROVE NOW.** Canonical `mem_*NeighborSet`; subset of `V(G)`; emptiness outside `V(G)`; undirected membership symmetry; subgraph monotonicity; exact induce formulas (including the base-vertex membership guard); restriction/deletion subset or equality lemmas; `outNeighborSet_reverse`/`inNeighborSet_reverse`.

**MAY DEFER.** `openNeighborSet`, common-neighbor theory, and algorithmic successor enumeration.

**Migration/clients/tests.** Move the temporary simple definition from Girth and `neighborSet_subset_vertexSet` from Moore. Delete `N`, `N+`, and `N-` notation. Clients are finite/degree, Girth/Moore, reachability, BFS/SCC specifications.

### 6.9 `Graph/Finite.lean`

**Purpose/types/imports.** Noncomputable mathematical finite-set views; import `Graph.Neighborhood` and incidence collections.

**MUST DEFINE NOW.** Uniformly define:

```lean
vertexFinset [Finite V(G)] : Finset α
edgeFinset   [Finite E(G)] : Finset ActualEdge
```

and local `neighborFinset`, directed neighbor finsets, `incidenceFinset`, directed incidence finsets, and `loopFinset`, each requiring finiteness of the Set it represents. Install subset-derived finite instances so finite vertices imply finite neighborhoods and finite actual edges imply finite incidence/loop sets. Only simple graph types derive `Finite E(G)` from `Finite V(G)`; general graphs must keep those hypotheses independent.

**SHOULD PROVE NOW.** Every `mem_*Finset` and `coe_*Finset`; vertex/edge Set finiteness bridges; subset relations; `ncard_vertexSet`, `ncard_edgeSet`; preserve the simple cardinal bounds under names `card_edgeFinset_le_card_vertexFinset_choose_two` and `card_edgeFinset_le_two_mul_card_vertexFinset_choose_two`.

**MAY DEFER.** Executable enumeration/refinement contracts and finite endpoint-image finsets.

**Migration/clients/tests.** Preserve the sound simple proofs, replace deprecated `Sym2.map_pair_eq`, expand to general actual edges, and delete `computeVertexFinset`, `computeEdgeFinset`, all of their correctness lemmas, and unused `fin_vertexSet_fin_edgeSet` names. Tests ensure general finite vertices do not synthesize finite actual edges.

### 6.10 `Graph/Degree.lean`

**Purpose/types/imports.** Finite-local degree and finite-graph extrema; import `Graph.Finite`.

**MUST DEFINE NOW.** Rewrite from scratch. Define natural-valued `degree`, `outDegree`, and `inDegree` only with relevant local finite instances. Use:

```lean
Graph.degree G v =
  (G.incidenceFinset v).card + (G.loopFinset v).card
```

so an undirected loop contributes two. Simple degree is neighbor-finset cardinality. Directed degrees are their respective incidence-finset cardinalities, so a directed loop contributes one to each.

Define `maxDegree`, `minDegree`, and directed `maxOutDegree`, `minOutDegree`, `maxInDegree`, `minInDegree` in `ℕ`. Maxima use zero for an empty vertex set; minima require `[Nonempty V(G)]`. Finite simple vertices supply all local finiteness; general extrema require finite actual edges separately.

**SHOULD PROVE NOW.** Cardinal characterizations; degree zero outside `V`; simple positive-degree/adjacency equivalence; loop-corrected edge-card bounds; subgraph/induce/delete monotonicity where hypotheses line up; min/max comparison and attainment; `exists_neighbor_ne_of_two_le_degree`; `exists_adj_of_nonempty_of_two_le_degree`.

**MAY DEFER.** `eDegree`, regularity, complement formulas, and advanced inequalities.

**Migration/clients/tests.** Replace, do not patch, the current broken file. Move two Moore helpers here. Delete `finMaxDegree`, `avgDegree`, incomplete `inc`, and all degree notation. Girth/Moore finite hypotheses must be converted to local instances at the migration boundary. Tests cover parallel edges, two loop edges giving degree four, directed loops, and locally finite degree in a globally infinite graph.

### 6.11 `Graph/DegreeSum.lean`

**Purpose/types/imports.** Finite counting identities and rational average degree; import `Graph.Degree`.

**MUST DEFINE NOW.** Define `SimpleGraph.averageDegree` and `Graph.averageDegree : ℚ` for finite nonempty graphs as the rational degree sum divided by `vertexFinset.card`.

**SHOULD PROVE NOW.** `sum_degrees_eq_twice_card_edges` for both undirected types, including loops/parallel edges; directed `sum_outDegrees_eq_card_edges`, `sum_inDegrees_eq_card_edges`, and equality of the two sums; average-degree cardinal formulas. These are foundational counting identities and should not remain `sorry`.

**MAY DEFER.** Odd-degree parity, average/min/max inequalities, weighted handshake, density theory.

**Migration/clients/tests.** New file. Immediate clients are graph theory, Moore-related counting, and flow sanity checks. Use concrete loop/parallel test graphs.

### 6.12 `Graph/Constructions.lean`

**Purpose/types/imports.** A small implemented constructor library; import Basic/Adjacency/Finite, never higher theory.

**MUST DEFINE NOW.** `empty` and `edgeless S` for all four types; `Graph.ofEdgeSet` and `DiGraph.ofArcSet` with vertices generated from actual endpoints; `Graph.ofEdge`, `DiGraph.ofArc`; `SimpleGraph.singleEdge u v hne`, `SimpleDiGraph.singleArc u v hne`; `SimpleGraph.complete S`, `SimpleDiGraph.complete S`.

**SHOULD PROVE NOW.** V/E membership simp lemmas, adjacency and link/arc characterizations, finite consequences, `empty = edgeless ∅`, and basic extensional equalities.

**MAY DEFER.** Path/cycle/star/complete-bipartite constructors until client signatures are fixed; wheel, grid, hypercube, Kneser, named sporadic graphs, products, complement, and Cayley graphs.

**Migration/clients/tests.** Delete `Graph/Graphs.lean`; do not forward its snake-case placeholders. These constructors provide small acceptance fixtures for every foundation family.

### 6.13 `Util/List.lean` and `Walk/VertexSeq/*`

**Purpose/types/imports.** Preserve the proven graph-independent nonempty sequence foundation. `Util/List.lean` owns GraphLib-specific list helpers; vertex-sequence leaves import only earlier leaves.

**MUST DEFINE NOW.** Move public declarations under `GraphLib` without changing the data representation. Keep `VertexSeq.singleton` and the historical right-extending `VertexSeq.cons`; `length`, `head`, `tail`, `toList`; `nodup`, `nonstalling`, `closed`; append/reverse/drop; prefix/suffix/take/drop/split; loop/cycle erasure; `edges`, `arcs`; map/zip/folds/indexing. Keep `Walk/VertexSeq.lean` as an umbrella.

Move `List.commonPrefix`, `commonPrefix_split`, and `commonPrefix_ne_nil` into a GraphLib-owned namespace in `Util/List.lean`; do not add declarations to root `List`.

The leaf responsibilities remain:

| File | Required contents and preserved theorem families |
|---|---|
| `Basic.lean` | carrier, constructor orientation, projections, membership/subset, drops, length-zero laws |
| `Predicates.lean` | `nodup`, `nonstalling`, `closed`, drop and list equivalences |
| `Append.lean` | append/reverse, length/head/tail, associativity, nodup/nonstalling, drop laws |
| `Subseq.lean` | prefix/suffix/take/drop/split, reconstruction, membership/length/predicate closure |
| `Erase.lean` | loop and cycle erase, endpoint preservation, nodup/nonstalling/subset results |
| `Edges.lean` | actual simple endpoint-pair `edges`/`arcs`, length/append/reverse/subset/nodup laws |
| `MapZip.lean` | map/folds/zip, injective preservation, functor laws |
| `Index.lean` | safe indexing and head/tail/index relationships |

**SHOULD PROVE NOW.** Preserve all existing compiling theorems and definitional equalities, especially `suffixFrom`, `eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one`, edge/arc append/reverse laws, and erase subset/endpoint laws.

**MAY DEFER.** New sequence algebra. Keep the generic scoped `Snoc`/`:+` only as a temporary compatibility detail if removal would disturb the mature spine; add no new instances.

**Migration/clients/tests.** Use forwarding import modules only during the file move; do not duplicate declarations. `SimpleCycle.ofTwoPaths` is the direct `commonPrefix` client. Build every leaf plus `SimpleCycle` after the move.

### 6.14 `Walk/SimpleWalk.lean`, `SimplePath.lean`, `SimpleCycle.lean`, and `SimpleDiCycle.lean`

These are separate files with the following common policy: graph-independent data stays under `GraphLib`; existing subtype chains and definitional equality are preserved; each file imports only its predecessor.

#### `SimpleWalk.lean`

**MUST DEFINE NOW.** Preserve `SimpleWalk α := {w : VertexSeq α // w.nonstalling}`, its `val`, support/edge/arc/head/tail/length/nodup/closed accessors, drop/append/glue/reverse/prefix/suffix/erase/injective-map operations, and `toSimpleGraph`/`toSimpleDiGraph`.

**SHOULD PROVE NOW.** Preserve all constructor, length, endpoint, membership, edge/arc append/reverse/subset, map, and generated-graph membership laws.

#### `SimplePath.lean`

**MUST DEFINE NOW.** Preserve the vertex-nodup subtype, accessors/coercion, singleton, append/glue/reverse/prefix/suffix/erase, and injective map. Add a concrete `extendTail` operation taking freshness; keep the current existential `exists_longer_of_adj_not_mem` later as a realization corollary.

**SHOULD PROVE NOW.** `vertices/head/tail/length/edges/arcs_extendTail`, existing singleton/append/reverse/nodup/subset families, and the definitional behavior used by Moore.

#### `SimpleCycle.lean`

**MUST DEFINE NOW.** Preserve the existing undirected convention (minimum length three), `SimpleWalk.IsCycle`, subtype/accessors, `interior`, `reverse`, `reroot`, `ofPathClosing`, `ofInternallyDisjointPaths`, and `ofTwoPaths`.

**SHOULD PROVE NOW.** Preserve all existing API, especially `length_ofTwoPaths`, `head_ofTwoPaths_mem_left`, `edges_ofTwoPaths_subset`, and edge/arc nodup/reverse lemmas.

#### `SimpleDiCycle.lean`

**MUST DEFINE NOW.** Direction genuinely changes the minimum-cycle convention, so define:

```lean
SimpleWalk.IsDiCycle w :=
  2 ≤ w.length ∧ w.closed ∧ w.dropTail.nodup

SimpleDiCycle α := {w : SimpleWalk α // w.IsDiCycle}
```

Add `val`, `vertices`, `support`, `arcs`, endpoints/length, `interior`, `reverse`, `reroot`, and directed `ofPathClosing`. A simple directed two-cycle is valid; a length-one cycle is excluded by simple looplessness.

**SHOULD PROVE NOW.** Projection simp laws, arc nodup, reverse/reroot preservation, and constructor computations.

**MAY DEFER for this family.** Cycle quotients modulo rotation/reversal, full path decomposition, and a directed `ofTwoPaths` selector until directed girth needs it.

**Migration/clients/tests.** Move existing files with minimal edits. Immediate clients are all simple realization layers and Girth/Moore. Tests freeze constructor/projection reduction and the length-three versus directed-length-two distinction.

### 6.15 `Walk/Walk.lean`

**Purpose/types/imports.** General graph-independent alternating vertex/tag data; import `Graph.Basic` and the vertex-sequence umbrella.

**MUST DEFINE NOW.** Preserve the inductive carrier and right-extending `cons`. Apply the locked vocabulary:

| Current | Target | Meaning |
|---|---|---|
| `toVertexList` | `vertices` | visited vertex list |
| `toEdgeList` | `tags` | raw step-tag list |
| `hasEdge` | `hasTag` | raw tag occurrence |
| `mapV` | `mapVertices` | vertex map |
| `mapE` | `mapTags` | tag map |

Remove `∈ₑ` and the mixed `HasSubset` instance. Preserve `head`, `tail`, `length`, vertex membership, drops, reverse, prefix/suffix, folds, erasures, `nodup`, `nonstalling`, `closed`, and `toVertexSeq`. Add raw `append` and `glue`.

Most importantly preserve:

```lean
edges : Walk α β → List (Edge α β)
arcs  : Walk α β → List (Arc α β)
toGraph   : Walk α β → Graph α β
toDiGraph : Walk α β → DiGraph α β
```

`edges`/`arcs` reconstruct full actual values from each tag and its adjacent vertices. Reusing a tag at different endpoints is therefore sound.

**SHOULD PROVE NOW.** Constructor and length laws for vertices/tags/edges/arcs; reverse formulas (`edges_reverse` is list reversal, `arcs_reverse` is reversal plus `Arc.reverse`); append/glue formulas; operation subset laws for actual lists; map identity/composition/commutation and reconstructed-step behavior; `toVertexSeq` commutation; V/E formulas for generated graphs.

**MAY DEFER.** Occurrence-index graphs and generic splice APIs.

**Migration/clients/tests.** No semantic aliases for the old tag-misleading names. Update Eulerian/Hamiltonian drafts atomically. Tests reuse one tag at two endpoint pairs and verify two distinct actual reconstructed bundles and the generated graph edge set.

### 6.16 `Walk/Trail.lean`, `Path.lean`, `Circuit.lean`, and `Cycle.lean`

**Purpose/types/imports.** Complete the graph-independent general combinatorial hierarchy above raw `Walk`.

A single unqualified `Trail α β` cannot serve both directions: `w.edges.Nodup` and `w.arcs.Nodup` disagree for antiparallel same-tag steps. This is an implementation-blocking semantic fact, not optional symmetry. Use the exact split:

```lean
Trail α β   := {w : Walk α β // w.edges.Nodup}
DiTrail α β := {w : Walk α β // w.arcs.Nodup}

Path α β := {w : Walk α β // w.vertices.Nodup}

Circuit α β   := {t : Trail α β // 0 < t.length ∧ t.closed}
DiCircuit α β := {t : DiTrail α β // 0 < t.length ∧ t.closed}

Cycle α β := {w : Walk α β //
  0 < w.length ∧ w.closed ∧ w.dropTail.vertices.Nodup ∧ w.edges.Nodup}

DiCycle α β := {w : Walk α β //
  0 < w.length ∧ w.closed ∧ w.dropTail.vertices.Nodup ∧ w.arcs.Nodup}
```

The ambient realization names remain `Graph.IsTrailIn` and `DiGraph.IsTrailIn`, not `IsDiTrailIn`.

**MUST DEFINE NOW in each file.** The displayed carriers; standard `val`/walk and vertices/tags/edges/arcs/head/tail/length accessors; coercions that do not erase semantic distinctions; extensionality; `Path.singleton`; raw reverse operations.

These conventions deliberately admit a general loop cycle of length one; an undirected length-two cycle only when it uses two distinct parallel full edges; and a directed two-cycle made of antiparallel actual arcs.

**SHOULD PROVE NOW.** Projection simp laws; reverse preservation for all appropriate carriers; drop/prefix/suffix closure; `Walk.toPath` through cycle erasure preserving endpoints; path append/glue under explicit vertex disjointness; circuit/cycle interior computations.

**MAY DEFER.** Closed-walk cycle decomposition, Euler existence theory, canonical cycle quotients.

**Migration/clients/tests.** Replace the current empty files; delete the conflicting obsolete `Theory/Structures/Basic.lean` first. Tests distinguish invalid repeated undirected edges from legal antiparallel same-tag directed arcs.

### 6.17 `Walk/InSimpleGraph/*` and `Walk/InSimpleDiGraph/*`

**Purpose/types/imports.** Realization of the vertex-only simple hierarchy. Import graph transformations and the corresponding data carriers, never higher theory.

#### `InSimpleGraph/{VertexSeq,Walk,Path,Cycle}.lean`

**MUST DEFINE NOW.** Move the existing `IsVertexSeqIn`, `IsSimpleWalkIn`, `IsSimplePathIn`, and `IsSimpleCycleIn` with minimal semantic change. Keep current constructor shapes and `iff_edges`. Replace `subgraphOf` with `≤`; rename generated graph bridge lemmas to `toSimpleGraph_le`, `of_toSimpleGraph_le`, and `iff_toSimpleGraph_le`. Keep every Girth/Moore-facing constructor and path-to-cycle result.

Move `HasSimpleCycle`/`IsAcyclic` definitions to `Connectivity/Acyclic.lean`; realization remains here.

**SHOULD PROVE NOW.** Preserve all current membership and operation closure; `mono`; exact induce/restrict/delete characterizations; bijective relabel transport; concrete path-tail extension realization plus the existing existential corollary.

#### `InSimpleDiGraph/{VertexSeq,Walk,Path,Cycle}.lean`

**MUST DEFINE NOW.** Split the existing 445-line module by its real size. Preserve current directed vertex-sequence/simple-walk realization, add `IsSimplePathIn` and `IsSimpleDiCycleIn`, and keep direction-preserving operations.

**SHOULD PROVE NOW.** `iff_arcs`, `arc_mem`, generated-digraph `≤` bridge, monotonicity, induce/delete/relabel families, directed-cycle constructors, and reverse transport only into `G.reverse` for sequences, walks, paths, and directed cycles.

**MAY DEFER for both.** Arbitrary noninjective-map preservation of paths (map to a sequence/walk and erase cycles instead), deep induced-path theory, directed `ofTwoPaths`, and directed girth.

**Migration/clients/tests.** Use forwarding imports during relocation only. Girth/Moore declarations and definitional equalities listed in section 8 are frozen regression targets. Test that no directed same-graph reverse theorem is accidentally introduced.

### 6.18 `Walk/InGraph.lean` and `Walk/InDiGraph.lean`

**Purpose/types/imports.** Identity-sensitive realization of general raw data and its hierarchy; import Subgraph/Delete/Map/Reverse plus general walk carriers.

**MUST DEFINE NOW.** Undirected realization checks reconstructed actual edges:

```lean
inductive Graph.IsWalkIn (G : Graph α β) : Walk α β → Prop
| singleton (v) (hv : v ∈ V(G))
| cons (w) (v) (t)
    (hw : G.IsWalkIn w)
    (hlink : G.IsLink ⟨t, s(w.tail, v)⟩ w.tail v)
```

Directed realization is analogous with `G.IsArc ⟨t, (w.tail, v)⟩ w.tail v`. Define thin `IsTrailIn`, `IsPathIn`, `IsCircuitIn`, and `IsCycleIn` over the direction-correct carriers.

**SHOULD PROVE NOW in both files.** `singleton_iff`, `cons_iff`, endpoint/visited-vertex membership, `edge_mem` or `arc_mem`, `iff_edges`/`iff_arcs`, drops/prefix/suffix, append/glue, subgraph `mono`, generated-graph bridges `toGraph_le`/`toDiGraph_le` and converses, exact induce/restrict/delete characterizations, and relabel transport. Undirected reverse stays in `G`; directed reverse lands in `G.reverse` while raw tags remain fixed.

Add `spannedSubgraph` only as a realization-associated definition if a proof client needs a subgraph that drops unused ambient vertices; do not pull it into `Graph/Subgraph`.

**MAY DEFER.** Repeated arbitrary-map realization transport/provenance flattening and residual-specific traversal theory.

**Migration/clients/tests.** Replace the empty `InGraph`, add `InDiGraph`. Tests prove realization depends on `w.edges`/`w.arcs`, never merely `w.tags`, and verify generated-graph/subgraph equivalences and directed reversal.

### 6.19 `Walk/Coverage.lean`

**Purpose/types/imports.** Correct specification predicates for coverage; import all four realization layers.

**MUST DEFINE NOW.** Graph-relative predicates:

```text
G.IsEulerianTrailIn
G.IsEulerianCircuitIn
G.IsHamiltonianPathIn
G.IsHamiltonianCycleIn
```

Eulerian predicates include realization and exact coverage of actual `E(G)`; general forms take `Trail`/`DiTrail` and `Circuit`/`DiCircuit`. Hamiltonian predicates include realization and exact vertex coverage. Simple variants may use the existing simple carriers and their actual endpoint-pair lists; do not invent `SimpleTrail` merely for symmetry.

**SHOULD PROVE NOW.** Projection to realization, actual edge/vertex membership, and extensionality under equality of the ambient V/E sets.

**MAY DEFER.** Euler/Hamilton existence characterizations and algorithms.

**Migration/clients/tests.** Delete, rather than alias, `Walk.IsEulerian*`, `Walk.IsHamiltonian*`, and simple-walk variants. Tests demonstrate that an unrealized covering sequence is not Eulerian/Hamiltonian and that general Eulerian coverage compares full bundles.

### 6.20 Umbrella modules

`GraphLib/Graph.lean`, `Walk.lean`, `Connectivity.lean`, and `Weight.lean` are true umbrellas importing their production children. `GraphLib/All.lean` imports every production GraphLib module intended to compile. `GraphLib.lean` imports the stable umbrellas and no development blueprint. Leaf files never import umbrellas.

**SHOULD PROVE/TEST NOW.** There are no declarations in umbrellas. `GraphLibTest/ImportAll.lean` imports `GraphLib.All`; CI also builds important leaves directly so an umbrella cannot conceal a dependency cycle.

### 6.21 `Connectivity/Reachability.lean`

**Purpose/types/imports.** Existential path reachability for all four graph types; import the four realization modules.

**MUST DEFINE NOW.** Use `SimplePath` for simple graph types and the shared general `Path` for general types:

```lean
G.Reachable u v :=
  ∃ p, G.IsPathIn p ∧ p.head = u ∧ p.tail = v
```

with the simple realization name substituted where appropriate.

**SHOULD PROVE NOW.** `reachable_iff_exists_simplePath/path`, `reachable_iff_exists_walk`; `Reachable.refl` with `u ∈ V(G)`; adjacency step; transitivity; subgraph monotonicity; left/right vertex membership; undirected symmetry; directed `reverse_reachable`; relabel equivalence. Prove the reflexive-transitive adjacency-closure characterization with an explicit vertex-membership conjunct—plain relation reflexivity would incorrectly include ambient vertices outside `V(G)`.

**MAY DEFER.** Finite decidability, executable search, distances, and arbitrary provenance-map reachability transport.

**Migration/clients/tests.** Replaces the empty connectivity placeholder. Immediate clients are connectedness, SCCs, trees, Hamiltonian theory, and future search correctness. Test reflexivity only on graph vertices, transitivity, symmetry/reversal, and monotonicity.

### 6.22 `Connectivity/Connected.lean`

**Purpose/types/imports.** Undirected connectivity and component sets for `SimpleGraph` and `Graph`; import Reachability.

**MUST DEFINE NOW.** Fix the empty-graph convention explicitly:

```lean
G.Preconnected := ∀ u ∈ V(G), ∀ v ∈ V(G), G.Reachable u v
G.Connected    := V(G).Nonempty ∧ G.Preconnected
G.connectedComponentSet v := {u | G.Reachable v u}
```

The empty graph is preconnected and not connected.

**SHOULD PROVE NOW.** Component membership, root membership under `v ∈ V`, subset of `V`, component equality iff roots are reachable, equal-or-disjoint components, connectedness via one component, and relabel invariance. State reachability monotonicity under subgraphs; do not state the false claim that connectedness is subgraph-monotone.

**MAY DEFER.** A quotient/bundled `ConnectedComponent`, induced-component connectedness if proof-heavy, cuts, blocks, and Menger theory.

**Migration/clients/tests.** Delete local `SimpleGraph.IsConnected`; update Tree. Test the empty convention and component equality/disjointness.

### 6.23 `Connectivity/StronglyConnected.lean`

**Purpose/types/imports.** Directed mutual reachability and component sets for both directed types; import Reachability and Reverse.

**MUST DEFINE NOW.** Define:

```lean
G.StronglyConnected u v := G.Reachable u v ∧ G.Reachable v u
G.IsStronglyConnected :=
  V(G).Nonempty ∧ ∀ u ∈ V(G), ∀ v ∈ V(G), G.StronglyConnected u v
G.stronglyConnectedComponentSet v := {u | G.StronglyConnected v u}
```

**SHOULD PROVE NOW.** Reflexivity on vertices, symmetry, transitivity; membership/subset/equality/equal-or-disjoint component laws; reverse invariance; relabel invariance; an equivalence relation on the vertex subtype if it shortens component proofs.

**MAY DEFER.** Public quotient carrier, condensation graph, Tarjan/Kosaraju, and executable enumeration.

**Migration/clients/tests.** Replaces SCC placeholder specifications, not the algorithm. Test mutual-reachability unfolding and reverse invariance.

### 6.24 `Connectivity/Acyclic.lean`

**Purpose/types/imports.** Cycle absence for all four graph types and basic undirected forest/tree definitions; import realized cycle modules and Connected/StronglyConnected as needed.

**MUST DEFINE NOW.** Move existing `SimpleGraph.HasSimpleCycle`/`IsAcyclic` without semantic change. Add corresponding definitions for `SimpleDiGraph`, `Graph`, and `DiGraph` using `SimpleDiCycle`, `Cycle`, and `DiCycle` respectively. On undirected types define `IsForest := IsAcyclic` and `IsTree := Connected ∧ IsAcyclic`; directed forest/tree are not applicable.

**SHOULD PROVE NOW.** Existence/negation characterizations; acyclicity descending to subgraphs; no-edge acyclicity; directed reverse invariance; relabel invariance; `isForest_iff_isAcyclic`; agreement with the old simple cycle semantics.

**MAY DEFER.** Unique-path tree characterization, spanning-tree existence, topological ordering, feedback sets, and advanced general-graph cycle theory.

**Migration/clients/tests.** Delete `SimpleGraph.Contains`; rewrite Forest/Tree on the formal realization/connectivity layer. Immediate clients include Girth. Test loops and two parallel edges as cycles for general graphs, simple length conventions, and subgraph monotonicity.

### 6.25 `Weight/Basic.lean`

**Purpose/types/imports.** Lightweight attached vertex/actual-edge data and explicit transport; import Map and Reverse.

**MUST DEFINE NOW.** Define graph-namespaced total function aliases whose values matter on active carriers:

| Graph type | `VertexWeight G W` | `EdgeWeight G W` / `Cost G W` |
|---|---|---|
| `SimpleGraph α` | `α → W` | `Sym2 α → W` |
| `SimpleDiGraph α` | `α → W` | `(α × α) → W` |
| `Graph α β` | `α → W` | `Edge α β → W` |
| `DiGraph α β` | `α → W` | `Arc α β → W` |

Define `Capacity` on the two directed types only, with the same actual-arc domains. Do not add graph structure fields or `WeightedGraph` variants.

Define equality-on-graph via `Set.EqOn` on `V(G)` or `E(G)`. Define transport along explicit vertex/actual-edge equivalences and the provenance correspondence supplied by general `mapVertices`. Same-carrier induce/restrict/delete reuse the original function directly.

**SHOULD PROVE NOW.** Transport application/id/composition/inverse; specialized relabel-vertices, relabel-tags, reverse, and provenance-map formulas; `EqOn` congruence; corresponding vertex-weight relabel laws.

**MAY DEFER.** Bundled data wrappers, typeclass algebra/order assumptions, and residual polarity types until a flow client needs them.

**Migration/clients/tests.** New module. Matching/MST/flow are stress clients. Test two full edges with the same tag at different endpoints receiving different weights and verify no public general type is `β → W`.

### 6.26 `Weight/Walk.lean`

**Purpose/types/imports.** Additive traversal weight over final carriers; import Weight.Basic and realization modules.

**MUST DEFINE NOW.** Under `[AddMonoid W]`, define graph-namespaced `walkWeight` and `pathWeight` on all applicable graph types. General undirected sums `w.edges : List (Edge α β)`; general directed sums `w.arcs : List (Arc α β)`; simple forms use endpoint-pair lists. Computation does not require a realization proof, but congruence for weights equal only on `E(G)` does.

**SHOULD PROVE NOW.** Singleton/one-step computations; `walkWeight_append`; path/walk compatibility; congruence under `Set.EqOn E(G)` plus realization; undirected reverse invariance; directed reverse under transported weight; relabel transport.

**MAY DEFER.** Vertex-visit weights, ordered/nonnegative path theory, distance, negative cycles, shortest paths, and optimization.

**Migration/clients/tests.** New module; it must consume reconstructed actual values, not `tags`. Test append and reverse on reused tags.

### 6.27 `Weight/Network.lean`

**Purpose/types/imports.** Flow/cut specification objects on identity-sensitive directed graphs; import Weight.Basic, Finite, and directed incidence.

**MUST DEFINE NOW.** On `DiGraph` define:

```lean
structure Network (G : DiGraph α β) (R : Type*) where
  source sink : α
  source_mem : source ∈ V(G)
  sink_mem : sink ∈ V(G)
  source_ne_sink : source ≠ sink
  capacity : Arc α β → R

abbrev Flow (N : Network G R) := Arc α β → R
```

`Network` itself imposes no finiteness, order, addition, or nonnegativity. In suitably constrained sections define `Flow.outflow`, `inflow`, `flowValue`, and `Flow.IsFeasible` (nonnegative active-arc flow, capacity bounds, and conservation at internal vertices). Define `DiGraph.cutArcSet`, `Network.IsCut`, and `Network.cutCapacity`. Finite sums require `[Finite E(G)]`; loops occur once in each direction and cancel in conservation; parallel arcs sum separately.

**SHOULD PROVE NOW.** Cut membership/subset/finiteness; flow/capacity extensionality on active arcs; zero-flow feasibility under suitable nonnegative capacities; conservation rewriting; relabel transport and reverse transport only where mathematically stated with source/sink swap.

**MAY DEFER.** Source-value equals sink-value, cut-flow identities, weak duality, residual networks, max-flow/min-cut, min-cost flow, and algorithms.

**Migration/clients/tests.** Replace only the specification part of the flow placeholder; do not implement an algorithm. Test that capacity/flow domains are `Arc α β`, antiparallel and parallel arcs remain separate, and finite vertices alone are insufficient for sums.

## 7. API coverage matrix

Legend: **complete** = definitions plus routine API in this round; **thin** = object is defined and usable but advanced theory is deferred; **shared** = inherited from graph-independent data or another exact API; **deferred** = no public declaration this round; **N/A** = mathematically not applicable.

| API family | `SimpleGraph` | `SimpleDiGraph` | `Graph` | `DiGraph` |
|---|---|---|---|---|
| `V(G)` / actual `E(G)` | complete | complete | complete, bundled | complete, bundled |
| `IsLink` / `IsArc` / `Inc` / `Adj` | complete | complete | complete | complete |
| lossy endpoint-pair image | use `E(G)` | use `E(G)` | complete `edgeEndpointPairSet` | complete `arcEndpointPairSet` |
| subgraph order / lattice / `≤s` / `≤i` | complete | complete | complete | complete |
| induce / actual-edge restriction | complete | complete | complete | complete |
| edge/vertex/endpoint-wide deletion | complete | complete | complete | complete |
| arbitrary `mapVertices` | complete, lossy simple quotient | complete, lossy simple quotient | complete, provenance tag | complete, provenance tag |
| vertex/tag relabel | vertices complete; tags N/A | vertices complete; tags N/A | both complete | both complete |
| reverse | N/A | complete | N/A | complete |
| explicit conversions | complete | complete | complete lossy `underlyingSimple` | complete lossy/provenance conversions |
| neighborhood Set/Finset | complete | complete in/out | complete | complete in/out |
| incidence Set/Finset / loops | complete | complete in/out | complete actual edges | complete actual arcs in/out |
| mathematical vertex/edge finsets | complete | complete | complete with independent finiteness | complete with independent finiteness |
| finite-local degree / extrema | complete | complete in/out | complete, loops count twice | complete in/out |
| degree sums / average | complete | directed sums complete | complete | directed sums complete |
| simple vertex-only walk spine | complete | complete plus `SimpleDiCycle` | N/A | N/A |
| raw tag walk | N/A (simple spine preferred) | N/A | shared | shared |
| trail/path/circuit/cycle data | simple carriers/shared | simple directed carriers/shared | complete undirected carriers | complete directed carriers |
| realization | complete | complete | complete | complete |
| reachability | complete | complete | complete, theory thin | complete, theory thin |
| connectedness / component sets | complete | N/A | complete, quotient deferred | N/A |
| SCC relation / component sets | N/A | complete | N/A | complete |
| acyclicity | complete | complete | thin but defined | thin but defined |
| forest/tree | complete definitions | N/A | thin definitions | N/A |
| Euler/Hamilton predicates | thin specifications | thin specifications | thin specifications | thin specifications |
| vertex/edge weights and costs | complete | complete | complete actual-edge domain | complete actual-arc domain |
| capacities/network/flow spec | N/A | shared through explicit `toDiGraph` if desired | N/A | complete |
| selected constructors | complete small set | complete small set | complete small set | complete small set |
| executable enumeration | deferred | deferred | deferred | deferred |
| Mathlib interop | deferred | deferred | deferred | deferred |
| `VertexSplit` | deferred | deferred | deferred | deferred |
| contraction | out of scope | out of scope | out of scope | out of scope |

## 8. Walk and connectivity construction plan

### 8.1 Preserve first, extend second

The simple spine is not a prototype to rewrite. Its carrier definitions, constructor orientation, subtype chain, and Girth/Moore-facing theorem statements are migration constraints. File moves use temporary forwarding imports; declarations are not duplicated. Public declarations move under `GraphLib` as required by `NAMING.md`, but the stems remain unchanged.

The following are specifically frozen unless a locked rename requires a local edit:

```text
VertexSeq.singleton / cons / suffixFrom
VertexSeq.eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one
SimplePath.singleton / append / vertices / head / tail / length
SimpleGraph.IsSimpleWalkIn.append
SimpleGraph.IsSimplePathIn.singleton
SimpleGraph.IsSimplePathIn.exists_longer_of_adj_not_mem
SimpleCycle.ofPathClosing / ofInternallyDisjointPaths / ofTwoPaths
SimpleCycle.length_ofTwoPaths
SimpleGraph.IsSimpleCycleIn.ofPathClosing / ofTwoPaths
exists_length_le_succ_of_adj_mem
exists_length_le_add_of_two_paths
```

The `subgraphOf → ≤` edit and file moves may make this chain red inside an unmerged branch, but each phase exit rebuilds the entire chain. There is no approved phase boundary at which it remains broken.

### 8.2 Raw tags versus actual traversed values

The public raw-walk vocabulary has three distinct layers:

```lean
w.tags      : List β
w.edges     : List (Edge α β)
w.arcs      : List (Arc α β)
```

Only `tags` may be inspected by `hasTag` or transformed by `mapTags`. Identity-sensitive predicates, trail nodup, Eulerian coverage, weights, and general realization always consume `edges` or `arcs`. No theorem may infer repeated actual-edge use from a repeated tag alone.

The direction-correct carrier split is mandatory:

```text
undirected: Trail → Circuit → Cycle, using reconstructed Edge values
directed:   DiTrail → DiCircuit → DiCycle, using reconstructed Arc values
shared:     Path, using vertex nonrepetition
```

This avoids both false rejection of legal antiparallel directed arcs and false acceptance of a repeated undirected edge.

### 8.3 Realization and transformations

Every realization layer provides a constructor view and a list view. General list views are:

```lean
G.IsWalkIn w ↔ w.head ∈ V(G) ∧ ∀ e ∈ w.edges, e ∈ E(G)
D.IsWalkIn w ↔ w.head ∈ V(D) ∧ ∀ a ∈ w.arcs,  a ∈ E(D)
```

They support subgraph monotonicity, induce/restrict/delete characterizations, and equivalence-based relabeling. Same-carrier transformations reuse the same raw walk. Directed reverse uses `w.reverse` and realizes it in `G.reverse`; raw tags stay fixed and reconstructed arcs reverse orientation.

Arbitrary simple-graph vertex maps may stall or identify vertices. Do not claim direct preservation of `SimplePath`; map to a vertex sequence/walk, then use loop/cycle erasure. For general graphs, one-step provenance mapping is defined, but repeated-map normalization and broad path transport remain deferred.

### 8.4 Reachability and components

Reachability is path existence over ambient vertex values. Reflexivity always requires graph membership. Undirected connectedness is split into vacuous `Preconnected` and nonempty `Connected`. Directed strong connectedness is mutual reachability. This round exposes component **sets** with exact `Set` suffixes; quotient carriers are intentionally deferred.

The formal forest/tree definitions consume the new acyclicity and connectedness, eliminating `SimpleGraph.Contains` and the local `IsConnected`. Sophisticated unique-path/tree theorems are not required for a coherent foundation.

### 8.5 Regression restoration points

1. After actual-edge Basic/Incidence/Adjacency, the current simple chain still compiles.
2. In the subgraph phase, update every `subgraphOf` client in the same PR; Girth/Moore is green at the phase exit.
3. File relocation may break imports transiently; forwarding imports keep downstream theorem code available, and the full chain is green before merge.
4. Neighborhood/degree migration removes duplicate Girth declarations atomically and rebuilds both odd and even Moore bounds before any further phase.
5. Final CI builds the moved modules and the root import-all target, so the chain can no longer be omitted accidentally.

## 9. Edge data, weights, and network plan

### 9.1 Domains and extensionality

General domains are fixed:

```lean
Graph.EdgeWeight G W = Edge α β → W
DiGraph.EdgeWeight G W = Arc α β → W
DiGraph.Capacity G R = Arc α β → R
Flow N = Arc α β → R
```

The graph parameter documents the active domain; equality relevant to a graph is `Set.EqOn` on `E(G)`. This total-function choice lets induce, restriction, and deletion reuse the same data without subtype casts. The same rule applies to `Cost`.

No public general declaration in this family has domain `β`. A client with globally unique tags may later add an explicit `TagInjective`-based convenience layer, but it is not foundational.

### 9.2 Transport boundaries

- Same-carrier induce/restrict/delete: reuse the function unchanged.
- Vertex or tag equivalence: transport along `Edge.relabel*`/`Arc.relabel*` equivalences.
- Directed reverse: transport along the `Arc.reverse` involution; data is not definitionally unchanged because the full arc value changes.
- Arbitrary general `mapVertices`: push data to the provenance-tagged target by projecting the target edge/arc's `tag`, which is the full source bundle.
- Simple arbitrary maps are lossy; unrestricted push-forward data is not defined when edges merge. Require an aggregation policy in a future client rather than choosing one in the foundation.

### 9.3 Traversal sums

`walkWeight` and `pathWeight` fold over reconstructed actual steps. Realization is needed only when replacing one weight by another that agrees on active edges. Directed reverse theorems explicitly mention the transported reverse weight. This keeps weight algebra separate from graph representation and path validity.

### 9.4 Networks and flows

`Network` is a specification record over a general `DiGraph`, with actual-arc capacity and no algebraic fields. Finiteness/order/addition enter only the definitions that need them. Flow feasibility checks only active arcs, includes nonnegativity and upper capacity, and uses actual in/out incidence finsets for conservation. Antiparallel arcs, parallel arcs, reused tags, and loops therefore have the correct distinct contributions.

Residual construction is not reverse and is deferred. A future residual tag must include the full source `Arc α β` plus forward/backward polarity; this compatibility requirement does not authorize a residual API now.

## 10. Current-code migration table

| Current file/declaration | Action | Target | Breaking? | Immediate clients to update | Phase |
|---|---|---|---|---|---|
| `Graph/Basic.lean`: `Edge.endpointsLabel`, `Arc.endpointsLabel` | rename | `tag` | yes | Basic constructors, prototypes only | 1 |
| general `HasEdgeSet` endpoint image | redefine | actual `edgeSet` | yes/type change | general adjacency | 1 |
| unnamed endpoint images | replace | `edgeEndpointPairSet`, `arcEndpointPairSet` | additive | interop/reporting | 1 |
| `incidence'`, directed pair closure | rename/split | `endpoints_mem`, `source_mem`, `target_mem` | yes | Subgraph, Finite, generated walk graphs | 1 |
| `loopless'` | rename | `loopless` projection | yes | Adjacency, Finite, generated graphs | 1 |
| closure theorems `Graph.incidence` etc. | delete/replace | `IsLink`, `IsArc`, `Inc` proof namespaces | yes | Adjacency | 1 |
| public directed pair projections | replace | `Arc.source`, `Arc.target` | yes | core/directed files | 1 |
| implicit simple→general `Coe` | delete | explicit `toGraph`, `toDiGraph` | yes | no observed source client | 1 |
| general `Adj` over endpoint-image `E` | rewrite | existential actual link/arc | semantic repair | future general clients | 1 |
| directed `Adj.left_mem/right_mem` | rename | `source_mem/target_mem` | yes | `InSimpleDiGraph` | 1 |
| `Graph/Subgraph.lean`: `subgraphOf` | replace | `IsSubgraph`, `H ≤ G` | yes | realization and Girth | 2 |
| four `G[S]` `GetElem` instances | delete | `G.induce S` | yes | none | 2 |
| existing `induce` | preserve/extend | same name and ambient types | no semantic break | realization | 2 |
| missing order/lattice/spanning/induced API | add | `≤`, `⊥/⊤/⊓/⊔`, `≤s`, `≤i` | additive | all transformations | 2 |
| missing edge restriction | add | `restrictEdges` on actual carriers | additive | delete/MST | 2 |
| missing deletion | add | `Graph/Delete.lean` | additive | future algorithms/theory | 3 |
| missing map/relabel/conversions | add | `Graph/Map.lean` | additive | weights/realization | 3 |
| missing reverse | add | `Graph/Reverse.lean` | additive | directed walks/SCC/data | 3 |
| `Theory/Structures/VertexSeq*` | move only plus namespace | `Walk/VertexSeq*` under `GraphLib` | broad mechanical | full simple spine | 4 |
| root `List.commonPrefix*` | move/namespace | `Util/List.lean` | yes | `SimpleCycle.ofTwoPaths` | 4 |
| `SimpleWalk`, `SimplePath`, `SimpleCycle` | move, preserve definitions | `Walk/*` | import break only | Girth/Moore | 4 |
| `InSimpleGraph/*` | move/rewrite relation names | `Walk/InSimpleGraph/*` | yes | Girth/Moore/Bipartite | 2/4 |
| `InSimpleDiGraph.lean` | move/split/extend | `Walk/InSimpleDiGraph/*` | imports/names | none mature beyond itself | 4/5 |
| `SimpleGraph_only/Bipartite.lean` | move | `Theory/Coloring/Bipartite.lean` | import break | Girth | 4 |
| `SimpleGraph_only/Girth.lean`, Moore files | move | `Theory/Girth.lean`, `Theory/MooreBound/*` | import break | regression umbrella | 4/6 |
| raw `Walk.toVertexList` | rename | `vertices` | yes | Hamiltonian draft | 5 |
| raw `Walk.toEdgeList` | rename | `tags` | yes | internal raw walk | 5 |
| `Walk.hasEdge`, `∈ₑ` | delete/rename | `hasTag`, tags membership | yes | no sound clients | 5 |
| `Walk.mapV`, `Walk.mapE` | rename | `mapVertices`, `mapTags` | yes | no clients | 5 |
| raw `Walk.HasSubset` | delete | no replacement until a precise relation is needed | yes | none | 5 |
| `Walk.edges`, `Walk.arcs` | preserve | actual reconstructed bundles | no | Eulerian/weights | 5 |
| `Walk.toGraph`, `Walk.toDiGraph` | preserve/update fields | same names | mechanical | generated graph tests | 1/5 |
| empty `Structures/{Trail,Path,Cycle,InGraph}` | replace | real `Walk/*` hierarchy/realization | no declarations to preserve | coverage/connectivity | 5 |
| missing `Circuit`, directed siblings, `InDiGraph` | add | new Walk modules | additive | coverage/connectivity | 5 |
| Eulerian/Hamiltonian drafts | rewrite, no aliases | `Walk/Coverage.lean`, graph-relative `G.Is...In` | yes | none mature | 5 |
| `Graph/Degree.lean` | delete then full rewrite | split Neighborhood/Finite/Degree/DegreeSum | yes; currently broken | Girth/Moore | 0/6 |
| general neighborhood excluding self | redefine | adjacency fiber including loops | semantic repair | no current general client | 6 |
| `*Finset` returning `Set` | replace | actual `Finset` declarations | yes; file broken | Degree | 6 |
| total `Set.ncard` degree | replace | finite-local natural degree | yes | Girth/Moore elaboration | 6 |
| once-counted undirected loops | correct | incidence card + loop card | semantic repair | no current general client | 6 |
| `finMaxDegree`, `avgDegree`, degree notation | delete/redefine | `maxDegree`, `averageDegree`, named API | yes | none | 6 |
| `computeVertexFinset`, `computeEdgeFinset` and lemmas | delete | none | yes | self-only | 6 |
| `fin_vertexSet_fin_edgeSet` | delete | instances and finite bridge lemmas | yes | none | 6 |
| temporary Girth `neighborSet`/`degree` | remove atomically | Graph foundation | yes | all Girth/Moore files | 6 |
| Moore's three temporary degree helpers | move | Neighborhood/Degree | import/name changes | Moore | 6 |
| Girth `infinite_*`, `finite_*` | rename | `eq_top_*`, `ne_top_*` | yes | Girth internal uses | 6 |
| connectivity placeholder | replace | four `Connectivity/*` modules | additive | Tree/SCC | 7 |
| `SimpleGraph.Contains` | delete | `IsSimpleWalkIn` | yes | Forest/Tree | 7 |
| local `SimpleGraph.IsConnected` | delete | `Preconnected`, `Connected` | yes | Tree | 7 |
| old `IsForest`, `IsTree` | rewrite/move | `Connectivity/Acyclic.lean` | yes | thin old clients | 7 |
| `Matching.edges` | rename/rewrite | `Matching.edgeSet ⊆ E(G)` | small | Matching only | 8 |
| `Matching.size` total `ncard` | require finiteness | finite cardinal API | yes | Matching only | 8 |
| absent weights/networks | add | `Weight/*` | additive | MST/flow/shortest path | 8 |
| `Graph/Graphs.lean` | delete | `Graph/Constructions.lean` | file currently broken | none | 0/9 |
| `Theory/Structures/Basic.lean` | delete | mature walk modules | file currently broken | none stable | 0 |
| existing empty `Theory/Minors/Basic.lean` draft | exclude from production imports; otherwise leave untouched in this round | none | no | root umbrella | 0 |
| fake `Theory/Basic`, `Algorithms/Basic` umbrellas | delete/replace with truthful umbrellas if retained | real umbrella modules | import change | root | 0/9 |
| duplicate Search/GraphTraversal placeholders | delete | future `Algorithms/Traversal` | no declarations | root | 0 |
| `GraphLib.lean` imports `UnionFind.Blueprint` | remove | explicit development import only | root surface | root users | 0 |
| `.DS_Store` files | delete | none | no | none | 0 |

No long-lived compatibility declaration is justified. Temporary **module forwarding imports** are useful for directory moves; aliases for semantically wrong names such as `subgraphOf`, `hasEdge`, or endpoint-image `E(G)` are not.

## 11. Implementation phases / PR-sized batches

### Phase 0 — truthful baseline and hygiene

**Files.** Delete the obsolete failing `Theory/Structures/Basic.lean`, placeholder `Graph/Graphs.lean`, and current broken `Graph/Degree.lean` (recreated in Phase 6); exclude the existing empty minor draft from production imports without otherwise touching it; remove duplicate traversal placeholders and `.DS_Store`; stop importing `UnionFind.Blueprint`; add `GraphLib/All.lean` and `GraphLibTest/ImportAll.lean`; freeze the dependency revision.

**Prerequisites.** None.

**Definitions/lemmas.** No mathematical API.

**Tests.** Independently compile every remaining production `.lean` file; `lake build GraphLib` and the import-all target; record current warnings separately.

**Exit condition.** The production import graph is truthful and green, with no known broken module hidden by an umbrella.

### Phase 1 — actual-edge core

**Files.** Rewrite `Graph/Basic.lean`; create `Graph/Incidence.lean`; rewrite `Graph/Adjacency.lean`; mechanically update constructors in Subgraph, Finite, SimpleWalk, raw Walk, and immediate clients.

**Definitions.** `tag`, `source`, `target`, actual `E(G)`, endpoint-pair images, `IsLink`, `IsArc`, `Inc`, incidence/loop Sets, actual-witness `Adj`, explicit conversions only.

**Routine lemmas.** All Basic extensionality/membership, incidence proof namespaces, adjacency symmetry/direction/membership.

**Migrations.** Remove coercions and old closure theorems; update directed endpoint proof names.

**Tests.** `Foundation/Basic.lean`; four exact `E` type checks; parallel bundles; tag reuse; no coercion; build the existing simple spine and Girth/Moore.

**Exit condition.** Public and internal general edge semantics agree everywhere; no endpoint image masquerades as `E(G)`.

### Phase 2 — subgraph order and same-carrier restriction

**Files.** Replace `Graph/Subgraph.lean`; update all `InSimpleGraph`, `InSimpleDiGraph`, and Girth `subgraphOf` clients.

**Definitions.** `IsSubgraph`/`≤`, partial order/lattice basics, `≤s`, `≤i`, `induce`, `restrictEdges`.

**Routine lemmas.** Full order, V/E, membership, monotonicity, nesting/idempotence, and relation-transport families from section 6.4.

**Migrations.** Remove `G[S]`; replace all `subgraphOf` uses without a declaration shim.

**Tests.** `Foundation/Transformations.lean` subgraph/induce/restrict examples; compile the complete Girth/Moore chain.

**Exit condition.** Same-ambient restriction is usable without casts, and all mature realization monotonicity proofs use `≤`.

### Phase 3 — deletion, mapping, relabeling, reversal, conversions

**Files.** Add `Graph/Delete.lean`, `Map.lean`, `Reverse.lean`.

**Definitions.** Every locked deletion name; safe provenance-bearing general `mapVertices`; lossy simple maps; `relabelVertices`, `relabelTags`; explicit underlying/direction conversions; directed reverse.

**Routine lemmas.** Projection, membership, relation, algebra, commutation, identity/involution, and transport-boundary theorems enumerated above.

**Tests.** Parallel delete-one/delete-between; constant-map provenance; relabel id/comp; reverse involution; loss exposed by conversions; same ambient types.

**Exit condition.** All foundational graph transformations are defined, identity-safe, and independently compilable.

### Phase 4 — mechanical relocation of the validated simple spine

**Files.** Add `Util/List.lean`; move `VertexSeq*`, `SimpleWalk`, `SimplePath`, `SimpleCycle`, `InSimpleGraph/*`, `InSimpleDiGraph`, Bipartite, Girth, and Moore to the target tree; add temporary old-path forwarding imports.

**Definitions.** No semantic redesign; declarations move under `GraphLib`. Add `SimplePath.extendTail` only if it can be isolated without disturbing the move.

**Routine lemmas.** Preserve all existing theorem bodies and definitional equality; update imports and `≤` bridge names.

**Tests.** Build every moved leaf and both Moore bounds. Compare `#check` signatures for the frozen declarations.

**Exit condition.** The full validated chain compiles at its final module paths; temporary forwarding modules are clearly marked for Phase 9 removal.

### Phase 5 — complete raw/general walks and realization

**Files.** Finalize `Walk/Walk.lean`; create `Trail`, `Path`, `Circuit`, `Cycle`, `SimpleDiCycle`, `InGraph`, `InDiGraph`; split/complete `InSimpleDiGraph`; create `Coverage`.

**Definitions.** Raw tag vocabulary; append/glue; actual reconstructed steps; direction-correct hierarchy; all four realization layers; directed simple cycles; Eulerian/Hamiltonian specification predicates.

**Routine lemmas.** Projection/operation/reverse/nodup; realization constructor/list views; generated-graph `≤`; subgraph/induce/delete/relabel transport; coverage projections.

**Migrations.** Remove old raw names/notation/subset instance; replace empty shells; rewrite Eulerian/Hamiltonian drafts.

**Tests.** `Foundation/Walk.lean`: tag reuse, undirected vs directed trail distinction, loop and parallel-edge cycles, simple cycle length conventions, generated-graph equivalence, directed reversal.

**Exit condition.** General walk/trail/path/circuit/cycle data and realization are definition-complete, with no identity-sensitive use of raw tags.

### Phase 6 — neighborhood, mathematical finiteness, degree, and counting

**Files.** Add `Neighborhood.lean`; rewrite/expand `Finite.lean`; recreate `Degree.lean`; add `DegreeSum.lean`; edit Girth/Moore imports and definitions atomically.

**Definitions.** Set/Finset families, finite-local degree, extrema, rational average degree.

**Routine lemmas.** All membership/coercion/subset bridges, loop/parallel semantics, extrema, handshake/directed sums, and moved Moore helpers.

**Migrations.** Delete `compute*Finset`; remove Girth-local definitions; move Moore helpers; rename girth top/non-top theorems.

**Tests.** `Foundation/FiniteDegree.lean`; finite-vertices/infinite-edges negative instance test; locally finite example; loop/parallel degree and handshake examples; build all Girth/Moore leaves.

**Exit condition.** No duplicate degree vocabulary remains; `*Finset` always means `Finset`; the Moore regression spine is green under finite-local degree.

### Phase 7 — reachability, components, acyclicity, tree/forest

**Files.** Add four `Connectivity/*` files and umbrella; rewrite/delete old connectivity, Forest, and Tree drafts.

**Definitions.** `Reachable`, `Preconnected`, `Connected`, component Sets, `StronglyConnected`, `IsStronglyConnected`, SCC Sets, four-type acyclicity, undirected forest/tree.

**Routine lemmas.** Reachability algebra/transports, component Set laws, reverse invariance, acyclicity monotonicity, forest/tree bridges.

**Tests.** `Foundation/Connectivity.lean`; empty convention, reachability endpoints/transitivity/symmetry/reversal, component equality/disjointness, SCC reverse, cycle conventions.

**Exit condition.** Current local/duplicate connectivity definitions are gone and the mathematical connectivity layer is usable without algorithmic enumeration.

### Phase 8 — attached data, traversal weights, networks, matching stress test

**Files.** Add `Weight/Basic.lean`, `Weight/Walk.lean`, `Weight/Network.lean`; repair `Theory/Matching/Basic.lean` to use `E(G)` and finite size semantics.

**Definitions.** Actual-carrier weights/costs/capacities; transport; walk/path sums; `Network`, `Flow`, feasibility, cuts/cut capacity.

**Routine lemmas.** `EqOn` extensionality, transport laws, append/reverse weights, incidence sums, zero flow, cut membership.

**Tests.** `Foundation/WeightNetwork.lean`; same-tag edges with different weights, reverse/relabel transport, actual-arc capacity/flow, loops/parallel flow contributions.

**Exit condition.** All attached data is identity-correct and no weighted graph type or tag-keyed general data has appeared.

### Phase 9 — selected constructors, final umbrellas, and cleanup

**Files.** Add `Graph/Constructions.lean`; finalize `Graph.lean`, `Walk.lean`, `Connectivity.lean`, `Weight.lean`, `All.lean`, root `GraphLib.lean`, test library/targets; remove forwarding modules and stale empty umbrellas.

**Definitions/lemmas.** Small constructor set and full simp API only.

**Tests.** Build root, All, every test module, Girth/Moore, and important leaves. Run naming/scope searches from section 12.

**Exit condition.** A fresh implementation agent can import the complete stable foundation from truthful umbrellas; every production file compiles without `sorry`; all forbidden names/scopes are absent.

## 12. Regression and acceptance tests

### 12.1 Compile-time type tests

```lean
open scoped GraphLib

variable
  (Gu : Graph α β) (Gs : SimpleGraph α)
  (Gd : DiGraph α β) (Gsd : SimpleDiGraph α)

#check (E(Gu)  : Set (Edge α β))
#check (E(Gs)  : Set (Sym2 α))
#check (E(Gd)  : Set (Arc α β))
#check (E(Gsd) : Set (α × α))

#check (Gu.edgeEndpointPairSet : Set (Sym2 α))
#check (Gd.arcEndpointPairSet : Set (α × α))

#check Gu.IsLink
#check Gd.IsArc
#check Gu.Inc
#check Gd.Inc
#check Gu.Adj
#check Gd.Adj

#check (Gu.induce S : Graph α β)
#check (Gu.restrictEdges F : Graph α β)
#check (Gu.deleteEdges F : Graph α β)
#check (Gu.deleteVerts S : Graph α β)
#check (Gd.reverse : DiGraph α β)

#check (Gu.mapVertices f : Graph γ (Edge α β))
#check (Gd.mapVertices f : DiGraph γ (Arc α β))
#check (Gu.relabelVertices σ : Graph γ β)
#check (Gd.relabelVertices σ : DiGraph γ β)
#check (Gu.relabelTags τ : Graph α δ)

#check (Gu.edgeFinset : Finset (Edge α β))
#check (Gd.edgeFinset : Finset (Arc α β))
#check (Gu.incidenceFinset v : Finset (Edge α β))
```

Negative compile/guard tests confirm there is no simple/general `Coe`, no `Edge.endpointsLabel`, no raw `∈ₑ`, and no general weight/capacity inferred as `β → W`.

### 12.2 Semantic fixture tests

Use implemented constructors or literal small graphs to prove:

1. **Parallel identity:** two different tags at common endpoints are two elements of `E(G)`; deleting one retains the other.
2. **Tag reuse:** the same tag at different endpoints gives different actual values and can receive different weights.
3. **Noninjective map:** two distinct source edges remain distinct after a constant `mapVertices`; the target tag projects to the full source edge.
4. **Endpoint-wide deletion:** `deleteEdgesBetween`/`deleteArcsFromTo` removes all matching parallel values.
5. **Loop semantics:** one undirected loop contributes two to degree; two loops contribute four; a directed loop contributes one to each directed degree.
6. **Neighborhood semantics:** a loop puts its vertex in `neighborSet`, while parallel edges do not change neighborhood cardinality.
7. **Finite separation:** a finite vertex set with infinitely many tagged bundled edges does not synthesize `Finite E(G)`; local finite degree remains expressible in a globally infinite graph.
8. **Degree sums:** handshake and directed in/out sums hold on loops and parallel edges.
9. **Trail direction:** an immediate reverse traversal with one tag repeats an undirected full edge but can be two distinct directed full arcs.
10. **Cycle conventions:** a general loop is a length-one cycle; two parallel undirected edges form a length-two cycle; `SimpleCycle` still requires three; `SimpleDiCycle` admits two.
11. **Realization:** `G.IsWalkIn w ↔ w.toGraph ≤ G` and the directed analogue; realization checks actual lists, not tags.
12. **Directed reverse:** realized directed walks land in `G.reverse`, and `reverse_reverse` returns the source graph/walk.
13. **Connectivity:** reflexivity requires membership; undirected reachability is symmetric; SCCs are reverse-invariant; empty is preconnected but not connected.
14. **Attached data:** reverse/relabel transport is explicit; same-carrier deletion/induce reuses data; network capacity and flow range over full arcs.
15. **Conversions:** `underlyingSimple` drops loops/merges parallels, simple `forgetDirection` merges antiparallel arcs, and no loss is implicit.

### 12.3 Build targets

At every phase exit, build the touched leaves plus:

```text
lake build GraphLib
lake build GraphLib.All
lake build GraphLibTest.ImportAll
lake build GraphLib.Walk.InSimpleGraph
lake build GraphLib.Walk.InSimpleDiGraph
lake build GraphLib.Theory.Girth
lake build GraphLib.Theory.MooreBound
```

Final CI also compiles every source module directly. Stable production modules reject `sorry`.

### 12.4 Naming and scope checks

CI/lint searches reject public occurrences of:

```text
endpointsLabel
subgraphOf
computeVertexFinset / computeEdgeFinset
FiniteAdjView / FiniteEdgeView / FiniteVertexView
finMaxDegree / avgDegree
mapV / mapE / hasEdge / ∈ₑ
G[S]
old Theory.Structures and SimpleGraph_only imports
Contraction.lean / contractSet / contractEdge
```

Also check mechanically that every public terminal `*Set` result is `Set`, every public terminal `*Finset` result is `Finset`, directed public endpoint names use source/target, and every new public definition has a mathematical docstring.

## 13. Deferred and out-of-scope items

### MAY DEFER

- executable adjacency/incidence/edge enumerations and concrete adjacency-list/array/hash representations;
- `TagInjective` and tag-keyed convenience APIs under an explicit hypothesis;
- extended infinite degree, regularity, advanced degree inequalities, weighted handshake, and density theory;
- component quotient carriers, condensation, connected induced-component theory, Menger/cut/block theory;
- unique-path tree theorems, spanning-tree existence, topological sorting, and feedback-set theory;
- cycle quotients/decomposition and deep Eulerian/Hamiltonian theory;
- residual networks, weak duality, max-flow/min-cut, min-cost flow, and all algorithms;
- full path/cycle/star/bipartite/named graph constructor catalog;
- a public morphism or `GraphLike` hierarchy;
- Mathlib adapters until a theorem client exists;
- repeated provenance normalization for arbitrary maps;
- `VertexSplit`, until the flow client needs a concrete reduction interface.

### OUT OF SCOPE

- every contraction-related Lean file or declaration, including `Contract`, `contractSet`, `contractEdge`, contraction algebra, minors, and contraction-specific path/weight transport;
- a contraction implementation phase or deliverable;
- `FiniteAdjView`, `FiniteEdgeView`, `FiniteVertexView`, `compute*Finset`, or the same speculative executable abstraction under another name;
- weighted/capacitated graph types;
- unrestricted general edge weights, costs, capacities, matching sets, MST sets, or flows keyed only by `β`;
- implicit lossy coercions;
- half-edge/dart/incidence-identity infrastructure without a client.

Future contraction is mentioned only as a compatibility stress test for safe noninjective `mapVertices`; it does not block or enlarge this construction round.

## 14. Final implementation checklist

1. Freeze the Lean/Mathlib dependency state and establish truthful root/import-all builds.
2. Remove obsolete failing drafts/placeholders; keep unrelated user work untouched.
3. Rename `tag`, add `source`/`target`, repair actual `E(G)`, and add explicit endpoint images.
4. Implement `IsLink`, `IsArc`, `Inc`, actual incidence/loop Sets, and actual-witness `Adj` for all four types.
5. Remove implicit simple/general coercions and verify the exact four edge-carrier types.
6. Install `H ≤ G`, `≤s`, `≤i`, lattice basics, `induce`, and `restrictEdges`; migrate all `subgraphOf` clients and remove `G[S]`.
7. Implement the complete deletion family and its membership/algebra API.
8. Implement safe provenance-bearing general `mapVertices`, lossy simple maps, vertex/tag relabeling, explicit conversions, and directed reverse.
9. Move the validated `VertexSeq → SimpleCycle → InSimpleGraph` spine with definitional equality preserved; rebuild Girth/Moore.
10. Rename raw walk tag APIs, preserve reconstructed `edges`/`arcs` and generated graphs, and add append/glue.
11. Implement `Trail`/`DiTrail`, shared `Path`, `Circuit`/`DiCircuit`, and `Cycle`/`DiCycle` with the fixed loop/parallel conventions.
12. Complete simple-directed, general-undirected, and general-directed realization and rewrite coverage predicates to include realization.
13. Add neighborhood Sets, expand mathematical finsets to all four types, and keep general vertex/edge finiteness independent.
14. Rebuild finite-local degree, extrema, degree sums, and rational average degree with correct loop semantics.
15. Atomically remove Girth/Moore duplicate degree vocabulary, move their helper lemmas, apply locked theorem renames, and rebuild both Moore bounds.
16. Implement reachability, connectedness, strong connectedness, component Sets, acyclicity, forest, and tree definitions plus routine API.
17. Add actual-carrier weights/costs/capacities, traversal sums, network/flow/cut specifications, and repair Matching as an identity stress client.
18. Add only the selected implemented constructors and their V/E/Adj/link/arc simp API.
19. Finalize true Graph/Walk/Connectivity/Weight/All umbrellas; remove temporary forwarding modules and development blueprint imports.
20. Run all build, semantic, negative-name, suffix-discipline, no-`sorry`, and no-contraction checks.

### Final sanity result

Every foundational concept requested in this round has a concrete carrier or operation and a routine theorem family above. All identity-sensitive general APIs use full `Edge`/`Arc` values. No tag-only weight/capacity, speculative executable view, contraction deliverable, implicit lossy conversion, or obvious dependency cycle remains. The only substantial remaining freedom for the implementation agent is Lean proof engineering and local private helper choice.
