# GraphLib general edge representation decision memo

**Date:** 2026-08-14  
**Scope:** general undirected `Graph` and directed `DiGraph` only  
**Decision:** preserve bundled `Edge` / `Arc`, repair the public actual-edge API, and localize
identity preservation for noninjective transformations  
**Supersedes:** the representation decision in §4.2 of
`2026-08-14_GRAPHLIB_ARCHITECTURE_PROPOSAL.md`; it does not supersede that report's unrelated
directory, simple-graph, or algorithm-layer recommendations

## Executive decision

GraphLib should **not** replace its bundled general edges with a separate abstract edge type and
`IsLink` / `IsArc` as the stored representation during the current construction phase.

The current representation already has a mathematically valid actual edge identity:

```lean
Edge α β = β × Sym2 α       -- schematically
Arc  α β = β × (α × α)
```

Identity is the **whole bundled value**, not `β` alone. This gives direct endpoint projections,
cast-free induced subgraphs, simple dynamic insertion/deletion, and a graph-independent walk
format in which a tag together with adjacent vertices determines the traversed bundled edge.

The current code nevertheless has a serious public API defect: `E(G)` is the image of the
endpoint projection. It therefore collapses parallel edges even though `G.edgeSet` does not.
That defect must be fixed independently of the representation decision:

```lean
-- Required semantics
E(G) = G.edgeSet : Set (Edge α β)       -- general undirected
E(G) = G.edgeSet : Set (Arc α β)        -- general directed
```

Endpoint-pair images should receive explicit derived names such as `G.edgeEnds` and
`G.arcEnds`.

The strongest argument for a separate identity type is real: it lets an arbitrary noninjective
vertex map preserve `ε`, weights, capacities, and walk edge values literally. The compiled
experiments show, however, that the only correctness failure in the bundle is a naive map that
keeps a repeated tag while collapsing endpoints. A transformation can prevent that locally by
using the complete source edge as provenance in the output tag. This is enough for the future
contraction stress test without implementing contraction or changing every ordinary graph now.

The conclusion is therefore:

- **`LOCKED`:** retain `Graph.edgeSet : Set (Edge α β)` and
  `DiGraph.edgeSet : Set (Arc α β)`.
- **`LOCKED`:** the full bundle is actual edge identity; `β` is a tag/discriminator and has no
  implicit global uniqueness property.
- **`LOCKED`:** make `E(G)` expose actual bundled values, not endpoint images.
- **`LOCKED`:** identity-sensitive weights, capacities, costs, deletion, trails, MSTs, and flows
  range over actual bundled values.
- **`PROVISIONAL`:** arbitrary noninjective vertex transformations return an explicit edge
  correspondence and use origin-preserving output tags. Exact production types and composition
  laws should be chosen with the first real client.
- **`DEFERRED`:** contraction itself, normalization of repeated provenance, and any later
  migration to a separate abstract identity type.

This recommendation deliberately prefers the existing design where the candidates are
comparable. The abstract-identity design should be reconsidered only if transport escapes the
transformation boundary in multiple real clients, not merely because it gives a prettier future
contraction signature.

## 1. Current-state diagnosis

### 1.1 What is an edge today?

`GraphLib/Graph/Basic.lean` defines:

```lean
structure Edge (α β : Type*) where
  endpointsLabel : β
  endpoints : Sym2 α

structure Arc (α β : Type*) where
  endpointsLabel : β
  endpoints : α × α
```

Structure equality makes the full pair `(endpointsLabel, endpoints)` the identity. Consequently:

- two parallel edges at the same endpoints are distinct exactly when their tags differ;
- the same tag may legally be reused at different endpoints;
- two records with the same tag and endpoints are one edge, as expected for a set carrier;
- no global or endpoint-fibre uniqueness invariant on `endpointsLabel` exists;
- `β → W` is not an unrestricted per-edge weight type;
- `Edge α β → W` and `Arc α β → W` are unrestricted per-edge data types.

This is coherent. A tag is part of identity, but is not identity by itself. If a client wants two
parallel edges with the same semantic label, it can use a tag such as `edgeKey × label` or keep
the semantic label in an external function on actual edges.

### 1.2 The proven `E(G)` defect

The general-graph `HasEdgeSet` instances currently return:

```lean
Edge.endpoints '' G.edgeSet
Arc.endpoints '' G.edgeSet
```

Thus `E(G)` has type `Set (Sym2 α)` or `Set (α × α)`, not the actual bundled carrier. Two
parallel edges become one endpoint pair.

This is already causing an API split:

- `Graph.subgraphOf` and `DiGraph.subgraphOf` deliberately compare `G.edgeSet`, because endpoint
  images would be wrong for parallel edges;
- incidence-set and degree code uses actual bundled records;
- `Matching` stores `Set (Edge α β)`;
- `Walk.IsEulerian` compares reconstructed bundled records with `G.edgeSet`;
- public general adjacency and incidence go through the lossy endpoint image.

The notation is therefore not merely inconvenient. It gives different meanings to “edge set”
in public and identity-sensitive code. Fixing it is mandatory whichever representation is
selected.

### 1.3 Proven bundle ergonomics

The local implementation demonstrates several low-friction properties:

- `Graph.induce` and `DiGraph.induce` retain ambient `α` and `β`, filter actual records by
  `e.endpoints`, and discharge incidence with ordinary set membership. No vertex or edge
  subtypes and no equality casts appear.
- Subgraph is literal inclusion of vertex and actual-edge sets. A shared bundled edge cannot be
  silently rewired in a subgraph because its endpoints are part of the shared value.
- Neighbor, incidence, matching, and future flow-conservation code can project endpoints
  directly.
- A raw `Walk α β` contains a tag at each step and adjacent vertices. It can reconstruct an
  actual `Edge α β` or `Arc α β` for every occurrence without consulting a graph.
- The current `Walk.toGraph` is always structurally meaningful even if the same tag is used at
  different endpoint pairs, because the resulting full bundled edges remain distinct.

These are real proof-engineering wins. They are not obtained from endpoint-image `E(G)` and do
not depend on retaining that bug.

### 1.4 Real pain and missing evidence

There is one genuine bundle-specific failure. Given legal distinct edges

```lean
e₁ = ⟨tag, s(a, b)⟩
e₂ = ⟨tag, s(c, d)⟩,
```

a noninjective `f` may make both endpoint images equal. The naive map

```lean
e ↦ ⟨e.endpointsLabel, e.endpoints.map f⟩
```

then collapses `e₁` and `e₂` in a set image. Unequal weights could be merged with no proof
obligation. An arbitrary noninjective edge-tag map has the analogous problem.

There is not yet evidence that this local failure is pervasive:

- general vertex-map, relabel, reverse, deletion, weight, and capacity APIs do not yet exist;
- general realized walks are not implemented;
- the MST and flow files are placeholders;
- current mature downstream proofs overwhelmingly use the simple-graph chain.

The repository therefore validates direct endpoint use and the `E(G)` bug, but it does not
contain mature MST or flow clients showing that bundle transport has become systemic.

## 2. Candidate representations

### 2.1 Candidate A: current representation unchanged

```lean
edgeSet : Set (Edge α β)
E(G)    : Set (Sym2 α)       -- endpoint image
```

This candidate is rejected. The internal carrier preserves parallel edges while the public edge
set erases them. It cannot state deletion of one parallel edge, an MST edge subset, or a
per-actual-edge capacity using the standard notation.

### 2.2 Candidate B: repaired bundles — recommended

Keep the structure fields and change the public views:

```lean
edgeSet : Set (Edge α β)
E(G)    : Set (Edge α β)

def Graph.IsLink (G : Graph α β) (e : Edge α β) (u v : α) : Prop :=
  e ∈ E(G) ∧ e.endpoints = s(u, v)

def Graph.edgeEnds (G : Graph α β) : Set (Sym2 α) :=
  Edge.endpoints '' E(G)
```

The directed definitions are analogous with `Arc` and `IsArc`. `IsLink` / `IsArc` become useful
derived vocabulary and interoperability views; they need not be the stored representation.
Endpoint uniqueness follows definitionally from the record field, so constructors do not gain a
functionality proof.

Identity-sensitive APIs use the whole record. No label uniqueness invariant is added. An
optional predicate may later describe clients whose tags happen to be injective:

```lean
def Graph.LabelInjective (G : Graph α β) : Prop :=
  Set.InjOn Edge.endpointsLabel E(G)
```

It must not be an invariant of every graph.

### 2.3 Candidate C: separate identity plus `IsLink` / `IsArc`

```lean
structure Graph (α ε : Type*) where
  vertexSet : Set α
  edgeSet   : Set ε
  IsLink    : ε → α → α → Prop
  -- symmetry, endpoint uniqueness, edge existence, and incidence axioms
```

This design makes `ε` actual identity independently of endpoints. It is the cleanest candidate
for arbitrary vertex maps: `edgeSet` and `ε → W` can remain definitionally unchanged while only
incidence is mapped. Parallel edges and loops are native, and delete-one-edge is set difference
on `ε`.

Its costs are also structural:

- an enumerated `e : ε` does not project its endpoints;
- obtaining endpoints may require witnesses or choice;
- every constructor proves symmetry/functionality/membership coherence;
- subgraph cannot mean only set inclusion, because the same `ε` could be rewired;
- union and insertion require freshness or endpoint compatibility;
- a raw walk may reuse one `ε` at inconsistent endpoint pairs and then cannot generate a valid
  graph without occurrence identities;
- the identity-sensitive directed version is not a shipped Mathlib API and would be GraphLib's
  own extrapolation.

The design is mathematically sound and remains the main future alternative. The current evidence
does not show that its global benefits outweigh those proof obligations and migration cost.

### 2.4 Candidate D: separate identity plus endpoint functions

The Isabelle-style hybrid stores:

```lean
edgeSet : Set ε
ends    : ε → Sym2 α
-- or source, target : ε → α
```

It combines stable identity with direct endpoint projection. For TCS algorithms this may be more
ergonomic than a purely relational core. Its total endpoint functions have meaningless values
outside `edgeSet`, complicating ordinary structure equality and extensionality. Restricting the
functions to the edge subtype instead introduces dependent values and casts. Independent graphs
using the same `ε` may also disagree about an edge's endpoints, so compatibility is still needed.

This is important survey evidence: even if GraphLib later separates identity, `IsLink` / `IsArc`
is not the only serious design. It is not a minimal change now.

### 2.5 Rejected minimal variant: globally unique bundle tags

Adding `Set.InjOn Edge.endpointsLabel G.edgeSet` to every graph would prevent the naive
same-tag collision and make `β` usable as identity. It is rejected because it:

- imposes freshness obligations on every insertion and dynamic update;
- adds disjointness/compatibility obligations to union;
- forbids legal tag reuse at different endpoints;
- conflicts with the current raw-walk construction when one tag occurs at different endpoint
  pairs;
- makes the bundle semantically redundant while retaining its transport costs.

Clients that deliberately use globally unique keys can opt into a predicate or wrapper later.

## 3. Survey findings

### 3.1 Pinned and current Mathlib

The repository pins Mathlib commit
[`d802ffd29d`](https://github.com/leanprover-community/mathlib4/commit/d802ffd29db1f5dc5a29206b1a8af62bfcc234a3)
from 2026-05-13 and Lean `v4.30.0-rc2`. The upstream snapshot available during this audit was
[`ac47869476`](https://github.com/leanprover-community/mathlib4/commit/ac47869476d367300219cbbb258ca07760b89821)
from 2026-08-11. The relevant representation is materially unchanged between them.

Mathlib's shipped undirected
[`Graph α β`](https://github.com/leanprover-community/mathlib4/blob/d802ffd29db1f5dc5a29206b1a8af62bfcc234a3/Mathlib/Combinatorics/Graph/Basic.lean#L91-L106)
uses `β` as actual edge identity and `IsLink` as graph-relative incidence. Its strongest evidence
for GraphLib is not authority but demonstrated properties:

- [`Graph.map`](https://github.com/leanprover-community/mathlib4/blob/d802ffd29db1f5dc5a29206b1a8af62bfcc234a3/Mathlib/Combinatorics/Graph/Maps.lean#L37-L57)
  keeps `E(G)` literally while a noninjective vertex map changes incidence and may create loops;
- [`deleteEdges` and `induce`](https://github.com/leanprover-community/mathlib4/blob/d802ffd29db1f5dc5a29206b1a8af62bfcc234a3/Mathlib/Combinatorics/Graph/Delete.lean#L99-L163)
  delete identities and retain ambient types;
- [subgraphs](https://github.com/leanprover-community/mathlib4/blob/d802ffd29db1f5dc5a29206b1a8af62bfcc234a3/Mathlib/Combinatorics/Graph/Subgraph.lean#L14-L34)
  are ordinary `Graph α β` values rather than dependent subtypes;
- endpoint recovery such as `Graph.Inc.other` uses choice, illustrating the cost of relational
  incidence for direct algorithmic endpoint access.

This is meaningful support for stable edge identity under maps. It does not establish that
GraphLib must store incidence relationally. In particular:

- Mathlib's shipped [`Digraph`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Digraph/Basic.html)
  is a vertex relation with no explicit arc identities or parallel arcs;
- neither the pin nor the audited current snapshot has a merged general-graph walk, contraction,
  minor, or complete morphism/edge-relabel API;
- Mathlib's general multigraph API is young: core, map, and deletion work landed in 2025–2026.

The current `Graph.Simple` bridge is merged, but that does not settle directed identity graphs or
walk carriers.

### 3.2 Experimental Mathlib proposals

As of the audit date, the following were open proposals rather than upstream APIs GraphLib can
rely on:

- dart-first graph-like infrastructure and dependent darts
  ([#36743](https://github.com/leanprover-community/mathlib4/pull/36743));
- its unified-walk follow-up
  ([#36756](https://github.com/leanprover-community/mathlib4/pull/36756));
- an incidence-first `HypergraphLike` / `GraphLike` alternative with generic walks
  ([#40204](https://github.com/leanprover-community/mathlib4/pull/40204)).

The incidence-first PR explicitly presents itself as an alternative to the dart-first proposal.
Their coexistence is evidence that generic graph walks and incidence abstraction remain a live
design space. GraphLib should not make a breaking change or create a large public typeclass
hierarchy in anticipation of one proposal winning.

### 3.3 Isabelle AFP

The mature [Isabelle AFP Graph Theory entry](https://devel.isa-afp.org/entries/Graph_Theory.html)
supports labelled multiedges, infinite graphs, arc walks, weighted graphs, deletion, shortest
paths, and Euler trails. Its
[`pre_digraph`](https://devel.isa-afp.org/browser_info/current/AFP/Munta_Certificate_Checker/Graph_Theory.Digraph.html)
has sets of abstract arc identities and total `tail` / `head` functions.

This is useful evidence that stable abstract identities can serve TCS clients, but it points to
the functional hybrid, not uniquely to Mathlib's relation. It also relies on a locale discipline
around well-formedness and values outside the active arc set. The lesson is to keep identity
semantics explicit and endpoint access ergonomic, not to copy a representation uncritically.

## 4. Empirical Lean tests

The isolated compiled experiments are in:

- `Prototypes/RepresentationStress.lean`;
- `Prototypes/RepresentationStressResults.md`.

They do not modify `GraphLib/`.

Validation succeeded:

```text
lake build Mathlib.Combinatorics.Graph.Delete Mathlib.Combinatorics.Graph.Maps
# success

lake env lean Prototypes/RepresentationStress.lean
# exit 0, no warnings or errors

lake build GraphLib
# success; existing unrelated linter and `sorry` warnings remain
```

### 4.1 Results by required scenario

| Required test | Repaired/current bundle evidence | Separate-identity evidence | Observed friction |
|---|---|---|---|
| Two parallel edges; delete one | Two `Edge Nat Bool` records at the same ends differ by tag; erasing one preserves the other | Pinned Mathlib `Graph.banana` uses two `Bool` identities; `deleteEdges {false}` preserves `true` | Current `E(G)` still reports the common endpoint pair after deletion, proving the notation bug |
| Noninjective endpoint map | Same-tag edges with different source ends become equal under a constant naive map | `Graph.map` / the directed sketch retain `ε = Bool` while endpoint pairs coincide | Real collision for naive bundles; no collision for abstract IDs |
| Weight/capacity transport | An arbitrary arc weight transports through a vertex equivalence by inverse endpoint relabeling; an origin-tagged noninjective map transports it by projection with `rfl` | `capacity : ε → Nat` is literally unchanged | Bundle needs an explicit correspondence; relation is definitionally strongest |
| Reverse digraph and realized walk | `Arc.reverse` plus `Walk.mapE Arc.reverse` and `Walk.reverse`; proof needed an explicit `change` to expose one-step normal form | Reverse swaps source/target while walk IDs stay fixed; only `Walk.reverse` is needed | Bundle has one explicit edge-map step |
| Residual arcs | `forward` / `reverse` role tags distinguish original, reverse residual, antiparallel original, and loops | The same role tagging is required on abstract `ε` | Representation alone never supplies residual polarity |
| Induced subgraph | Existing `DiGraph.induce` keeps exact `Arc α β`, ambient `α`, and has no casts | Sketch keeps exact `ε` and ambient `α`, also with no casts | No-cast win comes from embedded sets, not identity storage |
| Edge-aware walk | Walk instantiated with exact bundled arcs and realized by membership plus endpoint equality | `Walk α ε` realized through `G.IsArc` | Direct bundle endpoint test versus graph-relative incidence lookup |

### 4.2 The localized noninjective-map repair

The key stress-test prototype is:

```lean
def mapArcKeepOrigin (f : α → γ) (e : Arc α β) : Arc γ (Arc α β) :=
  ⟨e, (f e.endpoints.1, f e.endpoints.2)⟩
```

It has an unconditional one-line injectivity proof because the complete source arc is the new
tag. Even if every vertex maps to one point, two source arcs remain distinct. For arbitrary
`w : Arc α β → W`:

```lean
def transportWeight (w : Arc α β → W) (e : Arc γ (Arc α β)) : W :=
  w e.endpointsLabel

transportWeight w (mapArcKeepOrigin f e) = w e    -- rfl
```

Thus future contraction can preserve identity and data at the transformation boundary. The
prototype also exposes the real cost rather than concealing it: naive repetition yields a nested
type such as `Arc δ (Arc γ (Arc α β))`. A production API will need a named provenance record,
an origin projection, and composition/flattening laws if repeated maps become common.

### 4.3 What the prototypes do and do not prove

They prove that:

- the `E(G)` bug is independent of storage;
- the naive noninjective bundle map is unsafe;
- origin tagging prevents the collision and transports arbitrary edge data cleanly;
- both serious designs support delete-one-edge, residual tags, no-cast induction, and realized
  walks;
- separate identity is materially cleaner for arbitrary vertex maps and directed reversal.

They do not prove that origin-tagged composition will remain pleasant for a large contraction
theory. That question remains deferred until a real client exists.

## 5. Client-by-client stress analysis

### 5.1 Parallel edges, loops, and deletion

Under the recommendation, `e₁ ≠ e₂` means the bundled values differ. At common endpoints this
requires different tags. Multiple loops are handled the same way.

`G.deleteEdge e` removes one actual record. An endpoint-oriented operation must have a different
name, such as `deleteEdgesBetween u v`, because it may delete every parallel edge with those
ends. `E(G)` must support the first statement; `G.edgeEnds` supports the second view.

### 5.2 Weights, costs, capacities, and MST

Unrestricted data should be total functions on the actual carrier, with equality relevant only
on active edges:

```lean
Graph.EdgeWeight G W   := Edge α β → W
DiGraph.Capacity G R   := Arc α β → R
```

The graph argument may initially be namespace/documentation context rather than a bundled
dependent object. Extensionality uses `Set.EqOn` on `E(G)`.

Induce, restrict, and delete keep the same actual-edge type, so a weight is reused without casts.
A vertex equivalence induces an explicit edge equivalence; weight transport composes with its
inverse. Directed reverse uses the involution on `Arc α β`. These are localized, named
transports—not Lean equality casts.

An MST is a set of actual bundled edges. Kruskal-style clients benefit from projecting endpoints
directly. No `β → W` API should be called general unless accompanied by `LabelInjective` or an
equivalent client invariant.

### 5.3 Vertex and edge relabeling

The API must distinguish three operations:

1. `relabelVertices (f : α ≃ γ)` maps bundled endpoints injectively. It cannot merge actual
   edges and should return an explicit `Edge` / `Arc` equivalence for data transport.
2. `relabelTags (g : β ≃ δ)` is likewise collision-free and returns an actual-edge equivalence.
3. An arbitrary `mapVertices (f : α → γ)` or noninjective tag map is not a relabeling. It must
   preserve provenance, require injectivity on the active edge set, or explicitly advertise that
   it quotients/merges edges.

Using “relabel” for a noninjective operation would hide the central identity question.

### 5.4 Directed reversal and realized walks

Define `Arc.reverse` as the involution swapping the ordered endpoints and define
`DiGraph.reverse` as its image on the actual edge set. It is injective regardless of tag reuse,
so ordinary reversal cannot cause edge collision.

For the current tag-interleaved raw walk, reversing a realized directed walk keeps the step tags
but reverses the vertex order; its reconstructed actual arcs are the reversed records. For a
walk instantiated with exact bundled arcs, map each arc through `Arc.reverse` and reverse the
sequence. In either presentation the required theorem is:

```lean
h : G.IsWalkIn w
--------------------------------
h.reverse : G.reverse.IsWalkIn w.reverseDirected
```

It must not claim that a directed walk reverses in the same graph.

The naming plan must also distinguish the raw tag list from reconstructed actual edge/arc lists.
Trail and Eulerian predicates use the latter. Repeated tags at different endpoints do not by
themselves repeat an actual bundled edge.

### 5.5 Residual networks

Graph reversal is not residual construction. If the original network has `e : u → v` and an
antiparallel `f : v → u`, the residual graph may contain all of:

```text
forward e, backward f : u → v
backward e, forward f : v → u
```

All four need distinct identities. A loop's forward and backward residual roles may also need to
remain distinct. Every representation therefore needs an identity such as:

```lean
inductive ResidualId (κ : Type*)
  | forward  : κ → ResidualId κ
  | backward : κ → ResidualId κ
```

For repaired bundles, `κ` is the full original `Arc α β`, not `β`. The residual graph can then
use bundled arcs whose tag records origin and polarity. Capacities and costs derive by pattern
matching on that tag. This fully handles original, reverse residual, antiparallel, and loop
coexistence without a core representation change.

### 5.6 Induced subgraphs, restrictions, and dynamic updates

Keep all these operations in ambient types. The repaired bundle retains the current definitional
endpoint win:

- `induce S` filters actual records by endpoints in `S`;
- `restrictEdges F` intersects with `F : Set (Edge α β)` or `Set (Arc α β)`;
- `deleteEdges F` takes set difference;
- inserting `e` only requires proving its endpoints are in the new vertex set.

With full-record identity, changing an edge's endpoints changes the edge. A dynamic “rewire” is
therefore delete plus insert and should return an old/new correspondence if data must move. This
is explicit and avoids pretending that a reused tag alone fixes identity.

### 5.7 Future contraction and arbitrary vertex identification

Contraction remains out of scope. As a representation stress test, it should preserve each
source actual edge as origin and map only endpoints. Schematically:

```lean
G.contractSet S : Graph (Contract α S) (Edge α β)
```

with a mapped edge tagged by its entire source edge. Distinct source edges cannot collide,
weights pull back through the origin projection, and loops created by the contraction remain
available for whichever later API decides whether to retain or remove them.

The exact carrier, return record, and laws are **`PROVISIONAL`**. A useful result will likely
package:

- the target graph;
- an injective source-edge map;
- an origin projection on target edges;
- endpoint characterization;
- weight/capacity transport;
- composition/flattening support.

If repeated contractions, vertex maps, and relabelings make origin types and transports dominate
two or more real clients, that is the trigger to reopen the separate-identity decision.

## 6. Comparison table

| Criterion | Current unchanged | Repaired bundles | Abstract `ε` + relation | Abstract `ε` + endpoint functions |
|---|---|---|---|---|
| Mathematical edge identity | Internally full record; public `E` contradicts it | Full record, consistently public | `ε` | `ε` |
| Parallel edges / loops | Stored correctly, exposed incorrectly | Correct | Correct | Correct |
| Direct endpoint access | Definitional | Definitional | Witness/choice or added view | Definitional |
| Label uniqueness needed | No, but API is ambiguous | No | Not applicable | Not applicable |
| Delete one parallel edge | Only via private field semantics | Direct on `E(G)` | Direct on `ε` | Direct on `ε` |
| Induce/restrict casts | None | None | None if ambient sets retained | None with total functions |
| Vertex equivalence | Edge values transported | Explicit edge equivalence | Same `ε` | Same `ε` |
| Noninjective vertex map | Can silently collide | Origin tag/correspondence | Same `ε`, strongest | Same `ε`, strongest |
| Reverse graph | Arc values swap | Involutive explicit transport | Same `ε` | Same `ε` |
| Arbitrary edge data | Full records, but hidden by `E` | Full records | `ε` | `ε` |
| Raw walk consistency | Reconstructed full records | Reconstructed full records | Reused ID can have inconsistent steps | Reused ID checked against functions |
| Dynamic insertion / union | Low constructor friction | Low constructor friction | Freshness/incidence compatibility | Freshness/function compatibility |
| MST / flow endpoint use | Direct but public identity broken | Direct and identity-correct | Incidence witness/view | Direct |
| Residual identity | Requires role tag | Requires role tag | Requires role tag | Requires role tag |
| Mathlib interoperability | Misaligned public edge set | Straightforward adapter | Closest for undirected `Graph` | Adapter |
| Migration cost | None but unacceptable | Low | High | High |
| Premature-abstraction risk | N/A | Low | High | Medium–high |

The abstract designs win the arbitrary-map row decisively. The repaired bundle wins direct
endpoints, construction, compatibility, migration, and current-walk consistency. Most other
rows are ties once `E(G)` is repaired and residual/origin tags are explicit.

## 7. Concrete failure modes

### 7.1 Current representation unchanged

1. `E(G)` folds parallel edges into one endpoint pair.
2. Delete-one-edge, edge count, MST, and capacity statements split between notation and fields.
3. Naive noninjective maps can merge legal same-tag edges.
4. A `β → W` API silently treats a nonunique tag as identity.
5. Raw walk tag lists can be mistaken for actual edge lists.

This candidate is not acceptable.

### 7.2 Repaired bundles

1. Actual identity depends on the vertex type, so vertex relabeling requires an explicit edge
   equivalence and weight transport.
2. Directed reverse changes the actual arc value, so capacities/costs transport through an
   involution rather than remaining literal.
3. Noninjective maps need provenance or an injectivity proof.
4. Naive repeated origin tagging nests types and can expose old vertex types in the target edge
   carrier.
5. Tags cannot serve as general edge keys without an optional uniqueness hypothesis.
6. Endpoint mutation is identity mutation.

These are real costs, but the experiments keep them at transformation boundaries.

### 7.3 Abstract identity plus relations

1. Endpoint projection is no longer definitional; algorithmic clients repeatedly unpack
   incidence witnesses or depend on an executable view.
2. Constructors and extensionality carry symmetry, functionality, and edge-membership coherence.
3. Edge-set inclusion alone is an unsound subgraph relation because a shared identity can be
   rewired.
4. Union, insertion, and graph combination require compatibility/freshness.
5. A raw walk can assign one identity incompatible endpoints; a generated graph needs occurrence
   identities or an ambient realization proof.
6. Stable abstract IDs still do not distinguish residual direction automatically.
7. The directed design and general walk interoperation have no matching shipped Mathlib API.

### 7.4 Abstract identity plus endpoint functions

1. Endpoint values outside `E(G)` are junk but affect ordinary structure equality.
2. `EqOn` extensionality and graph-combination compatibility are required.
3. Edge-subtype functions avoid junk only by introducing dependency and casts.
4. It is still a full migration and is not the representation Mathlib currently exposes.

## 8. Minimal required GraphLib changes

No `Graph`, `DiGraph`, `Edge`, or `Arc` structure field needs to change for the recommended
decision. The minimal foundation repair is:

1. **Change general `HasEdgeSet` instances.** Return `G.edgeSet` with actual types
   `Set (Edge α β)` and `Set (Arc α β)`.
2. **Name endpoint images separately.** Add `Graph.edgeEnds` and `DiGraph.arcEnds` (final names
   subject to the naming review) with image-membership lemmas.
3. **Repair general incidence and adjacency.** Public `Inc`, `IsLink`, `IsArc`, and `Adj` quantify
   over actual bundled records and inspect their endpoint fields. Keep direct endpoint projection
   in the API.
4. **Keep subgraph/induce structure.** The existing actual-record inclusion and filters already
   have the right representation semantics; expose laws through `E(G)` after its repair.
5. **Add actual-edge restriction/deletion.** `restrictEdges`, `deleteEdges`, and singleton
   `deleteEdge` operate on sets/values of the actual bundled carrier. Endpoint-wide deletion is
   separately named.
6. **Document identity.** Replace wording that suggests `β` alone is an edge identity. State that
   it is a tag/discriminator and the whole bundle is identity. Do not add a uniqueness field.
7. **Key unrestricted edge data by full records.** Provide transport APIs for vertex/tag
   equivalences, reverse, and provenance-preserving maps.
8. **Add record transformations.** `Edge`/`Arc` vertex and tag relabel equivalences,
   `Arc.reverse`, graph reverse, and their `id`/`comp`/`involution` laws.
9. **Repair general walk vocabulary.** Add `Graph.IsWalkIn` / `DiGraph.IsWalkIn`; distinguish raw
   tag lists from reconstructed actual edges/arcs; define trail/Eulerian predicates on actual
   records; prove directed reverse realization.
10. **Reserve provenance-bearing result types.** Noninjective maps must not expose the unsafe
    same-tag set image as an identity-preserving operation.

Items 1–6 are the immediate representation repair. Items 7–10 belong to later API construction,
not to a core structure migration. Contraction is not part of this task.

## 9. Decision register

### `LOCKED`

1. General graphs retain bundled `Edge α β` / `Arc α β` edge sets for the current architecture
   and construction plan.
2. Actual identity is the full bundled value.
3. `E(G)` always denotes actual edges, including in general graphs.
4. Endpoint images never use the name or notation for actual edge sets.
5. There is no hidden or mandatory uniqueness invariant on `endpointsLabel`.
6. Delete-one-edge, weights, costs, capacities, MST edge sets, flow arcs, and edge repetition use
   actual bundled values.
7. Induced/restricted/deleted graphs retain ambient types and do not introduce endpoint subtypes.
8. A residual identity includes full origin and forward/backward polarity under every core
   representation.
9. Noninjective operations may not silently merge edges while claiming identity preservation.

### `PROVISIONAL`

1. The exact names `edgeEnds`, `arcEnds`, `label`, and `LabelInjective` await the naming/API
   review.
2. The exact result type for arbitrary vertex maps: likely an origin-tagged graph plus an edge
   correspondence, but the production wrapper and flattening laws need a client.
3. Whether edge data remains namespace aliases/functions or receives a small bundled wrapper.
4. Whether graph-independent `Walk` stores step tags and reconstructs bundles, stores exact
   bundles, or exposes both through a thin view. In all cases, identity-sensitive predicates use
   actual reconstructed edges/arcs.
5. Optional globally unique-tag support for clients that want stable `β → W` data.

### `DEFERRED`

1. Contraction implementation and its algebraic laws.
2. Repeated-provenance normalization across several noninjective transformations.
3. A future migration to abstract `ε`, including the choice between relations and endpoint
   functions.
4. Direct aliasing of Mathlib `Graph` rather than an adapter.
5. A public `GraphLike`, dart, or incidence hierarchy while upstream proposals remain unsettled.
6. Incidence identities/half-edges for embeddings or non-backtracking walks.

### Reopening criteria

The core representation decision should be reopened only with concrete evidence, for example:

- two independent near-term clients repeatedly need arbitrary vertex maps while preserving the
  same edge-indexed functions literally;
- edge-equivalence/reverse transports escape helper lemmas and dominate MST, flow, or walk
  statements;
- repeated contraction/map composition makes provenance carriers materially unmanageable;
- graph-independent certificates must share one edge identity type across many vertex types;
- direct reuse of substantial merged Mathlib multigraph theory outweighs adapter and endpoint
  ergonomics.

One future contraction API by itself is not sufficient evidence.

## 10. Consequences for the later naming/API plan

The later plan must respect this short list:

1. `E(G)` means actual edge objects for all four graph kinds.
2. Endpoint images have explicit names and never masquerade as `E(G)`.
3. Documentation calls `β` a tag/discriminator unless an optional uniqueness interface is in
   scope; it does not call `β` the general edge identity.
4. `IsLink e u v` / `IsArc e u v` take actual bundled `e` and are derived from membership plus
   direct endpoints.
5. API names distinguish deleting one edge from deleting all edges between endpoints.
6. `relabel` is injective/bijective; arbitrary `map` exposes provenance or quotienting.
7. `reverse` and `residual` are different constructions. Residual names expose origin and
   polarity.
8. Weight/cost/capacity domains and walk edge lists use actual bundled values; raw tag lists are
   named as tags.
9. Transformation results return explicit edge correspondences so data transport is discoverable
   and compositional.
10. No construction plan should implement contraction as part of this representation repair.

## Final recommendation

Revise the previous architecture proposal narrowly: retain the current bundled storage, correct
the public actual-edge semantics, and move collision prevention into the APIs that perform
noninjective or identity-creating transformations.

The repaired bundle is not perfect. Separate abstract identity has a meaningful long-term
advantage for maps, reversal, and stable edge-indexed data. Today, however, GraphLib has direct
evidence for bundle endpoint ergonomics and no mature general MST/flow clients demonstrating
pervasive transport pain. The required stress tests show that future contraction and residual
identity can be handled locally and correctly. A breaking migration now would therefore be
premature abstraction rather than an evidence-driven improvement.
