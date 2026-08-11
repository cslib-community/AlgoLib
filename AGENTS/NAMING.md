# GraphLib Naming Conventions

This document is the **prescriptive** naming standard for GraphLib. Follow it
when you add or rename declarations. It is not a summary of the current state:
where existing names disagree, they should drift toward these rules, not the
other way round. Every example below is a real declaration in the current
codebase.

## 0. North star

**Be short, but never distort the definition or the statement.**

Golden test for any name: *could a reader who knows the namespace reconstruct
the essential content of the statement from the name alone, without being misled?*
If shortening a name fails this test, the name is too short. If a name carries
words that the namespace, the statement, or the signature already make obvious,
it is too long.

When two names both pass the golden test, prefer the shorter, and prefer the one
that matches the closest existing sibling.

## 1. Lexical form

* **Types, structures, inductives, subtypes, and classifying predicates:**
  `CamelCase`. Examples: `SimpleGraph`, `SimpleDiGraph`, `VertexSeq`, `Walk`,
  `SimpleWalk`, `SimplePath`, `SimpleCycle`, and the `Is…`/`Has…` predicates
  `IsVertexSeqIn`, `IsSimpleWalkIn`, `IsAcyclic`, `IsBipartite`,
  `HasSimpleCycle`.
* **Data, accessors, and operations:** `lowerCamelCase`. Examples: `vertexSet`,
  `edgeSet`, `neighborSet`, `dropHead`, `dropTail`, `prefixUntil`, `suffixFrom`,
  `loopErase`, `cycleErase`.
* **Object-local predicates** (a plain property of one object, not a
  graph-theoretic classification): `lowerCamelCase`. Examples: `nodup`,
  `nonstalling`, `closed`, `subgraphOf`.
* **Classifying predicates** (a named graph-theoretic property) start with
  `Is…`/`Has…`: `IsAcyclic`, `IsBipartite`, `HasSimpleCycle`. Use this form only
  when the predicate deserves to be a first-class concept; otherwise use the
  object-local `lowerCamelCase` form.

## 2. Lemma name shape

A lemma name is read left to right as `conclusion` then, optionally,
`_of_<hypothesis>`. Common building blocks, all idiomatic in GraphLib:

* **Computation / rewrite:** `<operation>_<subject>` or
  `<result>_<operation>`. Examples: `head_cons`, `tail_dropHead`,
  `length_append`, `length_edges`, `edges_reverse`, `toVertexSeq_length`.
* **Membership:** prefix `mem_…`; endpoints use `head_mem`, `tail_mem`,
  `left_mem`, `right_mem`; ambient-graph membership uses `mem_vertexSet`.
* **Iff characterizations:** `<lhs>_iff` or `iff_<rhs>`. Examples:
  `singleton_iff`, `cons_iff`, `ge_iff`, `le_iff`, `iff_edges`, `iff_arcs`,
  `iff_isVertexSeqIn`, `same_color_iff_even`.
* **Directional consequences:** `<conclusion>_of_<hypothesis>` — but only under
  the rule in §3.

Keep the object being measured next to its measurement so lemmas about the same
accessor stay adjacent: `three_le_length_edges` sits beside the accessor
`length_edges` (not `three_le_edges_length`).

## 3. When to keep `_of_<hypothesis>`

This is the rule that most often decides length.

* **Keep** the `_of_<hyp>` suffix when `<hyp>` is the *substantive reason* the
  conclusion holds. The name should still say *why*.
  * `loopErase_eq_self_of_nonstalling` — non-stalling is exactly why it is the
    identity.
  * `head_not_mem_dropHead_of_nodup` — false without `nodup`.
  * `nodup_reverse_dropTail_of_closed` — closedness drives the result. Name the
    hypothesis by the predicate that is actually assumed (`closed`), not by an
    informal word for the situation (`cycle`); see §6.
  * `isAcyclic_of_no_edges`, `hasSimpleCycle_of_subgraph` — the hypothesis is the
    content.
* **Drop** the `_of_<hyp>` suffix when `<hyp>` is a routine domain/side
  condition already visible in the signature (a `length ≠ 0` guard, a
  decidability assumption, a well-formedness proof).
  * `dropTail_append` (was `…_of_length_ne_zero`).
  * `edges_eq_dropTail_concat` (was `…_of_length_ne_zero`).

Do **not** drop a hypothesis suffix just to save characters when doing so hides
the mathematical reason. Shorter is not worth a misleading name.

## 4. Predicate fragments keep `is`/`has`

When a lemma name refers to a classifying predicate, spell the predicate in
`lowerCamelCase` **including** its `is`/`has` prefix, matching the predicate
declaration so the lemma is greppable from the predicate.

* Predicate `IsAcyclic` → fragment `isAcyclic`: `isAcyclic_of_no_edges`,
  `infinite_iff_isAcyclic`, `infinite_of_isAcyclic`.
* Predicate `IsBipartite` → fragment `isBipartite`: `even_of_isBipartite`.
* Predicate `HasSimpleCycle` → fragment `hasSimpleCycle`:
  `hasSimpleCycle_of_subgraph`.

Do **not** drop the `is`/`has` to a bare adjective (`acyclic`, `bipartite`)
while the predicate still starts with `Is`/`Has`: that splits the predicate from
its lemmas. Renaming the predicates themselves to bare adjectives is out of
scope for this convention.

Bridge lemmas between two predicates keep both, minus the namespace: inside
`namespace IsSimpleWalkIn`, the bridge is `iff_isVertexSeqIn`, not
`isSimpleWalkIn_iff_isVertexSeqIn`.

## 5. `eq` before a right-hand side

* **Drop** `eq` when the right-hand side is a canonical constant (`zero`,
  `nil`): `length_zero_of_no_edges`, `edges_nil_of_length_zero`,
  `length_zero_of_nodup_closed`.
* **Keep** `eq` when the right-hand side is a compound expression:
  `edges_eq_dropTail_concat`, `tail_suffixFrom_eq_head_prefixUntil`.

## 6. Prefer meaning over encoding — but only real terms

Name the mathematical idea, not the Lean encoding, **when a defined name or a
standard term exists**.

* Girth `= ⊤` / `≠ ⊤`: use `infinite` / `finite`. "Infinite girth" and "finite
  girth" are standard graph theory. Hence `infinite_iff_isAcyclic`,
  `finite_of_two_le_degree`, not `eq_top_…` / `ne_top_…`.
* Use a defined predicate instead of its unfolding: `…_of_nodup_closed`, not
  `…_of_nodup_head_eq_tail`, because `closed` is defined as `head = tail`.
* Name the concept, not the field access: `edge_mem` (an edge is in `E(G)`),
  `last_adj` (the final step is an adjacency), not `mem_edgeSet_of_mem_edges` or
  `adj_dropTail_tail_tail_of_length_ne_zero`.

But do **not** invent informal or undefined vocabulary. A name may only use a
word that has a definition in the library or an unambiguous standard meaning.
Rejected because they name a concept that does not exist or is vague:
`finite_of_min_degree_two` (there is no `minDegree`; the hypothesis is
`∀ v, 2 ≤ G.degree v`, so `finite_of_two_le_degree`), `prefix_suffix_reassemble`
(`reassemble` is not a defined operation), `…_of_short_suffix`,
`…_of_fresh_adj`, `…_of_cycle` where no `cycle` predicate exists (the hypothesis
is `closed`, so write `…_of_closed`; this is the rule that fixes
`nodup_reverse_dropTail_of_cycle`, cf. §3).

## 7. Namespaces carry context; do not repeat them

Enter the object namespace and let it supply the leading noun. Do not repeat the
namespace, the object, or a word already forced by the statement.

* In `namespace girth`, write `even_of_isBipartite`, `infinite_of_no_edges`,
  `eq_length_of_minimal` — never repeat `girth`.
* In `namespace VertexSeq`, write `edges_nodup`, `head_cons` — not
  `vertexSeq_edges_nodup`.
* Nested predicate namespaces hold that predicate's API:
  `IsVertexSeqIn.head_mem`, `IsSimpleWalkIn.iff_edges`,
  `IsSimpleCycleIn.reverse`.

The same short name may legitimately recur in sibling namespaces
(`VertexSeq.edges_nodup`, `SimplePath.edges_nodup`, `SimpleCycle.edges_nodup`);
the namespace disambiguates. When referring across namespaces, qualify
explicitly (`VertexSeq.edges_nodup`).

## 8. Public API vs. implementation helpers

* Long, structure-describing names are fine — even preferred — for genuinely
  technical helper lemmas, especially any you expect to make `private`:
  `dropTail_prefixUntil_append_suffixFrom` (a `@[simp]` reconstruction lemma)
  earns its length because the name describes the left-hand side it rewrites.
* Do not spend effort shortening a lemma that should simply become `private` or
  a local `have`. Decide visibility first; a private helper does not need a
  polished public name.
* A public lemma name must describe the mathematical statement, never the proof
  strategy or an internal construction step.

## 9. Quick checklist for an agent

Before committing a new or changed name, confirm:

1. **Golden test:** the name reconstructs the statement's essence and misleads
   no one (§0).
2. **Lexical form** matches §1 (Type / accessor / predicate casing).
3. Every `_of_<hyp>` suffix is a *substantive reason*; routine guards are
   dropped (§3).
4. Predicate references keep their `is`/`has` fragment (§4).
5. `eq` is dropped before `zero`/`nil`, kept before compound RHS (§5).
6. Semantic words are real (defined or standard); no invented vocabulary (§6).
7. No word repeats the namespace or is forced by the statement (§7).
8. Sibling lemmas about the same object/accessor stay adjacent and parallel
   (§2).

When unsure, match the nearest existing sibling and prefer the more searchable
name.
