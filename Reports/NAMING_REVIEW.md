# GraphLib Lemma Naming Review

This report audits lemma/theorem names in the files listed by `new_files.md`.
It does not propose source edits yet; it records a naming pass for later.

`STYLE.md` (the previously inferred style guide) has been retired: it merely
summarised the *current* naming status quo, and the point of this pass is to
change that status quo. The conventions below are the intended new basis.

Scope rule used here:

* "word count >= 4" means at least four underscore-separated parts in the
  declaration name.
* CamelCase inside a part is not counted as extra words for the main table, but
  is still considered when judging readability.
* Duplicated names in different namespaces are reviewed separately when their
  intended local API differs.

Naming direction used here (finalised):

* Public API names should read like mathematical API, not a compressed proof
  goal. Shorten aggressively — **but never at the cost of meaning.**
* Namespaces carry context. Do not repeat `girth`, `edgeSet`, `SimpleWalk`,
  etc. when the namespace or statement already makes that clear.
* Prefer semantic words such as `finite`, `infinite`, `edge_mem`, `last_adj`
  over raw encodings such as `eq_top`, `ne_top`, `mem_edgeSet`, `tail_tail`.
  For girth, `finite`/`infinite` are standard graph-theory terms and read far
  better than `ne_top`/`eq_top`.
* **Keep the predicate's own `is`/`has` fragment.** The predicates are named
  `IsAcyclic`, `IsBipartite`, `HasSimpleCycle`; lemma names that refer to them
  keep `isAcyclic`, `isBipartite`, `hasSimpleCycle` so the name stays greppable
  and matches the predicate. Dropping `is` while the predicate still starts with
  `Is` would split the predicate from its lemmas — the worst of both worlds.
* Drop the `eq` before a canonical constant right-hand side (`nil`, `zero`):
  `length_zero`, `edges_nil`. Keep `eq` when the right-hand side is a compound
  expression (`edges_eq_dropTail_concat`).
* Drop a trailing `_of_<hyp>` only when `<hyp>` is a routine side/domain
  condition (`length_ne_zero`, a decidability assumption). **Keep it when
  `<hyp>` is the substantive reason the result holds** (`nonstalling`, `nodup`,
  `closed`/`cycle`): the name should still say *why*.
* Do not invent informal or undefined vocabulary (`reassemble`, `short`,
  `fresh`, `min_degree`, a bare `cycle` predicate that does not exist). Use only
  terms that have a definition or a standard graph-theory meaning.
* Do not rename a lemma derived from an accessor in a way that breaks
  parallelism with the accessor: keep `three_le_length_edges` next to the
  accessor lemma `length_edges`.
* Keep long names for genuinely technical helper lemmas, especially those likely
  to become `private`.

## 1. High-level recommendations

Most wrapper and computation names are already fine, especially names like
`head_singleton`, `tail_reverse`, `edges_reverse`, `arcs_suffixFrom_subset`.
The renames worth doing are concentrated in:

* graph-realization bridge lemmas in `InSimpleGraph.lean` and
  `InSimpleDiGraph.lean` (`mem_edgeSet_of_mem_edges`, `adj_..._tail_tail_...`);
* finite/infinite girth lemmas in `Girth.lean` (`eq_top`/`ne_top` encodings);
* a few endpoint/closing-edge helper lemmas in `VertexSeq/Edges.lean`.

Several of codex's earlier proposals are **rejected** here because they trade
meaning for brevity or drop the predicate's `is` fragment; those rows now read
"keep". The main rename batch should target the semantic wins first.

## 2. Candidate review table

### `GraphLib/Theory/Structures/VertexSeq/Basic.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:189` | `head_eq_tail_of_length_zero` | keep | none | Long but clear and canonical. `length_zero` is the preferred form. |

### `GraphLib/Theory/Structures/VertexSeq/Append.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:162` | `dropTail_append_of_length_ne_zero` | rename | `dropTail_append` | `length_ne_zero` is a routine domain condition already in the signature. |
| `:188` | `nodup_reverse_dropTail_of_cycle` | keep | none | `of_cycle` (closedness) is the substantive reason the result holds; keep it. Reordering the operations buys nothing and risks a term-structure mismatch. |

### `GraphLib/Theory/Structures/VertexSeq/Edges.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:77` | `edges_eq_nil_of_length_eq_zero` | rename | `edges_nil_of_length_zero` | Drop `eq` before the constant RHS `nil`/`zero`. |
| `:85` | `edges_eq_dropTail_concat_of_length_ne_zero` | rename | `edges_eq_dropTail_concat` | Drop the routine `length_ne_zero` suffix; keep `eq` since the RHS is a compound expression. |
| `:101` | `arcs_eq_nil_of_length_eq_zero` | rename | `arcs_nil_of_length_zero` | Same as edges. |
| `:109` | `arcs_eq_dropTail_concat_of_length_ne_zero` | rename | `arcs_eq_dropTail_concat` | Same as edges. |
| `:119` | `mem_of_mem_edges` | rename | `mem_of_edge_mem` | Grammar: an endpoint of an edge in `w.edges` is a vertex of `w`. |
| `:126` | `fst_mem_of_mem_arcs` | rename | `fst_mem_of_arc_mem` | Membership of an arc implies membership of its first endpoint. |
| `:133` | `snd_mem_of_mem_arcs` | rename | `snd_mem_of_arc_mem` | Same. |
| `:143` | `nodup_edges_of_nodup` | rename | `edges_nodup` | Idiomatic and matches the existing `SimpleCycle.edges_nodup`. |
| `:159` | `length_le_one_of_mem_edges_head_tail` | rename | `length_le_one_of_closing_edge_mem` | "closing edge" (head→tail) is a real graph-theory notion and clearer than listing endpoints. |
| `:179` | `nodup_arcs_of_nodup` | rename | `arcs_nodup` | Parallel to `edges_nodup`, matches `SimpleCycle.arcs_nodup`. |
| `:194` | `length_le_one_of_mem_arcs_tail_head` | rename | `length_le_one_of_closing_arc_mem` | Directed analogue of the closing-edge helper. |

### `GraphLib/Theory/Structures/VertexSeq/Erase.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:110` | `loopErase_eq_self_of_nonstalling` | keep | none | Non-stalling is exactly *why* `loopErase` is the identity (its own docstring says so). Keep `of_nonstalling`. |

### `GraphLib/Theory/Structures/VertexSeq/MapZip.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:102` | `fst_mem_of_mem_zip` | rename | `fst_mem_of_zip_mem` | Grammar: from membership in a zip, the first component is in the left sequence. |

### `GraphLib/Theory/Structures/VertexSeq/Predicates.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:85` | `length_zero_of_nodup_head_eq_tail` | rename | `length_zero_of_nodup_closed` | `head_eq_tail` *is* the defined predicate `closed`; use the definition, not the raw fields. |
| `:100` | `head_not_mem_dropHead_of_nodup` | keep | none | `nodup` is the essential hypothesis (false without it); keep `of_nodup`. |
| `:120` | `nodup_dropHead_of_closed_dropTail` | keep | none | There is no `cycle` predicate on `VertexSeq`; `of_cycle` would be imprecise. Keep `closed`. Consider `private` if only used internally. |
| `:139` | `nodup_iff_toList_nodup` | keep | none | Iff characterization; searchable and clear. |

### `GraphLib/Theory/Structures/VertexSeq/Subseq.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:81` | `eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one` | keep/defer | none | Accurate but machine-like. `short_suffix` was rejected (informal, imprecise). Prefer making it `private`/local rather than inventing vocabulary. |
| `:335` | `dropTail_prefixUntil_append_suffixFrom` | keep | none | `prefix_suffix_reassemble` was rejected: `reassemble` is non-idiomatic and vague. For a `@[simp]` reconstruction lemma, the name describing the LHS structure is worth its length. |

### `GraphLib/Theory/Structures/SimpleWalk.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:250` | `mem_of_mem_edges` | rename | `mem_of_edge_mem` | Same as `VertexSeq`. |
| `:317` | `fst_mem_of_mem_arcs` | rename | `fst_mem_of_arc_mem` | Same. |
| `:322` | `snd_mem_of_mem_arcs` | rename | `snd_mem_of_arc_mem` | Same. |

### `GraphLib/Theory/Structures/SimpleCycle.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:100` | `tail_suffixFrom_eq_head_prefixUntil` | keep/defer | none | Clunky but faithful. Abbreviating `suffixFrom`/`prefixUntil` to `suffix`/`prefix` loses the exact operation. If it stays only a `reroot` helper, make it `private` instead of renaming. |
| `:182` | `three_le_length_edges` | keep | none | Must stay parallel to the accessor lemma `length_edges` (`:178`). `three_le_edges_length` was rejected. |
| `:243` | `three_le_length_arcs` | keep | none | Parallel to `length_arcs` (`:239`). |

### `GraphLib/Theory/Structures/InSimpleGraph.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:227` | `length_eq_zero_of_no_edges` | rename | `length_zero_of_no_edges` | Drop `eq` before the constant `zero`. |
| `:274` | `mem_edgeSet_of_mem_edges` | rename | `edge_mem` | In `IsVertexSeqIn`, every traversed edge is in `E(G)`; the namespace supplies the graph context. |
| `:280` | `adj_dropTail_tail_tail_of_length_ne_zero` | rename | `last_adj` | The theorem says the final step of the walk is an adjacency. `tail_tail` is unreadable. |
| `:325` | `mem_edgeSet_of_mem_edges` | rename | `edge_mem` | Same API at the `IsSimpleWalkIn` layer; namespace disambiguates. |
| `:429` | `length_eq_zero_of_no_edges` | rename | `length_zero_of_no_edges` | Same. |
| `:480` | `exists_longer_of_adj_not_mem` | keep | none | `fresh_adj` was rejected (informal). The current name faithfully states "adjacent to a non-member". |
| `:501` | `length_succ_le_ncard_vertexSet` | rename | `length_succ_le_vertex_card` | `vertex_card` reads better than the implementation-ish `ncard_vertexSet`. |
| `:547` | `mem_edgeSet_of_mem_edges` | rename | `edge_mem` | Same API at the `IsSimpleCycleIn` layer. |
| `:574` | `length_le_ncard_vertexSet` | rename | `length_le_vertex_card` | Same cardinality simplification. |
| `:616` | `isAcyclic_of_no_edges` | keep | none | Keep the predicate fragment `isAcyclic` (matches `IsAcyclic`). |

### `GraphLib/Theory/Structures/InSimpleDiGraph.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:211` | `length_eq_zero_of_no_edges` | rename | `length_zero_of_no_edges` | Same convention. |
| `:258` | `mem_edgeSet_of_mem_arcs` | rename | `arc_mem` | Directed analogue of `edge_mem`: every traversed arc is in `E(G)`. |
| `:264` | `adj_dropTail_tail_tail_of_length_ne_zero` | rename | `last_adj` | Same final-step theorem as the undirected version. |
| `:312` | `mem_edgeSet_of_mem_arcs` | rename | `arc_mem` | Same API at the `IsSimpleWalkIn` layer. |
| `:412` | `length_eq_zero_of_no_edges` | rename | `length_zero_of_no_edges` | Same convention. |

### `GraphLib/Theory/Structures/SimpleGraph_only/Bipartite.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:70` | `color_head_eq_tail_iff_even` | rename | `same_color_iff_even` | In namespace `Bipartite`, colour is the context; `same_color` (of the endpoints) reads like the theorem. |

### `GraphLib/Theory/Structures/SimpleGraph_only/Girth.lean`

| Location | Current name | Decision | Proposed name | Reason |
|---|---|---|---|---|
| `:97` | `eq_top_iff_isAcyclic` | rename | `infinite_iff_isAcyclic` | `infinite` girth is the standard, readable form; keep the `isAcyclic` predicate fragment. |
| `:112` | `eq_top_of_isAcyclic` | rename | `infinite_of_isAcyclic` | Same. |
| `:141` | `le_of_cycle_length_le` | rename | `le_of_cycle_length` | Removes a doubled `le`; the hypothesis is still an inequality in the signature. |
| `:155` | `ne_top_of_two_le_degree` | rename | `finite_of_two_le_degree` | Use semantic `finite`. Rejected `min_degree_two`: there is no `minDegree` definition and the hypothesis is literally `∀ v, 2 ≤ G.degree v`. |
| `:247` | `eq_cycle_length_of_minimal` | rename | `eq_length_of_minimal` | In namespace `girth`, "cycle" is already in the hypotheses; `length` is enough. |
| `:269` | `eq_top_of_no_edges` | rename | `infinite_of_no_edges` | Use semantic `infinite`. |
| `:278` | `even_girth_of_isBipartite` | rename | `even_of_isBipartite` | **Prerequisite: move this theorem into `namespace girth`** (it is currently in `SimpleGraph`). Once inside `girth`, drop the redundant `girth`; keep the `isBipartite` predicate fragment. |

## 3. `is` in lemma names

Finalised convention: **keep the predicate's `is`/`has` fragment in lemma
names.** The predicates are `IsAcyclic`, `IsBipartite`, `HasSimpleCycle`, so the
matching lemma fragments are `isAcyclic`, `isBipartite`, `hasSimpleCycle`. This
keeps a lemma greppable from its predicate and matches how the rest of the Lean
ecosystem names such lemmas. Dropping `is` while the predicate keeps `Is` would
break that link; renaming the predicates to bare adjectives is out of scope.

Concrete decisions:

| Current pattern | Decision | Reason |
|---|---|---|
| `eq_top_iff_isAcyclic` | → `infinite_iff_isAcyclic` | Only the `eq_top` encoding changes to semantic `infinite`; the `isAcyclic` fragment stays. |
| `eq_top_of_isAcyclic` | → `infinite_of_isAcyclic` | Same. |
| `isAcyclic_of_no_edges` | keep | Predicate fragment; do not drop `is`. |
| `even_girth_of_isBipartite` | → `even_of_isBipartite` (after moving into `namespace girth`) | Drop the redundant `girth`; keep `isBipartite`. |
| `hasSimpleCycle_of_subgraph` | keep | Matches predicate `HasSimpleCycle`. |
| `isAcyclic_of_subgraph` | keep | Matches predicate `IsAcyclic`. |
| `isCycle_reverse`, `isCycle_reroot_glue` | keep name; consider `private` | Visibility, not naming, is the open question for the helper. |
| `iff_isVertexSeqIn`, `iff_isSimpleWalkIn` | keep | Bridge lemmas to exact predicate names; already good. |

For the specific question: with the theorem correctly living in `namespace
girth`, the best name is **`even_of_isBipartite`** — better than
`even_girth_of_isBipartite` (namespace makes `girth` redundant) and better than
`even_of_bipartite` (which would drop the `isBipartite` predicate fragment).

## 4. Names below the main threshold but worth watching

These have fewer than four underscore-separated parts but still carry API-style
questions:

| Name | Recommendation |
|---|---|
| `toSimpleGraph_subgraphOf` / `toSimpleDiGraph_subgraphOf` | Keep; they name the generated-graph bridge exactly. |
| `of_toSimpleGraph_subgraphOf` / `of_toSimpleDiGraph_subgraphOf` | Verbose but precise; could become `of_subgraph` inside the right namespace if unambiguous. |
| `iff_toSimpleGraph_subgraphOf` / `iff_toSimpleDiGraph_subgraphOf` | Long; consider `iff_subgraph` only if namespace + statement stay unambiguous. |
| `edges_subset_edgeSet` / `arcs_subset_edgeSet` | Consider `edges_subset` / `arcs_subset` if kept public; the namespace already names the target graph. |
| `hasSimpleCycle_of_subgraph` | Keep (predicate fragment). |
| `isAcyclic_of_subgraph` | Keep (predicate fragment). |

## 5. Suggested rename batches

Batch A: graph-realization bridge names.

* Files: `InSimpleGraph.lean`, `InSimpleDiGraph.lean`.
* Rename: `edge_mem`, `arc_mem`, `last_adj`, `length_zero_of_no_edges`,
  `length_succ_le_vertex_card`, `length_le_vertex_card`.
* Risk: medium, because these are likely referenced by theory files.

Batch B: girth semantic names.

* File: `SimpleGraph_only/Girth.lean`.
* Prerequisite (Lean move, not a rename): put `even_girth_of_isBipartite` into
  `namespace girth`.
* Rename: `infinite_iff_isAcyclic`, `infinite_of_isAcyclic`,
  `finite_of_two_le_degree`, `infinite_of_no_edges`, `even_of_isBipartite`,
  `le_of_cycle_length`, `eq_length_of_minimal`.
* Risk: medium; these are public theory names.

Batch C: pure `VertexSeq` / wrapper cleanup.

* Files: `VertexSeq/Edges.lean`, `VertexSeq/Predicates.lean`,
  `VertexSeq/Append.lean`, `VertexSeq/MapZip.lean`, `SimpleWalk.lean`,
  `Bipartite.lean`.
* Rename: `edges_nil_of_length_zero`, `arcs_nil_of_length_zero`,
  `edges_eq_dropTail_concat`, `arcs_eq_dropTail_concat`, `mem_of_edge_mem`,
  `fst_mem_of_arc_mem`, `snd_mem_of_arc_mem`, `fst_mem_of_zip_mem`,
  `edges_nodup`, `arcs_nodup`, `length_le_one_of_closing_edge_mem`,
  `length_le_one_of_closing_arc_mem`, `length_zero_of_nodup_closed`,
  `dropTail_append`, `same_color_iff_even`.
* Risk: low to medium. Prefer making implementation-only helpers `private`
  before spending API-naming effort on them.

Rejected (no change): `loopErase_eq_self_of_nonstalling`,
`head_not_mem_dropHead_of_nodup`, `nodup_dropHead_of_closed_dropTail`,
`nodup_reverse_dropTail_of_cycle`, `dropTail_prefixUntil_append_suffixFrom`,
`eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one`,
`three_le_length_edges`, `three_le_length_arcs`, `exists_longer_of_adj_not_mem`,
`isAcyclic_of_no_edges`, `hasSimpleCycle_of_subgraph`, `isAcyclic_of_subgraph` —
each either drops a substantive `_of_` reason, drops a predicate `is`/`has`
fragment, breaks accessor parallelism, or invents informal vocabulary.
