/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Adjacency
import GraphLib.Graph.Subgraph
import GraphLib.Theory.Structures.VertexSeq

/-!
# Vertex sequences realized in a simple graph

The predicate `SimpleGraph.IsVertexSeqIn G w` says the vertex sequence `w` is
*realized* in `G`: its head is a vertex of `G` and every consecutive pair is an
edge of `G` (phrased through `SimpleGraph.Adj`). This is the base layer of the
`InSimpleGraph` development; walks, paths and cycles build on it.

## Design choices

* **Adjacency, not edge sets.** The `cons` step is stated with `G.Adj w.tail u`
  rather than `s(w.tail, u) ∈ E(G)`. The two are definitionally equal, but `Adj`
  is the intended primitive and carries the reusable `symm`/`ne`/`left_mem`/
  `right_mem` API.

Part of the `InSimpleGraph` folder; see the umbrella module
`GraphLib.Theory.Structures.InSimpleGraph` for the overview.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## The realized-in predicate -/

/-- A vertex sequence is *realized in* `G` when its head is a vertex of `G` and
each consecutive pair is an edge of `G`. -/
@[grind] inductive IsVertexSeqIn (G : SimpleGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (he : G.Adj w.tail u) :
      IsVertexSeqIn G (w.cons u)

namespace IsVertexSeqIn

/-! ## Constructor characterizations -/

/-- A singleton is realized in `G` exactly when its vertex is in `G`. -/
@[simp, grind =] lemma singleton_iff (G : SimpleGraph α) (v : α) :
    G.IsVertexSeqIn (.singleton v) ↔ v ∈ V(G) :=
  ⟨fun h => by cases h; assumption, IsVertexSeqIn.singleton v⟩

/-- A `cons` is realized in `G` exactly when its prefix is realized and the new
step is an edge. -/
@[simp, grind =] lemma cons_iff (G : SimpleGraph α) (w : VertexSeq α) (u : α) :
    G.IsVertexSeqIn (w.cons u) ↔ G.IsVertexSeqIn w ∧ G.Adj w.tail u := by
  constructor
  · intro h; cases h with | cons w u hw he => exact ⟨hw, he⟩
  · intro ⟨hw, he⟩; exact .cons w u hw he

/-! ## Vertex membership -/

/-- The head of a realized sequence is a vertex of `G`. -/
@[grind →] lemma head_mem (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.head ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw he ih => exact ih

/-- The tail of a realized sequence is a vertex of `G`. -/
@[grind →] lemma tail_mem (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.tail ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw he ih => exact he.right_mem

/-- Every vertex of a realized sequence is a vertex of `G`. -/
@[grind →] lemma mem_vertexSet (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {v : α} (hv : v ∈ w) : v ∈ V(G) := by
  revert v
  induction hw <;> grind [SimpleGraph.Adj.right_mem]

/-! ## Shape of a realized sequence -/

/-- A realized sequence never stalls: consecutive vertices differ, because
adjacency in a simple graph forces distinct endpoints. Hence it underlies a
`SimpleWalk`. -/
@[grind →] lemma nonstalling (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.nonstalling := by
  induction hw <;> grind

/-! ## Closure under sequence operations -/

/-- Appending two realized sequences along an edge is realized. -/
@[grind] lemma append (G : SimpleGraph α) {w1 w2 : VertexSeq α}
    (h1 : G.IsVertexSeqIn w1) (h2 : G.IsVertexSeqIn w2)
    (he : G.Adj w1.tail w2.head) : G.IsVertexSeqIn (w1.append w2) := by
  induction h2 <;> grind [VertexSeq.tail_append]

/-- Prepending a vertex along an edge to the head preserves realization. -/
@[grind →] lemma prepend (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {u : α} (he : G.Adj u w.head) :
    G.IsVertexSeqIn ((VertexSeq.singleton u).append w) :=
  append G (.singleton u he.left_mem) hw he

/-- Reversing a realized sequence preserves realization (adjacency is symmetric
in a simple graph). -/
@[grind →] lemma reverse (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.reverse := by
  induction hw <;> grind [VertexSeq.reverse, VertexSeq.head_reverse]

/-- Dropping the last vertex preserves realization. -/
@[grind →] lemma dropTail (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropTail := by
  induction hw <;> grind

/-- Dropping the first vertex preserves realization. -/
@[grind →] lemma dropHead (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropHead := by
  induction hw with
  | singleton v hv => exact .singleton v hv
  | cons w u hw he ih =>
      cases w with
      | singleton x => exact .singleton u he.right_mem
      | cons t x => exact .cons _ u ih (by rw [VertexSeq.tail_dropHead]; exact he)

/-- Taking the prefix up to the first occurrence of `v` preserves realization. -/
@[grind →] lemma prefixUntil [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (v : α) (h : v ∈ w) :
    G.IsVertexSeqIn (w.prefixUntil v h) := by
  fun_induction VertexSeq.prefixUntil w v h <;> grind

/-- Dropping to the suffix from the first occurrence of `v` preserves
realization. -/
@[grind →] lemma suffixFrom [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (v : α) (h : v ∈ w) :
    G.IsVertexSeqIn (w.suffixFrom v h) := by
  fun_induction VertexSeq.suffixFrom w v h <;>
    grind [VertexSeq.tail_suffixFrom, SimpleGraph.Adj.right_mem]

/-- Taking the longest prefix on which `p` holds (plus its first failure)
preserves realization. -/
lemma takeWhile (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p] :
    G.IsVertexSeqIn (w.takeWhile p) := by
  fun_induction VertexSeq.takeWhile w p <;> grind

/-- Dropping the longest prefix on which `p` holds preserves realization. -/
lemma dropWhile (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p]
    (h : ∃ v ∈ w.toList, ¬ p v) : G.IsVertexSeqIn (w.dropWhile p h) := by
  fun_induction VertexSeq.dropWhile w p h <;>
    grind [VertexSeq.tail_dropWhile, SimpleGraph.Adj.right_mem]

/-- Removing immediate stalls preserves realization. (On a realized — hence
non-stalling — sequence `loopErase` is in fact the identity.) -/
lemma loopErase [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.loopErase := by
  rw [VertexSeq.loopErase_eq_self_of_nonstalling w (nonstalling G hw)]
  exact hw

/-- Cycle erasure preserves realization: dropping the detour between two
occurrences of a vertex keeps the sequence realized in `G`. -/
lemma cycleErase [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.cycleErase := by
  revert hw
  fun_induction VertexSeq.cycleErase w <;>
    intro hw <;> grind [IsVertexSeqIn.prefixUntil, VertexSeq.tail_cycleErase]

/-! ## Monotonicity -/

/-- Realization is monotone under passing to a supergraph. -/
@[grind →] lemma mono (G H : SimpleGraph α) {w : VertexSeq α}
    (hw : H.IsVertexSeqIn w) (hsub : SimpleGraph.subgraphOf H G) :
    G.IsVertexSeqIn w := by
  induction hw with
  | singleton v hv => exact .singleton v (hsub.1 hv)
  | cons w u hw he ih => exact .cons w u ih (hsub.2 he)

/-! ## Edge-free graphs -/

/-- If `G` has no edges, every realized sequence has length zero. -/
lemma length_zero_of_no_edges (G : SimpleGraph α) (hE : E(G) = ∅)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) : w.length = 0 := by
  induction hw <;> grind

/-! ## Edge-set characterization -/

/-- The edge-set view of realization, bridging the adjacency-based inductive
definition: `w` is realized in `G` exactly when its head is a vertex of `G` and
every edge it traverses is an edge of `G`. -/
theorem iff_edges (G : SimpleGraph α) (w : VertexSeq α) :
    G.IsVertexSeqIn w ↔ w.head ∈ V(G) ∧ ∀ e ∈ w.edges, e ∈ E(G) := by
  constructor
  · intro hw
    refine ⟨head_mem G hw, ?_⟩
    induction hw <;> grind [VertexSeq.mem_edges_cons]
  · induction w with
    | singleton v => intro h; exact .singleton v h.1
    | cons w u ih =>
        intro h
        rw [cons_iff]
        refine ⟨ih ⟨h.1, fun e he => h.2 e ?_⟩, h.2 s(w.tail, u) ?_⟩
        · rw [VertexSeq.mem_edges_cons]; exact Or.inl he
        · rw [VertexSeq.mem_edges_cons]; exact Or.inr rfl

/-- Any edge traversed by a realized vertex sequence is an edge of the graph. -/
@[grind →] lemma edge_mem (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {e : Sym2 α} (he : e ∈ w.edges) : e ∈ E(G) :=
  ((iff_edges G w).1 hw).2 e he

/-- The final step of a non-trivial realized vertex sequence is an adjacency in
the graph. -/
@[grind →] lemma last_adj (G : SimpleGraph α)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) (h : w.length ≠ 0) :
    G.Adj w.dropTail.tail w.tail := by
  apply edge_mem G hw
  rw [VertexSeq.edges_eq_dropTail_concat w h]
  simp [List.concat_eq_append]

end IsVertexSeqIn

end SimpleGraph

end GraphLib
