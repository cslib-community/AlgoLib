/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Adjacency
import GraphLib.Graph.Delete
import GraphLib.Graph.Map
import GraphLib.Graph.Reverse
import GraphLib.Graph.Subgraph
import GraphLib.Walk.VertexSeq

/-!
# Vertex sequences realized in simple directed graphs
-/

namespace GraphLib

variable {α γ : Type*}

open scoped GraphLib

namespace SimpleDiGraph

/-! ## Vertex sequences realized in a simple directed graph -/

/-- A vertex sequence is *realized in* a simple directed graph `G` when its head
is a vertex of `G` and each consecutive pair follows a directed edge of `G`. -/
@[grind] inductive IsVertexSeqIn (G : SimpleDiGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (ha : G.Adj w.tail u) :
      IsVertexSeqIn G (w.cons u)

namespace IsVertexSeqIn

/-! ## Constructor characterizations -/

/-- A singleton is realized in `G` exactly when its vertex is in `G`. -/
@[simp, grind =] lemma singleton_iff (G : SimpleDiGraph α) (v : α) :
    G.IsVertexSeqIn (.singleton v) ↔ v ∈ V(G) :=
  ⟨fun h => by cases h; assumption, IsVertexSeqIn.singleton v⟩

/-- A `cons` is realized in `G` exactly when its prefix is realized and the new
step is an arc. -/
@[simp, grind =] lemma cons_iff (G : SimpleDiGraph α) (w : VertexSeq α) (u : α) :
    G.IsVertexSeqIn (w.cons u) ↔ G.IsVertexSeqIn w ∧ G.Adj w.tail u := by
  constructor
  · intro h; cases h with | cons w u hw ha => exact ⟨hw, ha⟩
  · intro ⟨hw, ha⟩; exact .cons w u hw ha

/-! ## Vertex membership -/

/-- The head of a realized sequence is a vertex of `G`. -/
@[grind →] lemma head_mem (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.head ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw ha ih => exact ih

/-- The tail of a realized sequence is a vertex of `G`. -/
@[grind →] lemma tail_mem (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.tail ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw ha ih => exact ha.target_mem

/-- Every vertex of a realized sequence is a vertex of `G`. -/
@[grind →] lemma mem_vertexSet (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : ∀ v ∈ w, v ∈ V(G) := by
  induction hw <;> grind [SimpleDiGraph.Adj.target_mem]

/-- A realized sequence never stalls: consecutive vertices differ, because
adjacency in a simple directed graph forces distinct endpoints. Hence it
underlies a `SimpleWalk`. -/
@[grind →] lemma nonstalling (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.nonstalling := by
  induction hw <;> grind

/-! ## Closure under sequence operations -/

/-- Appending two realized sequences along an arc is realized. -/
@[grind] lemma append (G : SimpleDiGraph α) {w1 w2 : VertexSeq α}
    (h1 : G.IsVertexSeqIn w1) (h2 : G.IsVertexSeqIn w2)
    (ha : G.Adj w1.tail w2.head) : G.IsVertexSeqIn (w1.append w2) := by
  revert ha
  induction h2 with
  | singleton v hv => intro ha; exact .cons w1 v h1 ha
  | cons w u hw hadj ih =>
      intro ha
      exact .cons (w1.append w) u (ih ha) (by grind [VertexSeq.tail_append])

/-- Prepending a vertex along an arc to the head preserves realization. -/
@[grind →] lemma prepend (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {u : α} (ha : G.Adj u w.head) :
    G.IsVertexSeqIn ((VertexSeq.singleton u).append w) :=
  append G (.singleton u ha.source_mem) hw ha

/-- Dropping the last vertex preserves realization. -/
@[grind →] lemma dropTail (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropTail := by
  induction hw <;> grind

/-- Dropping the first vertex preserves realization. -/
@[grind →] lemma dropHead (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropHead := by
  induction hw with
  | singleton v hv => exact .singleton v hv
  | cons w u hw ha ih =>
      cases w with
      | singleton x => exact .singleton u ha.target_mem
      | cons t x => exact .cons _ u ih (by rw [VertexSeq.tail_dropHead]; exact ha)

/-- Realization is monotone under passing to a supergraph. -/
@[grind →] lemma mono (G H : SimpleDiGraph α) {w : VertexSeq α}
    (hw : H.IsVertexSeqIn w) (hsub : H ≤ G) :
    G.IsVertexSeqIn w := by
  induction hw with
  | singleton v hv => exact .singleton v (hsub.vertexSet_subset hv)
  | cons w u hw ha ih =>
      exact .cons w u ih (ha.mono hsub)

/-- Taking the prefix up to the first occurrence of `v` preserves realization. -/
@[grind →] lemma prefixUntil [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) :
    ∀ (v : α) (h : v ∈ w), G.IsVertexSeqIn (w.prefixUntil v h) := by
  induction hw with
  | singleton x hx => intro v h; grind
  | cons w u hw ha ih =>
      intro v h
      by_cases h2 : v ∈ w <;> grind

/-- Dropping to the suffix from the first occurrence of `v` preserves
realization. -/
@[grind →] lemma suffixFrom [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) :
    ∀ (v : α) (h : v ∈ w), G.IsVertexSeqIn (w.suffixFrom v h) := by
  induction hw with
  | singleton x hx => intro v h; grind
  | cons w u hw ha ih =>
      intro v h
      by_cases h2 : v ∈ w <;>
        grind [VertexSeq.tail_suffixFrom, SimpleDiGraph.Adj.target_mem]

/-- Taking the longest prefix on which `p` holds (plus its first failure)
preserves realization. -/
lemma takeWhile (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p] :
    G.IsVertexSeqIn (w.takeWhile p) := by
  induction hw with
  | singleton x hx => exact .singleton x hx
  | cons w u hw ha ih =>
      change G.IsVertexSeqIn (if ∃ v ∈ w.toList, ¬ p v then w.takeWhile p else w.cons u)
      by_cases hc : ∃ v ∈ w.toList, ¬ p v
      · rw [if_pos hc]; exact ih
      · rw [if_neg hc]; exact .cons w u hw ha

/-- Dropping the longest prefix on which `p` holds preserves realization. -/
lemma dropWhile (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p] :
    ∀ (h : ∃ v ∈ w.toList, ¬ p v), G.IsVertexSeqIn (w.dropWhile p h) := by
  induction hw with
  | singleton x hx => intro h; exact .singleton x hx
  | cons w u hw ha ih =>
      intro h
      change G.IsVertexSeqIn
        (if hq : ∃ v ∈ w.toList, ¬ p v then (w.dropWhile p hq).cons u else .singleton u)
      by_cases hc : ∃ v ∈ w.toList, ¬ p v
      · rw [dif_pos hc]
        exact .cons (w.dropWhile p hc) u (ih hc)
          (by rw [VertexSeq.tail_dropWhile]; exact ha)
      · rw [dif_neg hc]; exact .singleton u ha.target_mem

/-- If `G` has no arcs, every realized sequence has length zero. -/
lemma length_zero_of_no_edges (G : SimpleDiGraph α) (hE : E(G) = ∅)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) : w.length = 0 := by
  induction hw <;> grind

/-- Removing immediate stalls preserves realization. (On a realized — hence
non-stalling — sequence `loopErase` is in fact the identity.) -/
lemma loopErase [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.loopErase := by
  rw [VertexSeq.loopErase_eq_self_of_nonstalling w (nonstalling G hw)]
  exact hw

/-- Cycle erasure preserves realization: dropping the detour between two
occurrences of a vertex keeps the sequence realized in `G`. -/
lemma cycleErase [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.cycleErase := by
  revert hw
  fun_induction VertexSeq.cycleErase w <;>
    intro hw <;> grind [IsVertexSeqIn.prefixUntil, VertexSeq.tail_cycleErase]

/-! ## Arc-list characterization -/

/-- The arc-list view of realization, bridging the adjacency-based inductive
definition: `w` is realized in `G` exactly when its head is a vertex of `G` and
every arc it traverses is an edge of `G`. -/
theorem iff_arcs (G : SimpleDiGraph α) (w : VertexSeq α) :
    G.IsVertexSeqIn w ↔ w.head ∈ V(G) ∧ ∀ a ∈ w.arcs, a ∈ E(G) := by
  constructor
  · intro hw
    refine ⟨head_mem G hw, ?_⟩
    induction hw with
    | singleton v hv => intro a ha; simp [VertexSeq.arcs] at ha
    | cons w u hw ha ih =>
        intro a hmem
        rw [VertexSeq.mem_arcs_cons] at hmem
        rcases hmem with hmem | rfl
        · exact ih a hmem
        · exact (G.adj_iff w.tail u).1 ha
  · induction w with
    | singleton v => intro h; exact .singleton v h.1
    | cons w u ih =>
        intro h
        rw [cons_iff]
        refine ⟨ih ⟨h.1, fun a ha => h.2 a (by
          rw [VertexSeq.mem_arcs_cons]
          exact Or.inl ha)⟩, ?_⟩
        apply (G.adj_iff w.tail u).2
        exact h.2 (w.tail, u) (by
          rw [VertexSeq.mem_arcs_cons]
          exact Or.inr rfl)

/-! ## Graph transformations -/

/-- Inducing a digraph preserves exactly the sequences whose vertices lie in the set. -/
theorem induce_iff (G : SimpleDiGraph α) (S : Set α) (w : VertexSeq α) :
    (G.induce S).IsVertexSeqIn w ↔ G.IsVertexSeqIn w ∧ ∀ v ∈ w, v ∈ S := by
  constructor
  · intro h
    exact ⟨mono G (G.induce S) h (G.induce_le S), fun v hv =>
      ((G.mem_vertexSet_induce S v).1 (mem_vertexSet (G.induce S) h v hv)).1⟩
  · rintro ⟨hG, hS⟩
    rw [iff_arcs]
    refine ⟨(G.mem_vertexSet_induce S w.head).2 ⟨hS _ (by simp), head_mem G hG⟩, ?_⟩
    intro a ha
    rw [G.mem_edgeSet_induce]
    exact ⟨((iff_arcs G w).1 hG).2 a ha, hS _ (VertexSeq.source_mem_of_arc_mem w ha),
      hS _ (VertexSeq.target_mem_of_arc_mem w ha)⟩

/-- Restricting arcs preserves exactly the sequences whose traversed arcs survive. -/
theorem restrictEdges_iff (G : SimpleDiGraph α) (F : Set (α × α)) (w : VertexSeq α) :
    (G.restrictEdges F).IsVertexSeqIn w ↔
      G.IsVertexSeqIn w ∧ ∀ a ∈ w.arcs, a ∈ F := by
  simp only [iff_arcs, G.mem_vertexSet_restrictEdges, G.mem_edgeSet_restrictEdges]
  aesop

/-- Deleting arcs preserves exactly the sequences avoiding those arcs. -/
theorem deleteEdges_iff (G : SimpleDiGraph α) (F : Set (α × α)) (w : VertexSeq α) :
    (G.deleteEdges F).IsVertexSeqIn w ↔
      G.IsVertexSeqIn w ∧ ∀ a ∈ w.arcs, a ∉ F := by
  simp only [iff_arcs, G.vertexSet_deleteEdges, G.mem_edgeSet_deleteEdges]
  aesop

/-- Deleting vertices preserves exactly the sequences avoiding the deleted set. -/
theorem deleteVerts_iff (G : SimpleDiGraph α) (S : Set α) (w : VertexSeq α) :
    (G.deleteVerts S).IsVertexSeqIn w ↔
      G.IsVertexSeqIn w ∧ ∀ v ∈ w, v ∉ S := by
  simpa [Set.mem_compl_iff] using induce_iff G Sᶜ w

/-- Vertex relabeling transports a realized sequence. -/
theorem relabelVertices {G : SimpleDiGraph α} {w : VertexSeq α} (f : α ≃ γ)
    (h : G.IsVertexSeqIn w) : (G.relabelVertices f).IsVertexSeqIn (w.map f) := by
  induction h with
  | singleton v hv => exact .singleton (f v) ⟨v, hv, rfl⟩
  | cons w u hw hadj ih =>
      exact .cons (w.map f) (f u) ih (by
        simpa using ((G.relabelVertices_adj f w.tail u).2 hadj))

/-- Reversing a realized directed sequence realizes it in the reversed digraph. -/
theorem reverse (G : SimpleDiGraph α) {w : VertexSeq α} (hw : G.IsVertexSeqIn w) :
    G.reverse.IsVertexSeqIn w.reverse := by
  rw [iff_arcs]
  refine ⟨by simpa using tail_mem G hw, ?_⟩
  intro a ha
  rw [VertexSeq.arcs_reverse] at ha
  rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
  rw [G.mem_edgeSet_reverse]
  simpa using ((iff_arcs G w).1 hw).2 b (List.mem_reverse.mp hb)

/-- Any arc traversed by a realized vertex sequence is an edge of the graph. -/
@[grind →] lemma arc_mem (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {a : α × α} (ha : a ∈ w.arcs) : a ∈ E(G) :=
  ((iff_arcs G w).1 hw).2 a ha

/-- The final step of a non-trivial realized vertex sequence is an adjacency in
the graph. -/
@[grind →] lemma last_adj (G : SimpleDiGraph α)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) (h : w.length ≠ 0) :
    G.Adj w.dropTail.tail w.tail := by
  apply (G.adj_iff _ _).2
  exact arc_mem G hw
    (by
      rw [VertexSeq.arcs_eq_dropTail_concat w h]
      simp [List.concat_eq_append])

end IsVertexSeqIn

end SimpleDiGraph

end GraphLib
