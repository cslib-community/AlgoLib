/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Fable 5.1)
-/
module

public import AlgoLib.Theory.Graph.Structures.InSimpleDiGraph
public import AlgoLib.Theory.Graph.Connectivity.Reachable
public import Mathlib.Data.ENat.Lattice

/-!
# Reachability and distance in a simple directed graph

The directed analogue of `AlgoLib.Theory.Graph.Connectivity.Reachable`, together with the
*distance* — the least length of a walk between two vertices. The distance is the
specification that breadth-first search (`AlgoLib.Algorithms.Graph.Traversal.BFS`) is
proved to compute.

Because every simple graph has a symmetric orientation `SimpleGraph.toSimpleDiGraph` in
which walks are the same walks, the undirected distance is *defined* through the directed
one rather than duplicated; the transfer lemmas at the end of this file are what make
that definition usable.

## Main definitions

* `SimpleDiGraph.Reachable G u v` — some simple walk realized in `G` runs from `u` to `v`.
* `SimpleDiGraph.dist G u v` — the least length of such a walk, in `ℕ∞`; `⊤` when `v` is
  not reachable from `u`.
* `SimpleGraph.dist G u v` — the distance in the symmetric orientation.

## Main results

* `SimpleDiGraph.Reachable.refl`, `SimpleDiGraph.Reachable.trans` — reachability is a
  preorder on `V(G)`. There is no symmetry: this is the directed setting.
* `SimpleDiGraph.dist_le_length`, `SimpleDiGraph.le_dist_iff` — the infimum API.
* `SimpleDiGraph.dist_eq_top_iff`, `SimpleDiGraph.reachable_iff_dist_ne_top` — the
  distance is finite exactly on reachable pairs.
* `SimpleDiGraph.dist_exists` — a finite distance is attained by a walk.
* `SimpleGraph.reachable_toSimpleDiGraph_iff` — reachability in `G` is reachability in
  its symmetric orientation, and likewise `SimpleGraph.dist_comm` for the distance.

## Design choices

* **Walks, not paths, in the definitions**, for the same reason as in the undirected
  file: gluing two walks is a walk, while gluing two paths needs cycle erasure, hence
  `[DecidableEq α]` inside a `Prop`. A shortest walk is automatically a path, so nothing
  is lost.
* **Nested `⨅`, mirroring `girth` and `κ`.** `dist` has the shape
  `⨅ (w) (_ : P w), f w`, so the standard infimum API (`le_iInf₂_iff`, `iInf₂_le`,
  `iInf_eq_top`) applies verbatim, and `⊤` on unreachable pairs is the empty-index
  convention rather than a special case.
* **The undirected distance is the directed one.** `SimpleGraph.dist` unfolds to
  `SimpleDiGraph.dist` on `G.toSimpleDiGraph`: one definition, one algorithm, and one
  correctness proof serve both kinds of graph.
-/

@[expose] public section

variable {α : Type*}

namespace AlgoLib

open scoped AlgoLib

namespace SimpleDiGraph

/-! ## Reachability -/

/-- `v` is *reachable* from `u` in the simple directed graph `G` when some simple walk
realized in `G` runs from `u` to `v`. Reachability is reflexive only at vertices of `G`
and, unlike the undirected notion, not symmetric. -/
@[grind] def Reachable (G : SimpleDiGraph α) (u v : α) : Prop :=
  ∃ w : SimpleWalk α, G.IsSimpleWalkIn w ∧ w.head = u ∧ w.tail = v

/-- The source of a reachability is a vertex of `G`. -/
@[grind →] theorem Reachable.left_mem {G : SimpleDiGraph α} {u v : α}
    (h : G.Reachable u v) : u ∈ V(G) := by
  obtain ⟨w, hw, rfl, -⟩ := h
  exact IsSimpleWalkIn.head_mem G hw

/-- The target of a reachability is a vertex of `G`. -/
@[grind →] theorem Reachable.right_mem {G : SimpleDiGraph α} {u v : α}
    (h : G.Reachable u v) : v ∈ V(G) := by
  obtain ⟨w, hw, -, rfl⟩ := h
  exact IsSimpleWalkIn.tail_mem G hw

/-- Reachability is reflexive on `V(G)`, witnessed by the one-vertex walk. -/
theorem Reachable.refl (G : SimpleDiGraph α) {v : α} (hv : v ∈ V(G)) : G.Reachable v v :=
  ⟨(SimplePath.singleton v).val, IsVertexSeqIn.singleton v hv, rfl, rfl⟩

/-- Reachability is transitive: glue the two witnessing walks at their shared vertex. -/
theorem Reachable.trans {G : SimpleDiGraph α} {u v w : α}
    (h₁ : G.Reachable u v) (h₂ : G.Reachable v w) : G.Reachable u w := by
  obtain ⟨p, hp, rfl, rfl⟩ := h₁
  obtain ⟨q, hq, hqh, rfl⟩ := h₂
  exact ⟨p.glue q hqh.symm, IsSimpleWalkIn.glue G hp hq hqh.symm,
    SimpleWalk.head_glue p q _, SimpleWalk.tail_glue p q _⟩

/-- A vertex reaches itself exactly when it is a vertex of `G`. -/
@[simp] theorem reachable_self_iff {G : SimpleDiGraph α} {v : α} :
    G.Reachable v v ↔ v ∈ V(G) :=
  ⟨Reachable.left_mem, Reachable.refl G⟩

/-- The target of an arc is reachable from its source, by the length-one walk. -/
theorem Adj.reachable {G : SimpleDiGraph α} {u v : α} (h : G.Adj u v) : G.Reachable u v := by
  refine ⟨⟨(VertexSeq.singleton u).cons v, by simpa [VertexSeq.nonstalling] using h.ne⟩,
    ?_, rfl, rfl⟩
  exact IsVertexSeqIn.cons (VertexSeq.singleton u) v
    (IsVertexSeqIn.singleton u h.left_mem) (by simpa using h)

/-- Reachability is monotone under passing to a supergraph. -/
theorem Reachable.mono {G H : SimpleDiGraph α} {u v : α} (h : H.Reachable u v)
    (hsub : SimpleDiGraph.subgraphOf H G) : G.Reachable u v := by
  obtain ⟨w, hw, h1, h2⟩ := h
  exact ⟨w, IsSimpleWalkIn.mono G H hw hsub, h1, h2⟩

/-! ## Distance -/

/-- The *distance* from `u` to `v` in `G`: the least length of a simple walk realized in
`G` from `u` to `v`, and `⊤` when there is none. -/
noncomputable def dist (G : SimpleDiGraph α) (u v : α) : ℕ∞ :=
  ⨅ (w : SimpleWalk α) (_ : G.IsSimpleWalkIn w ∧ w.head = u ∧ w.tail = v), (w.length : ℕ∞)

/-- Every walk from `u` to `v` bounds the distance from above. -/
lemma dist_le_length {G : SimpleDiGraph α} {u v : α} {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) (hu : w.head = u) (hv : w.tail = v) :
    G.dist u v ≤ w.length :=
  iInf₂_le w ⟨hw, hu, hv⟩

/-- The lower-bound characterization of the distance: the workhorse lemma. -/
theorem le_dist_iff {G : SimpleDiGraph α} {u v : α} {n : ℕ∞} :
    n ≤ G.dist u v ↔
      ∀ w : SimpleWalk α, G.IsSimpleWalkIn w → w.head = u → w.tail = v → n ≤ w.length := by
  simp [dist, le_iInf_iff]

/-- The distance is infinite exactly when `v` is not reachable from `u`. -/
theorem dist_eq_top_iff {G : SimpleDiGraph α} {u v : α} :
    G.dist u v = ⊤ ↔ ¬ G.Reachable u v := by
  simp [dist, iInf_eq_top, Reachable]
  exact ⟨fun h w hG hu hns => h w hns hG hu, fun h w hns hG hu => h w hG hu hns⟩

/-- `v` is reachable from `u` exactly when the distance is finite. -/
theorem reachable_iff_dist_ne_top {G : SimpleDiGraph α} {u v : α} :
    G.Reachable u v ↔ G.dist u v ≠ ⊤ := by
  rw [Ne, dist_eq_top_iff, not_not]

/-- A finite distance is attained: some walk from `u` to `v` has exactly that length. -/
theorem dist_exists {G : SimpleDiGraph α} {u v : α} (h : G.Reachable u v) :
    ∃ w : SimpleWalk α, G.IsSimpleWalkIn w ∧ w.head = u ∧ w.tail = v ∧
      (w.length : ℕ∞) = G.dist u v := by
  have hne : Nonempty {w : SimpleWalk α // G.IsSimpleWalkIn w ∧ w.head = u ∧ w.tail = v} :=
    nonempty_subtype.mpr h
  obtain ⟨w, hw⟩ := @ENat.exists_eq_iInf _ hne fun w => (w.val.length : ℕ∞)
  exact ⟨w.val, w.property.1, w.property.2.1, w.property.2.2, hw.trans iInf_subtype⟩

/-- A vertex is at distance zero from itself, by the one-vertex walk. -/
@[simp] theorem dist_self {G : SimpleDiGraph α} {v : α} (hv : v ∈ V(G)) : G.dist v v = 0 := by
  have hw : G.IsSimpleWalkIn (SimplePath.singleton v).val := IsVertexSeqIn.singleton v hv
  have := dist_le_length (u := v) (v := v) hw rfl rfl
  simp only [SimpleWalk.length, SimplePath.vertices_singleton, VertexSeq.length_singleton,
    Nat.cast_zero, nonpos_iff_eq_zero] at this
  exact this

/-- The endpoints of an arc are at distance at most one, by the length-one walk. -/
theorem dist_le_one_of_adj {G : SimpleDiGraph α} {u v : α} (h : G.Adj u v) :
    G.dist u v ≤ 1 := by
  have := dist_le_length (u := u) (v := v)
    (w := ⟨(VertexSeq.singleton u).cons v, by simpa [VertexSeq.nonstalling] using h.ne⟩)
    (IsVertexSeqIn.cons (VertexSeq.singleton u) v (IsVertexSeqIn.singleton u h.left_mem)
      (by simpa using h)) rfl rfl
  simpa [VertexSeq.length] using this

/-- The triangle inequality: a shortest walk to `v` glued to a shortest walk from `v` to
`w` is a walk from `u` to `w` of the summed length. -/
theorem dist_triangle (G : SimpleDiGraph α) (u v w : α) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  by_cases h₁ : G.Reachable u v
  · by_cases h₂ : G.Reachable v w
    · obtain ⟨p, hp, hpu, hpv, hplen⟩ := dist_exists h₁
      obtain ⟨q, hq, hqv, hqw, hqlen⟩ := dist_exists h₂
      rw [← hplen, ← hqlen]
      calc G.dist u w ≤ ((p.glue q (hpv.trans hqv.symm)).length : ℕ∞) :=
            dist_le_length (IsSimpleWalkIn.glue G hp hq _) (by simp [hpu]) (by simp [hqw])
        _ = (p.length : ℕ∞) + q.length := by rw [SimpleWalk.length_glue]; push_cast; rfl
    · rw [dist_eq_top_iff.2 h₂, add_top]
      exact le_top
  · rw [dist_eq_top_iff.2 h₁, top_add]
    exact le_top

end SimpleDiGraph

/-! ## The symmetric orientation

A simple walk is realized in `G` exactly when it is realized in the symmetric orientation
`G.toSimpleDiGraph`, because adjacency is the same relation. Reachability and distance
transfer accordingly, and the undirected distance is defined through the directed one. -/

namespace SimpleGraph

/-- A vertex sequence is realized in the symmetric orientation exactly when it is realized
in the graph. -/
@[simp] theorem isVertexSeqIn_toSimpleDiGraph_iff (G : SimpleGraph α) {w : VertexSeq α} :
    G.toSimpleDiGraph.IsVertexSeqIn w ↔ G.IsVertexSeqIn w := by
  induction w with
  | singleton v => simp
  | cons w u ih => simp [ih]

/-- A simple walk is realized in the symmetric orientation exactly when it is realized in
the graph. -/
@[simp] theorem isSimpleWalkIn_toSimpleDiGraph_iff (G : SimpleGraph α) {w : SimpleWalk α} :
    G.toSimpleDiGraph.IsSimpleWalkIn w ↔ G.IsSimpleWalkIn w :=
  G.isVertexSeqIn_toSimpleDiGraph_iff

/-- Reachability in the symmetric orientation is reachability in the graph. -/
@[simp] theorem reachable_toSimpleDiGraph_iff (G : SimpleGraph α) {u v : α} :
    G.toSimpleDiGraph.Reachable u v ↔ G.Reachable u v := by
  simp [SimpleDiGraph.Reachable, Reachable]

/-- The *distance* between `u` and `v` in the simple graph `G`: the least length of a
simple walk realized in `G` from `u` to `v`, and `⊤` when there is none. Defined as the
distance in the symmetric orientation, so that the directed theory and the breadth-first
search that computes it serve both kinds of graph. -/
noncomputable def dist (G : SimpleGraph α) (u v : α) : ℕ∞ := G.toSimpleDiGraph.dist u v

/-- Every walk from `u` to `v` bounds the distance from above. -/
lemma dist_le_length {G : SimpleGraph α} {u v : α} {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) (hu : w.head = u) (hv : w.tail = v) :
    G.dist u v ≤ w.length :=
  SimpleDiGraph.dist_le_length (G.isSimpleWalkIn_toSimpleDiGraph_iff.2 hw) hu hv

/-- The lower-bound characterization of the undirected distance. -/
theorem le_dist_iff {G : SimpleGraph α} {u v : α} {n : ℕ∞} :
    n ≤ G.dist u v ↔
      ∀ w : SimpleWalk α, G.IsSimpleWalkIn w → w.head = u → w.tail = v → n ≤ w.length := by
  simp [dist, SimpleDiGraph.le_dist_iff]

/-- The distance is infinite exactly when `u` and `v` are not reachable. -/
theorem dist_eq_top_iff {G : SimpleGraph α} {u v : α} :
    G.dist u v = ⊤ ↔ ¬ G.Reachable u v := by
  rw [dist, SimpleDiGraph.dist_eq_top_iff, reachable_toSimpleDiGraph_iff]

/-- `u` and `v` are reachable exactly when their distance is finite. -/
theorem reachable_iff_dist_ne_top {G : SimpleGraph α} {u v : α} :
    G.Reachable u v ↔ G.dist u v ≠ ⊤ := by
  rw [Ne, dist_eq_top_iff, not_not]

/-- A vertex is at distance zero from itself. -/
@[simp] theorem dist_self {G : SimpleGraph α} {v : α} (hv : v ∈ V(G)) : G.dist v v = 0 :=
  SimpleDiGraph.dist_self hv

/-- The undirected distance is symmetric: reverse the witnessing walks. -/
theorem dist_comm (G : SimpleGraph α) (u v : α) : G.dist u v = G.dist v u := by
  have key : ∀ a b : α, G.dist a b ≤ G.dist b a := fun a b =>
    le_dist_iff.2 fun w hw hb ha => by
      have := dist_le_length (u := a) (v := b) (IsSimpleWalkIn.reverse G hw)
        (by simp [SimpleWalk.reverse, ha]) (by simp [SimpleWalk.reverse, hb])
      simpa [SimpleWalk.reverse] using this
  exact le_antisymm (key u v) (key v u)

end SimpleGraph

end AlgoLib
