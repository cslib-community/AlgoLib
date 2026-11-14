/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Fable 5.1)
-/
module

public import AlgoLib.Theory.Graph.Decidable
public import AlgoLib.Theory.Graph.Connectivity.Directed

/-!
# Breadth-first search

Breadth-first search (BFS) from a source vertex `s` of a simple directed graph `G`
explores the graph *layer by layer*: the layer `L₀ = {s}` is the source, and the layer
`Lₖ₊₁` consists of the out-neighbours of `Lₖ` that lie in no earlier layer. The layers
are the *spheres* around `s`: `Lₖ` is exactly the set of vertices at distance `k` from
`s`, and their union is the set of vertices reachable from `s`.

This file defines the search on a graph whose vertex set is finite as data and whose
arcs have decidable membership, and proves it correct against the specifications
`SimpleDiGraph.Reachable` and `SimpleDiGraph.dist` of
`AlgoLib.Theory.Graph.Connectivity.Directed`.

## Main definitions

* `SimpleDiGraph.BFSState` — the state of the search: the vertices `visited` so far and
  the current `frontier`, i.e. the most recent layer.
* `SimpleDiGraph.bfsStep G` — one round: expand the frontier to its unvisited
  out-neighbours.
* `SimpleDiGraph.bfsRun G s k` — the state after `k` rounds from `s`;
  `SimpleDiGraph.bfsLayer G s k` and `SimpleDiGraph.bfsVisited G s k` are its two
  components.
* `SimpleDiGraph.bfsReachableFinset G s` — the vertices reachable from `s`: the visited
  set after `|V(G)|` rounds.
* `SimpleDiGraph.bfsLayers G s` — the list of all layers, collected by one run.
* `SimpleDiGraph.bfsDist G s v` — the distance from `s` to `v`: the index of the layer
  containing `v`, or `⊤` if there is none.

## Main results

* `SimpleDiGraph.exists_walk_of_mem_bfsLayer` — *soundness*: a vertex of layer `k` is the
  endpoint of a walk of length `k` from `s`.
* `SimpleDiGraph.mem_bfsVisited_of_isVertexSeqIn` — *completeness*: the endpoint of a
  walk of length `ℓ` from `s` is visited after `ℓ` rounds.
* `SimpleDiGraph.lt_card_of_nonempty_bfsLayer` — *termination*: at most `|V(G)|` layers
  are non-empty, because the layers are pairwise disjoint subsets of `V(G)`.
* `SimpleDiGraph.mem_bfsReachableFinset_iff` — BFS computes reachability.
* `SimpleDiGraph.mem_bfsLayer_iff_dist_eq` — the `k`-th layer is the sphere of radius `k`.
* `SimpleDiGraph.bfsDist_eq_dist` — BFS computes the distance.
* `SimpleDiGraph.instDecidableReachable` — reachability in a finite directed graph is
  decidable.

## Design choices

* **Rounds by `Nat.iterate`, not well-founded recursion.** A recursive BFS whose
  termination rests on the measure `|V(G) \ visited|` is irreducible to the kernel, so
  `decide` cannot evaluate it. Iterating one round a fixed number of times is
  structurally recursive, hence reduces, and `|V(G)|` rounds always suffice: each
  non-empty layer contains a vertex no earlier layer does, so there are at most `|V(G)|`
  of them. The termination *argument* of the recursive formulation survives as the
  theorem `lt_card_of_nonempty_bfsLayer`, where it belongs.
* **Layers, not a distance map.** The state is the pair (visited, frontier) rather than
  a partial function `α → ℕ∞`: the frontier *is* the current sphere, so the level
  invariant "every frontier vertex is at distance `k`" is a statement about a `Finset`
  and needs no bookkeeping over an accumulated map. The distance is read off afterwards
  as the index of the first layer containing the vertex, in the list of layers
  `bfsLayers` that a single run of the search collects — so a distance query runs the
  search once, not once per candidate index.
* **Walks, not paths, in the correctness statements**, matching `dist`. Soundness builds
  a walk by appending one arc per round; completeness inducts on the `IsVertexSeqIn`
  derivation of an arbitrary walk, so no cycle erasure is ever needed.
* **The source is guarded.** `bfsStart G s` is `{s}` when `s` is a vertex of `G` and `∅`
  otherwise, so every statement below holds with no hypothesis on `s`: nothing outside
  `V(G)` reaches anything, and `Reachable s s ↔ s ∈ V(G)` is reproduced exactly.
-/

@[expose] public section

namespace AlgoLib

variable {α : Type*}

open scoped AlgoLib

namespace SimpleDiGraph

/-! ## The search -/

/-- The state of a breadth-first search: the set of vertices discovered so far, and the
*frontier* — the vertices discovered in the most recent round, whose out-neighbours are
explored next. The frontier is always contained in the visited set. -/
structure BFSState (α : Type*) where
  /-- All vertices discovered so far. -/
  visited : Finset α
  /-- The vertices discovered in the last round: the current layer. -/
  frontier : Finset α

/-- The next layer: the out-neighbours of the frontier that have not been visited. -/
def bfsNext (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (S : BFSState α) : Finset α :=
  S.frontier.biUnion G.computeOutNeighborFinset \ S.visited

/-- One round of breadth-first search: the next layer is discovered, and becomes the new
frontier. -/
def bfsStep (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (S : BFSState α) : BFSState α :=
  ⟨S.visited ∪ G.bfsNext S, G.bfsNext S⟩

/-- The initial state of the search from `s`: the single layer `{s}` if `s` is a vertex
of `G`, and the empty search otherwise. -/
def bfsStart (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet] (s : α) :
    BFSState α :=
  if s ∈ G.computeVertexFinset then ⟨{s}, {s}⟩ else ⟨∅, ∅⟩

/-- The state of the search from `s` after `k` rounds. -/
def bfsRun (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (s : α) (k : ℕ) : BFSState α :=
  (G.bfsStep)^[k] (G.bfsStart s)

/-- The `k`-th *layer* of the search from `s`: the frontier after `k` rounds. By
`mem_bfsLayer_iff_dist_eq` this is the set of vertices at distance exactly `k` from `s`. -/
def bfsLayer (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (s : α) (k : ℕ) : Finset α :=
  (G.bfsRun s k).frontier

/-- The vertices visited within `k` rounds of the search from `s`: the union of the layers
`0, …, k` (see `mem_bfsVisited_iff`), i.e. the vertices at distance at most `k`. -/
def bfsVisited (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (s : α) (k : ℕ) : Finset α :=
  (G.bfsRun s k).visited

/-- The vertices reachable from `s`, computed by breadth-first search: the visited set
after `|V(G)|` rounds, by which time every layer has been exhausted
(`lt_card_of_nonempty_bfsLayer`). -/
def bfsReachableFinset (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (s : α) : Finset α :=
  G.bfsVisited s G.computeVertexFinset.card

/-- The first `m` layers of the search started in state `S`, collected along a single run:
`[S.frontier, (bfsStep S).frontier, …]`. -/
def bfsLayersFrom (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] : ℕ → BFSState α → List (Finset α)
  | 0, _ => []
  | m + 1, S => S.frontier :: G.bfsLayersFrom m (G.bfsStep S)

/-- All the layers of the search from `s`, as the list `[L₀, …, L_{|V(G)|-1}]`, computed by
one run of the search. Every later layer is empty (`lt_card_of_nonempty_bfsLayer`), so
nothing is lost by stopping there. -/
def bfsLayers (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (s : α) : List (Finset α) :=
  G.bfsLayersFrom G.computeVertexFinset.card (G.bfsStart s)

/-- The distance from `s` to `v`, computed by breadth-first search: the index of the first
layer containing `v`, and `⊤` if no layer does. The layers come from a single run of the
search (`bfsLayers`). -/
def bfsDist (G : SimpleDiGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (s v : α) : ℕ∞ :=
  match (G.bfsLayers s).findIdx? (fun L => decide (v ∈ L)) with
  | some k => k
  | none => ⊤

variable {G : SimpleDiGraph α} [DecidableEq α] [Fintype G.vertexSet]
  [DecidablePred (· ∈ G.edgeSet)] {s v : α}

/-! ## Unfolding the rounds -/

lemma mem_bfsNext {S : BFSState α} :
    v ∈ G.bfsNext S ↔ (∃ u ∈ S.frontier, G.Adj u v) ∧ v ∉ S.visited := by
  simp [bfsNext]

@[simp] lemma bfsRun_zero : G.bfsRun s 0 = G.bfsStart s := rfl

lemma bfsRun_succ (k : ℕ) : G.bfsRun s (k + 1) = G.bfsStep (G.bfsRun s k) :=
  Function.iterate_succ_apply' _ _ _

/-- The zeroth layer is the source, provided it is a vertex. -/
lemma mem_bfsLayer_zero : v ∈ G.bfsLayer s 0 ↔ v = s ∧ s ∈ V(G) := by
  unfold bfsLayer bfsRun bfsStart
  split_ifs with h <;> simp_all

/-- Initially only the source is visited, provided it is a vertex. -/
lemma mem_bfsVisited_zero : v ∈ G.bfsVisited s 0 ↔ v = s ∧ s ∈ V(G) := by
  unfold bfsVisited bfsRun bfsStart
  split_ifs with h <;> simp_all

/-- The `(k + 1)`-st layer: unvisited out-neighbours of the `k`-th layer. -/
lemma mem_bfsLayer_succ (k : ℕ) :
    v ∈ G.bfsLayer s (k + 1) ↔ (∃ u ∈ G.bfsLayer s k, G.Adj u v) ∧ v ∉ G.bfsVisited s k := by
  rw [bfsLayer, bfsRun_succ]
  exact mem_bfsNext

/-- After `k + 1` rounds, the visited set has grown by exactly the `(k + 1)`-st layer. -/
lemma bfsVisited_succ (k : ℕ) :
    G.bfsVisited s (k + 1) = G.bfsVisited s k ∪ G.bfsLayer s (k + 1) := by
  rw [bfsVisited, bfsLayer, bfsRun_succ]
  rfl

/-! ## Invariants of the search -/

/-- The frontier is part of the visited set. -/
lemma bfsLayer_subset_bfsVisited (k : ℕ) : G.bfsLayer s k ⊆ G.bfsVisited s k := by
  cases k with
  | zero => intro v hv; rw [mem_bfsVisited_zero]; exact mem_bfsLayer_zero.1 hv
  | succ k => rw [bfsVisited_succ]; exact Finset.subset_union_right

/-- The visited set only grows. -/
lemma bfsVisited_subset_succ (k : ℕ) : G.bfsVisited s k ⊆ G.bfsVisited s (k + 1) := by
  rw [bfsVisited_succ]; exact Finset.subset_union_left

/-- The visited set is monotone in the number of rounds. -/
lemma bfsVisited_mono {j k : ℕ} (h : j ≤ k) : G.bfsVisited s j ⊆ G.bfsVisited s k := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (bfsVisited_subset_succ _)

/-- A new layer is disjoint from everything visited before it. -/
lemma disjoint_bfsLayer_succ_bfsVisited (k : ℕ) :
    Disjoint (G.bfsLayer s (k + 1)) (G.bfsVisited s k) := by
  rw [bfsLayer, bfsRun_succ]
  exact Finset.sdiff_disjoint

/-- Only vertices of `G` are ever visited. -/
lemma bfsVisited_subset_computeVertexFinset (k : ℕ) :
    G.bfsVisited s k ⊆ G.computeVertexFinset := by
  induction k with
  | zero =>
    intro v hv
    obtain ⟨rfl, hs⟩ := mem_bfsVisited_zero.1 hv
    simpa using hs
  | succ k ih =>
    rw [bfsVisited_succ]
    refine Finset.union_subset ih fun v hv => ?_
    obtain ⟨⟨u, -, hadj⟩, -⟩ := (mem_bfsLayer_succ k).1 hv
    simpa using hadj.right_mem

/-- The visited set after `k` rounds is the union of the first `k + 1` layers. -/
lemma mem_bfsVisited_iff (k : ℕ) : v ∈ G.bfsVisited s k ↔ ∃ j ≤ k, v ∈ G.bfsLayer s j := by
  induction k with
  | zero =>
    rw [mem_bfsVisited_zero]
    refine ⟨fun h => ⟨0, le_rfl, mem_bfsLayer_zero.2 h⟩, ?_⟩
    rintro ⟨j, hj, hv⟩
    rw [Nat.le_zero.1 hj] at hv
    exact mem_bfsLayer_zero.1 hv
  | succ k ih =>
    rw [bfsVisited_succ, Finset.mem_union, ih]
    constructor
    · rintro (⟨j, hj, hv⟩ | hv)
      · exact ⟨j, hj.trans (Nat.le_succ k), hv⟩
      · exact ⟨k + 1, le_rfl, hv⟩
    · rintro ⟨j, hj, hv⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inl ⟨j, Nat.lt_succ_iff.1 hlt, hv⟩
      · exact Or.inr (le_antisymm hj hge ▸ hv)

/-! ## Soundness: every layer vertex is the end of a walk of that length -/

/-- A vertex of the `k`-th layer is the endpoint of a walk of length `k` from `s`. -/
theorem exists_walk_of_mem_bfsLayer {k : ℕ} (hv : v ∈ G.bfsLayer s k) :
    ∃ w : SimpleWalk α, G.IsSimpleWalkIn w ∧ w.head = s ∧ w.tail = v ∧ w.length = k := by
  induction k generalizing v with
  | zero =>
    obtain ⟨rfl, hs⟩ := mem_bfsLayer_zero.1 hv
    exact ⟨(SimplePath.singleton v).val, IsVertexSeqIn.singleton v hs, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨⟨u, hu, hadj⟩, -⟩ := (mem_bfsLayer_succ k).1 hv
    obtain ⟨w, hw, hhead, htail, hlen⟩ := ih hu
    have htail' : w.val.tail = u := htail
    have hlen' : w.val.length = k := hlen
    have hne : w.val.tail ≠ v := by rw [htail']; exact hadj.ne
    refine ⟨⟨w.val.cons v, ⟨w.nonstalling, hne⟩⟩, ?_, hhead, rfl, ?_⟩
    · exact IsVertexSeqIn.cons w.val v hw (by rw [htail']; exact hadj)
    · change 1 + w.val.length = k + 1
      omega

/-- Every visited vertex is reachable from the source. -/
theorem reachable_of_mem_bfsVisited {k : ℕ} (hv : v ∈ G.bfsVisited s k) :
    G.Reachable s v := by
  obtain ⟨j, -, hj⟩ := (mem_bfsVisited_iff k).1 hv
  obtain ⟨w, hw, hhead, htail, -⟩ := exists_walk_of_mem_bfsLayer hj
  exact ⟨w, hw, hhead, htail⟩

/-! ## Completeness: the end of a walk of length `ℓ` is visited within `ℓ` rounds -/

/-- The out-neighbours of a visited vertex are visited one round later. -/
lemma mem_bfsVisited_succ_of_adj {u : α} {k : ℕ} (hu : u ∈ G.bfsVisited s k)
    (hadj : G.Adj u v) : v ∈ G.bfsVisited s (k + 1) := by
  induction k generalizing u with
  | zero =>
    rw [bfsVisited_succ, Finset.mem_union]
    by_cases hv : v ∈ G.bfsVisited s 0
    · exact Or.inl hv
    · exact Or.inr ((mem_bfsLayer_succ 0).2
        ⟨⟨u, mem_bfsLayer_zero.2 (mem_bfsVisited_zero.1 hu), hadj⟩, hv⟩)
  | succ k ih =>
    rw [bfsVisited_succ, Finset.mem_union] at hu
    rcases hu with hu | hu
    · exact bfsVisited_subset_succ (k + 1) (ih hu hadj)
    · rw [bfsVisited_succ, Finset.mem_union]
      by_cases hv : v ∈ G.bfsVisited s (k + 1)
      · exact Or.inl hv
      · exact Or.inr ((mem_bfsLayer_succ (k + 1)).2 ⟨⟨u, hu, hadj⟩, hv⟩)

/-- The endpoint of a realized vertex sequence of length `ℓ` starting at `s` is visited
within `ℓ` rounds. -/
theorem mem_bfsVisited_of_isVertexSeqIn {w : VertexSeq α} (hw : G.IsVertexSeqIn w)
    (hhead : w.head = s) : w.tail ∈ G.bfsVisited s w.length := by
  induction hw with
  | singleton x hx =>
    rw [VertexSeq.head_singleton] at hhead
    subst hhead
    exact mem_bfsVisited_zero.2 ⟨rfl, hx⟩
  | cons w u hw hadj ih =>
    rw [VertexSeq.head_cons] at hhead
    rw [VertexSeq.tail_cons, VertexSeq.length, Nat.add_comm]
    exact mem_bfsVisited_succ_of_adj (ih hhead) hadj

/-! ## Termination: at most `|V(G)|` layers are non-empty -/

/-- Once a layer is empty, so is the next. -/
lemma bfsLayer_succ_eq_empty {k : ℕ} (h : G.bfsLayer s k = ∅) :
    G.bfsLayer s (k + 1) = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv => by
    obtain ⟨⟨u, hu, -⟩, -⟩ := (mem_bfsLayer_succ k).1 hv
    simp [h] at hu

/-- A non-empty layer is preceded by a non-empty layer. -/
lemma nonempty_bfsLayer_of_succ {k : ℕ} (h : (G.bfsLayer s (k + 1)).Nonempty) :
    (G.bfsLayer s k).Nonempty := by
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty] at hcon
  exact h.ne_empty (bfsLayer_succ_eq_empty hcon)

/-- If the `k`-th layer is non-empty then at least `k + 1` vertices have been visited:
each of the layers `0, …, k` contributed a new one. -/
lemma succ_le_card_bfsVisited {k : ℕ} (h : (G.bfsLayer s k).Nonempty) :
    k + 1 ≤ (G.bfsVisited s k).card := by
  induction k with
  | zero => exact Finset.card_pos.2 (h.mono (bfsLayer_subset_bfsVisited 0))
  | succ k ih =>
    have hk := ih (nonempty_bfsLayer_of_succ h)
    have hpos := Finset.card_pos.2 h
    rw [bfsVisited_succ, Finset.card_union_of_disjoint (disjoint_bfsLayer_succ_bfsVisited k).symm]
    omega

/-- The termination bound: a non-empty layer has index below `|V(G)|`. -/
theorem lt_card_of_nonempty_bfsLayer {k : ℕ} (h : (G.bfsLayer s k).Nonempty) :
    k < G.computeVertexFinset.card :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
    ((succ_le_card_bfsVisited h).trans
      (Finset.card_le_card (bfsVisited_subset_computeVertexFinset k)))

/-- Every visited vertex lies in a layer of index below `|V(G)|`. -/
lemma exists_bfsLayer_lt_card_of_mem_bfsVisited {k : ℕ} (hv : v ∈ G.bfsVisited s k) :
    ∃ j, j ≤ k ∧ j < G.computeVertexFinset.card ∧ v ∈ G.bfsLayer s j := by
  obtain ⟨j, hj, hvj⟩ := (mem_bfsVisited_iff k).1 hv
  exact ⟨j, hj, lt_card_of_nonempty_bfsLayer ⟨v, hvj⟩, hvj⟩

/-! ## Correctness -/

/-- **BFS computes reachability.** -/
@[simp] theorem mem_bfsReachableFinset_iff : v ∈ G.bfsReachableFinset s ↔ G.Reachable s v := by
  refine ⟨reachable_of_mem_bfsVisited, ?_⟩
  rintro ⟨w, hw, rfl, rfl⟩
  obtain ⟨j, -, hjlt, hvj⟩ :=
    exists_bfsLayer_lt_card_of_mem_bfsVisited (mem_bfsVisited_of_isVertexSeqIn hw rfl)
  exact bfsVisited_mono hjlt.le (bfsLayer_subset_bfsVisited j hvj)

/-- The reachable set, as a set, is the set of vertices reachable from `s`. -/
lemma coe_bfsReachableFinset :
    (G.bfsReachableFinset s : Set α) = {v | G.Reachable s v} :=
  Set.ext fun _ => by simp

/-- Reachability in a finite simple directed graph is decidable, by breadth-first search. -/
instance instDecidableReachable (u v : α) : Decidable (G.Reachable u v) :=
  decidable_of_iff _ mem_bfsReachableFinset_iff

/-- A vertex of the `k`-th layer is at distance at most `k`, by soundness. -/
lemma dist_le_of_mem_bfsLayer {k : ℕ} (hv : v ∈ G.bfsLayer s k) : G.dist s v ≤ k := by
  obtain ⟨w, hw, hhead, htail, hlen⟩ := exists_walk_of_mem_bfsLayer hv
  rw [← hlen]
  exact dist_le_length hw hhead htail

/-- A vertex of the `(k + 1)`-st layer is at distance more than `k`: by completeness, a
walk of length at most `k` would have had it visited within `k` rounds, but a new layer
avoids everything visited before it. -/
lemma lt_dist_of_mem_bfsLayer_succ {k : ℕ} (hv : v ∈ G.bfsLayer s (k + 1)) :
    (k : ℕ∞) < G.dist s v := by
  obtain ⟨-, hnot⟩ := (mem_bfsLayer_succ k).1 hv
  rw [← not_le]
  intro hle
  have hr : G.Reachable s v :=
    reachable_iff_dist_ne_top.2 (ne_top_of_le_ne_top (ENat.coe_ne_top k) hle)
  obtain ⟨w, hw, hhead, htail, hlen⟩ := dist_exists hr
  rw [← hlen, Nat.cast_le] at hle
  have htail' : w.val.tail = v := htail
  have hvis := mem_bfsVisited_of_isVertexSeqIn hw hhead
  rw [htail'] at hvis
  exact hnot (bfsVisited_mono hle hvis)

/-- A vertex of the `k`-th layer is at distance exactly `k`. -/
theorem dist_eq_of_mem_bfsLayer {k : ℕ} (hv : v ∈ G.bfsLayer s k) : G.dist s v = k := by
  refine le_antisymm (dist_le_of_mem_bfsLayer hv) ?_
  cases k with
  | zero => exact zero_le
  | succ k =>
    rw [Nat.cast_succ]
    exact (ENat.add_one_le_iff (ENat.coe_ne_top k)).2 (lt_dist_of_mem_bfsLayer_succ hv)

/-- **The layers are the spheres.** The `k`-th layer of the search from `s` is exactly the
set of vertices at distance `k` from `s`. -/
theorem mem_bfsLayer_iff_dist_eq (k : ℕ) : v ∈ G.bfsLayer s k ↔ G.dist s v = k := by
  refine ⟨dist_eq_of_mem_bfsLayer, fun hd => ?_⟩
  have hr : G.Reachable s v := reachable_iff_dist_ne_top.2 (by rw [hd]; exact ENat.coe_ne_top k)
  obtain ⟨w, hw, hhead, htail, -⟩ := dist_exists hr
  have htail' : w.val.tail = v := htail
  have hvis := mem_bfsVisited_of_isVertexSeqIn hw hhead
  rw [htail'] at hvis
  obtain ⟨j, -, hvj⟩ := (mem_bfsVisited_iff _).1 hvis
  have hjk : j = k := by exact_mod_cast (dist_eq_of_mem_bfsLayer hvj).symm.trans hd
  exact hjk ▸ hvj

/-! ## The list of layers -/

lemma length_bfsLayersFrom (m : ℕ) (S : BFSState α) : (G.bfsLayersFrom m S).length = m := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih => simp [bfsLayersFrom, ih]

/-- The `k`-th entry of the collected layers is the frontier after `k` rounds. -/
lemma getElem_bfsLayersFrom (m : ℕ) (S : BFSState α) {k : ℕ} (hk : k < m) :
    (G.bfsLayersFrom m S)[k]'(by rw [length_bfsLayersFrom]; exact hk) =
      ((G.bfsStep)^[k] S).frontier := by
  induction m generalizing S k with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [bfsLayersFrom, List.getElem_cons_succ, Function.iterate_succ_apply]
      exact ih _ (Nat.lt_of_succ_lt_succ hk)

@[simp] lemma length_bfsLayers : (G.bfsLayers s).length = G.computeVertexFinset.card :=
  length_bfsLayersFrom _ _

/-- The `k`-th collected layer is the `k`-th layer. -/
lemma getElem_bfsLayers {k : ℕ} (hk : k < G.computeVertexFinset.card) :
    (G.bfsLayers s)[k]'(by rw [length_bfsLayers]; exact hk) = G.bfsLayer s k :=
  getElem_bfsLayersFrom _ _ hk

/-- The collected layers are exactly the layers of index below `|V(G)|`. -/
lemma mem_bfsLayers_iff {L : Finset α} :
    L ∈ G.bfsLayers s ↔ ∃ k < G.computeVertexFinset.card, G.bfsLayer s k = L := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [length_bfsLayers] at hk
    exact ⟨k, hk, (getElem_bfsLayers hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by rw [length_bfsLayers]; exact hk, getElem_bfsLayers hk⟩

/-! ## The computed distance -/

/-- Two layers of different index are disjoint: the later one avoids everything visited
before it, and the earlier one has been visited. -/
lemma disjoint_bfsLayer_of_lt {j k : ℕ} (h : j < k) :
    Disjoint (G.bfsLayer s j) (G.bfsLayer s k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
  exact Finset.disjoint_of_subset_left
    ((bfsLayer_subset_bfsVisited j).trans (bfsVisited_mono (Nat.le_add_right j m)))
    (disjoint_bfsLayer_succ_bfsVisited (j + m)).symm

/-- A vertex lies in at most one layer. -/
lemma eq_of_mem_bfsLayer {j k : ℕ} (hj : v ∈ G.bfsLayer s j) (hk : v ∈ G.bfsLayer s k) :
    j = k := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact Finset.disjoint_left.1 (disjoint_bfsLayer_of_lt h) hj hk
  · exact Finset.disjoint_left.1 (disjoint_bfsLayer_of_lt h) hk hj

/-- The computed distance is `k` exactly when `v` lies in the `k`-th layer. -/
theorem bfsDist_eq_coe_iff {k : ℕ} : G.bfsDist s v = k ↔ v ∈ G.bfsLayer s k := by
  unfold bfsDist
  rcases hfind : (G.bfsLayers s).findIdx? (fun L => decide (v ∈ L)) with _ | j
  · simp only [ENat.top_ne_coe, false_iff]
    intro hv
    have hlt := lt_card_of_nonempty_bfsLayer ⟨v, hv⟩
    have := List.findIdx?_eq_none_iff.1 hfind _ (mem_bfsLayers_iff.2 ⟨k, hlt, rfl⟩)
    simp [hv] at this
  · obtain ⟨hj, hvj, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
    rw [length_bfsLayers] at hj
    rw [getElem_bfsLayers hj, decide_eq_true_iff] at hvj
    simp only [Nat.cast_inj]
    exact ⟨fun h => h ▸ hvj, fun hk => eq_of_mem_bfsLayer hvj hk⟩

/-- The computed distance is infinite exactly when no layer contains `v`. -/
theorem bfsDist_eq_top_iff_forall : G.bfsDist s v = ⊤ ↔ ∀ k, v ∉ G.bfsLayer s k := by
  constructor
  · intro htop k hv
    have := bfsDist_eq_coe_iff.2 hv
    rw [htop] at this
    exact ENat.top_ne_coe k this
  · intro h
    unfold bfsDist
    rcases hfind : (G.bfsLayers s).findIdx? (fun L => decide (v ∈ L)) with _ | j
    · rfl
    · obtain ⟨hj, hvj, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
      rw [length_bfsLayers] at hj
      rw [getElem_bfsLayers hj, decide_eq_true_iff] at hvj
      exact absurd hvj (h j)

/-- **BFS computes the distance.** -/
theorem bfsDist_eq_dist : G.bfsDist s v = G.dist s v := by
  by_cases hr : G.Reachable s v
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (reachable_iff_dist_ne_top.1 hr)
    rw [← hk]
    exact bfsDist_eq_coe_iff.2 ((mem_bfsLayer_iff_dist_eq k).2 hk.symm)
  · rw [dist_eq_top_iff.2 hr]
    exact bfsDist_eq_top_iff_forall.2 fun k hk =>
      hr (reachable_of_mem_bfsVisited (bfsLayer_subset_bfsVisited k hk))

/-- The distance is infinite exactly when BFS never reaches the vertex. -/
theorem bfsDist_eq_top_iff : G.bfsDist s v = ⊤ ↔ v ∉ G.bfsReachableFinset s := by
  rw [bfsDist_eq_dist, dist_eq_top_iff, mem_bfsReachableFinset_iff]

/-! ## Smoke tests

Concrete evaluation on a small directed graph, confirming that the search really reduces
in the kernel. As in `AlgoLib.Algorithms.Graph.Connectivity.Basic`, the `Fintype` and
`DecidablePred` instances of a concrete graph have to be given by hand. -/

section Examples

/-- The directed path `0 → 1 → 2`, with the arc `2 → 0` closing a cycle, and an isolated
vertex `3`. -/
private def cycleG : SimpleDiGraph (Fin 4) where
  vertexSet := {0, 1, 2, 3}
  edgeSet := {(0, 1), (1, 2), (2, 0)}
  incidence' := by decide
  loopless' := by decide

private instance : Fintype cycleG.vertexSet :=
  inferInstanceAs (Fintype ({0, 1, 2, 3} : Set (Fin 4)))

private instance : DecidablePred (· ∈ cycleG.edgeSet) :=
  inferInstanceAs (DecidablePred (· ∈ ({(0, 1), (1, 2), (2, 0)} : Set (Fin 4 × Fin 4))))

example : cycleG.bfsLayer 0 0 = {0} := by decide
example : cycleG.bfsLayer 0 1 = {1} := by decide
example : cycleG.bfsLayer 0 2 = {2} := by decide
example : cycleG.bfsLayer 0 3 = ∅ := by decide
example : cycleG.bfsReachableFinset 0 = {0, 1, 2} := by decide
example : cycleG.bfsReachableFinset 3 = {3} := by decide
example : cycleG.bfsLayers 0 = [{0}, {1}, {2}, ∅] := by decide
example : cycleG.bfsDist 0 2 = 2 := by decide
example : cycleG.bfsDist 2 1 = 2 := by decide
example : cycleG.bfsDist 0 3 = ⊤ := by decide
example : cycleG.Reachable 1 0 := by decide
example : ¬ cycleG.Reachable 0 3 := by decide

-- …and therefore `dist 0 2 = 2`, through the agreement theorem.
example : cycleG.dist 0 2 = 2 := by
  rw [← bfsDist_eq_dist]; decide

end Examples

end SimpleDiGraph

end AlgoLib
