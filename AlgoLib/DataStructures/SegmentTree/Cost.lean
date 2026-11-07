/-
Copyright (c) 2026 Tomás Hoch, Nicolas Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomás Hoch, Nicolas Alvarez
-/
import AlgoLib.DataStructures.SegmentTree.Basic
import Mathlib.Data.Nat.Log

/-!
# Complexity of segment tree operations

Bounds on the `.time` field of the operations defined in
`AlgoLib.DataStructures.SegmentTree.Basic`. Since those operations are defined *once*, in
CSLib's cost monad `Cslib.Algorithms.Lean.TimeM ℕ`, the bounds below speak about exactly the
algorithms that were verified there — there is no second definition that could drift.

## Cost model

We count **node visits**: each `✓` corresponds to reaching a node, deciding one comparison
on ℕ and performing at most one `+` of the monoid.

WARNING. This assumes `(+ : α → α → α)` is O(1). True for `ℕ`, `ℤ`, `Fin n`, `Float` and
the like. NOT true for monoids such as `List β` under `++` or `Multiset β`, where the
operation is linear in the accumulator; there one would have to charge inside `+` and the
bounds below are false. This assumption is external to the formal development.

## Main definitions

* `SegmentTree.height`: the metric in which path-following bounds are stated.

## Main results

* `SegmentTree.height_build`: a built tree has height exactly `⌈log₂ n⌉`.
* `SegmentTree.height_update`: `update` preserves the height, so the bounds below hold
  along any sequence of updates.
* `SegmentTree.updateT_time_le`: `update` costs at most `height + 1` node visits.
* `SegmentTree.updateT_build_time_le`: consequently `update` on a built tree is
  `O(log n)`.
* `SegmentTree.queryT_time_le`: `query` costs at most `4 * height + 1` node visits.
* `SegmentTree.queryT_build_time_le`: consequently `query` on a built tree is
  `O(log n)`.
* `SegmentTree.buildT_time`: `build` on an array of size `n` visits exactly `2 * n - 1`
  nodes.
-/

namespace SegmentTree

open Cslib.Algorithms.Lean

variable {α : Type*}

/-! ### Height -/

/-- Height of the tree: the natural metric for `update` and `query`, which follow paths
from the root. A leaf has height `0`. -/
@[simp] def height : SegmentTree α → ℕ
  | leaf _ _ _ => 0
  | node _ l r _ _ => max l.height r.height + 1

variable [AddMonoid α]

/-! ### Height of a built tree

`Valid` does not imply balance — a valid tree may be a comb of height `n`. Balance is a
property of `build`, which splits at `mid = (lo + hi) / 2`, so these are the only lemmas
in this file that mention `buildAux`.

Note the **ceiling** logarithm. The recurrence is `T(n) = max (T ⌊n/2⌋) (T ⌈n/2⌉) + 1`,
and it is the `⌈n/2⌉` side that dominates, so the floor logarithm is *not* a bound:
already at `n = 3` the tree has height `2` while `Nat.log 2 3 = 1`. -/

/-- The subtree covering `[lo, hi)` has height exactly `⌈log₂ (hi - lo)⌉`. -/
theorem height_buildAux (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size) :
    (buildAux arr l h h1 hle).height = Nat.clog 2 (h - l) := by
  unfold buildAux
  fun_induction buildAuxT arr l h h1 hle with
  | case1 l h h1 hle hone => simp [show h - l = 1 by omega]
  | case2 l h h1 hle hone mid hlm hmh ihL ihR =>
      have hmid : mid = (l + h) / 2 := rfl
      have harg : (h - l + 2 - 1) / 2 = h - mid := by omega
      have hrec : Nat.clog 2 (h - l) = Nat.clog 2 (h - mid) + 1 := by
        rw [Nat.clog_of_two_le (by omega) (by omega), harg]
      have hmono : Nat.clog 2 (mid - l) ≤ Nat.clog 2 (h - mid) :=
        Nat.clog_mono_right 2 (by omega)
      simp only [TimeM.ret_bind, TimeM.ret_pure, height, ihL, ihR]
      omega

/-- `build` produces a balanced tree: height exactly `⌈log₂ n⌉` on an array of size
`n`. This is what turns the `height` bounds of this file into `O(log n)` bounds. -/
theorem height_build (arr : Array α) (h : 0 < arr.size) :
    (build arr h).height = Nat.clog 2 arr.size := by
  simp [build, buildT, buildAuxT_ret, height_buildAux]

/-! ### Shape preservation

`update` only rewrites cached values along a path, so it does not change the height. This
is what lets the `O(log n)` bounds below hold along any sequence of operations started
from `build`, not only for a single operation on a freshly built tree. -/

@[simp] theorem height_update (st : SegmentTree α) (i : ℕ) (v : α) :
    (st.update i v).height = st.height := by
  induction st with
  | leaf w l h => simp
  | node w left right l h ihl ihr =>
      by_cases hil : i < left.hi
      · simp [update_node_of_lt hil, ihl]
      · simp [update_node_of_le hil, ihr]

/-! ### Cost of `update` -/

/-- A point update visits at most one node per level. -/
theorem updateT_time_le (st : SegmentTree α) (i : ℕ) (v : α) :
    (st.updateT i v).time ≤ st.height + 1 := by
  induction st with
  | leaf w l h => simp [updateT]
  | node w left right l h ihl ihr =>
      by_cases hil : i < left.hi <;> grind [updateT, height]

/-- Correctness and complexity of a point update on a built tree, in one statement. -/
theorem updateT_build_spec (arr : Array α) (h₀ : 0 < arr.size) {i : ℕ}
    (hia : i < arr.size) (v : α) (j : ℕ) :
    ((build arr h₀).updateT i v).ret.valAt j
        = (if j = i then v else (build arr h₀).valAt j)
      ∧ ((build arr h₀).updateT i v).time ≤ (build arr h₀).height + 1 := by
  refine ⟨?_, updateT_time_le _ i v⟩
  rw [updateT_ret]
  exact valAt_update (valid_build arr h₀) v
    (by rw [lo_build]; exact Nat.zero_le i) (by rw [hi_build]; exact hia) j

/-- A point update on a built tree is `O(log n)`: at most `⌈log₂ n⌉ + 1` node visits on an
array of size `n`. -/
theorem updateT_build_time_le (arr : Array α) (h : 0 < arr.size) (i : ℕ) (v : α) :
    ((build arr h).updateT i v).time ≤ Nat.clog 2 arr.size + 1 :=
  (updateT_time_le _ i v).trans (Nat.add_le_add_right (height_build arr h).le 1)

/-! ### Cost of `query`

`query` branches into both children, so the naive induction gives `T(d) ≤ 2 T(d-1) + 1`,
which is exponential and useless. The real argument splits into two regimes: below the
(unique) node at which the query range splits in two, every descent is *one-sided* — the
range covers one end of the subtree — with recurrence `T₁(d) ≤ T₁(d-1) + 2`. The
one-sided lemmas require `Valid st`, since the argument uses `left.hi = right.lo` to
locate `mid`. Note that `queryT` also charges a tick on disjoint and fully covered
nodes — in particular a leaf costs `1` while its height is `0`, hence the `+ 1`s. -/

/-! #### Cost equation lemmas for `queryT`

The time analogue of the equation lemmas for `query` in
`AlgoLib.DataStructures.SegmentTree.Basic`: one lemma per branch of `queryT`, so the bounds
below never unfold the cost monad. -/

@[simp] lemma queryT_time_leaf (v : α) (l h ql qr : ℕ) :
    ((leaf v l h).queryT ql qr).time = 1 := rfl

lemma queryT_time_node_of_disjoint {v : α} {left right : SegmentTree α} {l h ql qr : ℕ}
    (hd : h ≤ ql ∨ qr ≤ l) :
    ((node v left right l h).queryT ql qr).time = 1 := by
  rw [queryT, if_pos hd]
  rfl

lemma queryT_time_node_of_covered {v : α} {left right : SegmentTree α} {l h ql qr : ℕ}
    (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ql ≤ l ∧ h ≤ qr) :
    ((node v left right l h).queryT ql qr).time = 1 := by
  rw [queryT, if_neg hd, if_pos hc]
  rfl

lemma queryT_time_node_of_partial {v : α} {left right : SegmentTree α} {l h ql qr : ℕ}
    (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ¬ (ql ≤ l ∧ h ≤ qr)) :
    ((node v left right l h).queryT ql qr).time
      = (left.queryT ql qr).time + (right.queryT ql qr).time + 1 := by
  rw [queryT, if_neg hd, if_neg hc]
  grind

/-- A query whose range misses the subtree resolves at the root: exactly one node
visit, on any tree. -/
lemma queryT_time_of_disjoint {st : SegmentTree α} {ql qr : ℕ}
    (hd : st.hi ≤ ql ∨ qr ≤ st.lo) :
    (st.queryT ql qr).time = 1 := by
  cases st with
  | leaf v l h => exact queryT_time_leaf v l h ql qr
  | node v left right l h => exact queryT_time_node_of_disjoint (by simpa using hd)

/-- A query whose range covers the subtree resolves at the root (the cached aggregate is
returned): exactly one node visit, on any tree. -/
lemma queryT_time_of_covered {st : SegmentTree α} {ql qr : ℕ}
    (h₁ : ql ≤ st.lo) (h₂ : st.hi ≤ qr) :
    (st.queryT ql qr).time = 1 := by
  cases st with
  | leaf v l h => exact queryT_time_leaf v l h ql qr
  | node v left right l h =>
      by_cases hd : h ≤ ql ∨ qr ≤ l
      · exact queryT_time_node_of_disjoint hd
      · exact queryT_time_node_of_covered hd ⟨by simpa using h₁, by simpa using h₂⟩

/-- One-sided query, left end: if the range starts at or before the subtree, the query
costs at most `2 * height + 1` node visits.

At a partially covered node the split point `mid = left.hi` decides which side recurses: if
`qr ≤ mid` the right child is disjoint and the descent into the left child is again
one-sided; otherwise the left child is covered and the descent goes right, where
`ql ≤ lo ≤ mid = right.lo` still holds. -/
theorem queryT_time_le_of_le_lo {st : SegmentTree α} (hv : Valid st) {ql qr : ℕ}
    (h : ql ≤ st.lo) :
    (st.queryT ql qr).time ≤ 2 * st.height + 1 := by
  induction hv with
  | @leaf v l hh h_len => simp
  | @node v left right l hh h_val h_lo h_mid h_hi hl hr ih_L ih_R =>
      simp only [lo, height] at h ⊢
      by_cases hd : hh ≤ ql ∨ qr ≤ l
      · simp [queryT_time_node_of_disjoint hd]
      by_cases hc : ql ≤ l ∧ hh ≤ qr
      · simp [queryT_time_node_of_covered hd hc]
      · rw [queryT_time_node_of_partial hd hc]
        have hL := hl.lo_lt_hi
        by_cases hqr : qr ≤ left.hi <;>
          grind [queryT_time_of_disjoint, queryT_time_of_covered]

/-- One-sided query, right end: if the range ends at or after the subtree, the query
costs at most `2 * height + 1` node visits.

At a partially covered node the split point `mid = left.hi` decides which side recurses: if
`mid ≤ ql` the left child is disjoint and the descent goes right, where
`right.hi = hi ≤ qr` still holds; otherwise the right child is covered and the descent goes
left, where `left.hi = mid ≤ right.hi ≤ qr`. -/
theorem queryT_time_le_of_hi_le {st : SegmentTree α} (hv : Valid st) {ql qr : ℕ}
    (h : st.hi ≤ qr) :
    (st.queryT ql qr).time ≤ 2 * st.height + 1 := by
  induction hv with
  | @leaf v l hh h_len => simp
  | @node v left right l hh h_val h_lo h_mid h_hi hl hr ih_L ih_R =>
      simp only [hi, height] at h ⊢
      by_cases hd : hh ≤ ql ∨ qr ≤ l
      · simp [queryT_time_node_of_disjoint hd]
      by_cases hc : ql ≤ l ∧ hh ≤ qr
      · simp [queryT_time_node_of_covered hd hc]
      · rw [queryT_time_node_of_partial hd hc]
        have hR := hr.lo_lt_hi
        by_cases hql : left.hi ≤ ql <;>
          grind [queryT_time_of_disjoint, queryT_time_of_covered]

/-- A range query visits `O(height)` nodes: below the unique node at which the range
splits, both descents are one-sided. -/
theorem queryT_time_le {st : SegmentTree α} (hv : Valid st) (ql qr : ℕ) :
    (st.queryT ql qr).time ≤ 4 * st.height + 1 := by
  induction hv with
  | @leaf v l h h_len => simp
  | @node v left right l h h_val h_lo h_mid h_hi hl hr ih_L ih_R =>
      simp only [height]
      by_cases hd : h ≤ ql ∨ qr ≤ l
      · simp [queryT_time_node_of_disjoint hd]
      by_cases hc : ql ≤ l ∧ h ≤ qr
      · simp [queryT_time_node_of_covered hd hc]
      · rw [queryT_time_node_of_partial hd hc]
        grind [queryT_time_of_disjoint, queryT_time_le_of_hi_le, queryT_time_le_of_le_lo]

/-- A range query on a built tree is `O(log n)` on an array of size `n`. -/
theorem queryT_build_time_le (arr : Array α) (h : 0 < arr.size) (ql qr : ℕ) :
    ((build arr h).queryT ql qr).time ≤ 4 * (Nat.clog 2 arr.size + 1) := by
  have hle := queryT_time_le (valid_build arr h) ql qr
  rw [height_build] at hle
  omega

/-! ### Cost of `build`

Unlike `query` and `update`, `build` touches every node, so the bound is linear rather
than logarithmic: a tree over `n` leaves has `n - 1` internal nodes, hence `2 * n - 1`
node visits. By strong induction on `hi - lo`, which is what `fun_induction` on
`buildAuxT` performs. -/

/-- Building the subtree covering `[lo, hi)` visits exactly `2 * (hi - lo) - 1` nodes. -/
theorem buildAuxT_time (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size) :
    (buildAuxT arr l h h1 hle).time = 2 * (h - l) - 1 := by
  fun_induction buildAuxT arr l h h1 hle with
  | case1 l h h1 hle hone => simp [show h - l = 1 by omega]
  | case2 l h h1 hle hone mid hlm hmh ihL ihR =>
      have hmid : mid = (l + h) / 2 := rfl
      simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ihL, ihR]
      omega

/-- Building a tree over an array of size `n` visits exactly `2 * n - 1` nodes. -/
theorem buildT_time (arr : Array α) (h : 0 < arr.size) :
    (buildT arr h).time = 2 * arr.size - 1 := by
  simp [buildT, buildAuxT_time]

end SegmentTree
