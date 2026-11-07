/-
Copyright (c) 2026 Tomás Hoch, Nicolas Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomás Hoch, Nicolas Alvarez
-/
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Algebra.BigOperators.Group.List.Basic
import AlgoLib.Mathlib.Data.List.Intervals

/-!
# Segment trees

A `SegmentTree α` over an additive monoid `α` is a binary tree caching, at every subtree,
the aggregate (sum) of the values stored on the half-open interval `[lo, hi)` of indices
that the subtree covers.

## Main definitions

* `SegmentTree.build`: build a segment tree from a nonempty `Array α`.
* `SegmentTree.queryT`: range query in the cost monad `TimeM ℕ`.
* `SegmentTree.query`: the pure projection of `queryT`; the sum of the values on
  `[ql, qr)`, in `O(log n)` on balanced trees.
* `SegmentTree.updateT`: point update in the cost monad `TimeM ℕ`, recomputing the
  aggregates along the path.
* `SegmentTree.update`: the pure projection of `updateT`; the function one reasons about.
* `SegmentTree.valAt`: the array that a tree logically represents.
* `SegmentTree.Valid`: the structural invariant (contiguous, correctly aggregated intervals).

## Main results

* `SegmentTree.valid_build`: `build` produces a valid tree.
* `SegmentTree.query_build`: `query` on a built tree computes the sum of the array
  on the requested range.
* `SegmentTree.Valid.update`: `update` preserves validity.
* `SegmentTree.valAt_update`: `update` sets exactly one index of the represented array.
* `SegmentTree.query_update_build`: `query` after a point `update` computes the sum of
  the updated array on the requested range.

## Implementation notes

Aggregation only assumes `AddMonoid α` (no commutativity), hence sums are stated over
`List.Ico` rather than `Finset.Ico`.

Operations are written **once**, in CSLib's cost monad `Cslib.Algorithms.Lean.TimeM ℕ`
(the writer monad over `(ℕ, +, 0)`), and their pure counterparts are defined as
projections (`update := fun st i v => (st.updateT i v).ret`). This keeps a
single source of truth: there is no separate "cost version" that could silently drift
away from the algorithm being verified. Reasoning about the pure functions proceeds
through the exported equation lemmas (`query_leaf`, `query_node_of_disjoint`,
`query_node_of_covered`, `query_node_of_partial`, `update_leaf`, `update_node_of_lt`,
`update_node_of_le`) rather than by unfolding the definitions, so proofs read the same as
if `query` and `update` had been defined by direct pattern matching.

This discipline covers all three operations: `build`, `query` and `update` are the
projections of `buildT`, `queryT` and `updateT` respectively.

Complexity bounds live in `AlgoLib.DataStructures.SegmentTree.Cost` and speak about the
`.time` field of the same definitions used here.
-/

/-- A segment tree over `α`: a binary tree caching, at every subtree, the aggregate of the
values stored on the half-open interval `[lo, hi)` of indices covered by that subtree. -/
inductive SegmentTree (α : Type*) where
  /-- A leaf covering the singleton interval `[lo, hi) = [lo, lo + 1)`. -/
  | leaf (val : α) (lo hi : ℕ) : SegmentTree α
  /-- An internal node covering `[lo, hi)`, with `val` the aggregate of both children. -/
  | node (val : α) (left right : SegmentTree α) (lo hi : ℕ) : SegmentTree α

namespace SegmentTree

open Cslib.Algorithms.Lean

variable {α : Type*}

/-! ### Bounds and root value -/

/-- The lower bound of the range covered by the tree. -/
@[simp] def lo : SegmentTree α → ℕ
  | leaf _ l _ => l
  | node _ _ _ l _ => l

/-- The upper bound (exclusive) of the range covered by the tree. -/
@[simp] def hi : SegmentTree α → ℕ
  | leaf _ _ h => h
  | node _ _ _ _ h => h

/-- The cached aggregate at the root. -/
def rootValue : SegmentTree α → α
  | leaf v _ _ => v
  | node v _ _ _ _ => v

/- Everything below aggregates values, so we fix a monoid structure once.
`lo`, `hi` and `rootValue` above stay instance-free on purpose. -/
variable [AddMonoid α]

/-! ### Construction

As with `query` and `update` below, the construction is written once, in the cost monad,
charging one `✓` per node created; `buildAux`/`build` are its pure projections, which is
what the correctness lemmas speak about. `AlgoLib.DataStructures.SegmentTree.Cost` proves
the cost bound on `(buildT ..).time`. -/

/-- Build the subtree of `arr` covering `[lo, hi)` in the cost monad, charging one `✓`
per node created. -/
def buildAuxT (arr : Array α) (lo hi : ℕ) (h : lo < hi) (hle : hi ≤ arr.size) :
    TimeM ℕ (SegmentTree α) :=
  if h1 : hi - lo = 1 then
    do ✓ return leaf (arr[lo]'(by omega)) lo hi
  else
    let mid := (lo + hi) / 2
    have hlm : lo < mid := by omega
    have hmh : mid < hi := by omega
    do
      let left ← buildAuxT arr lo mid hlm (by omega)
      let right ← buildAuxT arr mid hi hmh hle
      ✓ return node (left.rootValue + right.rootValue) left right lo hi
  termination_by hi - lo
  decreasing_by all_goals omega

/-- Build a segment tree covering all of `arr`, in the cost monad. -/
def buildT (arr : Array α) (h : 0 < arr.size) : TimeM ℕ (SegmentTree α) :=
  buildAuxT arr 0 arr.size h le_rfl

/-- Build the subtree of `arr` covering the half-open interval `[lo, hi)`: the pure
projection of `buildAuxT`. -/
def buildAux (arr : Array α) (lo hi : ℕ) (h : lo < hi) (hle : hi ≤ arr.size) :
    SegmentTree α :=
  (buildAuxT arr lo hi h hle).ret

/-- Build a segment tree covering all of `arr`: the pure projection of `buildT`. -/
def build (arr : Array α) (h : 0 < arr.size) : SegmentTree α :=
  (buildT arr h).ret

@[simp] theorem buildAuxT_ret (arr : Array α) (lo hi : ℕ) (h : lo < hi)
    (hle : hi ≤ arr.size) : (buildAuxT arr lo hi h hle).ret = buildAux arr lo hi h hle :=
  rfl

@[simp] theorem buildT_ret (arr : Array α) (h : 0 < arr.size) :
    (buildT arr h).ret = build arr h :=
  rfl

/-! ### Range query

As with `update` below, the algorithm is written once in `TimeM ℕ` and `query` is its pure
projection. Each `✓` marks one node visit. -/

/-- Range query in the cost monad: the sum of the values on `[ql, qr)`, together with the
number of nodes visited. `O(log n)` on balanced trees. -/
def queryT (st : SegmentTree α) (ql qr : ℕ) : TimeM ℕ α :=
  match st with
  | leaf val lo hi => do ✓ return (if ql ≤ lo ∧ hi ≤ qr then val else 0)
  | node val left right lo hi =>
      if hi ≤ ql ∨ qr ≤ lo then do ✓ return (0 : α)
      else if ql ≤ lo ∧ hi ≤ qr then do ✓ return val
      else do
        let a ← left.queryT ql qr
        let b ← right.queryT ql qr
        ✓ return (a + b)

/-- The sum of the values on `[ql, qr)`: the pure projection of `queryT`. -/
def query (st : SegmentTree α) (ql qr : ℕ) : α := (st.queryT ql qr).ret

/-! #### Equation lemmas for `query`

These recover the pattern-matching view of `query`. Prefer them over `unfold query`:
they keep proofs independent of how the cost monad desugars. -/

@[simp] theorem queryT_ret (st : SegmentTree α) (ql qr : ℕ) :
    (st.queryT ql qr).ret = st.query ql qr := rfl

@[simp] lemma query_leaf (val : α) (lo hi ql qr : ℕ) :
    (leaf val lo hi).query ql qr = if ql ≤ lo ∧ hi ≤ qr then val else 0 := rfl

lemma query_node_of_disjoint {v : α} {left right : SegmentTree α} {l h ql qr : ℕ}
    (hd : h ≤ ql ∨ qr ≤ l) :
    (node v left right l h).query ql qr = 0 := by
  rw [query, queryT, if_pos hd]
  rfl

lemma query_node_of_covered {v : α} {left right : SegmentTree α} {l h ql qr : ℕ}
    (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ql ≤ l ∧ h ≤ qr) :
    (node v left right l h).query ql qr = v := by
  rw [query, queryT, if_neg hd, if_pos hc]
  rfl

lemma query_node_of_partial {v : α} {left right : SegmentTree α} {l h ql qr : ℕ}
    (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ¬ (ql ≤ l ∧ h ≤ qr)) :
    (node v left right l h).query ql qr
      = left.query ql qr + right.query ql qr := by
  rw [query, queryT, if_neg hd, if_neg hc]
  rfl

/-- The value logically stored at index `i` (and `0` outside the tree's range):
the array that the tree represents. -/
def valAt (st : SegmentTree α) (i : ℕ) : α :=
  match st with
  | leaf val lo _ => if lo = i then val else 0
  | node _ left right _ _ => if i < left.hi then valAt left i else valAt right i

/-! ### Point update

The algorithm is defined once, in `TimeM ℕ`, and `update` is its pure projection. Each `✓`
marks one node visit; see `AlgoLib.DataStructures.SegmentTree.Cost` for the resulting
complexity bound.

Note that the branch on `i < left.hi` sits *outside* the `do` block. This matters for the
cost analysis: with the test inside the `let`s, both recursive calls would appear in the
term and `bind` would charge for both, yielding a bound exponential in the height instead
of linear. -/
def updateT : SegmentTree α → ℕ → α → TimeM ℕ (SegmentTree α)
  | leaf w l h, i, v => do ✓ return (leaf (if l = i then v else w) l h)
  | node _ left right l h, i, v =>
      if i < left.hi then do
        let left' ← left.updateT i v
        ✓ return (node (left'.rootValue + right.rootValue) left' right l h)
      else do
        let right' ← right.updateT i v
        ✓ return (node (left.rootValue + right'.rootValue) left right' l h)

/-- Point update: `st.update i v` sets the value at index `i` to `v`, recomputing the
cached aggregates along the path to `i`. Indices outside `[st.lo, st.hi)` are left
unchanged. `O(log n)` on balanced trees. -/
def update (st : SegmentTree α) (i : ℕ) (v : α) : SegmentTree α :=
  (st.updateT i v).ret

/-! #### Equation lemmas for `update`

These recover the pattern-matching view of `update`. Prefer them over `unfold update`:
they keep proofs independent of how the cost monad desugars. -/

@[simp] theorem updateT_ret (st : SegmentTree α) (i : ℕ) (v : α) :
    (st.updateT i v).ret = st.update i v := rfl

@[simp] lemma update_leaf (w : α) (l h i : ℕ) (v : α) :
    (leaf w l h).update i v = leaf (if l = i then v else w) l h := rfl

lemma update_node_of_lt {w : α} {left right : SegmentTree α} {l h i : ℕ} {v : α}
    (hil : i < left.hi) :
    (node w left right l h).update i v =
      node ((left.update i v).rootValue + right.rootValue) (left.update i v) right l h := by
  rw [update, updateT, if_pos hil]
  rfl

lemma update_node_of_le {w : α} {left right : SegmentTree α} {l h i : ℕ} {v : α}
    (hil : ¬ i < left.hi) :
    (node w left right l h).update i v =
      node (left.rootValue + (right.update i v).rootValue) left (right.update i v) l h := by
  rw [update, updateT, if_neg hil]
  rfl

@[simp] lemma lo_update (st : SegmentTree α) (i : ℕ) (v : α) :
    (st.update i v).lo = st.lo := by
  cases st <;> grind [update_leaf, update_node_of_lt, update_node_of_le, lo]

@[simp] lemma hi_update (st : SegmentTree α) (i : ℕ) (v : α) :
    (st.update i v).hi = st.hi := by
  cases st <;> grind [update_leaf, update_node_of_lt, update_node_of_le, hi]

/-! ### The validity invariant -/

/-- Structural invariant of a segment tree: leaves cover singleton intervals, children
cover contiguous intervals partitioning the parent's, and every cached value is the sum
of the children's. -/
inductive Valid : SegmentTree α → Prop
  | leaf {v l h} (h_len : h = l + 1) : Valid (leaf v l h)
  | node {v left right l h}
      (h_val : v = left.rootValue + right.rootValue)
      (h_lo : l = left.lo)
      (h_mid : left.hi = right.lo)
      (h_hi : h = right.hi)
      (hl : Valid left) (hr : Valid right) : Valid (node v left right l h)

lemma Valid.lo_lt_hi {st : SegmentTree α} (h : Valid st) : st.lo < st.hi := by
  induction h <;> simp <;> omega

@[simp] lemma valAt_leaf (val : α) (lo hi i : ℕ) :
    (leaf val lo hi).valAt i = if lo = i then val else 0 := rfl

@[simp] lemma valAt_node_of_lt {v : α} {left right : SegmentTree α} {l h i : ℕ}
    (hil : i < left.hi) : (node v left right l h).valAt i = left.valAt i :=
  if_pos hil

@[simp] lemma valAt_node_of_hi_le {v : α} {left right : SegmentTree α} {l h i : ℕ}
    (hil : left.hi ≤ i) : (node v left right l h).valAt i = right.valAt i :=
  if_neg (Nat.not_lt.mpr hil)

lemma map_valAt_node_left {v : α} {left right : SegmentTree α} {l h a b : ℕ}
    (hb : b ≤ left.hi) :
    (List.Ico a b).map (node v left right l h).valAt = (List.Ico a b).map left.valAt :=
  List.map_congr_left fun _ hmem =>
    valAt_node_of_lt ((List.Ico.mem.mp hmem).2.trans_le hb)

lemma map_valAt_node_right {v : α} {left right : SegmentTree α} {l h a b : ℕ}
    (ha : left.hi ≤ a) :
    (List.Ico a b).map (node v left right l h).valAt = (List.Ico a b).map right.valAt :=
  List.map_congr_left fun _ hmem =>
    valAt_node_of_hi_le (ha.trans (List.Ico.mem.mp hmem).1)

/-- On a valid tree, the cached root value is the sum of the represented array over the
covered range. -/
lemma rootValue_eq_sum_valAt {st : SegmentTree α} (h : Valid st) :
    st.rootValue = ((List.Ico st.lo st.hi).map st.valAt).sum := by
  induction h with
  | @leaf v l h h_len =>
      subst h_len
      simp [rootValue]
  | @node v left right l h h_val h_lo h_mid h_hi hl hr ih_L ih_R =>
      simp only [rootValue, lo, hi]
      subst h_lo h_hi
      rw [← List.Ico.append_consecutive (m := left.hi) hl.lo_lt_hi.le (h_mid ▸ hr.lo_lt_hi.le),
        List.map_append, List.sum_append]
      nth_rw 1 [h_val]
      rw [ih_L, ih_R, ← h_mid, map_valAt_node_left le_rfl, map_valAt_node_right le_rfl]

/-! ### Correctness of `build` -/

@[simp] lemma lo_buildAux (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size) :
    (buildAux arr l h h1 hle).lo = l := by
  unfold buildAux
  fun_induction buildAuxT arr l h h1 hle <;> simp

@[simp] lemma hi_buildAux (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size) :
    (buildAux arr l h h1 hle).hi = h := by
  unfold buildAux
  fun_induction buildAuxT arr l h h1 hle <;> simp

@[simp] lemma lo_build (arr : Array α) (h : 0 < arr.size) : (build arr h).lo = 0 :=
  lo_buildAux arr 0 arr.size h le_rfl

@[simp] lemma hi_build (arr : Array α) (h : 0 < arr.size) : (build arr h).hi = arr.size :=
  hi_buildAux arr 0 arr.size h le_rfl

lemma valid_buildAux (arr : Array α) {l h : ℕ} {h1 : l < h} {hle : h ≤ arr.size} :
    Valid (buildAux arr l h h1 hle) := by
  unfold buildAux
  fun_induction buildAuxT arr l h h1 hle with
  | case1 l h h_less hle h_one => exact Valid.leaf (by omega)
  | case2 l h _ _ _ mid hlm hmh ihL ihR =>
      simp only [TimeM.ret_bind, TimeM.ret_pure, buildAuxT_ret]
      refine Valid.node rfl ?_ ?_ ?_ ihL ihR <;>
        simp only [lo_buildAux, hi_buildAux]

theorem valid_build (arr : Array α) (h : 0 < arr.size) : Valid (build arr h) :=
  valid_buildAux arr

lemma valAt_buildAux (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size)
    (i : ℕ) (h_in : l ≤ i ∧ i < h) :
    (buildAux arr l h h1 hle).valAt i = arr.getD i 0 := by
  unfold buildAux
  fun_induction buildAuxT arr l h h1 hle with
  | case1 l h h_less hle h_one =>
      obtain rfl : l = i := by omega
      simp [show l < arr.size by omega]
  | case2 l h _ _ _ mid hlm hmh ihL ihR =>
      simp only [TimeM.ret_bind, TimeM.ret_pure, buildAuxT_ret, valAt, hi_buildAux]
      split_ifs with go_left
      · exact ihL (by omega)
      · exact ihR (by omega)

/-- The tree built from `arr` represents exactly `arr`. -/
lemma valAt_build (arr : Array α) (h : 0 < arr.size) (i : ℕ) (h_in : i < arr.size) :
    (build arr h).valAt i = arr[i] :=
  (valAt_buildAux arr 0 arr.size h le_rfl i ⟨Nat.zero_le i, h_in⟩).trans
    (Array.getElem_eq_getD 0).symm

/-! ### Correctness of `query` -/

/-- On a valid tree, `query` computes the sum of the represented array over the
intersection of the tree's range with `[ql, qr)`. -/
theorem query_eq_sum_valAt {st : SegmentTree α} (h : Valid st) (ql qr : ℕ) :
    st.query ql qr = ((List.Ico (max st.lo ql) (min st.hi qr)).map st.valAt).sum := by
  induction h with
  | @leaf v l h h_len =>
      subst h_len
      rw [query_leaf]
      split_ifs with h_bounds
      · simp [show max l ql = l by omega, show min (l + 1) qr = l + 1 by omega]
      · simp [List.Ico.eq_nil_of_le (show min (l + 1) qr ≤ max l ql by omega)]
  | @node v left right l h h_val h_lo h_mid h_hi hl hr ih_L ih_R =>
      by_cases h_bounds : h ≤ ql ∨ qr ≤ l
      · rw [query_node_of_disjoint h_bounds]
        simp [List.Ico.eq_nil_of_le (show min h qr ≤ max l ql by omega)]
      by_cases h_full : ql ≤ l ∧ h ≤ qr
      · rw [query_node_of_covered h_bounds h_full]
        simpa [rootValue, show max l ql = l by omega, show min h qr = h by omega] using
          rootValue_eq_sum_valAt (.node h_val h_lo h_mid h_hi hl hr)
      · rw [query_node_of_partial h_bounds h_full]
        simp only [lo, hi]
        rw [ih_L, ih_R, h_lo, h_hi, ← h_mid,
          ← List.Ico.append_consecutive_max_min (n := left.lo) (l := right.hi)
            hl.lo_lt_hi.le (h_mid ▸ hr.lo_lt_hi.le),
          List.map_append, List.sum_append,
          map_valAt_node_left (min_le_left _ _), map_valAt_node_right (le_max_left _ _)]

/-- `query` on a built tree computes the sum of the array on the requested range. -/
theorem query_build (arr : Array α) (h : 0 < arr.size) (ql qr : ℕ) :
    (build arr h).query ql qr
      = ((List.Ico ql (min arr.size qr)).map (arr.getD · 0)).sum := by
  rw [query_eq_sum_valAt (valid_build arr h), lo_build, hi_build,
    show max 0 ql = ql from by omega]
  refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
  rw [List.Ico.mem] at ha
  exact valAt_buildAux arr 0 arr.size h le_rfl a ⟨Nat.zero_le a, by omega⟩

/-! ### Correctness of `update` -/

/-- `update` preserves the validity invariant. -/
protected lemma Valid.update {st : SegmentTree α} (hv : Valid st) (i : ℕ) (v : α) :
    Valid (st.update i v) := by
  induction hv with
  | @leaf w l h h_len => exact update_leaf w l h i v ▸ .leaf h_len
  | @node w left right l h h_val h_lo h_mid h_hi hl hr ihl ihr =>
      by_cases hil : i < left.hi
      · exact update_node_of_lt hil ▸ .node rfl (h_lo.trans (lo_update left i v).symm)
          ((hi_update left i v).trans h_mid) h_hi ihl hr
      · exact update_node_of_le hil ▸ .node rfl h_lo (h_mid.trans (lo_update right i v).symm)
          (h_hi.trans (hi_update right i v).symm) hl ihr

/-- `update` does not change the represented array away from the updated index. -/
lemma valAt_update_of_ne {st : SegmentTree α} {i j : ℕ} (hne : j ≠ i) (v : α) :
    (st.update i v).valAt j = st.valAt j := by
  induction st with
  | leaf w l h =>
      grind [update_leaf, valAt_leaf]
  | node w left right l h ihl ihr =>
      by_cases hil : i < left.hi
      · grind [update_node_of_lt hil, valAt, hi_update]
      · grind [update_node_of_le hil, valAt]

/-- On a valid tree, `update` stores the new value at the updated index. -/
lemma valAt_update_self {st : SegmentTree α} (hv : Valid st) {i : ℕ} (v : α) :
    st.lo ≤ i → i < st.hi → (st.update i v).valAt i = v := by
  induction hv with
  | @leaf w l h h_len =>
      grind [update_leaf, valAt_leaf, lo, hi]
  | @node w left right l h h_val h_lo h_mid h_hi hl hr ihl ihr =>
      intro h₁ h₂
      simp only [lo, hi] at h₁ h₂
      by_cases hil : i < left.hi
      · grind [update_node_of_lt hil, valAt, hi_update]
      · grind [update_node_of_le hil, valAt]

/-- On a valid tree, the array represented by `st.update i v` is that of `st` with the
value at index `i` replaced by `v`. -/
theorem valAt_update {st : SegmentTree α} (hv : Valid st) {i : ℕ} (v : α)
    (h₁ : st.lo ≤ i) (h₂ : i < st.hi) (j : ℕ) :
    (st.update i v).valAt j = if j = i then v else st.valAt j := by
  split_ifs with hji
  · subst hji
    exact valAt_update_self hv v h₁ h₂
  · exact valAt_update_of_ne hji v

/-- `query` after a point `update` computes the sum of the updated array on the
requested range. -/
theorem query_update_build (arr : Array α) (h₀ : 0 < arr.size) {i : ℕ}
    (hia : i < arr.size) (v : α) (ql qr : ℕ) :
    ((build arr h₀).update i v).query ql qr
      = ((List.Ico ql (min arr.size qr)).map ((arr.set i v hia).getD · 0)).sum := by
  rw [query_eq_sum_valAt ((valid_build arr h₀).update i v), lo_update, hi_update,
    lo_build, hi_build, show max 0 ql = ql from by omega]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  rw [List.Ico.mem] at hj
  have hja : j < arr.size := by omega
  rcases eq_or_ne j i with rfl | hne
  · rw [valAt_update_self (valid_build arr h₀) v ((lo_build arr h₀).trans_le (Nat.zero_le j))
      (lt_of_lt_of_eq hja (hi_build arr h₀).symm)]
    simp [Array.getD, hja]
  · rw [valAt_update_of_ne hne v, valAt_build arr h₀ j hja]
    simp [Array.getD, hja, hne.symm]

end SegmentTree
