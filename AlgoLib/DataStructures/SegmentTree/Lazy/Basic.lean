/-
Copyright (c) 2026 Tomás Hoch, Nicolas Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomás Hoch, Nicolas Alvarez
-/
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Algebra.GroupWithZero.Action.Defs
import AlgoLib.Mathlib.Data.List.Intervals

/-!
# Lazy segment trees

A `LazySegmentTree α M` is a segment tree over an additive monoid `α` whose internal nodes
additionally carry a pending *tag* `t : M`. Tags are range updates, acting on values
through a distributive action `[DistribMulAction M α]`; a tag is applied to a node in
`O(1)` and only pushed to its children when an operation later needs to descend past it.

## Main definitions

* `LazySegmentTree.build`: build a lazy segment tree (with neutral tags) from a nonempty
  `Array α`.
* `LazySegmentTree.applyTag`: apply a tag to the root of a subtree, in `O(1)`.
* `LazySegmentTree.valAt`: the array that a tree logically represents, with every pending
  tag applied.
* `LazySegmentTree.Valid`: the structural invariant.
* `LazySegmentTree.induction_push`: induction where a node may assume the result for its
  children with the pending tag pushed.
* `LazySegmentTree.rangeRecT`: the traversal shared by all range operations.
* `LazySegmentTree.queryT`, `LazySegmentTree.query`: range query, an instance of
  `rangeRecT`, in the cost monad and as its pure projection.
* `LazySegmentTree.rangeUpdateT`, `LazySegmentTree.rangeUpdate`: range update (act by a tag
  on every value in a range), another instance of `rangeRecT`.

## Main results

* `LazySegmentTree.valid_build`, `LazySegmentTree.valAt_build`: `build` produces a valid
  tree representing the input array.
* `LazySegmentTree.rootValue_eq_sum_valAt`: on a valid tree the cached root value is the
  sum of the represented array.
* `LazySegmentTree.valAt_applyTag`, `LazySegmentTree.Valid.applyTag`: applying a tag acts
  pointwise on the represented array and preserves validity.
* `LazySegmentTree.query_eq_sum_valAt`, `LazySegmentTree.query_build`: `query` computes the
  sum of the represented array on the requested range.
* `LazySegmentTree.Valid.rangeUpdate`, `LazySegmentTree.valAt_rangeUpdate`: `rangeUpdate`
  preserves validity and acts pointwise on the represented array exactly inside the range.
* `LazySegmentTree.query_rangeUpdate_build`: `query` after a `rangeUpdate` on a built tree.

## Implementation notes

The `val` stored at a node already includes the effect of the node's own `tag`; the tag
records what has not yet been applied to the children. Hence the invariant reads
`val = tag • (left.rootValue + right.rootValue)`, and `valAt` applies the tags met on the
way down. Leaves carry no tag.

Tags compose as `m * t` ("first `t`, then `m`"), so `M` need not be commutative: range
assignment and affine maps are valid tag monoids. As in
`AlgoLib.DataStructures.SegmentTree.Basic`, values only form an `AddMonoid`, so sums are
stated over `List.Ico`.

All range operations visit the same nodes, so they share one traversal, `rangeRecT`,
parametrised by what to return at disjoint and covered nodes and how to combine the two
recursive results. `query` is the instance `(0, rootValue, +)` and `rangeUpdate` the
instance `(id, applyTag m, rebuild the node with a neutral tag)`. Proofs about the instances
go by `induction_push`, whose hypotheses are exactly the recursive calls.

As in `AlgoLib.DataStructures.SegmentTree.Basic`, operations are written in CSLib's cost
monad `Cslib.Algorithms.Lean.TimeM ℕ` and the pure functions are their `.ret` projections.
`applyTag` is constant-time and stays pure; its cost is charged to the node visit that calls
it.

## TODO

This file is work in progress. Correctness of `query` and `rangeUpdate` is complete; still
missing are:

* the cost bound for `rangeRecT` (node visits `O(height)`, plus `O(height)` times the cost of
  the per-node work), and its consequences `O(log n)` for `query` and `rangeUpdate` on a
  built tree;
* point operations (`get`, point `update`) as instances of `rangeRecT`;
* standard instances of the tag algebra (range add with sum, range assign, affine maps).
-/

/-- A lazy segment tree over values `α` with tags `M`: a binary tree caching, at every
subtree, the aggregate of the values on the half-open interval `[lo, hi)` it covers, and,
at every internal node, a tag pending to be applied to both children. -/
inductive LazySegmentTree (α M : Type*) where
  /-- A leaf covering the singleton interval `[lo, hi) = [lo, lo + 1)`. -/
  | leaf (val : α) (lo hi : ℕ) : LazySegmentTree α M
  /-- An internal node covering `[lo, hi)`. `val` is the true aggregate of the range, and
  `tag` is the update already accounted for in `val` but not yet applied to the
  children. -/
  | node (val : α) (tag : M) (left right : LazySegmentTree α M) (lo hi : ℕ) :
      LazySegmentTree α M

namespace LazySegmentTree

open Cslib.Algorithms.Lean

variable {α M : Type*}

/-! ### Bounds and root value -/

/-- The lower bound of the range covered by the tree. -/
@[simp] def lo : LazySegmentTree α M → ℕ
  | leaf _ l _ => l
  | node _ _ _ _ l _ => l

/-- The upper bound (exclusive) of the range covered by the tree. -/
@[simp] def hi : LazySegmentTree α M → ℕ
  | leaf _ _ h => h
  | node _ _ _ _ _ h => h

/-- The cached aggregate at the root. -/
def rootValue : LazySegmentTree α M → α
  | leaf v _ _ => v
  | node v _ _ _ _ _ => v

/-- The height of the tree: the number of edges on a longest root-to-leaf path. A leaf has
height `0`. Range operations recurse on pushed children, which is not structural recursion,
so they terminate by `height`. -/
@[simp] def height : LazySegmentTree α M → ℕ
  | leaf _ _ _ => 0
  | node _ _ l r _ _ => max l.height r.height + 1

variable [AddMonoid α] [Monoid M]

/-! ### Construction

Identical to `SegmentTree.buildAuxT`, with every tag neutral. -/

/-- Build the subtree of `arr` covering `[lo, hi)` in the cost monad, charging one `✓`
per node created. All tags are `1`. -/
def buildAuxT (arr : Array α) (lo hi : ℕ) (h : lo < hi) (hle : hi ≤ arr.size) :
    TimeM ℕ (LazySegmentTree α M) :=
  if h1 : hi - lo = 1 then
    do ✓ return leaf (arr[lo]'(by omega)) lo hi
  else
    let mid := (lo + hi) / 2
    have hlm : lo < mid := by omega
    have hmh : mid < hi := by omega
    do
      let left ← buildAuxT arr lo mid hlm (by omega)
      let right ← buildAuxT arr mid hi hmh hle
      ✓ return node (left.rootValue + right.rootValue) 1 left right lo hi
  termination_by hi - lo
  decreasing_by all_goals omega

/-- Build a lazy segment tree covering all of `arr`, in the cost monad. -/
def buildT (arr : Array α) (h : 0 < arr.size) : TimeM ℕ (LazySegmentTree α M) :=
  buildAuxT arr 0 arr.size h le_rfl

/-- Build the subtree of `arr` covering `[lo, hi)`: the pure projection of `buildAuxT`. -/
def buildAux (arr : Array α) (lo hi : ℕ) (h : lo < hi) (hle : hi ≤ arr.size) :
    LazySegmentTree α M :=
  (buildAuxT arr lo hi h hle).ret

/-- Build a lazy segment tree covering all of `arr`: the pure projection of `buildT`. -/
def build (arr : Array α) (h : 0 < arr.size) : LazySegmentTree α M :=
  (buildT arr h).ret

@[simp] theorem buildAuxT_ret (arr : Array α) (lo hi : ℕ) (h : lo < hi)
    (hle : hi ≤ arr.size) :
    (buildAuxT (M := M) arr lo hi h hle).ret = buildAux arr lo hi h hle :=
  rfl

@[simp] theorem buildT_ret (arr : Array α) (h : 0 < arr.size) :
    (buildT (M := M) arr h).ret = build arr h :=
  rfl

@[simp] lemma lo_buildAux (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size) :
    (buildAux (M := M) arr l h h1 hle).lo = l := by
  unfold buildAux
  fun_induction buildAuxT (M := M) arr l h h1 hle <;> simp

@[simp] lemma hi_buildAux (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size) :
    (buildAux (M := M) arr l h h1 hle).hi = h := by
  unfold buildAux
  fun_induction buildAuxT (M := M) arr l h h1 hle <;> simp

@[simp] lemma lo_build (arr : Array α) (h : 0 < arr.size) :
    (build (M := M) arr h).lo = 0 :=
  lo_buildAux arr 0 arr.size h le_rfl

@[simp] lemma hi_build (arr : Array α) (h : 0 < arr.size) :
    (build (M := M) arr h).hi = arr.size :=
  hi_buildAux arr 0 arr.size h le_rfl

variable [DistribMulAction M α]

/-! ### Applying a tag -/

/-- Apply the tag `m` to the root of a subtree, after whatever it already has pending:
update the cached aggregate and compose `m` onto the pending tag. Constant time; the
children are left untouched. -/
def applyTag (m : M) : LazySegmentTree α M → LazySegmentTree α M
  | leaf v l h => leaf (m • v) l h
  | node v t left right l h => node (m • v) (m * t) left right l h

@[simp] lemma lo_applyTag (m : M) (st : LazySegmentTree α M) : (st.applyTag m).lo = st.lo := by
  cases st <;> rfl

@[simp] lemma hi_applyTag (m : M) (st : LazySegmentTree α M) : (st.applyTag m).hi = st.hi := by
  cases st <;> rfl

@[simp] lemma rootValue_applyTag (m : M) (st : LazySegmentTree α M) :
    (st.applyTag m).rootValue = m • st.rootValue := by
  cases st <;> rfl

@[simp] lemma height_applyTag (m : M) (st : LazySegmentTree α M) :
    (st.applyTag m).height = st.height := by
  cases st <;> rfl

/-! ### The represented array -/

/-- The value logically stored at index `i` (and `0` outside the tree's range), with every
pending tag on the path from the root applied: the array that the tree represents. -/
def valAt (st : LazySegmentTree α M) (i : ℕ) : α :=
  match st with
  | leaf val lo _ => if lo = i then val else 0
  | node _ t left right _ _ => t • if i < left.hi then valAt left i else valAt right i

@[simp] lemma valAt_leaf (val : α) (lo hi i : ℕ) :
    (leaf val lo hi : LazySegmentTree α M).valAt i = if lo = i then val else 0 := rfl

@[simp] lemma valAt_node_of_lt {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h i : ℕ} (hil : i < left.hi) :
    (node v t left right l h).valAt i = t • left.valAt i :=
  congrArg (t • ·) (if_pos hil)

@[simp] lemma valAt_node_of_hi_le {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h i : ℕ} (hil : left.hi ≤ i) :
    (node v t left right l h).valAt i = t • right.valAt i :=
  congrArg (t • ·) (if_neg (Nat.not_lt.mpr hil))

/-- Applying a tag at the root acts pointwise on the represented array. -/
@[simp] lemma valAt_applyTag (m : M) (st : LazySegmentTree α M) (i : ℕ) :
    (st.applyTag m).valAt i = m • st.valAt i := by
  cases st with
  | leaf v l h => by_cases hli : l = i <;> simp [applyTag, hli]
  | node v t left right l h => simp [applyTag, valAt, mul_smul]

/-- On the left child's range, a node represents its left child with the pending tag
pushed. -/
lemma map_valAt_node_left {v : α} {t : M} {left right : LazySegmentTree α M} {l h a b : ℕ}
    (hb : b ≤ left.hi) :
    (List.Ico a b).map (node v t left right l h).valAt
      = (List.Ico a b).map (left.applyTag t).valAt :=
  List.map_congr_left fun _ hmem =>
    (valAt_node_of_lt ((List.Ico.mem.mp hmem).2.trans_le hb)).trans (valAt_applyTag ..).symm

/-- On the right child's range, a node represents its right child with the pending tag
pushed. -/
lemma map_valAt_node_right {v : α} {t : M} {left right : LazySegmentTree α M} {l h a b : ℕ}
    (ha : left.hi ≤ a) :
    (List.Ico a b).map (node v t left right l h).valAt
      = (List.Ico a b).map (right.applyTag t).valAt :=
  List.map_congr_left fun _ hmem =>
    (valAt_node_of_hi_le (ha.trans (List.Ico.mem.mp hmem).1)).trans (valAt_applyTag ..).symm

/-! ### Induction along pushes

Operations that descend into a node first push its pending tag, so they recurse on
`applyTag t left` and `applyTag t right` rather than on `left` and `right`. This induction
principle provides exactly those hypotheses. -/

/-- Induction on a lazy segment tree where, at a node, the hypotheses are about the children
with the node's pending tag pushed. -/
@[elab_as_elim]
theorem induction_push {motive : LazySegmentTree α M → Prop}
    (leaf : ∀ v l h, motive (leaf v l h))
    (node : ∀ v t left right l h, motive (left.applyTag t) → motive (right.applyTag t) →
      motive (node v t left right l h))
    (st : LazySegmentTree α M) : motive st :=
  (go st).1
where
  go : ∀ st : LazySegmentTree α M, motive st ∧ ∀ m, motive (st.applyTag m)
    | .leaf v l h => ⟨leaf v l h, fun m => leaf (m • v) l h⟩
    | .node v t left right l h =>
        ⟨node v t left right l h ((go left).2 t) ((go right).2 t),
          fun m => node (m • v) (m * t) left right l h ((go left).2 _) ((go right).2 _)⟩

/-! ### The validity invariant -/

/-- Structural invariant of a lazy segment tree: leaves cover singleton intervals, children
cover contiguous intervals partitioning the parent's, and every cached value is the node's
pending tag applied to the sum of the children's. -/
inductive Valid : LazySegmentTree α M → Prop
  | leaf {v l h} (h_len : h = l + 1) : Valid (leaf v l h)
  | node {v t left right l h}
      (h_val : v = t • (left.rootValue + right.rootValue))
      (h_lo : l = left.lo)
      (h_mid : left.hi = right.lo)
      (h_hi : h = right.hi)
      (hl : Valid left) (hr : Valid right) : Valid (node v t left right l h)

lemma Valid.lo_lt_hi {st : LazySegmentTree α M} (h : Valid st) : st.lo < st.hi := by
  induction h <;> simp <;> omega

/-- Applying a tag at the root preserves validity. -/
protected lemma Valid.applyTag {st : LazySegmentTree α M} (h : Valid st) (m : M) :
    Valid (st.applyTag m) := by
  cases h with
  | leaf h_len => exact .leaf h_len
  | node h_val h_lo h_mid h_hi hl hr =>
      exact .node (by rw [h_val, mul_smul]) h_lo h_mid h_hi hl hr

/-- On a valid tree, the cached root value is the sum of the represented array over the
covered range. -/
lemma rootValue_eq_sum_valAt {st : LazySegmentTree α M} (h : Valid st) :
    st.rootValue = ((List.Ico st.lo st.hi).map st.valAt).sum := by
  induction st using induction_push with
  | leaf v l h =>
      cases h with | leaf h_len => subst h_len; simp [rootValue]
  | node v t left right l h ih_L ih_R =>
      cases h with | node h_val h_lo h_mid h_hi hl hr =>
      simp only [rootValue, lo, hi]
      subst h_lo h_hi
      rw [← List.Ico.append_consecutive (m := left.hi) hl.lo_lt_hi.le (h_mid ▸ hr.lo_lt_hi.le),
        List.map_append, List.sum_append, map_valAt_node_left le_rfl,
        map_valAt_node_right le_rfl, h_val, smul_add, ← rootValue_applyTag, ← rootValue_applyTag,
        ih_L (hl.applyTag t), ih_R (hr.applyTag t), lo_applyTag, hi_applyTag, lo_applyTag,
        hi_applyTag, h_mid]

/-! ### Range operations

A node disjoint from the range or covered by it is answered in `O(1)`, and a partially
covered node pushes its pending tag (`applyTag`) and recurses on both children. The push
only builds the children `applyTag t left` and `applyTag t right` to recurse on; `query`
discards them afterwards, so it does not modify the tree. -/

/-- One traversal of the nodes that `[ql, qr)` touches, in the cost monad, charging one `✓`
per node visited plus whatever the per-node work costs. A disjoint node runs `disj` on
itself, a covered one `cov` on itself, and a partially covered node
`node _ t left right lo hi` runs `comb lo hi a b`, where `a` and `b` are the results on the
pushed children `applyTag t left` and `applyTag t right`. On a leaf, which is never
partially covered on a valid tree, anything not covered counts as disjoint.

The per-node work `disj`, `cov` and `comb` is in `TimeM` too, so its cost is added to that
of the traversal instead of being assumed constant. The push itself is charged to the node's
`✓`. -/
def rangeRecT {β : Type*} (ql qr : ℕ) (disj cov : LazySegmentTree α M → TimeM ℕ β)
    (comb : ℕ → ℕ → β → β → TimeM ℕ β) (st : LazySegmentTree α M) : TimeM ℕ β :=
  match st with
  | leaf _ lo hi => if ql ≤ lo ∧ hi ≤ qr then do ✓ cov st else do ✓ disj st
  | node _ t left right lo hi =>
      if hi ≤ ql ∨ qr ≤ lo then do ✓ disj st
      else if ql ≤ lo ∧ hi ≤ qr then do ✓ cov st
      else do
        let a ← rangeRecT ql qr disj cov comb (left.applyTag t)
        let b ← rangeRecT ql qr disj cov comb (right.applyTag t)
        ✓ comb lo hi a b
  termination_by st.height
  decreasing_by all_goals simp only [height_applyTag, height]; omega

/-- Range query in the cost monad: the sum of the represented values on `[ql, qr)`,
together with the number of nodes visited. -/
def queryT (st : LazySegmentTree α M) (ql qr : ℕ) : TimeM ℕ α :=
  rangeRecT ql qr (fun _ => pure 0) (fun st => pure st.rootValue) (fun _ _ a b => pure (a + b))
    st

/-- The sum of the represented values on `[ql, qr)`: the pure projection of `queryT`. -/
def query (st : LazySegmentTree α M) (ql qr : ℕ) : α := (st.queryT ql qr).ret

/-! #### Equation lemmas for `query` -/

@[simp] theorem queryT_ret (st : LazySegmentTree α M) (ql qr : ℕ) :
    (st.queryT ql qr).ret = st.query ql qr := rfl

@[simp] lemma query_leaf (val : α) (lo hi ql qr : ℕ) :
    (leaf val lo hi : LazySegmentTree α M).query ql qr
      = if ql ≤ lo ∧ hi ≤ qr then val else 0 := by
  rw [query, queryT, rangeRecT]
  split_ifs <;> rfl

lemma query_node_of_disjoint {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h ql qr : ℕ} (hd : h ≤ ql ∨ qr ≤ l) :
    (node v t left right l h).query ql qr = 0 := by
  rw [query, queryT, rangeRecT, if_pos hd]
  rfl

lemma query_node_of_covered {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h ql qr : ℕ} (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ql ≤ l ∧ h ≤ qr) :
    (node v t left right l h).query ql qr = v := by
  rw [query, queryT, rangeRecT, if_neg hd, if_pos hc]
  rfl

lemma query_node_of_partial {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h ql qr : ℕ} (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ¬ (ql ≤ l ∧ h ≤ qr)) :
    (node v t left right l h).query ql qr
      = (left.applyTag t).query ql qr + (right.applyTag t).query ql qr := by
  rw [query, queryT, rangeRecT, if_neg hd, if_neg hc]
  rfl

/-! ### Correctness of `query` -/

/-- On a valid tree, `query` computes the sum of the represented array over the
intersection of the tree's range with `[ql, qr)`. -/
theorem query_eq_sum_valAt {st : LazySegmentTree α M} (h : Valid st) (ql qr : ℕ) :
    st.query ql qr = ((List.Ico (max st.lo ql) (min st.hi qr)).map st.valAt).sum := by
  induction st using induction_push with
  | leaf v l h =>
      cases h with | leaf h_len =>
      subst h_len
      rw [query_leaf]
      split_ifs with h_bounds
      · simp [show max l ql = l by omega, show min (l + 1) qr = l + 1 by omega]
      · simp [List.Ico.eq_nil_of_le (show min (l + 1) qr ≤ max l ql by omega)]
  | node v t left right l h ih_L ih_R =>
      cases h with | node h_val h_lo h_mid h_hi hl hr =>
      by_cases h_bounds : h ≤ ql ∨ qr ≤ l
      · rw [query_node_of_disjoint h_bounds]
        simp [List.Ico.eq_nil_of_le (show min h qr ≤ max l ql by omega)]
      by_cases h_full : ql ≤ l ∧ h ≤ qr
      · rw [query_node_of_covered h_bounds h_full]
        simpa [rootValue, show max l ql = l by omega, show min h qr = h by omega] using
          rootValue_eq_sum_valAt (.node h_val h_lo h_mid h_hi hl hr)
      · rw [query_node_of_partial h_bounds h_full, ih_L (hl.applyTag t), ih_R (hr.applyTag t)]
        simp only [lo_applyTag, hi_applyTag, lo.eq_2, hi.eq_2]
        rw [h_lo, h_hi, ← h_mid,
          ← List.Ico.append_consecutive_max_min (n := left.lo) (l := right.hi)
            hl.lo_lt_hi.le (h_mid ▸ hr.lo_lt_hi.le),
          List.map_append, List.sum_append,
          map_valAt_node_left (min_le_left _ _), map_valAt_node_right (le_max_left _ _)]

/-! ### Correctness of `build` -/

lemma valid_buildAux (arr : Array α) {l h : ℕ} {h1 : l < h} {hle : h ≤ arr.size} :
    Valid (buildAux (M := M) arr l h h1 hle) := by
  unfold buildAux
  fun_induction buildAuxT (M := M) arr l h h1 hle with
  | case1 l h h_less hle h_one => exact Valid.leaf (by omega)
  | case2 l h _ _ _ mid hlm hmh ihL ihR =>
      simp only [TimeM.ret_bind, TimeM.ret_pure, buildAuxT_ret]
      refine Valid.node (one_smul M _).symm ?_ ?_ ?_ ihL ihR <;>
        simp only [lo_buildAux, hi_buildAux]

theorem valid_build (arr : Array α) (h : 0 < arr.size) : Valid (build (M := M) arr h) :=
  valid_buildAux arr

lemma valAt_buildAux (arr : Array α) (l h : ℕ) (h1 : l < h) (hle : h ≤ arr.size)
    (i : ℕ) (h_in : l ≤ i ∧ i < h) :
    (buildAux (M := M) arr l h h1 hle).valAt i = arr.getD i 0 := by
  unfold buildAux
  fun_induction buildAuxT (M := M) arr l h h1 hle with
  | case1 l h h_less hle h_one =>
      obtain rfl : l = i := by omega
      simp [show l < arr.size by omega]
  | case2 l h _ _ _ mid hlm hmh ihL ihR =>
      simp only [TimeM.ret_bind, TimeM.ret_pure, buildAuxT_ret, valAt, hi_buildAux, one_smul]
      split_ifs with go_left
      · exact ihL (by omega)
      · exact ihR (by omega)

/-- The tree built from `arr` represents exactly `arr`. -/
lemma valAt_build (arr : Array α) (h : 0 < arr.size) (i : ℕ) (h_in : i < arr.size) :
    (build (M := M) arr h).valAt i = arr[i] :=
  (valAt_buildAux arr 0 arr.size h le_rfl i ⟨Nat.zero_le i, h_in⟩).trans
    (Array.getElem_eq_getD 0).symm

/-- `query` on a built tree computes the sum of the array on the requested range. -/
theorem query_build (arr : Array α) (h : 0 < arr.size) (ql qr : ℕ) :
    (build (M := M) arr h).query ql qr
      = ((List.Ico ql (min arr.size qr)).map (arr.getD · 0)).sum := by
  rw [query_eq_sum_valAt (valid_build arr h), lo_build, hi_build,
    show max 0 ql = ql by omega]
  refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
  rw [List.Ico.mem] at ha
  exact valAt_buildAux arr 0 arr.size h le_rfl a ⟨Nat.zero_le a, by omega⟩

/-! ### Range update -/

/-- Range update in the cost monad: act by `m` on every represented value in `[ql, qr)`,
together with the number of nodes visited. It is the instance of `rangeRecT` that leaves
disjoint nodes alone, applies `m` at the root of covered ones, and rebuilds a partially
covered node from its two updated (pushed) children, with a neutral tag. -/
def rangeUpdateT (st : LazySegmentTree α M) (ql qr : ℕ) (m : M) :
    TimeM ℕ (LazySegmentTree α M) :=
  rangeRecT ql qr pure (fun st => pure (st.applyTag m))
    (fun lo hi a b => pure (node (a.rootValue + b.rootValue) 1 a b lo hi)) st

/-- Act by `m` on every represented value in `[ql, qr)`: the pure projection of
`rangeUpdateT`. -/
def rangeUpdate (st : LazySegmentTree α M) (ql qr : ℕ) (m : M) : LazySegmentTree α M :=
  (st.rangeUpdateT ql qr m).ret

/-! #### Equation lemmas for `rangeUpdate` -/

@[simp] theorem rangeUpdateT_ret (st : LazySegmentTree α M) (ql qr : ℕ) (m : M) :
    (st.rangeUpdateT ql qr m).ret = st.rangeUpdate ql qr m := rfl

@[simp] lemma rangeUpdate_leaf (val : α) (lo hi ql qr : ℕ) (m : M) :
    (leaf val lo hi : LazySegmentTree α M).rangeUpdate ql qr m
      = if ql ≤ lo ∧ hi ≤ qr then leaf (m • val) lo hi else leaf val lo hi := by
  rw [rangeUpdate, rangeUpdateT, rangeRecT]
  split_ifs <;> rfl

lemma rangeUpdate_node_of_disjoint {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h ql qr : ℕ} {m : M} (hd : h ≤ ql ∨ qr ≤ l) :
    (node v t left right l h).rangeUpdate ql qr m = node v t left right l h := by
  rw [rangeUpdate, rangeUpdateT, rangeRecT, if_pos hd]
  rfl

lemma rangeUpdate_node_of_covered {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h ql qr : ℕ} {m : M} (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ql ≤ l ∧ h ≤ qr) :
    (node v t left right l h).rangeUpdate ql qr m = (node v t left right l h).applyTag m := by
  rw [rangeUpdate, rangeUpdateT, rangeRecT, if_neg hd, if_pos hc]
  rfl

lemma rangeUpdate_node_of_partial {v : α} {t : M} {left right : LazySegmentTree α M}
    {l h ql qr : ℕ} {m : M} (hd : ¬ (h ≤ ql ∨ qr ≤ l)) (hc : ¬ (ql ≤ l ∧ h ≤ qr)) :
    (node v t left right l h).rangeUpdate ql qr m
      = node (((left.applyTag t).rangeUpdate ql qr m).rootValue
          + ((right.applyTag t).rangeUpdate ql qr m).rootValue) 1
          ((left.applyTag t).rangeUpdate ql qr m) ((right.applyTag t).rangeUpdate ql qr m)
          l h := by
  rw [rangeUpdate, rangeUpdateT, rangeRecT, if_neg hd, if_neg hc]
  rfl

/-! #### Shape preservation -/

@[simp] lemma lo_rangeUpdate (st : LazySegmentTree α M) (ql qr : ℕ) (m : M) :
    (st.rangeUpdate ql qr m).lo = st.lo := by
  cases st with
  | leaf v l h => rw [rangeUpdate_leaf]; split_ifs <;> rfl
  | node v t left right l h =>
      by_cases hd : h ≤ ql ∨ qr ≤ l
      · rw [rangeUpdate_node_of_disjoint hd]
      by_cases hc : ql ≤ l ∧ h ≤ qr
      · rw [rangeUpdate_node_of_covered hd hc, lo_applyTag]
      · rw [rangeUpdate_node_of_partial hd hc]; rfl

@[simp] lemma hi_rangeUpdate (st : LazySegmentTree α M) (ql qr : ℕ) (m : M) :
    (st.rangeUpdate ql qr m).hi = st.hi := by
  cases st with
  | leaf v l h => rw [rangeUpdate_leaf]; split_ifs <;> rfl
  | node v t left right l h =>
      by_cases hd : h ≤ ql ∨ qr ≤ l
      · rw [rangeUpdate_node_of_disjoint hd]
      by_cases hc : ql ≤ l ∧ h ≤ qr
      · rw [rangeUpdate_node_of_covered hd hc, hi_applyTag]
      · rw [rangeUpdate_node_of_partial hd hc]; rfl

/-- `rangeUpdate` preserves the shape of the tree, hence its height: cost bounds in terms of
`height` keep holding along any sequence of operations. -/
@[simp] lemma height_rangeUpdate (st : LazySegmentTree α M) (ql qr : ℕ) (m : M) :
    (st.rangeUpdate ql qr m).height = st.height := by
  induction st using induction_push with
  | leaf v l h => rw [rangeUpdate_leaf]; split_ifs <;> rfl
  | node v t left right l h ih_L ih_R =>
      by_cases hd : h ≤ ql ∨ qr ≤ l
      · rw [rangeUpdate_node_of_disjoint hd]
      by_cases hc : ql ≤ l ∧ h ≤ qr
      · rw [rangeUpdate_node_of_covered hd hc, height_applyTag]
      · rw [rangeUpdate_node_of_partial hd hc, height, height, ih_L, ih_R, height_applyTag,
          height_applyTag]

/-! #### Correctness of `rangeUpdate` -/

/-- A valid tree represents `0` outside the range it covers. -/
lemma Valid.valAt_eq_zero {st : LazySegmentTree α M} (h : Valid st) {i : ℕ}
    (hout : i < st.lo ∨ st.hi ≤ i) : st.valAt i = 0 := by
  induction h with
  | leaf h_len => simp at hout ⊢; omega
  | node h_val h_lo h_mid h_hi hl hr ih_L ih_R =>
      simp only [lo, hi] at hout
      rcases hout with hout | hout
      · rw [valAt_node_of_lt (by have := hl.lo_lt_hi; omega), ih_L (by omega), smul_zero]
      · rw [valAt_node_of_hi_le (by have := hr.lo_lt_hi; omega), ih_R (by omega), smul_zero]

/-- `rangeUpdate` preserves validity. -/
protected lemma Valid.rangeUpdate {st : LazySegmentTree α M} (h : Valid st) (ql qr : ℕ)
    (m : M) : Valid (st.rangeUpdate ql qr m) := by
  induction st using induction_push with
  | leaf v l h' =>
      cases h with | leaf h_len =>
      rw [rangeUpdate_leaf]; split_ifs <;> exact .leaf h_len
  | node v t left right l h' ih_L ih_R =>
      by_cases hd : h' ≤ ql ∨ qr ≤ l
      · rwa [rangeUpdate_node_of_disjoint hd]
      by_cases hc : ql ≤ l ∧ h' ≤ qr
      · rw [rangeUpdate_node_of_covered hd hc]; exact h.applyTag m
      · cases h with | node h_val h_lo h_mid h_hi hl hr =>
        rw [rangeUpdate_node_of_partial hd hc]
        refine .node (one_smul M _).symm ?_ ?_ ?_ (ih_L (hl.applyTag t)) (ih_R (hr.applyTag t))
          <;> simp only [lo_rangeUpdate, hi_rangeUpdate, lo_applyTag, hi_applyTag]
          <;> assumption

/-- On a valid tree, `rangeUpdate ql qr m` acts by `m` on the represented values with index
in `[ql, qr)`, and leaves the others unchanged. -/
theorem valAt_rangeUpdate {st : LazySegmentTree α M} (h : Valid st) (ql qr : ℕ) (m : M)
    (i : ℕ) :
    (st.rangeUpdate ql qr m).valAt i
      = if ql ≤ i ∧ i < qr then m • st.valAt i else st.valAt i := by
  induction st using induction_push with
  | leaf v l h' =>
      cases h with | leaf h_len =>
      subst h_len
      rw [rangeUpdate_leaf]
      by_cases hli : l = i
      · subst hli; split_ifs <;> simp_all <;> omega
      · split_ifs <;> simp [hli]
  | node v t left right l h' ih_L ih_R =>
      have hv := h
      cases h with | node h_val h_lo h_mid h_hi hl hr =>
      by_cases hd : h' ≤ ql ∨ qr ≤ l
      · rw [rangeUpdate_node_of_disjoint hd]
        split_ifs with hiq
        · rw [hv.valAt_eq_zero (by simp only [lo, hi]; omega), smul_zero]
        · rfl
      by_cases hc : ql ≤ l ∧ h' ≤ qr
      · rw [rangeUpdate_node_of_covered hd hc, valAt_applyTag]
        split_ifs with hiq
        · rfl
        · rw [hv.valAt_eq_zero (by simp only [lo, hi]; omega), smul_zero]
      · rw [rangeUpdate_node_of_partial hd hc]
        rcases lt_or_ge i left.hi with hil | hil
        · rw [valAt_node_of_lt (by rwa [hi_rangeUpdate, hi_applyTag]), one_smul,
            ih_L (hl.applyTag t), valAt_node_of_lt hil, valAt_applyTag]
        · rw [valAt_node_of_hi_le (by rwa [hi_rangeUpdate, hi_applyTag]), one_smul,
            ih_R (hr.applyTag t), valAt_node_of_hi_le hil, valAt_applyTag]

/-- On a built tree, `rangeUpdate ql qr m` represents `arr` with `m` acting on the indices
in `[ql, qr)`. -/
theorem valAt_rangeUpdate_build (arr : Array α) (h : 0 < arr.size) (ql qr : ℕ) (m : M)
    {i : ℕ} (hia : i < arr.size) :
    ((build arr h).rangeUpdate ql qr m).valAt i
      = if ql ≤ i ∧ i < qr then m • arr[i] else arr[i] := by
  rw [valAt_rangeUpdate (valid_build arr h), valAt_build arr h i hia]

/-- `query` after a `rangeUpdate` on a built tree computes the sum, on the requested range,
of the array with `m` acting on the indices in `[ql, qr)`. -/
theorem query_rangeUpdate_build (arr : Array α) (h : 0 < arr.size) (ql qr : ℕ) (m : M)
    (a b : ℕ) :
    ((build arr h).rangeUpdate ql qr m).query a b
      = ((List.Ico a (min arr.size b)).map fun i =>
          if ql ≤ i ∧ i < qr then m • arr.getD i 0 else arr.getD i 0).sum := by
  rw [query_eq_sum_valAt ((valid_build arr h).rangeUpdate ql qr m), lo_rangeUpdate,
    hi_rangeUpdate, lo_build, hi_build, show max 0 a = a by omega]
  refine congrArg List.sum (List.map_congr_left fun i hmem => ?_)
  rw [List.Ico.mem] at hmem
  rw [valAt_rangeUpdate (valid_build arr h), show (build (M := M) arr h).valAt i = arr.getD i 0
    from valAt_buildAux arr 0 arr.size h le_rfl i ⟨Nat.zero_le i, by omega⟩]

end LazySegmentTree
