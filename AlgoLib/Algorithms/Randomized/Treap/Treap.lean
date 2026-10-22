/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Correctness.Correctness
import AlgoLib.Util.Partition
import AlgoLib.Algorithms.Randomized.FisherYates.FisherYates
import Mathlib.Data.Nat.Log

/-!
# Treap / randomized binary search tree

A treap assigns each key a random priority and keeps a BST on keys /
heap on priorities; equivalently, the resulting tree is the BST
obtained by inserting the keys in a uniformly random order. We
model this directly via a random shuffle, keeping the randomness
explicit and the output distribution exact.

## Architecture

Two classically equivalent models, both polymorphic in the random
monad `M` (they run in `IO`, specify distributions in `PMF`, …):

* `randomBST`: insert the keys in a uniformly random order
  (`shuffle` + `foldl insert`);
* `treap`: pick a uniformly random root and recurse on the two sides
  (the shape distribution of a treap).

Neither draws `MonadCost` ticks: for a data structure the analogue of
runtime is a structural measure of the output (the tree height),
handled by the `expVal` output-functional API from `AlgoLib.Infrastructure.Complexity.ExpectedCost`.

## Main results

For `n` the number of (distinct) keys, we have:

* `randomBST_correct` (insertion model) and `treap_correct`
  (recursive model): every tree the sampler can output is a valid
  BST over the (distinct) keys: its in-order traversal is sorted and a
  permutation of the keys. So the traversal is deterministic even
  though the tree shape is random.
* `randomBST_height_le`: deterministic bound: height ≤ number of keys.
* `treap_expVal_exp_height`: the exponential-height bound
  `E[2^height] ≤ C(n+3, 3)` (CLRS-style; the hockey-stick identity
  makes the induction close with equality).
* `treap_expected_height_le`: the expected height is logarithmic:
  `E[height] ≤ 3·log₂(n+3) + 4`, extracted from the exponential bound
  by the pointwise inequality `h ≤ k + 2^h/2^k` (no Jensen needed).
  The sharp constant is `≈ 3` in base 2 (Devroye 1986).

The formal equivalence of the two models (their output distributions
coincide) is future work.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean

/-! ## Binary search trees -/

/-- A binary tree with `ℕ` keys. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → ℕ → Tree → Tree
deriving Repr

namespace Tree

/-- Standard (duplicate-dropping) BST insertion. -/
def insert : Tree → ℕ → Tree
  | leaf, k => node leaf k leaf
  | node l x r, k =>
      if k < x then node (insert l k) x r
      else if x < k then node l x (insert r k)
      else node l x r

/-- Height of the tree (a `leaf` has height `0`). -/
def height : Tree → ℕ
  | leaf => 0
  | node l _ r => 1 + max l.height r.height

/-- Number of nodes. -/
def size : Tree → ℕ
  | leaf => 0
  | node l _ r => 1 + l.size + r.size

/-- In-order traversal (the sorted key sequence of a BST). -/
def inorder : Tree → List ℕ
  | leaf => []
  | node l x r => l.inorder ++ x :: r.inorder

/-- Membership in a tree, via its in-order traversal. -/
@[simp] lemma mem_inorder_leaf (a : ℕ) : a ∈ leaf.inorder ↔ False := by
  simp [inorder]

/-- Insertion adds exactly the new key to the element set. -/
lemma mem_inorder_insert (t : Tree) (k a : ℕ) :
    a ∈ (t.insert k).inorder ↔ a = k ∨ a ∈ t.inorder := by
  induction t with
  | leaf => simp [insert, inorder]
  | node l x r ihl ihr =>
    rw [insert]
    split_ifs with h1 h2
    · simp only [inorder, List.mem_append, List.mem_cons, ihl]
      tauto
    · simp only [inorder, List.mem_append, List.mem_cons, ihr]
      tauto
    · -- `k = x`, already present.
      have hkx : k = x := by omega
      simp only [inorder, List.mem_append, List.mem_cons]
      rw [hkx]; tauto

/-- Insertion preserves in-order sortedness (the BST invariant). -/
lemma sorted_inorder_insert (t : Tree) (k : ℕ)
    (hs : t.inorder.Pairwise (· < ·)) :
    (t.insert k).inorder.Pairwise (· < ·) := by
  induction t with
  | leaf => simp [insert, inorder]
  | node l x r ihl ihr =>
    rw [inorder, List.pairwise_append] at hs
    obtain ⟨hsl, hsxr, hlt⟩ := hs
    rw [List.pairwise_cons] at hsxr
    obtain ⟨hxr, hsr⟩ := hsxr
    have hlx : ∀ a ∈ l.inorder, a < x := fun a ha => hlt a ha x (by simp)
    rw [insert]
    split_ifs with h1 h2
    · -- `k < x`: recurse left; new left block still all `< x`.
      rw [inorder, List.pairwise_append]
      refine ⟨ihl hsl, List.pairwise_cons.mpr ⟨hxr, hsr⟩, fun a ha b hb => ?_⟩
      rw [mem_inorder_insert] at ha
      rcases List.mem_cons.mp hb with rfl | hb'
      · rcases ha with rfl | ha'
        · exact h1
        · exact hlx a ha'
      · rcases ha with rfl | ha'
        · exact lt_trans h1 (hxr b hb')
        · exact lt_trans (hlx a ha') (hxr b hb')
    · -- `x < k`: recurse right; new right block still all `> x`.
      rw [inorder, List.pairwise_append]
      refine ⟨hsl, ?_, fun a ha b hb => ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, ihr hsr⟩
        rw [mem_inorder_insert] at hb
        rcases hb with rfl | hb'
        · exact h2
        · exact hxr b hb'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact hlx a ha
        · rw [mem_inorder_insert] at hb'
          rcases hb' with rfl | hb''
          · exact lt_trans (hlx a ha) h2
          · exact lt_trans (hlx a ha) (hxr b hb'')
    · -- `k = x`: unchanged.
      rw [inorder, List.pairwise_append]
      exact ⟨hsl, List.pairwise_cons.mpr ⟨hxr, hsr⟩, hlt⟩

/-- Folding insertion over a list: element set is exactly the list. -/
lemma mem_inorder_foldl (L : List ℕ) (t : Tree) (a : ℕ) :
    a ∈ (L.foldl Tree.insert t).inorder ↔ a ∈ L ∨ a ∈ t.inorder := by
  induction L generalizing t with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, mem_inorder_insert]
    simp only [List.mem_cons]
    tauto

/-- Folding insertion keeps the in-order traversal sorted. -/
lemma sorted_inorder_foldl (L : List ℕ) (t : Tree)
    (hs : t.inorder.Pairwise (· < ·)) :
    (L.foldl Tree.insert t).inorder.Pairwise (· < ·) := by
  induction L generalizing t with
  | nil => simpa using hs
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih _ (sorted_inorder_insert t x hs)

/-- The in-order traversal lists exactly the nodes. -/
lemma length_inorder (t : Tree) : t.inorder.length = t.size := by
  induction t with
  | leaf => simp [inorder, size]
  | node l x r ihl ihr =>
    simp only [inorder, size, List.length_append, List.length_cons, ihl, ihr]
    omega

/-- Height is bounded by the number of nodes. -/
lemma height_le_size (t : Tree) : t.height ≤ t.size := by
  induction t with
  | leaf => simp [height, size]
  | node l x r ihl ihr =>
    simp only [height, size]
    omega

/-- Insertion adds at most one node. -/
lemma size_insert_le (t : Tree) (k : ℕ) : (t.insert k).size ≤ t.size + 1 := by
  induction t with
  | leaf => simp [insert, size]
  | node l x r ihl ihr =>
    rw [insert]
    split_ifs <;> simp only [size] <;> omega

/-- Folding insertion over `L` yields at most `|L|` nodes. -/
lemma size_foldl_le (L : List ℕ) (t : Tree) :
    (L.foldl Tree.insert t).size ≤ t.size + L.length := by
  induction L generalizing t with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.length_cons]
    exact le_trans (ih (t.insert x)) (by have := size_insert_le t x; omega)

end Tree

/-! ## Algorithm -/

/-- Build a randomized BST by inserting the keys in a uniformly random
order (`shuffle` is the Fisher–Yates sampler from
`AlgoLib.Algorithms.FisherYates`). -/
def randomBST {M} [Monad M] [RandMonad M] (keys : List ℕ) : M Tree := do
  let perm ← shuffle keys
  return perm.foldl Tree.insert Tree.leaf

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

def randomBST_IO : List ℕ → IO Tree := randomBST

#eval do IO.println s!"{repr (← randomBST_IO [3, 1, 4, 1, 5, 9, 2, 6])}"

noncomputable example : List ℕ → PMF Tree := randomBST

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-!
## Correctness: every output is a valid BST

The shuffle only ever produces permutations of the input, and folding
BST-insertion over a permutation of distinct keys always yields a tree
whose in-order traversal is the sorted key list, so the traversal is
deterministic even as the shape varies.
-/

/-- A strictly-increasing list has no duplicates. -/
private lemma pairwise_lt_nodup {l : List ℕ} (h : l.Pairwise (· < ·)) :
    l.Nodup :=
  h.imp (fun hab => ne_of_lt hab)

/-- Correctness. For any `LawfulRandMonad`, every tree the sampler
can produce from distinct `keys` is a valid BST over them: its in-order
traversal is sorted and a permutation of `keys`. -/
theorem randomBST_correct
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (keys : List ℕ) (hnd : keys.Nodup) (t : Tree)
    (ht : t ∈ 𝒟_{M}[randomBST keys].support) :
    t.inorder.Pairwise (· < ·) ∧ t.inorder.Perm keys := by
  rw [randomBST] at ht
  obtain ⟨perm, hperm, rfl⟩ := mem_support_toPMF_bind_pure.mp ht
  -- `t = perm.foldl insert leaf` and `perm ~ keys`.
  have hp : perm.Perm keys := support_shuffle keys perm hperm
  have hsorted : (perm.foldl Tree.insert Tree.leaf).inorder.Pairwise (· < ·) :=
    Tree.sorted_inorder_foldl perm Tree.leaf (by simp [Tree.inorder])
  refine ⟨hsorted, ?_⟩
  -- Same element set as `perm` (nodup on both sides), hence a permutation.
  refine List.Perm.trans ?_ hp
  refine (List.perm_ext_iff_of_nodup (pairwise_lt_nodup hsorted)
    (hp.nodup_iff.mpr hnd)).mpr fun a => ?_
  rw [Tree.mem_inorder_foldl]
  simp [Tree.inorder]

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem randomBST_correct_pmf (keys : List ℕ) (hnd : keys.Nodup) (t : Tree)
    (ht : (randomBST keys : PMF Tree) t ≠ 0) :
    t.inorder.Pairwise (· < ·) ∧ t.inorder.Perm keys :=
  randomBST_correct (M := PMF) keys hnd t ht

-- ----------------------------------------
-- Structural bound: height
-- ----------------------------------------

/-!
## Height

A deterministic, honest bound: the height never exceeds the number of
keys (a treap on `n` keys has at most `n` nodes, and height ≤ nodes).
The `Θ(log n)` expected height for the recursive model is proven
below (`treap_expected_height_le`); for this insertion model it would
follow from the (future-work) equivalence of the two models.
-/

/-- Deterministic height bound. Every tree the sampler can output
has height at most `keys.length`. -/
theorem randomBST_height_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (keys : List ℕ) (t : Tree)
    (ht : t ∈ 𝒟_{M}[randomBST keys].support) :
    t.height ≤ keys.length := by
  rw [randomBST] at ht
  obtain ⟨perm, hperm, rfl⟩ := mem_support_toPMF_bind_pure.mp ht
  have hp : perm.Perm keys := support_shuffle keys perm hperm
  calc (perm.foldl Tree.insert Tree.leaf).height
      ≤ (perm.foldl Tree.insert Tree.leaf).size := Tree.height_le_size _
    _ ≤ Tree.leaf.size + perm.length := Tree.size_foldl_le perm Tree.leaf
    _ = perm.length := by simp [Tree.size]
    _ = keys.length := hp.length_eq

-- ----------------------------------------
-- The recursive model and the expected height
-- ----------------------------------------

/-!
## The recursive model and the expected height

`randomBST` above inserts in a random order. The classically
equivalent recursive characterization picks a uniformly random root
and recurses on the two sides, the exact shape distribution of a
treap. The recursive form exposes the pivot structure that the
framework's partition machinery consumes, which is what makes the
expected-height analysis tractable. (The formal equivalence of the
two models is future work.)

The height analysis is the classic exponential-height argument: the
recurrence `2^H = 2·max(2^{H_l}, 2^{H_r}) ≤ 2·(2^{H_l} + 2^{H_r})`
solves against the closed form `E[2^H] ≤ C(n+3, 3)` (the hockey-stick
identity makes the induction close with equality), and the pointwise
inequality `h ≤ k + 2^h/2^k` extracts the logarithm without Jensen.
-/

/-- Recursive treap: pick a uniformly random root, recurse on the
strictly-smaller and the `≥` side of the remainder. -/
def treap {M} [Monad M] [RandMonad M] : List ℕ → M Tree
  | [] => return Tree.leaf
  | L@(_ :: _) => do
      let i ← randIdx L
      let l ← treap ((L.eraseIdx i).filter (· < L[i]))
      let r ← treap ((L.eraseIdx i).filter (· ≥ L[i]))
      return Tree.node l L[i] r
  termination_by L => L.length
  decreasing_by all_goals grind

def treap_IO : List ℕ → IO Tree := treap

#eval do IO.println s!"{repr (← treap_IO [3, 1, 4, 1, 5, 9, 2, 6])}"

noncomputable example : List ℕ → PMF Tree := treap

/-- Decomposition of `treap` on a nonempty list (definitional). -/
private lemma treap_eq_bind {M} [Monad M] [RandMonad M]
    (x : ℕ) (xs : List ℕ) :
    (treap (x :: xs) : M Tree) =
    randIdx (x :: xs) >>= fun i =>
      treap (pivotLT (x :: xs) i) >>= fun l =>
        treap (pivotGE (x :: xs) i) >>= fun r =>
          pure (Tree.node l (x :: xs)[i] r) := by
  rw [treap.eq_2]

/-! ### The combinatorial core -/

/-- Hockey stick, specialized: `Σ_{r<n} C(r+3, 3) = C(n+3, 4)`. -/
private lemma sum_choose_three (n : ℕ) :
    ∑ r ∈ Finset.range n, (r + 3).choose 3 = (n + 3).choose 4 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      show n + 1 + 3 = (n + 3) + 1 from by omega,
      Nat.choose_succ_succ (n + 3) 3]
    show (n + 3).choose 4 + (n + 3).choose 3 =
      (n + 3).choose 3 + (n + 3).choose 4
    omega

/-- `4·C(n+3, 4) = n·C(n+3, 3)`. -/
private lemma four_mul_choose_four (n : ℕ) :
    4 * (n + 3).choose 4 = n * (n + 3).choose 3 := by
  have h := Nat.choose_succ_right_eq (n + 3) 3
  rw [Nat.add_sub_cancel] at h
  rw [mul_comm 4 _, mul_comm n _]
  exact h

/-- Per-rank sum for the exponential-height recurrence: the branch
bounds average back to the bound itself (with equality, in fact). -/
private lemma sum_exp_height_bound (n : ℕ) :
    ∑ r ∈ Finset.range n,
      (2 * ((r + 3).choose 3) + 2 * ((n - 1 - r + 3).choose 3)) ≤
      n * (n + 3).choose 3 := by
  rcases n with _ | m
  · simp
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      show (∑ r ∈ Finset.range (m + 1), (m + 1 - 1 - r + 3).choose 3) =
          ∑ r ∈ Finset.range (m + 1), (r + 3).choose 3 from
        Finset.sum_range_reflect (fun r => (r + 3).choose 3) (m + 1),
      sum_choose_three]
    have h4 := four_mul_choose_four (m + 1)
    omega

/-- Pointwise: `2^{height(node l p r)} ≤ 2·2^{h_l} + 2·2^{h_r}`. -/
private lemma two_pow_node_height_le (l r : Tree) (p : ℕ) :
    (2 : ENNReal) ^ (Tree.node l p r).height ≤
      2 * 2 ^ l.height + 2 * 2 ^ r.height := by
  show (2 : ENNReal) ^ (1 + max l.height r.height) ≤ _
  rw [pow_add, pow_one]
  rcases max_cases l.height r.height with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
  · exact le_self_add
  · exact le_add_self

set_option maxHeartbeats 400000 in
/-- Exponential-height bound (CLRS-style): on distinct keys,
`E[2^height] ≤ C(n+3, 3)`. -/
theorem treap_expVal_exp_height
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) :
    expVal 𝒟_{M}[treap L] (fun t => 2 ^ t.height) ≤
      ((L.length + 3).choose 3 : ENNReal) := by
  revert hnd
  induction L using treap.induct with
  | case1 =>
    intro _
    rw [treap.eq_1, inst.toPMF_pure, pmf_pure_eq, expVal_pure]
    simp [Tree.height]
  | case2 x xs ih1 ih2 =>
    intro hnd
    rw [treap_eq_bind, expVal_toPMF_randIdx_bind]
    refine uniform_avg_le ?_
    -- Bound each branch by `2·C(|lt|+3,3) + 2·C(|ge|+3,3)` via the IHs.
    have hbranch : ∀ i : Fin (x :: xs).length,
        expVal (inst.toPMF
          (treap (pivotLT (x :: xs) i) >>= fun l =>
            treap (pivotGE (x :: xs) i) >>= fun r =>
              pure (Tree.node l (x :: xs)[i] r)))
          (fun t => 2 ^ t.height) ≤
        2 * ((((pivotLT (x :: xs) i).length + 3).choose 3 : ℕ) : ENNReal) +
          2 * ((((pivotGE (x :: xs) i).length + 3).choose 3 : ℕ) : ENNReal) := by
      intro i
      have hnd' : ((x :: xs).eraseIdx i).Nodup := hnd.eraseIdx _
      -- The divide-and-conquer combinator turns the two-bind branch
      -- into an iterated expectation; bound it inside-out.
      rw [expVal_toPMF_seq₂]
      refine le_trans (expVal_mono _ fun l => le_trans
        (expVal_mono _ fun r => two_pow_node_height_le l r (x :: xs)[i])
        (le_of_eq (by rw [expVal_add, expVal_const, expVal_const_mul]))) ?_
      rw [expVal_add, expVal_const, expVal_const_mul]
      exact add_le_add
        (mul_le_mul' le_rfl (ih1 i (hnd'.filter _)))
        (mul_le_mul' le_rfl (ih2 i (hnd'.filter _)))
    refine le_trans (Finset.sum_le_sum fun i _ => hbranch i) ?_
    -- Reindex by pivot rank and close with the ℕ-level identity.
    rw [nodup_partition_sum₂ (x :: xs) hnd
      (fun a b => 2 * ((a + 3).choose 3 : ENNReal) +
        2 * ((b + 3).choose 3 : ENNReal))]
    rw [show (∑ r ∈ Finset.range (x :: xs).length,
        (2 * ((r + 3).choose 3 : ENNReal) +
          2 * ((((x :: xs).length - 1 - r + 3).choose 3 : ℕ) : ENNReal))) =
      (((∑ r ∈ Finset.range (x :: xs).length,
        (2 * ((r + 3).choose 3) + 2 * (((x :: xs).length - 1 - r + 3).choose 3)) : ℕ)) :
        ENNReal) from by push_cast; rfl]
    rw [show ((x :: xs).length : ENNReal) *
          (((((x :: xs).length + 3).choose 3 : ℕ) : ENNReal)) =
        (((x :: xs).length * (((x :: xs).length + 3).choose 3) : ℕ) : ENNReal) from by
      push_cast; rfl]
    exact Nat.cast_le.mpr (sum_exp_height_bound (x :: xs).length)

/-! ### Extracting the logarithm -/

/-- Pointwise Jensen substitute: `h ≤ k + 2^h·2^{-k}` for all `h k`. -/
private lemma height_le_add_div (h k : ℕ) :
    (h : ENNReal) ≤ k + 2 ^ h * ((2 : ENNReal) ^ k)⁻¹ := by
  by_cases hle : h ≤ k
  · exact le_add_right (by exact_mod_cast hle)
  · have hpow : (2 : ENNReal) ^ h * ((2 : ENNReal) ^ k)⁻¹ = 2 ^ (h - k) := by
      rw [show h = (h - k) + k from by omega, pow_add, mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), mul_one]
      congr 1
      omega
    rw [hpow]
    calc (h : ENNReal) = ((k + (h - k) : ℕ) : ENNReal) := by
          congr 1
          omega
      _ ≤ ((k + 2 ^ (h - k) : ℕ) : ENNReal) := by
          refine Nat.cast_le.mpr (Nat.add_le_add_left ?_ k)
          exact (Nat.lt_pow_self (by norm_num)).le
      _ = k + 2 ^ (h - k) := by push_cast; ring

set_option maxHeartbeats 400000 in
/-- Expected height of a treap is logarithmic. On `n` distinct
keys, `E[height] ≤ 3·log₂(n+3) + 4` (illustrative constants; the
sharp constant is `≈ 3` in base 2, Devroye 1986). -/
theorem treap_expected_height_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) :
    expVal 𝒟_{M}[treap L] (fun t => (t.height : ENNReal)) ≤
      ((3 * Nat.log 2 (L.length + 3) + 4 : ℕ) : ENNReal) := by
  -- `k` is one more than the log of the exponential-height bound.
  refine le_trans (expVal_mono _ fun t =>
    height_le_add_div t.height (Nat.log 2 ((L.length + 3).choose 3) + 1)) ?_
  rw [expVal_add, expVal_const, expVal_mul_right]
  -- The exponential-height term contributes at most `1`.
  have h1 : expVal (inst.toPMF (treap L)) (fun t => 2 ^ t.height) ≤
      (2 : ENNReal) ^ (Nat.log 2 ((L.length + 3).choose 3) + 1) := by
    refine le_trans (treap_expVal_exp_height L hnd) (le_trans
      (Nat.cast_le.mpr (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) _).le) ?_)
    rw [show ((2 ^ (Nat.log 2 ((L.length + 3).choose 3) + 1) : ℕ) : ENNReal) =
      (2 : ENNReal) ^ (Nat.log 2 ((L.length + 3).choose 3) + 1) from by
        push_cast; rfl]
  have hEY : expVal (inst.toPMF (treap L)) (fun t => 2 ^ t.height) *
      ((2 : ENNReal) ^ (Nat.log 2 ((L.length + 3).choose 3) + 1))⁻¹ ≤ 1 := by
    refine le_trans (mul_le_mul' h1 le_rfl) ?_
    rw [ENNReal.mul_inv_cancel (by positivity) (by finiteness)]
  refine le_trans (add_le_add le_rfl hEY) ?_
  -- `k + 1 ≤ 3·log₂(n+3) + 4` by the crude bound `C(n+3,3) ≤ (n+3)³`.
  have hlog : Nat.log 2 ((L.length + 3).choose 3) + 1 + 1 ≤
      3 * Nat.log 2 (L.length + 3) + 4 := by
    have hCpos : (L.length + 3).choose 3 ≠ 0 :=
      (Nat.choose_pos (by omega)).ne'
    have hC3 : (L.length + 3).choose 3 <
        2 ^ (3 * (Nat.log 2 (L.length + 3) + 1)) := by
      refine lt_of_le_of_lt (Nat.choose_le_pow (L.length + 3) 3) ?_
      calc (L.length + 3) ^ 3
          < (2 ^ (Nat.log 2 (L.length + 3) + 1)) ^ 3 :=
            Nat.pow_lt_pow_left
              (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) _) (by norm_num)
        _ = 2 ^ (3 * (Nat.log 2 (L.length + 3) + 1)) := by
            rw [← pow_mul, mul_comm]
    have := Nat.log_lt_of_lt_pow hCpos hC3
    omega
  refine le_trans (le_of_eq ?_) (Nat.cast_le.mpr hlog)
  push_cast
  ring

/-- Expected height at `M = PMF`, in explicit `∑'` form (the original
target statement, with honest constants). -/
theorem treap_expected_height_le_pmf (keys : List ℕ) (hnd : keys.Nodup) :
    (∑' t : Tree, (treap keys : PMF Tree) t * (t.height : ENNReal)) ≤
      ((3 * Nat.log 2 (keys.length + 3) + 4 : ℕ) : ENNReal) :=
  treap_expected_height_le (M := PMF) keys hnd

/-! ### Correctness of the recursive model -/

/-- Correctness (recursive model). Every tree in the support of
`treap L` is a valid BST over the distinct keys `L`. -/
theorem treap_correct
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) (t : Tree)
    (ht : t ∈ 𝒟_{M}[treap L].support) :
    t.inorder.Pairwise (· < ·) ∧ t.inorder.Perm L := by
  revert hnd t
  induction L using treap.induct with
  | case1 =>
    intro _ t ht
    rw [treap.eq_1] at ht
    toPMF_step at ht
    subst ht
    simp [Tree.inorder]
  | case2 x xs ih1 ih2 =>
    intro hnd t ht
    -- Deconstruct the support of `randIdx >>= (bind ∘ bind ∘ pure)`.
    rw [treap_eq_bind] at ht
    obtain ⟨i, ht⟩ := mem_support_toPMF_randIdx_bind.mp ht
    obtain ⟨l, hl, r, hr, rfl⟩ := mem_support_toPMF_seq₂.mp ht
    have hnd' : ((x :: xs).eraseIdx i).Nodup := hnd.eraseIdx _
    obtain ⟨hsl, hpl⟩ := ih1 i (hnd'.filter _) l hl
    obtain ⟨hsr, hpr⟩ := ih2 i (hnd'.filter _) r hr
    -- The two subtrees hold exactly the `<`- and `≥`-side keys.
    have hmem_l : ∀ a ∈ l.inorder, a < (x :: xs)[i] := fun a ha => by
      have hmem := hpl.mem_iff.mp ha
      simp only [List.mem_filter, decide_eq_true_eq] at hmem
      exact hmem.2
    have hpiv_not : (x :: xs)[i] ∉ (x :: xs).eraseIdx i := by
      have hperm := perm_getElem_cons_eraseIdx (x :: xs) i
      exact (List.nodup_cons.mp (hperm.nodup_iff.mp hnd)).1
    have hmem_r : ∀ a ∈ r.inorder, (x :: xs)[i] < a := fun a ha => by
      have hmem := hpr.mem_iff.mp ha
      simp only [List.mem_filter, decide_eq_true_eq, ge_iff_le] at hmem
      rcases lt_or_eq_of_le hmem.2 with h | h
      · exact h
      · rw [← h] at hmem
        exact absurd hmem.1 hpiv_not
    constructor
    · -- Sortedness: assemble `left ++ pivot :: right`.
      show (l.inorder ++ (x :: xs)[i] :: r.inorder).Pairwise (· < ·)
      rw [List.pairwise_append]
      refine ⟨hsl, List.pairwise_cons.mpr ⟨hmem_r, hsr⟩, fun a ha b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hmem_l a ha
      · exact lt_trans (hmem_l a ha) (hmem_r b hb')
    · -- Permutation: `left ++ pivot :: right ~ lt ++ pivot :: ge ~ L`.
      show (l.inorder ++ (x :: xs)[i] :: r.inorder).Perm (x :: xs)
      have hpart := perm_filter_partition (x :: xs) i
      rw [List.append_assoc, List.singleton_append] at hpart
      exact List.Perm.trans (hpl.append (hpr.cons _)) hpart

/-- Deterministic height bound (recursive model). Every tree the
recursive sampler can output has height at most the number of keys,
the twin of `randomBST_height_le` for the other model. -/
theorem treap_height_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) (t : Tree)
    (ht : t ∈ 𝒟_{M}[treap L].support) :
    t.height ≤ L.length := by
  obtain ⟨-, hperm⟩ := treap_correct L hnd t ht
  calc t.height ≤ t.size := Tree.height_le_size t
    _ = t.inorder.length := (Tree.length_inorder t).symm
    _ = L.length := hperm.length_eq

/-- Correctness of the recursive model at `M = PMF`. -/
theorem treap_correct_pmf (keys : List ℕ) (hnd : keys.Nodup) (t : Tree)
    (ht : (treap keys : PMF Tree) t ≠ 0) :
    t.inorder.Pairwise (· < ·) ∧ t.inorder.Perm keys :=
  treap_correct (M := PMF) keys hnd t ht

end AlgoLib
