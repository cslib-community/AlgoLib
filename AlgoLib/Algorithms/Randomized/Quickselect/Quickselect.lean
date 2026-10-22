/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Correctness.Correctness
import AlgoLib.Util.Partition
import Mathlib.Data.List.GetD
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Quickselect

This module implements a modular version of Quickselect.

## Architecture

Like `Quicksort`, a single definition parameterized by `RandMonad`
and `MonadCost` serves as executable program (`M = IO`), as
specification (`M = PMF`), and as timed algorithm (`M = TimeMT ℕ M'`).

## Main results

For `L` the input list, `n` its length and `k` the selected rank
(0-indexed), we have:

* `quickselect_correct`: over any `LawfulRandMonad`, the output
  distribution is the Dirac mass at the true order statistic
  `orderStat L k`; the answer never depends on the random pivots.
  No hypotheses on `L` or `k` are required.
* `quickselect_cost_le_quadratic_real`: for arbitrary lists (possibly
  with duplicates) and any rank, the expected cost is at most `C(n,2)`,
  tight on all-equal inputs.
* `quickselect_cost_le_linear`: with one tick per pivot
  comparison, the expected cost on a list of `n` distinct elements
  is at most `4 n`: a linear bound, in contrast to QuickSort's
  `Θ(n log n)`.
* `quickselect_cost_exact`: Knuth's (1971) exact
  expected cost of selecting rank `k` (0-indexed) from `n` distinct
  elements: `2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))`
  comparisons.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean
open List

variable {α : Type} [LinearOrder α] [Inhabited α]

/-! ## Specification -/

/-- The `k`-th order statistic of `L` (0-indexed): the `k`-th element
of the sorted list, with `default` as out-of-range default. This is the
specification `Quickselect` must meet.

`sortSpec L` is the sorted list of `L` (`AlgoLib.Helpers.Partition`), a
definite description built from `SortedLE`, so this reads as "the
`k`-th smallest element of `L`" — which is how `Quickselect.md` states
the problem. `sortSpec` is noncomputable and so is `orderStat`; neither
is ever run, only proved equal to what `Quickselect` returns. -/
noncomputable def orderStat (L : List α) (k : ℕ) : α :=
  (sortSpec L).getD k default

/-! ## Algorithm -/

/-- Randomized Quickselect, polymorphic in the random monad `M` and
the cost monad `MonadCost ℕ M`. Partition around a uniformly random
pivot, then recurse into the (strictly smaller) side containing rank
`k`, or stop if the pivot itself has rank `k`. -/
def Quickselect
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List α → ℕ → M α
  | [], _ => return default
  | L@(_ :: _), k => do
      let idx ← randIdx L
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let lt := rest.filter (· < pivot)
      MonadCost.tick rest.length
      if k < lt.length then
        Quickselect lt k
      else if k = lt.length then
        return pivot
      else
        Quickselect (rest.filter (· ≥ pivot)) (k - lt.length - 1)
  termination_by L _ => L.length
  decreasing_by all_goals grind

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO version (executable, untimed; `RandMonad IO` comes from
-- `AlgoLib.Infrastructure.Randomness.LawfulRandMonad`)
def Quickselect_IO : List ℕ → ℕ → IO ℕ := Quickselect

#eval Quickselect_IO [5, 3, 8, 1, 9, 2] 2

-- PMF reading (noncomputable specification; an `example` suffices,
-- theorems are stated about `Quickselect` itself)
noncomputable example : List ℕ → ℕ → PMF ℕ := Quickselect

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

-- IO timed version (executable; `RandMonad (TimeMT ℕ M)` comes from
-- `AlgoLib.Infrastructure.Complexity.ExpectedCost`)
def Quickselect_IO_Timed : List ℕ → ℕ → TimeMT ℕ IO ℕ := Quickselect

#eval (Quickselect_IO_Timed [5, 3, 8, 1, 9, 2] 2).run

-- PMF timed reading (noncomputable specification)
noncomputable example : List ℕ → ℕ → TimeMT ℕ PMF ℕ := Quickselect

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-!
### Abbreviations

As for `Quicksort`, we abstract the deterministic partition-and-recurse
step at a fixed pivot index; the algorithm is `randIdx >>= branch`.
-/

/-- Branch: partition around pivot `L[i]` and recurse into the side
containing rank `k` (or stop). Used for both correctness and
complexity proofs. -/
private abbrev qsel_branch
    (M : Type → Type) [Monad M] [RandMonad M] [MonadCost ℕ M]
    (L : List α) (k : ℕ) (i : Fin L.length) : M α := do
  let pivot := L[i]
  let rest := L.eraseIdx i
  let lt := rest.filter (· < pivot)
  MonadCost.tick rest.length
  if k < lt.length then
    Quickselect lt k
  else if k = lt.length then
    return pivot
  else
    Quickselect (rest.filter (· ≥ pivot)) (k - lt.length - 1)

-- ### Structural decomposition

/-- `Quickselect` on a nonempty list decomposes as
`randIdx L >>= qsel_branch M L k`. -/
private lemma quickselect_eq_bind
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (head : α) (tail : List α) (k : ℕ) :
    (Quickselect (head :: tail) k : M α) =
    randIdx (head :: tail) >>=
      fun idx => qsel_branch M (head :: tail) k idx := by
  rw [Quickselect.eq_2]

/-!
### Order-statistic case lemmas

By `sortSpec_partition` (from `AlgoLib.Helpers.Partition`), the sorted
version of `L` splits around any pivot as
`sorted(< pivot) ++ [pivot] ++ sorted(≥ pivot)`, so the order statistic
of `L` reduces to the order statistic of one side. All three case
lemmas are hypothesis-free (out-of-range ranks yield `default` on both
sides).
-/

/-- Rank `k` falls in the `< pivot` side: the order statistic is found
left of the pivot. Stated with a ℕ index in `simp`-normal form and
oriented "branch = spec" (the pivot occurs on the left, so simp can
instantiate it), the convention `dirac_correct` consumes. -/
@[spec_transport]
private lemma orderStat_lt_branch (L : List α) (i : ℕ) (hi : i < L.length)
    {k : ℕ} (hk : k < ((L.eraseIdx i).filter (· < L[i])).length) :
    orderStat ((L.eraseIdx i).filter (· < L[i])) k = orderStat L k := by
  symm
  have h := (sortSpec_partition L ⟨i, hi⟩).symm
  simp only [Fin.getElem_fin, pivotLT, pivotGE] at h
  unfold orderStat
  -- Index `k` lands inside the first block of the split sorted list.
  rw [h, List.append_assoc, List.getD_append _ _ _ _ (by simpa using hk)]

/-- Rank `k` is exactly the pivot's rank: the order statistic is the
pivot itself. The rank is spelled out on the left so that after
`simp_all` substitutes the guard `k = …length`, the rule matches
syntactically. -/
@[spec_transport]
private lemma orderStat_eq_branch (L : List α) (i : ℕ) (hi : i < L.length) :
    orderStat L ((L.eraseIdx i).filter (· < L[i])).length = L[i] := by
  have h := (sortSpec_partition L ⟨i, hi⟩).symm
  simp only [Fin.getElem_fin, pivotLT, pivotGE] at h
  unfold orderStat
  -- Index `k` lands exactly on the singleton `[pivot]` block.
  rw [h, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- Rank `k` falls in the `≥ pivot` side: shift the rank past the left
block and the pivot. Also covers out-of-range ranks (both sides yield
`default`). -/
@[spec_transport]
private lemma orderStat_gt_branch (L : List α) (i : ℕ) (hi : i < L.length)
    {k : ℕ} (hk1 : ((L.eraseIdx i).filter (· < L[i])).length ≤ k)
    (hk2 : ¬ k = ((L.eraseIdx i).filter (· < L[i])).length) :
    orderStat ((L.eraseIdx i).filter (· ≥ L[i]))
        (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) =
      orderStat L k := by
  have hk : ((L.eraseIdx i).filter (· < L[i])).length < k := by omega
  symm
  have h := (sortSpec_partition L ⟨i, hi⟩).symm
  simp only [Fin.getElem_fin, pivotLT, pivotGE] at h
  unfold orderStat
  -- Index `k` lands in the last block; subtract the first block's length…
  rw [h, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp only [length_sortSpec]; omega)]
  rw [List.singleton_append]
  -- …and one more for the pivot.
  have hidx : k - (sortSpec ((L.eraseIdx i).filter (· < L[i]))).length =
      (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) + 1 := by
    simp only [length_sortSpec]; omega
  rw [hidx, List.getD_cons_succ]

/-!
### Generic correctness theorem

Stated over any lawful cost model (`LawfulMonadCost`), so the one
theorem covers the cost-free and the timed readings.
-/

/-- For any `LawfulRandMonad` and any lawful cost model,
`Quickselect L k` returns exactly the `k`-th order statistic:
its output distribution is the Dirac mass at `orderStat L k`,
independently of the random pivot choices.
-/
theorem quickselect_correct
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (L : List α) (k : ℕ) :
    𝒟_{M}[Quickselect L k] = PMF.pure (orderStat L k) := by
  dirac_correct Quickselect
  -- Leftover base case: `orderStat` of `[]` is `default`.
  simp [orderStat, LawfulRandMonad.toPMF_pure, pmf_pure_eq]

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem quickselect_correct_pmf (L : List α) (k : ℕ) :
    (Quickselect L k : PMF α) = PMF.pure (orderStat L k) :=
  quickselect_correct (M := PMF) L k

/-- Timed PMF correctness for free: `TimeMT ℕ PMF` is itself a lawful
random monad (`instLawfulRandMonadTimeMT`), so the generic theorem
instantiates directly, since erasing the clock is its `toPMF`. -/
theorem quickselect_correct_timed_pmf (L : List α) (k : ℕ) :
    𝒟_{TimeMT ℕ PMF}[Quickselect L k] = PMF.pure (orderStat L k) :=
  quickselect_correct (M := TimeMT ℕ PMF) L k

-- ----------------------------------------
-- Generic Complexity Proof
-- ----------------------------------------

/-!
## Complexity

The expected cost obeys
`E[n] = (n-1) + (1/n) Σ_i E[side_i]`. Three results follow, all by
functional induction on `Quickselect`:

* bounding the recursion by the whole `rest` gives `E ≤ C(n,2)` for
  arbitrary lists (tight on all-equal inputs), which also yields
  finiteness of the expected cost;
* recursing always into a side of size at most `max(r, n-1-r)` (for
  pivot rank `r`) gives the linear bound `E ≤ 4n` for distinct lists;
* for distinct lists the recurrence solves exactly: rank reindexing
  turns the sum over pivots into Knuth's (1971) bivariate harmonic
  closed form (`quickselect_cost_exact`).

The upper bounds are stated in `ENNReal`, where no summability
bookkeeping is needed; the exact formula descends to `ℝ` via `toReal`,
with finiteness supplied by the `C(n,2)` bound.
-/

/-- The recursive part of the per-pivot step cost, the cost of the
branch actually taken, named once so no proof ever restates the
if-tree. -/
private noncomputable def qselRecCost (M : Type → Type) [Monad M]
    [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) (i : Fin L.length) : ENNReal :=
  if k < (pivotLT L i).length then
    𝔼_{M}[cost Quickselect (pivotLT L i) k]
  else if k = (pivotLT L i).length then 0
  else
    𝔼_{M}[cost Quickselect (pivotGE L i) (k - (pivotLT L i).length - 1)]

/-- The per-pivot step cost: the partition work plus `qselRecCost`. -/
private noncomputable def qselStepCost (M : Type → Type) [Monad M]
    [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) (i : Fin L.length) : ENNReal :=
  ((L.eraseIdx i).length : ENNReal) + qselRecCost M L k i

/-- The expected cost of `qsel_branch` in `TimeMT` is the tick cost
plus the expected cost of the branch actually taken. -/
private lemma expected_cost_qsel_branch
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (k : ℕ) (i : Fin L.length) :
    𝔼_{M}[cost qsel_branch (TimeMT ℕ M) L k i] = qselStepCost M L k i := by
  -- Peel the tick with the bridge lemmas, then the `pure` branch is free.
  unfold qsel_branch qselStepCost qselRecCost
  cost_step
  congr 1
  split_ifs
  · rfl
  · exact expected_cost_toPMF_pure _
  · rfl

/-- The expected cost of `Quickselect` on a nonempty list is the
uniform average of the branch costs. -/
lemma expected_cost_quickselect_step
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (head : α) (tail : List α) (k : ℕ) :
    𝔼_{M}[cost Quickselect (head :: tail) k] =
    ((head :: tail).length : ENNReal)⁻¹ *
      ∑ i : Fin (head :: tail).length, qselStepCost M (head :: tail) k i := by
  rw [quickselect_eq_bind head tail k]
  exact expected_cost_uniform_step' (by simp)
    fun i => expected_cost_qsel_branch (head :: tail) k i

/-- The empty list costs nothing (for any rank). -/
lemma expected_cost_quickselect_nil
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] (k : ℕ) :
    𝔼_{M}[cost Quickselect ([] : List α) k] = 0 := by
  rw [Quickselect.eq_1]; cost_step

/-!
### The `C(n,2)` bound for arbitrary lists

The linear bound below needs distinct elements: on an all-equal list
the `≥`-side keeps every duplicate, so selecting rank `n-1` degenerates
to `T(n) = (n-1) + T(n-1) = C(n,2)`. That worst case is itself an upper
bound for every list and rank, by the same argument as for `Quicksort`.
Its `ENNReal` form also provides finiteness of the expected cost for free.
-/

/-- For an arbitrary list (possibly
with duplicates) and any rank `k`, the expected cost of `Quickselect`
is bounded by `L.length.choose 2`. Tight on all-equal inputs. -/
theorem quickselect_cost_le_quadratic
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    𝔼_{M}[cost Quickselect L k] ≤
      (L.length.choose 2 : ENNReal) := by
  induction L, k using Quickselect.induct with
  | case1 k =>
    rw [expected_cost_quickselect_nil]
    exact bot_le
  | case2 head tail k ih1 ih2 =>
    rw [expected_cost_quickselect_step head tail k]
    -- Whichever branch is taken recurses on at most `tail.length`
    -- elements; Pascal + `C(·,2)`-monotonicity bound each branch, and
    -- the uniform average of the bounds closes the case.
    refine uniform_avg_le_of_forall fun i => ?_
    unfold qselStepCost qselRecCost
    rw [show ((head :: tail).length.choose 2 : ENNReal) =
        (tail.length : ENNReal) + (tail.length.choose 2 : ENNReal) from by
      simp only [List.length_cons, choose_two_succ]; push_cast; ring]
    refine add_le_add (le_of_eq (by rw [length_eraseIdx_cons])) ?_
    split_ifs with h1 h2
    · exact le_trans (ih1 i) (Nat.cast_le.mpr (Nat.choose_le_choose 2 (by grind)))
    · exact bot_le
    · exact le_trans (ih2 i) (Nat.cast_le.mpr (Nat.choose_le_choose 2 (by grind)))

/-- For an arbitrary list (possibly with duplicates) and any rank, the
expected cost of `Quickselect` is at most `C(n,2)` comparisons.
Real-valued corollary of `quickselect_cost_le_quadratic`. -/
theorem quickselect_cost_le_quadratic_real
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    𝔼ℝ_{M}[cost Quickselect L k] ≤ L.length.choose 2 := by
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _)
    (quickselect_cost_le_quadratic (M := M) L k)
  simpa using this

/-- Finiteness of the expected cost, a free corollary of the `C(n,2)`
bound, no separate induction needed. Feeds the `toReal` steps of the
exact-formula theorem below. -/
lemma expected_cost_quickselect_ne_top
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    𝔼_{M}[cost Quickselect L k] ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (quickselect_cost_le_quadratic L k)

/-!
### The linear bound for distinct lists
-/

/-- With one tick per pivot comparison, selecting from a list
of `n` distinct elements costs at most `4 n` comparisons
in expectation, a linear bound, unlike QuickSort's `Θ(n log n)`. -/
theorem quickselect_cost_le_linear
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (k : ℕ) (hnd : L.Nodup) :
    𝔼_{M}[cost Quickselect L k] ≤
      4 * (L.length : ENNReal) := by
  revert hnd
  induction L, k using Quickselect.induct with
  | case1 k =>
    intro _
    rw [expected_cost_quickselect_nil]
    exact bot_le
  | case2 head tail k ih1 ih2 =>
    intro hnd
    rw [expected_cost_quickselect_step head tail k]
    -- Bound each branch by `tail.length + 4·max(|lt|, |ge|)` using the IH:
    -- whichever side is recursed into has at most `max` elements.
    have hbound : ∀ i : Fin (head :: tail).length,
        qselStepCost M (head :: tail) k i ≤
        ((tail.length : ENNReal) +
          4 * ((max
            ((pivotLT (head :: tail) i).length)
            ((pivotGE (head :: tail) i).length) : ℕ) :
            ENNReal)) := by
      intro i
      unfold qselStepCost qselRecCost
      refine add_le_add (le_of_eq (by rw [length_eraseIdx_cons])) ?_
      have hnd' : (((head :: tail).eraseIdx i)).Nodup := hnd.eraseIdx _
      split_ifs with h1 h2
      · -- `<`-side: the IH gives `4·|lt|`, and `|lt| ≤ max`.
        refine le_trans (ih1 i (hnd'.filter _)) ?_
        exact mul_le_mul' le_rfl (Nat.cast_le.mpr (le_max_left _ _))
      · -- pivot hit: free.
        exact bot_le
      · -- `≥`-side: the IH gives `4·|ge|`, and `|ge| ≤ max`.
        refine le_trans (ih2 i (hnd'.filter _)) ?_
        exact mul_le_mul' le_rfl (Nat.cast_le.mpr (le_max_right _ _))
    -- Reindex the per-pivot bound by rank (`nodup_partition_sum₂`).
    have hsum : (∑ i : Fin (head :: tail).length,
        ((tail.length : ENNReal) +
          4 * ((max
            ((pivotLT (head :: tail) i).length)
            ((pivotGE (head :: tail) i).length) : ℕ) :
            ENNReal))) =
        ∑ r ∈ Finset.range (head :: tail).length,
          ((tail.length : ENNReal) +
            4 * ((max r ((head :: tail).length - 1 - r) : ℕ) : ENNReal)) :=
      nodup_partition_sum₂ (head :: tail) hnd
        (fun a b => (tail.length : ENNReal) + 4 * ((max a b : ℕ) : ENNReal))
    -- ℕ-level bound for the reindexed sum, in `n * (4n)` shape
    -- (`sum_max_le` is the arithmetic core, from `AlgoLib.Helpers.Partition`).
    have hkey : (∑ r ∈ Finset.range (tail.length + 1),
        (tail.length + 4 * max r (tail.length - r))) ≤
        (tail.length + 1) * (4 * (tail.length + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h4 := sum_max_le (tail.length + 1)
      simp only [Nat.add_sub_cancel] at h4
      have hf : (tail.length + 1) ^ 2 = tail.length ^ 2 + 2 * tail.length + 1 := by
        ring
      have he : (tail.length + 1) * (4 * (tail.length + 1)) =
          4 * tail.length ^ 2 + 8 * tail.length + 4 := by ring
      have hd : (tail.length + 1) * tail.length = tail.length ^ 2 + tail.length := by
        ring
      omega
    -- Average the `n` bounds: `n⁻¹ * (n * 4n) ≤ 4n`.
    refine uniform_avg_le
      (le_trans (Finset.sum_le_sum fun i _ => hbound i) ?_)
    rw [hsum]
    simp only [List.length_cons, Nat.add_sub_cancel]
    refine le_trans (le_of_eq ?_) (le_trans (Nat.cast_le.mpr hkey) (le_of_eq ?_))
    · push_cast
      rfl
    · push_cast
      ring

/-!
### The exact expected cost for arbitrary rank (Knuth 1971)

For general `k` the recursion enters the `<`-side (size `r`, rank `k`)
when the pivot rank `r` exceeds `k`, stops at `r = k`, and enters the
`≥`-side (size `n−1−r`, rank `k−1−r`) when `r < k`, so

`n·C(n,k) = n(n−1) + Σ_{r=k+1}^{n−1} C(r,k) + Σ_{s=0}^{k−1} C(n−k+s, s)`

(the second sum reindexed by `s := k−1−r`). Its solution (Knuth 1971,
Mathematical analysis of algorithms) is the bivariate harmonic
closed form `expected_qsel_cost` below. Each partial sum telescopes
against an explicit closed form by a one-variable induction
(`qsel_sumA`, `qsel_sumB`), phrased via the ℕ-subtraction-free
reparametrization `qselCost j k = expected_qsel_cost (j + k) k`.
-/

/-- Knuth's exact expected number of comparisons for selecting rank `k`
(0-indexed) from `n` distinct elements:
`2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))`.
Specializes to `2n − 2·H(n)` at `k = 0` (`expected_qsel_cost_zero`). -/
def expected_qsel_cost (n k : ℕ) : ℚ :=
  2 * (n + 3 + (n + 1) * harmonic n
      - (k + 3) * harmonic (k + 1)
      - (n + 2 - k) * harmonic (n - k))

/-- At `k = 0`, Knuth's formula collapses to the classic
minimum-selection cost `2n − 2·H(n)`. -/
lemma expected_qsel_cost_zero (n : ℕ) :
    expected_qsel_cost n 0 = 2 * n - 2 * harmonic n := by
  unfold expected_qsel_cost
  rw [Nat.sub_zero, harmonic_succ 0, harmonic_zero]
  push_cast
  ring

/-- `j`-parametrized form of `expected_qsel_cost`, avoiding
ℕ-subtraction: `qselCost j k` is the expected cost for length `j + k`
and rank `k`. All telescoping runs through this form. -/
private def qselCost (j k : ℕ) : ℚ :=
  2 * (j + k + 3 + (j + k + 1) * harmonic (j + k)
      - (k + 3) * harmonic (k + 1)
      - (j + 2) * harmonic j)

private lemma expected_qsel_cost_add (j s : ℕ) :
    expected_qsel_cost (j + s) s = qselCost j s := by
  unfold expected_qsel_cost qselCost
  rw [Nat.add_sub_cancel]
  push_cast
  ring

/-- Closed form for the `<`-side partial sum `Σ_{t<d} C(k+1+t, k)`:
the ranks strictly above `k` contribute a telescoping harmonic sum. -/
private lemma qsel_sumA (k d : ℕ) :
    ∑ t ∈ Finset.range d, qselCost (t + 1) k =
      d * (d + 2 * k + 7)
      + (k + d + 1) * (k + d + 2) * harmonic (k + d)
      - (k + d) * (k + d + 3) / 2
      - ((k + 1) * (k + 2) + 2 * d * (k + 3)) * harmonic (k + 1)
      + (k + 2) + k * (k + 3) / 2
      - (d + 1) * (d + 4) * harmonic d
      + d * (d + 7) / 2 := by
  induction d with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero, harmonic_zero]
      rw [harmonic_succ k]
      have hk : (k : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      unfold qselCost
      rw [show d + 1 + k = k + d + 1 from by omega,
        show k + (d + 1) = k + d + 1 from by omega,
        harmonic_succ (k + d), harmonic_succ d]
      have h1 : (k : ℚ) + d + 1 ≠ 0 := by positivity
      have h2 : (d : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- Closed form for the `≥`-side partial sum `Σ_{s<k} C(j+s, s)`: the
ranks strictly below `k`, reindexed, contribute a diagonal harmonic
sum with fixed side-length offset `j`. -/
private lemma qsel_sumB (j k : ℕ) :
    ∑ s ∈ Finset.range k, qselCost j s =
      k * (2 * j + k + 5)
      + (j + k) * (j + k + 1) * harmonic (j + k)
      - (j + k) * (j + k + 3) / 2
      - j * (j + 1) * harmonic j
      + j * (j + 3) / 2
      - (k + 1) * (k + 4) * harmonic (k + 1)
      + (k + 4) + k * (k + 7) / 2
      - 2 * k * (j + 2) * harmonic j := by
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
      rw [harmonic_succ 0, harmonic_zero]
      push_cast
      ring
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      unfold qselCost
      rw [show j + (k + 1) = j + k + 1 from by omega,
        harmonic_succ (j + k), harmonic_succ (k + 1)]
      have h1 : (j : ℚ) + k + 1 ≠ 0 := by positivity
      have h2 : (k : ℚ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- Recurrence satisfaction: summing the branch costs over all `n`
pivot ranks gives `n·C(n,k) − n(n−1)`, i.e. `expected_qsel_cost`
solves Quickselect's three-way recurrence. The sum splits at rank `k`
into the two telescoped partial sums. -/
private lemma qsel_cost_sum_eq (n k : ℕ) (hk : k < n) :
    ∑ r ∈ Finset.range n,
      (if k < r then expected_qsel_cost r k
       else if k = r then 0
       else expected_qsel_cost (n - 1 - r) (k - r - 1)) =
    n * expected_qsel_cost n k - n * (n - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (by omega : k + 1 ≤ k + 1 + d),
    ← Finset.range_eq_Ico]
  -- Ranks below `k` (reflected) and the vanishing `r = k` term.
  have hB : (∑ r ∈ Finset.range (k + 1),
      (if k < r then expected_qsel_cost r k
       else if k = r then 0
       else expected_qsel_cost (k + 1 + d - 1 - r) (k - r - 1))) =
      ∑ s ∈ Finset.range k, qselCost (d + 1) s := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl k), if_pos rfl, add_zero,
      ← Finset.sum_range_reflect (fun s => qselCost (d + 1) s) k]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r < k := Finset.mem_range.mp hr
    rw [if_neg (by omega), if_neg (by omega),
      show k - r - 1 = k - 1 - r from by omega,
      show k + 1 + d - 1 - r = d + 1 + (k - 1 - r) from by omega,
      expected_qsel_cost_add]
  -- Ranks above `k`.
  have hA : (∑ r ∈ Finset.Ico (k + 1) (k + 1 + d),
      (if k < r then expected_qsel_cost r k
       else if k = r then 0
       else expected_qsel_cost (k + 1 + d - 1 - r) (k - r - 1))) =
      ∑ t ∈ Finset.range d, qselCost (t + 1) k := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [show k + 1 + d - (k + 1) = d from by omega]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [if_pos (by omega : k < k + 1 + t),
      show k + 1 + t = t + 1 + k from by omega,
      expected_qsel_cost_add]
  -- Combine the closed forms; one final harmonic-step rewrite closes it.
  rw [hB, hA, qsel_sumA k d, qsel_sumB (d + 1) k,
    show k + 1 + d = d + 1 + k from by omega,
    expected_qsel_cost_add]
  unfold qselCost
  rw [show d + 1 + k = k + d + 1 from by omega,
    harmonic_succ (k + d), harmonic_succ d]
  have h1 : (k : ℚ) + d + 1 ≠ 0 := by positivity
  have h2 : (d : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Exact expected complexity of Quickselect (Knuth 1971's analysis).
Selecting rank `k` (0-indexed, `k < n`) from a list
of `n` distinct elements costs exactly
`2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))` comparisons in
expectation. -/
theorem quickselect_cost_exact
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) (k : ℕ) (hnd : L.Nodup) (hk : k < L.length) :
    𝔼ℝ_{M}[cost Quickselect L k] =
      (expected_qsel_cost L.length k : ℚ) := by
  revert hnd hk
  induction L, k using Quickselect.induct with
  | case1 k =>
    -- Vacuous: no rank is below length `0`.
    intro _ hk
    simp only [List.length_nil] at hk
    omega
  | case2 head tail k ih1 ih2 =>
    intro hnd hk
    rw [expected_cost_quickselect_step head tail k]
    -- Every branch is finite (from the `C(n,2)` bound), so `toReal`
    -- distributes through the average.
    have hite : ∀ i : Fin (head :: tail).length,
        qselRecCost M (head :: tail) k i ≠ ⊤ := by
      intro i
      unfold qselRecCost
      split_ifs
      · exact expected_cost_quickselect_ne_top _ _
      · exact ENNReal.zero_ne_top
      · exact expected_cost_quickselect_ne_top _ _
    have hne : ∀ i : Fin (head :: tail).length,
        qselStepCost M (head :: tail) k i ≠ ⊤ := fun i => by
      unfold qselStepCost
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hite i⟩
    rw [toReal_uniform_avg hne]
    have hknat : k < tail.length + 1 := by simpa using hk
    -- Rewrite each summand with the IH (in `ℝ`); the `≥`-branch rank
    -- stays in range because the two filters partition `rest`.
    have hterm : ∀ i : Fin (head :: tail).length,
        (qselStepCost M (head :: tail) k i).toReal =
        (tail.length : ℝ) +
          ((if k < (pivotLT (head :: tail) i).length then
            expected_qsel_cost
              ((pivotLT (head :: tail) i).length) k
          else if k = (pivotLT (head :: tail) i).length then 0
          else
            expected_qsel_cost
              ((pivotGE (head :: tail) i).length)
              (k - (pivotLT (head :: tail) i).length - 1) :
            ℚ) : ℝ) := by
      intro i
      have hlen : (pivotLT (head :: tail) i).length +
          (pivotGE (head :: tail) i).length =
          tail.length := by
        rw [length_filter_lt_ge ((head :: tail).eraseIdx i) (head :: tail)[i]]
        exact length_eraseIdx_cons head tail i
      unfold qselStepCost
      rw [ENNReal.toReal_add (ENNReal.natCast_ne_top _) (hite i),
        ENNReal.toReal_natCast, length_eraseIdx_cons head tail i]
      unfold qselRecCost
      congr 1
      split_ifs with h1 h2
      · exact ih1 i ((hnd.eraseIdx _).filter _) h1
      · simp
      · exact ih2 i ((hnd.eraseIdx _).filter _)
          (by simp only [pivotLT, pivotGE] at *; omega)
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    -- Reindex by rank (`|lt_i| = rank i`, `|ge_i| = n−1−rank i`).
    rw [nodup_partition_sum₂ (head :: tail) hnd
      (fun a b => (tail.length : ℝ) +
        ((if k < a then expected_qsel_cost a k
          else if k = a then 0
          else expected_qsel_cost b (k - a - 1) : ℚ) : ℝ))]
    -- Separate the constant part and apply the recurrence identity.
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show (∑ r ∈ Finset.range (head :: tail).length,
          ((if k < r then expected_qsel_cost r k
            else if k = r then 0
            else expected_qsel_cost ((head :: tail).length - 1 - r) (k - r - 1) : ℚ) : ℝ)) =
        ((∑ r ∈ Finset.range (head :: tail).length,
          (if k < r then expected_qsel_cost r k
            else if k = r then 0
            else expected_qsel_cost ((head :: tail).length - 1 - r) (k - r - 1)) : ℚ) : ℝ)
        from by push_cast; rfl,
      qsel_cost_sum_eq (head :: tail).length k hk]
    -- Close with field arithmetic in `ℝ`.
    have hn1 : ((tail.length : ℝ) + 1) ≠ 0 := by positivity
    simp only [List.length_cons]
    push_cast
    field_simp
    ring

/-!
## Named corollaries at `M = PMF`
-/

/-- Expected number of comparisons performed by `Quickselect L k`:
the expected runtime of the instrumented algorithm interpreted in
`PMF`, one tick per pivot comparison. -/
noncomputable def quickselectComparisons (L : List α) (k : ℕ) : ENNReal :=
  𝔼_{PMF}[cost Quickselect L k]

/-- Expected cost is linear. Selecting from a list of `n` distinct
elements takes at most `4 n` comparisons in expectation. -/
theorem quickselect_cost_le_linear_pmf
    (L : List α) (k : ℕ) (hnd : L.Nodup) :
    quickselectComparisons L k ≤ 4 * (L.length : ENNReal) :=
  quickselect_cost_le_linear L k hnd

/-- Exact expected cost (Knuth 1971): selecting rank `k` from `n`
distinct elements takes exactly
`2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))` comparisons
in expectation. -/
theorem quickselect_cost_exact_pmf
    (L : List α) (k : ℕ) (hnd : L.Nodup) (hk : k < L.length) :
    (quickselectComparisons L k).toReal = (expected_qsel_cost L.length k : ℚ) :=
  quickselect_cost_exact (M := PMF) L k hnd hk

end AlgoLib
