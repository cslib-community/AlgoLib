/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Correctness.Correctness

/-!
# Reservoir sampling (Algorithm R, k = 1)

Sample one element uniformly at random from a list in a single pass,
without knowing its length in advance: keep the `i`-th element seen
with probability `1/i`, replacing the current sample.

## Architecture

As for `Quicksort`/`Quickselect`, a single definition parameterized by
`RandMonad` and `MonadCost` serves as executable program (`M = IO`),
as specification (`M = PMF`), and as timed algorithm
(`M = TimeMT ℕ M'`).

## Main results

For `L` the input stream and `n` its length, we have:

* `reservoir_correct`: exact uniformity: each element is
  returned with probability `count a / |L|`. Unlike
  `Quicksort`/`Quickselect`, the output distribution is not a point
  mass, this is an example of the framework's distributional tier, the
  headline claim of the `PMF` shallow embedding.
* `reservoir_none_eq_zero`: the sampler never returns `none` on a nonempty
  list.
* `reservoir_cost_exact` / `reservoir_costPMF`: one coin per stream
  element after the first: exactly `n − 1` ticks, on every run, a
  single pass.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean

variable {α : Type}

/-! ## Algorithm -/

/-- Streaming core: having seen `seen` elements so far with `cur`
currently held, process the rest. On reaching the next element,
replace `cur` by it with probability `1/(seen+1)` (one tick per
element processed). -/
def reservoirAux {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    ℕ → α → List α → M α
  | _, cur, [] => return cur
  | seen, cur, x :: xs => do
      let i ← RandMonad.randFin (seen + 1)
      MonadCost.tick 1
      reservoirAux (seen + 1) (if i.val = 0 then x else cur) xs

/-- Reservoir sampling for `k = 1`: a uniformly random element of `L`
(`none` only for the empty list). -/
def reservoir {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List α → M (Option α)
  | [] => return none
  | x :: xs => some <$> reservoirAux 1 x xs

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

def reservoir_IO : List ℕ → IO (Option ℕ) := reservoir

#eval reservoir_IO [3, 1, 4, 1, 5, 9, 2, 6]

noncomputable example : List ℕ → PMF (Option ℕ) := reservoir

def reservoir_IO_Timed : List ℕ → TimeMT ℕ IO (Option ℕ) := reservoir

#eval (reservoir_IO_Timed [3, 1, 4, 1, 5, 9, 2, 6]).run

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-!
## Correctness: the exact output distribution

The streaming invariant: in `reservoirAux seen cur xs` the held
element survives with probability `seen/(seen+m)` and each stream
element is output with probability `1/(seen+m)` (`m = |xs|`): it wins
its `1/(seen+j)` coin and survives all later coins. Stated with
multiplicities via `List.count`, over any `LawfulRandMonad`.
-/

/-- Streaming invariant. The output distribution of the core loop:
`cur` weighted `seen`, every stream element weighted its multiplicity,
normalized by the total number of elements seen at the end. -/
private lemma toPMF_reservoirAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] [DecidableEq α]
    (xs : List α) (seen : ℕ) (hseen : seen ≠ 0) (cur y : α) :
    𝒟_{M}[reservoirAux seen cur xs] y =
    ((if y = cur then (seen : ENNReal) else 0) + (xs.count y : ENNReal)) /
      ((seen : ENNReal) + (xs.length : ENNReal)) := by
  revert hseen
  induction seen, cur, xs using reservoirAux.induct with
  | case1 seen cur =>
    intro hseen
    rw [reservoirAux.eq_1, inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply]
    simp only [List.count_nil, List.length_nil, Nat.cast_zero, add_zero]
    split_ifs with h
    · rw [ENNReal.div_self (by exact_mod_cast hseen) (ENNReal.natCast_ne_top _)]
    · rw [ENNReal.zero_div]
  | case2 seen cur x xs ih =>
    intro _
    have hstep : ∀ i : Fin (seen + 1),
        𝒟_{M}[reservoirAux (seen + 1) (if i.val = 0 then x else cur) xs] y =
          ((if y = (if i.val = 0 then x else cur)
              then ((seen + 1 : ℕ) : ENNReal) else 0) +
            (xs.count y : ENNReal)) /
          (((seen + 1 : ℕ) : ENNReal) + (xs.length : ENNReal)) :=
      fun i => ih i (by omega)
    rw [reservoirAux.eq_2]
    simp only [toPMF_simp]
    rw [inst.toPMF_randFin, PMF.bind_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    simp only [hstep]
    rw [← Finset.mul_sum, Fin.sum_univ_succ]
    -- The coin: index `0` adopts `x`, the `seen` others keep `cur`.
    simp only [Fin.val_zero, Fin.val_succ, reduceIte, Nat.succ_ne_zero]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_div_assoc, ENNReal.div_add_div_same,
      show ((seen + 1 : ℕ) : ENNReal) + (xs.length : ENNReal) =
          (seen : ENNReal) + ((x :: xs).length : ENNReal) from by
        simp only [List.length_cons]; push_cast; ring,
      ← mul_div_assoc]
    congr 1
    -- Numerators: pull the `(seen+1)` factor out, then cancel it.
    rw [show (if y = x then ((seen + 1 : ℕ) : ENNReal) else 0) + (xs.count y : ENNReal) +
          (seen : ENNReal) *
            ((if y = cur then ((seen + 1 : ℕ) : ENNReal) else 0) + (xs.count y : ENNReal)) =
        ((seen + 1 : ℕ) : ENNReal) *
          ((if y = cur then (seen : ENNReal) else 0) + ((x :: xs).count y : ENNReal)) from by
      simp only [List.count_cons, beq_iff_eq]
      rcases eq_or_ne y x with hyx | hyx <;> rcases eq_or_ne y cur with hyc | hyc
      · simp only [if_pos hyx, if_pos hyc, if_pos hyx.symm]; push_cast; ring
      · simp only [if_pos hyx, if_neg hyc, if_pos hyx.symm]; push_cast; ring
      · simp only [if_neg hyx, if_pos hyc, if_neg fun h : x = y => hyx h.symm]; push_cast; ring
      · simp only [if_neg hyx, if_neg hyc, if_neg fun h : x = y => hyx h.symm]; push_cast; ring]
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _),
      one_mul]

/-- Correctness (exact uniformity). For any `LawfulRandMonad`, each
element of `L` is returned with probability `count a / |L|`; on a
distinct list, every element has probability exactly `1/n`. Note the
statement is about the whole distribution, not a point mass. -/
theorem reservoir_correct
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] [DecidableEq α]
    (L : List α) (a : α) :
    ℙ_{M}[reservoir L = some a] =
      (L.count a : ENNReal) /
    (L.length : ENNReal) := by
  cases L with
  | nil =>
    rw [reservoir.eq_1, inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply]
    simp
  | cons x xs =>
    rw [reservoir.eq_2, toPMF_map_apply _ (Option.some_injective α) a,
      toPMF_reservoirAux xs 1 one_ne_zero x a]
    simp only [List.count_cons, List.length_cons, beq_iff_eq]
    congr 1
    · rcases eq_or_ne a x with h | h
      · simp only [if_pos h, if_pos h.symm]; push_cast; ring
      · simp only [if_neg h, if_neg fun hh : x = a => h hh.symm]; push_cast; ring
    · push_cast; ring

/-- The sampler never returns `none` on a nonempty list. -/
theorem reservoir_none_eq_zero
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (L : List α) (hL : L ≠ []) :
    ℙ_{M}[reservoir L = none] = 0 := by
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    rw [reservoir.eq_2, toPMF_map_apply_eq_zero _ (by simp)]

/-- On a list of distinct elements, every member is returned with
probability exactly `1/n`. -/
theorem reservoir_correct_of_nodup
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] [DecidableEq α]
    (L : List α) (hnd : L.Nodup) (a : α) (ha : a ∈ L) :
    ℙ_{M}[reservoir L = some a] =
      ((L.length : ENNReal))⁻¹ := by
  rw [reservoir_correct, List.count_eq_one_of_mem hnd ha]
  simp

-- ----------------------------------------
-- Generic Complexity Proof
-- ----------------------------------------

/-!
## Complexity

One coin flip and one tick per stream element: the pass costs exactly
`|xs|` on `reservoirAux _ _ xs`, hence `n − 1` for a list of length
`n`. The cost is deterministic; the proof is the uniform-step recipe
with a constant recurrence.
-/

private lemma expected_cost_reservoirAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (xs : List α) (seen : ℕ) (cur : α) :
    𝔼_{M}[cost reservoirAux seen cur xs] = (xs.length : ENNReal) := by
  induction seen, cur, xs using reservoirAux.induct with
  | case1 seen cur =>
    rw [reservoirAux.eq_1, expected_cost_toPMF_pure]
    simp
  | case2 seen cur x xs ih =>
    haveI : NeZero (seen + 1) := ⟨seen.succ_ne_zero⟩
    rw [reservoirAux.eq_2, expected_cost_uniform_step_fin]
    have hbranch : ∀ i : Fin (seen + 1),
        𝔼_{M}[cost (MonadCost.tick 1 : TimeMT ℕ M Unit) >>= fun _ =>
          reservoirAux (seen + 1) (if i.val = 0 then x else cur) xs] =
        1 + (xs.length : ENNReal) := by
      intro i
      cost_step
      rw [ih i]
    rw [uniform_avg_eq_of_forall hbranch]
    simp only [List.length_cons]
    push_cast
    ring

/-- Exact cost. Reservoir sampling makes exactly `n − 1` coin
flips/ticks on a list of length `n`, a single pass. -/
theorem reservoir_cost_exact
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    𝔼_{M}[cost reservoir L] = ((L.length - 1 : ℕ) : ENNReal) := by
  cases L with
  | nil =>
    rw [reservoir.eq_1, expected_cost_toPMF_pure]
    simp
  | cons x xs =>
    rw [reservoir.eq_2, expected_cost_toPMF_map, expected_cost_reservoirAux]
    simp

/-!
## Named corollaries at `M = PMF`
-/

/-- Uniformity at `M = PMF` (where `toPMF` is the identity). -/
theorem reservoir_correct_pmf [DecidableEq α] (L : List α) (a : α) :
    (reservoir L : PMF (Option α)) (some a) =
      (L.count a : ENNReal) / (L.length : ENNReal) :=
  reservoir_correct (M := PMF) L a

/-- The streaming loop's cost law is the point mass at the number of
elements processed: one tick per element, on every run. -/
private lemma costPMF_reservoirAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ (xs : List α) (seen : ℕ) (cur : α),
      costPMF (reservoirAux seen cur xs : TimeMT ℕ M α) =
        PMF.pure xs.length := by
  intro xs seen cur
  induction seen, cur, xs using reservoirAux.induct with
  | case1 seen cur =>
    rw [reservoirAux.eq_1]
    exact costPMF_eq_pure_zero (by cost_step)
  | case2 seen cur x xs ih =>
    rw [reservoirAux.eq_2, randFin_timeMT]
    exact costPMF_lift_bind_const _ _ fun i => by
      rw [MonadCost.tick_timeMT, costPMF_tick_bind, ih i, PMF.pure_map]
      simp [Nat.add_comm]

/-- Deterministic cost. The cost law of reservoir sampling is the
point mass at `n − 1`: a run makes exactly `n − 1` coin flips, not
merely `n − 1` on average. -/
theorem reservoir_costPMF
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    costPMF (reservoir L : TimeMT ℕ M (Option α)) =
      PMF.pure (L.length - 1) := by
  cases L with
  | nil =>
    rw [reservoir.eq_1]
    exact costPMF_eq_pure_zero (by cost_step)
  | cons x xs =>
    rw [reservoir.eq_2, map_eq_bind_pure_comp]
    simp only [Function.comp_def]
    rw [costPMF_bind_pure, costPMF_reservoirAux]
    simp

end AlgoLib
