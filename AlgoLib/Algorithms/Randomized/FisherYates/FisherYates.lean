/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Correctness.Correctness
import AlgoLib.Util.Partition
import Mathlib.Data.List.Permutation

/-!
# Fisher–Yates shuffle

Shuffle a list by repeatedly moving a uniformly random remaining
element to the front, the selection form of the Fisher–Yates
algorithm. Its output distribution is exactly uniform over the
permutations of the input: the canonical exact-distribution result
of the framework's distributional tier.

Like `randBit`/`randVec`, the shuffle is a sampler: it consumes
randomness but draws no `MonadCost` ticks (`expected_cost_shuffle`),
so client algorithms (`Treap.randomBST` is the first) pay only for
their own work.

## Main results

For `L` the input list and `n` its length, we have:

* `shuffle_uniform`: on a duplicate-free list, the output
  distribution is exactly uniform over `L.permutations`.
* `shuffle_perm_apply`: pointwise form: each permutation of `L`
  appears with probability exactly `1 / n!`.
* `support_shuffle`: for any list, every output is a permutation
  of the input (no `Nodup` needed).
* `expected_cost_shuffle` / `costPMF_shuffle`: the shuffle is free,
  on every run and not just on average.

The pointwise form is the exchangeability lemma the treap
model-equivalence roadmap item (insertion model ↔ recursive model)
will consume.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean
open List
open scoped Nat

variable {α : Type}

/-! ## Algorithm -/

/-- Fisher–Yates, selection form: move a uniformly random element to
the front, shuffle the rest. -/
def shuffle {M} [Monad M] [RandMonad M] : List α → M (List α)
  | [] => return []
  | L@(_ :: _) => do
      let i ← randIdx L
      let rest ← shuffle (L.eraseIdx i)
      return (L[i] :: rest)
  termination_by L => L.length
  decreasing_by all_goals grind

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

def shuffle_IO : List ℕ → IO (List ℕ) := shuffle

#eval shuffle_IO [1, 2, 3, 4, 5]

noncomputable example : List ℕ → PMF (List ℕ) := shuffle

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-!
## Support: outputs are permutations
-/

/-- Every output of the shuffle is a permutation of the input, for
any list, duplicates allowed. -/
theorem support_shuffle
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    ∀ out ∈ (𝒟_{M}[shuffle L]).support, out.Perm L := by
  induction L using shuffle.induct with
  | case1 =>
    intro out hout
    rw [shuffle.eq_1, inst.toPMF_pure, pmf_pure_eq, PMF.support_pure,
      Set.mem_singleton_iff] at hout
    rw [hout]
  | case2 x xs ih =>
    intro out hout
    rw [shuffle.eq_2] at hout
    obtain ⟨i, hi⟩ := mem_support_toPMF_randIdx_bind.mp hout
    obtain ⟨rest, hrest, rfl⟩ := mem_support_toPMF_bind_pure.mp hi
    exact ((ih i rest hrest).cons _).trans (perm_getElem_cons_eraseIdx _ i).symm

/-!
## The exact distribution
-/

open Classical in
private lemma toPMF_shuffle_apply
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    L.Nodup → ∀ out : List α, out.Perm L →
      𝒟_{M}[shuffle L] out = ((L.length ! : ℕ) : ENNReal)⁻¹ := by
  induction L using shuffle.induct with
  | case1 =>
    intro _ out hout
    rw [List.perm_nil.mp hout, shuffle.eq_1, inst.toPMF_pure, pmf_pure_eq,
      PMF.pure_apply, if_pos rfl]
    simp
  | case2 x xs ih =>
    intro hnd out hout
    cases out with
    | nil => exact absurd hout.length_eq (by simp)
    | cons h t =>
      rw [shuffle.eq_2, toPMF_randIdx_bind_apply]
      -- Each pivot branch is a cons: it hits `h :: t` iff its head is `h`.
      have hbranch : ∀ i : Fin (x :: xs).length,
          inst.toPMF ((shuffle ((x :: xs).eraseIdx i) : M (List α)) >>=
            fun rest => pure ((x :: xs)[i] :: rest)) (h :: t) =
          if h = (x :: xs)[i] then 𝒟_{M}[shuffle ((x :: xs).eraseIdx i)] t
          else 0 := by
        intro i
        by_cases hx : h = (x :: xs)[i]
        · rw [if_pos hx, hx]
          exact toPMF_bind_pure_apply _ List.cons_injective t
        · rw [if_neg hx]
          exact toPMF_bind_pure_apply_eq_zero _
            fun ⟨rest, hrest⟩ => hx (List.cons_eq_cons.mp hrest).1.symm
      simp only [hbranch]
      -- With no duplicates, exactly one pivot has head `h`.
      obtain ⟨j, hj, hLj⟩ := List.getElem_of_mem (hout.subset (List.mem_cons_self ..))
      rw [Fintype.sum_eq_single (⟨j, hj⟩ : Fin (x :: xs).length)
        (fun i hne => by
          refine if_neg fun hh => hne ?_
          have hh2 : h = (x :: xs)[(i : ℕ)]'i.isLt := hh
          exact Fin.ext (hnd.getElem_inj_iff.mp (hh2.symm.trans hLj.symm))),
        if_pos (show h = (x :: xs)[(⟨j, hj⟩ : Fin (x :: xs).length)] from hLj.symm)]
      -- The recursive call: the tail is a permutation of the rest.
      have hperm' : t.Perm ((x :: xs).eraseIdx ((⟨j, hj⟩ : Fin (x :: xs).length) : ℕ)) := by
        have h1 := hout.trans (perm_getElem_cons_eraseIdx (x :: xs) ⟨j, hj⟩)
        rw [show (x :: xs)[(⟨j, hj⟩ : Fin (x :: xs).length)] = h from hLj] at h1
        exact h1.cons_inv
      rw [ih ⟨j, hj⟩ (hnd.sublist (List.eraseIdx_sublist ..)) t hperm',
        List.length_eraseIdx_of_lt
          (show ((⟨j, hj⟩ : Fin (x :: xs).length) : ℕ) < (x :: xs).length from hj)]
      -- `n⁻¹ · ((n−1)!)⁻¹ = (n!)⁻¹`.
      simp only [List.length_cons, Nat.add_sub_cancel]
      have hfact : (((xs.length + 1) * xs.length ! : ℕ) : ENNReal)⁻¹ =
          ((xs.length + 1 : ℕ) : ENNReal)⁻¹ * ((xs.length ! : ℕ) : ENNReal)⁻¹ := by
        rw [Nat.cast_mul, ENNReal.mul_inv
          (Or.inl (by exact_mod_cast Nat.succ_ne_zero xs.length))
          (Or.inl (ENNReal.natCast_ne_top _))]
      rw [Nat.factorial_succ, hfact]

/-- Pointwise uniformity. On a duplicate-free list, each
permutation of `L` is produced with probability exactly `1 / n!`,
the exchangeability lemma of the shuffle. -/
theorem shuffle_perm_apply
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {L out : List α} (hnd : L.Nodup) (hperm : out.Perm L) :
    ℙ_{M}[shuffle L = out] = ((L.length ! : ℕ) : ENNReal)⁻¹ :=
  toPMF_shuffle_apply L hnd out hperm

/-- Fisher–Yates samples uniformly. On a duplicate-free list the
output distribution is exactly the uniform distribution over all
permutations of the input. -/
theorem shuffle_uniform
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [DecidableEq α] {L : List α} (hnd : L.Nodup) :
    𝒟_{M}[shuffle L] =
      PMF.uniformOfFinset L.permutations.toFinset
        ⟨L, List.mem_toFinset.mpr (List.mem_permutations.mpr (List.Perm.refl L))⟩ := by
  ext out
  rw [PMF.uniformOfFinset_apply]
  by_cases hperm : out.Perm L
  · rw [if_pos (List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)),
      shuffle_perm_apply hnd hperm,
      List.toFinset_card_of_nodup (List.nodup_permutations L hnd),
      List.length_permutations]
  · rw [if_neg fun hmem => hperm (List.mem_permutations.mp (List.mem_toFinset.mp hmem)),
      (PMF.apply_eq_zero_iff _ _).mpr fun hsupp => hperm (support_shuffle L out hsupp)]

/-- Uniformity at `M = PMF` (where `toPMF` is the identity). -/
theorem shuffle_uniform_pmf [DecidableEq α] {L : List α} (hnd : L.Nodup) :
    (shuffle L : PMF (List α)) =
      PMF.uniformOfFinset L.permutations.toFinset
        ⟨L, List.mem_toFinset.mpr (List.mem_permutations.mpr (List.Perm.refl L))⟩ :=
  shuffle_uniform (M := PMF) hnd

/-! ## Costs: the shuffle is free -/

/-- The shuffle draws no ticks: like `randBit`/`randVec` it is a pure
sampler, so client algorithms pay only for their own work. -/
lemma expected_cost_shuffle
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    𝔼_{M}[cost shuffle L] = 0 := by
  induction L using shuffle.induct with
  | case1 => rw [shuffle.eq_1, expected_cost_toPMF_pure]
  | case2 x xs ih =>
    rw [shuffle.eq_2]
    exact (expected_cost_uniform_step' (by simp) fun i =>
      (expected_cost_toPMF_bind_pure _ _).trans (ih i)).trans
      (by rw [Finset.sum_const_zero, mul_zero])

/-- The shuffle's cost law is the point mass at `0`: it is free on
every run, not merely in expectation. -/
lemma costPMF_shuffle
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    costPMF (shuffle L : TimeMT ℕ M (List α)) = PMF.pure 0 :=
  costPMF_eq_pure_zero (expected_cost_shuffle L)

end AlgoLib
