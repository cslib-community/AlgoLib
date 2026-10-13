/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.RandVec
import AlgoLib.Theory.Randomized.Complexity.ExpectedCost

/-!
# Sampler costs: the entropy sources are free

The samplers of `Randomness/RandVec.lean` draw randomness but never
tick, so their expected cost is `0`. These are cost-tier facts about
randomness-tier objects, which is why they live here (in `Complexity/`)
rather than with the samplers: `Randomness/` stays strictly below
`Complexity/` in the folder order.

All four lemmas are `@[expected_cost_simp]`, so `cost_step` closes the
cost proof of any algorithm whose only randomness comes from these
samplers (`schwartzZippel_cost_exact` and `freivalds_cost_exact` are
one `cost_step` each).
-/

namespace AlgoLib

open Cslib.Algorithms.Lean

variable {R : Type} [Zero R] [One R]

/-- `randBit` performs no ticks. -/
@[expected_cost_simp] lemma expected_cost_randBit
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    𝔼_{M}[cost (randBit : TimeMT ℕ M R)] = 0 := by
  unfold randBit
  cost_step

/-- `randVec` performs no ticks. -/
@[expected_cost_simp] lemma expected_cost_randVec
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ n : ℕ,
    𝔼[cost (randVec n : TimeMT ℕ M (Fin n → R))] = 0 := by
  intro n
  induction n with
  | zero =>
    rw [randVec, expected_cost_toPMF_pure]
  | succ n ih =>
    rw [show (randVec (n + 1) : TimeMT ℕ M (Fin (n + 1) → R)) =
      (randBit : TimeMT ℕ M R) >>= fun b =>
        (randVec n : TimeMT ℕ M (Fin n → R)) >>= fun rest =>
          pure (Fin.cons b rest) from rfl,
      expected_cost_toPMF_bind_const _ _ fun b =>
        (expected_cost_toPMF_bind_pure _ _).trans ih,
      expected_cost_randBit, zero_add]

/-- `randElem` performs no ticks. -/
@[expected_cost_simp] lemma expected_cost_randElem
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] {α : Type}
    (s : Finset α) (hs : s.Nonempty) :
    𝔼_{M}[cost randElem s hs] = 0 := by
  unfold randElem
  cost_step

/-- `randVecOn` performs no ticks. -/
@[expected_cost_simp] lemma expected_cost_randVecOn
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {α : Type}
    (s : Finset α) (hs : s.Nonempty) :
    ∀ n : ℕ, 𝔼_{M}[cost randVecOn s hs n] = 0 := by
  intro n
  induction n with
  | zero =>
    rw [randVecOn, expected_cost_toPMF_pure]
  | succ n ih =>
    rw [randVecOn,
      expected_cost_toPMF_bind_const _ _ fun b =>
        (expected_cost_toPMF_bind_pure _ _).trans ih,
      expected_cost_randElem, zero_add]

end AlgoLib
