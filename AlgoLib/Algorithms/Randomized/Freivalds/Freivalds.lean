/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.RandVec
import AlgoLib.Theory.Randomized.Complexity.SamplerCosts
import AlgoLib.Util.Counting
import AlgoLib.Theory.Randomized.Correctness.Correctness
import Mathlib.Data.Matrix.Mul

/-!
# Freivalds' algorithm (matrix-product verification)

Given `n × n` matrices `A, B, C`, decide whether `A * B = C` in
`O(n²)` ring operations by picking a uniformly random `0/1` vector `r`
(`randVec`, from `AlgoLib.Infrastructure.Randomness.RandVec`) and testing
`A (B r) = C r`.

## Architecture

As for the other algorithms, one definition parameterized by
`RandMonad` and `MonadCost` serves as executable program, as
specification, and as timed algorithm.

## Main results

For `A`, `B`, `C` the `n × n` input matrices, we have:

* `freivalds_complete`: no false negatives: if `A * B = C` the
  test accepts with probability `1`.
* `freivalds_sound`: one-sided error: if `A * B ≠ C` the test
  accepts with probability at most `1/2`. This is the framework's
  bounded-error tier (amplify by repetition). Proved over any
  `CommRing` by the pairing argument: flipping the `j`-th bit of a
  witness column pairs each accepting vector with a rejecting one.
* `freivalds_cost_exact` / `freivalds_costPMF`: `3n²` ring multiplications
  (three matrix-vector products), against `n³` for naive
  recomputation. Honesty note: the cost model charges the three
  matrix-vector products as one wholesale tick, so this theorem reads
  the model back rather than deriving it; a per-multiplication
  instrumented `mulVec` is future work.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean

variable {R : Type} [CommRing R] {n : ℕ}

/-! ## Algorithm -/

/-- The deterministic verifier at a fixed test vector `r`: accept iff
`A (B r) = C r`. -/
def freivaldsCheck [DecidableEq R] (A B C : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R) : Bool :=
  decide (A.mulVec (B.mulVec r) = C.mulVec r)

/-- Freivalds' algorithm: sample a random `0/1` vector and run the
verifier: `3n²` ring multiplications (three matrix-vector products)
instead of the `n³` of recomputing `A * B`. -/
def freivalds {M} [Monad M] [RandMonad M] [MonadCost ℕ M] [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) : M Bool := do
  MonadCost.tick (3 * n * n)
  let r ← (randVec n : M (Fin n → R))
  return freivaldsCheck A B C r

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

def freivalds_IO (A B C : Matrix (Fin n) (Fin n) ℤ) : IO Bool :=
  freivalds A B C

noncomputable example (A B C : Matrix (Fin n) (Fin n) ℤ) : PMF Bool :=
  freivalds A B C

def freivalds_IO_Timed (A B C : Matrix (Fin n) (Fin n) ℤ) :
    TimeMT ℕ IO Bool :=
  freivalds A B C

/-!
## Completeness and soundness
-/

/-- The check, propositionally: `r` is in the kernel of `A*B − C`. -/
private lemma freivaldsCheck_iff [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) (r : Fin n → R) :
    freivaldsCheck A B C r = true ↔ (A * B - C).mulVec r = 0 := by
  rw [freivaldsCheck, decide_eq_true_eq, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, sub_eq_zero]

/-- Completeness (no false negatives). If `A * B = C`, Freivalds
always accepts, over any `LawfulRandMonad` and any lawful cost
model. -/
theorem freivalds_complete
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) (h : A * B = C) :
    ℙ_{M}[freivalds A B C = true] = 1 := by
  have hcheck : ∀ r, freivaldsCheck A B C r = true := fun r =>
    (freivaldsCheck_iff A B C r).mpr (by rw [h, sub_self, Matrix.zero_mulVec])
  rw [freivalds]
  simp only [toPMF_simp, hcheck]
  simp only [PMF.bind_const, PMF.pure_apply]
  simp

/-! ### Soundness: the pairing argument

If `D := A*B − C` has a nonzero entry `D i j`, flipping the `j`-th bit
of any test vector changes `(D r) i` by `± D i j ≠ 0`, so of the two
vectors that differ exactly in bit `j`, at most one can pass the test.
The flip is an involution, so at most half of the `2^n` vectors
accept. This works over any `CommRing`, with no field needed. -/

/-- `mulVec` after updating one coordinate of the vector. -/
private lemma mulVec_update (D : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R) (j : Fin n) (c : R) (i : Fin n) :
    D.mulVec (Function.update r j c) i =
      D.mulVec r i + D i j * (c - r j) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (g := fun k =>
      D i k * r k + if k = j then D i j * (c - r j) else 0)
    fun k _ => by
      rcases eq_or_ne k j with rfl | hk
      · simp [Function.update_self]; ring
      · simp [hk],
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j
      (fun _ => D i j * (c - r j))]
  simp

/-- Flipping a bit at `j` updates the `0/1` vector at `j`. -/
private lemma bitVec_update (v : Fin n → Fin 2) (j : Fin n) (b : Fin 2) :
    (bitVec (Function.update v j b) : Fin n → R) =
      Function.update (bitVec v) j (if b = 0 then 0 else 1) := by
  funext k
  rcases eq_or_ne k j with rfl | hk
  · simp [bitVec, Function.update_self]
  · simp [bitVec, Function.update_of_ne hk]

/-- In any commutative ring, if `d² = 1` and `x * d = 0` then `x = 0`:
`d` is a unit (`±1`), so it cancels. -/
private lemma eq_zero_of_mul_unit {x d : R} (hd : d * d = 1) (h : x * d = 0) :
    x = 0 := by
  have : x * d * d = 0 := by rw [h, zero_mul]
  rwa [mul_assoc, hd, mul_one] at this

/-- The two vectors differing exactly in bit `j` cannot both pass the
test when `D i j ≠ 0`: flipping bit `j` moves `(D r) i` by `±D i j`. -/
private lemma not_check_both [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R)
    {i j : Fin n} (hD : (A * B - C) i j ≠ 0) (v : Fin n → Fin 2) :
    ¬(freivaldsCheck A B C (bitVec v) = true ∧
      freivaldsCheck A B C (bitVec (Function.update v j (v j + 1))) = true) := by
  rintro ⟨h1, h2⟩
  rw [freivaldsCheck_iff] at h1 h2
  rw [bitVec_update] at h2
  have hi := congrFun h2 i
  rw [mulVec_update, congrFun h1 i] at hi
  simp only [Pi.zero_apply, zero_add] at hi
  -- `hi : (A*B-C) i j * ((updated bit) - bitVec v j) = 0`; the factor is `±1`.
  refine hD (eq_zero_of_mul_unit ?_ hi)
  simp only [bitVec]
  rcases (by decide : ∀ b : Fin 2, b = 0 ∨ b = 1) (v j) with hv | hv
  · rw [hv, if_neg (by decide : ¬ (0 : Fin 2) + 1 = 0), if_pos rfl]; ring
  · rw [hv, if_pos (by decide : (1 : Fin 2) + 1 = 0),
      if_neg (by decide : ¬ (1 : Fin 2) = 0)]; ring

/-- Soundness (one-sided error). If `A * B ≠ C`, Freivalds accepts
with probability at most `1/2`, over any commutative ring. -/
theorem freivalds_sound
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) (h : A * B ≠ C) :
    ℙ_{M}[freivalds A B C = true] ≤ 1 / 2 := by
  -- A nonzero witness entry of `D = A*B − C`.
  have hD : ∃ i j, (A * B - C) i j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h (by ext i j; simpa [sub_eq_zero] using hall i j)
  obtain ⟨i, j, hD⟩ := hD
  rw [freivalds, toPMF_tick_bind, toPMF_randVec_true_card]
  -- The bit-flip at `j` is an involution pairing accept with reject
  -- (`two_mul_card_filter_le_of_involutive`, from `AlgoLib.Helpers.Counting`),
  -- so at most half of the `2^n` bit vectors accept.
  have hinv : Function.Involutive
      (fun v : Fin n → Fin 2 => Function.update v j (v j + 1)) := by
    intro v
    funext k
    rcases eq_or_ne k j with rfl | hk
    · simp only [Function.update_self]
      exact (by decide : ∀ b : Fin 2, b + 1 + 1 = b) (v k)
    · simp [Function.update_of_ne hk]
  have hcard : 2 * (Finset.univ.filter fun v : Fin n → Fin 2 =>
      freivaldsCheck A B C (bitVec v)).card ≤ 2 ^ n :=
    le_trans
      (two_mul_card_filter_le_of_involutive _ _ hinv
        fun v hv hv' => not_check_both A B C hD v ⟨hv, hv'⟩)
      (le_of_eq (by simp))
  -- Conclude `#accepting / 2^n ≤ 1/2`.
  rw [one_div, ENNReal.div_le_iff (by positivity)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
  calc ((Finset.univ.filter fun v : Fin n → Fin 2 =>
        freivaldsCheck A B C (bitVec v)).card : ENNReal)
      = 2⁻¹ * (2 * _) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
          one_mul]
    _ ≤ 2⁻¹ * 2 ^ n := mul_le_mul' le_rfl (by exact_mod_cast hcard)

-- ----------------------------------------
-- Generic Complexity Proof
-- ----------------------------------------

/-!
## Complexity

The cost model charges the three matrix-vector products wholesale:
one `tick (3 * n * n)` and nothing else (the random vector is free,
`expected_cost_randVec`). The theorem below therefore reads the model
back; instrumenting `mulVec` per multiplication is future work.
-/

/-- Exact cost. Freivalds performs exactly `3n²` ring
multiplications (three matrix-vector products) against the `n³` of
recomputing `A * B`. -/
theorem freivalds_cost_exact
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) :
    𝔼_{M}[cost freivalds A B C] = ((3 * n * n : ℕ) : ENNReal) := by
  rw [freivalds]
  cost_step

/-- Deterministic cost. The cost law is a point mass: every run
costs exactly `3n²`, not merely on average. -/
theorem freivalds_costPMF
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) :
    costPMF (freivalds A B C : TimeMT ℕ M Bool) = PMF.pure (3 * n * n) := by
  rw [freivalds, MonadCost.tick_timeMT, costPMF_tick_bind,
    costPMF_eq_pure_zero
      (by rw [expected_cost_toPMF_bind_pure]; exact expected_cost_randVec n),
    PMF.pure_map, Nat.add_zero]

/-!
## Named corollaries at `M = PMF`
-/

/-- Completeness at `M = PMF`. -/
theorem freivalds_complete_pmf [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) (h : A * B = C) :
    (freivalds A B C : PMF Bool) true = 1 :=
  freivalds_complete (M := PMF) A B C h

/-- Soundness at `M = PMF`: amplify by repetition. -/
theorem freivalds_sound_pmf [DecidableEq R]
    (A B C : Matrix (Fin n) (Fin n) R) (h : A * B ≠ C) :
    (freivalds A B C : PMF Bool) true ≤ 1 / 2 :=
  freivalds_sound (M := PMF) A B C h

end AlgoLib
