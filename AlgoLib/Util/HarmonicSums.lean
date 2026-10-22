/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Harmonic prefix sums

Closed forms for the prefix sums `Σ H_r`, `Σ r·H_r` and `Σ (r+1)·H_r`
of Mathlib's harmonic numbers (`harmonic : ℕ → ℚ`). These are the
standard closing identities of average-case recurrences: summing a
per-rank harmonic cost over a uniformly chosen rank produces exactly
these sums.

All three follow by induction from `harmonic_succ` and telescoping.
-/

namespace AlgoLib

/-- `Σ_{s=1}^{n} H_s = (n+1)·H_n − n`. -/
theorem sum_range_harmonic (n : ℕ) :
    ∑ r ∈ Finset.range n, harmonic (r + 1) =
      (n + 1) * harmonic n - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : (n : ℚ) + 1 ≠ 0 := by positivity
    rw [Finset.sum_range_succ, ih, harmonic_succ]
    push_cast
    field_simp
    ring

/-- `Σ_{s=1}^{n} s·H_s = n(n+1)/2 · H_n − n(n−1)/4`. -/
theorem sum_range_mul_harmonic (n : ℕ) :
    ∑ r ∈ Finset.range n, ((r : ℚ) + 1) * harmonic (r + 1) =
      n * (n + 1) * harmonic n / 2 - n * (n - 1) / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : (n : ℚ) + 1 ≠ 0 := by positivity
    rw [Finset.sum_range_succ, ih, harmonic_succ]
    push_cast
    field_simp
    ring

/-- `Σ_{s=1}^{n} (s+1)·H_s = (n+1)(n+2)/2 · H_n − n(n+3)/4`. -/
theorem sum_range_succ_mul_harmonic (n : ℕ) :
    ∑ r ∈ Finset.range n, ((r : ℚ) + 2) * harmonic (r + 1) =
      (n + 1) * (n + 2) * harmonic n / 2 - n * (n + 3) / 4 := by
  have split : ∀ r : ℕ, ((r : ℚ) + 2) * harmonic (r + 1) =
      ((r : ℚ) + 1) * harmonic (r + 1) + harmonic (r + 1) :=
    fun r => by ring
  simp only [split, Finset.sum_add_distrib,
    sum_range_mul_harmonic, sum_range_harmonic]
  ring

end AlgoLib
