/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.Geometric
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# The coupon collector

`n` coupon types, uniform independent draws: collecting every type
takes `n·H(n)` draws in expectation, the classical harmonic-number
bound, exactly.

## Modelling: a cost law, not a program

This case study deliberately bypasses the program layer, and it is
the only one that does. "Draw until a new type appears" is a retry
loop that terminates only almost surely, so it is not a structurally
terminating Lean program and cannot be written in the `RandMonad` /
`MonadCost` style of the other case studies; that is precisely the
expressivity gate a sub-probability layer would open.

What is expressible, and is the object below, is its cost law:
each stage is a `geometricTrials` distribution (the number of draws
until the current success probability `m/n` fires), and the stages
compose by `bind`. So this file exercises the framework's
distribution tier (`PMF`, `𝔼[·]`, `mean_bind_add`) rather than its
program tier, and the theorem is an exact expectation over that law.

## Main results

For `n` the number of coupon types, we have:

* `couponCollector_cost_exact`: `𝔼[draws] = Σ_{r<n} n/(r+1)`, exactly,
  in `ENNReal`.
* `couponCollector_cost_exact_real`: the classical form
  `𝔼[draws] = n·H(n)` in `ℝ`.
-/

namespace AlgoLib

open ENNReal

/-! ## The cost law -/

/-- Stage decomposition: with `m` of the `n` types still missing, the
next new type takes `geometricTrials (m/n)` draws; then the rest. -/
noncomputable def couponCollectorAux (n : ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | m + 1 =>
      (geometricTrials (((m + 1 : ℕ) : ENNReal) / (n : ENNReal))
        (by simp [ENNReal.div_eq_zero_iff])).bind fun draws =>
        (couponCollectorAux n m).bind fun rest => PMF.pure (draws + rest)

/-- The coupon-collector cost law: total draws to collect all `n`
types. -/
noncomputable def couponCollector (n : ℕ) : PMF ℕ := couponCollectorAux n n

/-! ## Expected number of draws -/

private lemma mean_couponCollectorAux (n : ℕ) :
    ∀ m : ℕ, m ≤ n →
      𝔼[couponCollectorAux n m] =
        ∑ r ∈ Finset.range m, (n : ENNReal) / ((r : ENNReal) + 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [couponCollectorAux, mean_pure]
    simp
  | succ m ih =>
    intro hmn
    have hn0 : (n : ENNReal) ≠ 0 := by
      have h : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hmn
      exact_mod_cast h.ne'
    -- The stage's success probability `p = (m+1)/n`, hence `1/p = n/(m+1)` draws.
    set p : ENNReal := ((m + 1 : ℕ) : ENNReal) / (n : ENNReal) with hp
    have hp0 : p ≠ 0 := by rw [hp]; simp [ENNReal.div_eq_zero_iff]
    have hptop : p ≠ ⊤ := by rw [hp]; simp [ENNReal.div_eq_top, hn0]
    have hp1 : p ≤ 1 := by
      rw [hp, ENNReal.div_le_iff hn0 (ENNReal.natCast_ne_top n), one_mul]
      exact_mod_cast hmn
    have hpinv : p⁻¹ = (n : ENNReal) / ((m : ENNReal) + 1) := by
      rw [hp, ennreal_natCast_div_inv (Nat.succ_ne_zero m)]
      push_cast
      rfl
    rw [couponCollectorAux, mean_bind_add, mean_geometricTrials hp0 hptop hp1,
      ih (Nat.le_of_succ_le hmn), Finset.sum_range_succ, hpinv, add_comm]

/-- The coupon collector, exactly (in `ENNReal`): collecting all `n`
types takes `Σ_{r<n} n/(r+1)` draws in expectation. -/
theorem couponCollector_cost_exact (n : ℕ) :
    𝔼[couponCollector n] = ∑ r ∈ Finset.range n, (n : ENNReal) / ((r : ENNReal) + 1) :=
  mean_couponCollectorAux n n le_rfl

/-- The coupon collector, classically: `n·H(n)` expected draws. -/
theorem couponCollector_cost_exact_real (n : ℕ) :
    (𝔼[couponCollector n]).toReal = ((n * harmonic n : ℚ) : ℝ) := by
  rw [couponCollector_cost_exact,
    ENNReal.toReal_sum fun r _ => by simp [ENNReal.div_eq_top]]
  have hterm : ∀ r : ℕ, ((n : ENNReal) / ((r : ENNReal) + 1)).toReal =
      (n : ℝ) / ((r : ℝ) + 1) := by
    intro r
    rw [ENNReal.toReal_div,
      ENNReal.toReal_add (ENNReal.natCast_ne_top r) ENNReal.one_ne_top]
    simp
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  push_cast [harmonic]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

end AlgoLib
