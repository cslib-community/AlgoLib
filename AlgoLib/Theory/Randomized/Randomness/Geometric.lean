/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.Prob

/-!
# The geometric distribution

The law of the number of failures before the first success of a
Bernoulli process with failure probability `q < 1`:
`P(k) = qᵏ(1 − q)`. It is the cost law of a retry-until-success loop,
the loop itself terminates only almost surely, so it is not a
structurally terminating program, but its cost distribution is a
perfectly well-defined `PMF` (total mass `1`). `CouponCollector` is
the first client; a sub-probability layer for the program-level loop
is future work.

Everything is proved directly in `ENNReal` (Mathlib's geometric
distribution is measure-theoretic and real-valued; the expectation
computation below (the layer-cake exchange) needs no summability
side conditions at all).

## Main declarations

* `geometric q hq`: the law of the failure count, `P(k) = qᵏ(1 − q)`
* `mean_geometric`: `𝔼 = q/(1 − q)` failures
* `geometricTrials p hp`: the law of the trial count of a
  Bernoulli process with success probability `p` (failures plus the
  successful trial)
* `mean_geometricTrials`: `𝔼 = 1/p` trials, the form a
  retry-until-success cost analysis actually consumes
-/

namespace AlgoLib

open ENNReal

private lemma geometric_mass (q : ENNReal) (hq : q < 1) :
    HasSum (fun k : ℕ => q ^ k * (1 - q)) 1 := by
  have htsum : ∑' k : ℕ, q ^ k * (1 - q) = 1 := by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
      ENNReal.inv_mul_cancel (tsub_pos_of_lt hq).ne'
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
  convert ENNReal.summable.hasSum
  exact htsum.symm

/-- A nonzero success probability leaves failure probability `< 1`. -/
lemma one_sub_lt_one {p : ENNReal} (hp0 : p ≠ 0) : 1 - p < 1 :=
  ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0

/-- The geometric distribution: `k` failures before the first success,
`P(k) = qᵏ(1 − q)`, for failure probability `q < 1`. -/
noncomputable def geometric (q : ENNReal) (hq : q < 1) : PMF ℕ :=
  ⟨fun k => q ^ k * (1 - q), geometric_mass q hq⟩

@[simp] lemma geometric_apply (q : ENNReal) (hq : q < 1) (k : ℕ) :
    geometric q hq k = q ^ k * (1 - q) := rfl

/-- Expectation of the geometric law: `q/(1 − q)` expected
failures before the first success. Proved by the layer-cake exchange
`k = #{j | j < k}`; in `ENNReal` the double-sum swap is unconditional. -/
theorem mean_geometric (q : ENNReal) (hq : q < 1) :
    𝔼[geometric q hq] = q * (1 - q)⁻¹ := by
  unfold mean
  have h0 : (1 - q) ≠ 0 := (tsub_pos_of_lt hq).ne'
  have htop : (1 - q) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  -- `k` as a sum of indicators.
  have hk : ∀ k : ℕ, (k : ENNReal) = ∑' j : ℕ, if j < k then 1 else 0 := by
    intro k
    rw [tsum_eq_sum (s := Finset.range k) fun j hj =>
      if_neg fun h => hj (Finset.mem_range.mpr h)]
    rw [Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.mp hj)]
    simp
  unfold expVal
  calc ∑' k, geometric q hq k * (k : ENNReal)
      = ∑' k, ∑' j, if j < k then q ^ k * (1 - q) else 0 := by
        refine tsum_congr fun k => ?_
        rw [hk k, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun j => by
          rw [mul_ite, mul_one, mul_zero, geometric_apply]
    _ = ∑' j, ∑' k, if j < k then q ^ k * (1 - q) else 0 := ENNReal.tsum_comm
    _ = ∑' j : ℕ, ∑' i : ℕ, q ^ (i + (j + 1)) * (1 - q) := by
        refine tsum_congr fun j => ?_
        have hsplit := Summable.sum_add_tsum_nat_add'
          (f := fun k => if j < k then q ^ k * (1 - q) else 0) (k := j + 1)
          ENNReal.summable
        rw [← hsplit,
          Finset.sum_eq_zero fun i hi =>
            if_neg (by have := Finset.mem_range.mp hi; omega),
          zero_add]
        exact tsum_congr fun i => if_pos (by omega)
    _ = ∑' j : ℕ, q ^ (j + 1) := by
        refine tsum_congr fun j => ?_
        rw [tsum_congr fun i => show q ^ (i + (j + 1)) * (1 - q) =
              q ^ (j + 1) * (q ^ i * (1 - q)) from by rw [pow_add]; ring,
          ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          ENNReal.tsum_geometric, ENNReal.inv_mul_cancel h0 htop, mul_one]
    _ = q * (1 - q)⁻¹ := ENNReal.tsum_geometric_add_one q

/-!
## Trials until the first success
-/

/-- The law of the number of trials until the first success, for
success probability `p`: the failure count plus the successful trial.
This is the cost law of one retry-until-success stage. -/
noncomputable def geometricTrials (p : ENNReal) (hp0 : p ≠ 0) : PMF ℕ :=
  (geometric (1 - p) (one_sub_lt_one hp0)).map (· + 1)

/-- Expected number of trials until the first success: `1/p`.
The form a retry-until-success cost analysis consumes directly (the
coupon collector's stage `m` has `p = m/n`, hence `n/m` draws). -/
theorem mean_geometricTrials {p : ENNReal} (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (hp1 : p ≤ 1) :
    𝔼[geometricTrials p hp0] = p⁻¹ := by
  rw [geometricTrials, mean_map_add_one, mean_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top hp1]
  -- `(1 − p)·p⁻¹ + 1 = p⁻¹`, via `1 = p·p⁻¹`.
  have h1 : (1 - p) * p⁻¹ + 1 = (1 - p) * p⁻¹ + p * p⁻¹ := by
    rw [ENNReal.mul_inv_cancel hp0 hptop]
  rw [h1, ← add_mul, tsub_add_cancel_of_le hp1, one_mul]

end AlgoLib
