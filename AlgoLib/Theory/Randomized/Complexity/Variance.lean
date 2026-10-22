/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.Prob

/-!
# Variance and Chebyshev's inequality

The second-moment upgrade of the tail-bound tier: where Markov bounds
`ℙ(g ≥ k)` by `E[g]/k`, Chebyshev bounds the probability of a
deviation from the mean by `Var[g]/k²`, strictly sharper whenever
the second moment is controlled, and much cheaper than Chernoff.

Everything lives in `ENNReal`, where subtraction truncates; the absolute
deviation is therefore taken symmetrically:
`absSub x y = (x − y) + (y − x)`: exactly one summand is nonzero, so
this is `|x − y|`.

## Main declarations

* `absSub x y` (`x ⊖ y`): `|x − y|` in `ENNReal`
* `variance`: `Var[g] = E[(g ⊖ E[g])²]`
* `variance_add_sq_mean` / `variance_eq_sub`: the classical identity
  `Var[g] = E[g²] − E[g]²` (no hypothesis beyond a finite mean)
* `chebyshev`: `ℙ(|g − E[g]| ≥ k) ≤ Var[g] / k²`
-/

namespace AlgoLib

open ENNReal

/-! ## The symmetric distance -/

/-- `|x − y|` in `ENNReal`: truncated subtraction in both directions,
exactly one summand is nonzero. Written `x ⊖ y`. -/
noncomputable def absSub (x y : ENNReal) : ENNReal := (x - y) + (y - x)

/-- `x ⊖ y`: the symmetric distance `|x − y|` in `ENNReal`, where
ordinary subtraction truncates. -/
scoped notation:70 x " ⊖ " y => absSub x y

lemma absSub_comm (x y : ENNReal) : absSub x y = absSub y x := by
  rw [absSub, absSub, add_comm]

@[simp] lemma absSub_self (x : ENNReal) : absSub x x = 0 := by
  simp [absSub]

lemma absSub_of_le {x y : ENNReal} (h : y ≤ x) : absSub x y = x - y := by
  rw [absSub, tsub_eq_zero_of_le h, add_zero]

/-- The algebraic core of the variance identity, valid for all
`x, y : ENNReal` (including `∞`): `|x − y|² + 2xy = x² + y²`. -/
lemma absSub_sq_add_two_mul (x y : ENNReal) :
    absSub x y ^ 2 + 2 * x * y = x ^ 2 + y ^ 2 := by
  -- Ordered finite case: write the larger side as `b + c`.
  have key : ∀ {a b : ENNReal}, b ≤ a → b ≠ ⊤ →
      absSub a b ^ 2 + 2 * a * b = a ^ 2 + b ^ 2 := by
    intro a b hba hb
    obtain ⟨c, rfl⟩ := exists_add_of_le hba
    rw [absSub_of_le le_self_add, ENNReal.add_sub_cancel_left hb]
    ring
  -- One infinite argument: both sides are `⊤ + _`.
  have htop : ∀ {b : ENNReal}, b ≠ ⊤ →
      absSub ⊤ b ^ 2 + 2 * ⊤ * b = ⊤ ^ 2 + b ^ 2 := by
    intro b hb
    have habs : absSub ⊤ b = ⊤ := by
      rw [absSub_of_le le_top]
      exact ENNReal.sub_eq_top_iff.mpr ⟨rfl, hb⟩
    rw [habs, ENNReal.top_pow two_ne_zero, top_add, top_add]
  rcases eq_or_ne x ⊤ with rfl | hx
  · rcases eq_or_ne y ⊤ with rfl | hy
    · rw [absSub_self, ENNReal.top_pow two_ne_zero]
      simp
    · exact htop hy
  · rcases eq_or_ne y ⊤ with rfl | hy
    · rw [absSub_comm, show 2 * x * ⊤ = 2 * ⊤ * x from by ring,
        show x ^ 2 + ⊤ ^ 2 = ⊤ ^ 2 + x ^ 2 from add_comm _ _]
      exact htop hx
    · rcases le_total y x with h | h
      · exact key h hy
      · rw [absSub_comm, show 2 * x * y = 2 * y * x from by ring,
          show x ^ 2 + y ^ 2 = y ^ 2 + x ^ 2 from add_comm _ _]
        exact key h hx

/-! ## Variance -/

/-- Variance: the expected squared deviation from the mean. -/
noncomputable def variance {α : Type*} (p : PMF α) (g : α → ENNReal) : ENNReal :=
  expVal p (fun a => (g a ⊖ expVal p g) ^ 2)

/-- The variance identity in cancellation-free form,
`Var[g] + 2·E[g]² = E[g²] + E[g]²`, valid with no hypotheses. -/
lemma variance_add_sq_mean {α : Type*} (p : PMF α) (g : α → ENNReal) :
    variance p g + 2 * expVal p g ^ 2 =
      expVal p (fun a => g a ^ 2) + expVal p g ^ 2 := by
  have hpt : ∀ a, (g a ⊖ expVal p g) ^ 2 + 2 * expVal p g * g a
      = g a ^ 2 + expVal p g ^ 2 := fun a => by
    rw [show 2 * expVal p g * g a = 2 * g a * expVal p g from by ring]
    exact absSub_sq_add_two_mul (g a) (expVal p g)
  have h := congrArg (expVal p) (funext hpt)
  rw [expVal_add, expVal_const_mul, expVal_add, expVal_const] at h
  unfold variance
  rw [mul_assoc] at h
  rw [← pow_two] at h
  exact h

/-- The variance identity `Var[g] = E[g²] − E[g]²`, whenever the
mean is finite. -/
theorem variance_eq_sub {α : Type*} (p : PMF α) (g : α → ENNReal)
    (hμ : expVal p g ≠ ⊤) :
    variance p g = expVal p (fun a => g a ^ 2) - expVal p g ^ 2 := by
  have hμ2 : expVal p g ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hμ
  refine ENNReal.eq_sub_of_add_eq hμ2 ?_
  have h2 : variance p g + expVal p g ^ 2 + expVal p g ^ 2
      = expVal p (fun a => g a ^ 2) + expVal p g ^ 2 := by
    rw [add_assoc, ← two_mul]
    exact variance_add_sq_mean p g
  exact (ENNReal.add_left_inj hμ2).mp h2

/-! ## Chebyshev's inequality -/

/-- Chebyshev's inequality: the probability that `g` deviates from
its mean by at least `k` is at most `Var[g] / k²`. -/
theorem chebyshev {α : Type*} (p : PMF α) (g : α → ENNReal) {k : ENNReal}
    (hk0 : k ≠ 0) (hktop : k ≠ ⊤) :
    prob p {a | k ≤ g a ⊖ expVal p g} ≤ variance p g / k ^ 2 := by
  have h := prob_ge_le_expVal_div p
    (fun a => absSub (g a) (expVal p g) ^ 2) (k := k ^ 2)
    (pow_ne_zero 2 hk0) (ENNReal.pow_ne_top hktop)
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).symm

end AlgoLib
