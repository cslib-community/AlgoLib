import Mathlib.Tactic

-- Arithmetic Helpers
-- Authors: Weixuan Yuan, Yuchen Zhong
-- LLM: Gemini, GPT-5.5 on codex

/-!
References are to Luca Trevisan's Lecture 2, Lemma 5, and Lecture 3, Fact 2:
https://lucatrevisan.github.io/41000-22/lecture02.pdf
https://lucatrevisan.github.io/41000-22/lecture03.pdf
-/

namespace GraphLib
namespace Spectral

/-- Lecture 2, Lemma 5, p. 7: the edgewise inequality for positive/negative splitting. -/
lemma pos_neg_sub_sq_add_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  -- Lemma 5: equality for endpoints of the same sign; an inequality for opposite signs.
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb <;>
    simp [ha, hb, neg_nonpos.mpr, neg_nonneg.mpr] <;>
    nlinarith

/-- Lecture 3, Fact 2, pp. 1–2: a finite-sum version of the ratio-of-expectations argument.
Allowing zero denominators also handles the weighted average in Lecture 2, Lemma 5. -/
lemma exists_ratio_le_of_sum_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (R : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hb_sum : 0 < ∑ i ∈ s, b i) (h_sum : ∑ i ∈ s, a i ≤ R * ∑ i ∈ s, b i) :
    ∃ i ∈ s, 0 < b i ∧ a i / b i ≤ R := by
  -- Fact 2: if every eligible ratio exceeds R, then every aᵢ - R bᵢ is nonnegative.
  by_contra! h
  have hle : ∀ i ∈ s, R * b i ≤ a i := by
    intro i hi
    by_cases hbi : 0 < b i
    · exact ((lt_div_iff₀ hbi).1 (h i hi hbi)).le
    · have : b i = 0 := le_antisymm (le_of_not_gt hbi) (hb i hi)
      simpa [this] using ha i hi
  -- Fact 2: one strict term makes the total positive, contradicting the sum bound.
  obtain ⟨i, hi, hbi⟩ := (Finset.sum_pos_iff_of_nonneg hb).1 hb_sum
  have := Finset.sum_lt_sum hle ⟨i, hi, (lt_div_iff₀ hbi).1 (h i hi hbi)⟩
  rw [← Finset.mul_sum] at this
  exact (not_lt_of_ge h_sum) this

end Spectral
end GraphLib
