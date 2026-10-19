import GraphLib.Theory.Spectral.Coarea
import GraphLib.Theory.Spectral.Fiedler

-- Cheeger upper bound, main proof
-- Authors: Weixuan Yuan, Yuchen Zhong
-- LLM: Gemini, GPT-5.6, 6.1 Sol on codex

/-!
The main steps follow Luca Trevisan's Lecture 2, §4 (Lemmas 3–5), and Lecture 3, §1:
https://lucatrevisan.github.io/41000-22/lecture02.pdf
https://lucatrevisan.github.io/41000-22/lecture03.pdf
-/

namespace GraphLib
namespace Spectral

open Finset Cuts

variable {α : Type*} (G : SimpleGraph α)
  [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
/-- Lecture 2, Lemma 5, p. 7: choose a median with at most |V|/2 entries strictly on each side. -/
lemma exists_balanced_median (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) : ∃ m : ℝ,
    (G.vertexFinset.filter (fun v => x v > m)).card ≤ (G.vertexFinset).card / 2 ∧
    (G.vertexFinset.filter (fun v => x v < m)).card ≤ (G.vertexFinset).card / 2 := by
  classical
  -- Formal support for the median choice in Lemma 5: select the middle sorted entry.
  let sortedV := (G.vertexFinset.toList).mergeSort (fun u v => x u ≤ x v)
  let n := (G.vertexFinset).card
  let k := n / 2
  have h_len : sortedV.length = n := by simp [sortedV, n]
  have hk_lt : k < sortedV.length := by grind
  let m := x (sortedV[k]'hk_lt); use m
  have h_sorted : List.Pairwise (fun u v => x u ≤ x v) sortedV := by
    simpa [sortedV] using
      (List.pairwise_mergeSort
        (le := fun u v : α => decide (x u ≤ x v))
        (fun a b c hab hbc => by simpa using (show decide (x a ≤ x c) = true from
          decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))))
        (fun a b => by grind)
        (G.vertexFinset.toList))
  have h_mem_sorted_iff : ∀ v, v ∈ sortedV ↔ v ∈ G.vertexFinset := by
    intro v; simp [sortedV]
  -- Lemma 5, p. 7: count the entries strictly above and strictly below this median.
  constructor
  · let upper := G.vertexFinset.filter (fun v => x v > m)
    let toTailIndex : α → ℕ := fun v => sortedV.length - 1 - sortedV.idxOf v
    have h_maps : Set.MapsTo toTailIndex upper (Finset.range k) := by
      intro v hv; rw [Finset.mem_coe, Finset.mem_filter] at hv
      have hv_sorted : v ∈ sortedV := (h_mem_sorted_iff v).2 hv.1
      have hidx_lt : sortedV.idxOf v < sortedV.length := List.idxOf_lt_length_iff.2 hv_sorted
      have hk_le_not : ¬ sortedV.idxOf v ≤ k := by
        intro hle
        have hrel := h_sorted.rel_get_of_le
          (a := ⟨sortedV.idxOf v, hidx_lt⟩) (b := ⟨k, hk_lt⟩)
          (show (⟨sortedV.idxOf v, hidx_lt⟩ : Fin sortedV.length) ≤ ⟨k, hk_lt⟩ from hle)
        grind
      grind
    have h_inj : (upper : Set α).InjOn toTailIndex := by
      intro a ha b hb h_eq; rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha_sorted : a ∈ sortedV := (h_mem_sorted_iff a).2 ha.1
      have hidx_eq : sortedV.idxOf a = sortedV.idxOf b := by grind
      exact (List.idxOf_inj ha_sorted).1 hidx_eq
    simpa [upper, k, n] using Finset.card_le_card_of_injOn toTailIndex h_maps h_inj
  · let lower := G.vertexFinset.filter (fun v => x v < m)
    have h_maps : Set.MapsTo (fun v => sortedV.idxOf v) lower (Finset.range k) := by
      intro v hv; rw [Finset.mem_coe, Finset.mem_range] at *; rw [Finset.mem_filter] at hv
      have hv_sorted : v ∈ sortedV := (h_mem_sorted_iff v).2 hv.1
      have hidx_lt : sortedV.idxOf v < sortedV.length := List.idxOf_lt_length_iff.2 hv_sorted
      by_contra hnot
      have hk_le : k ≤ sortedV.idxOf v := Nat.le_of_not_gt hnot
      have hrel := h_sorted.rel_get_of_le (a := ⟨k, hk_lt⟩) (b := ⟨sortedV.idxOf v, hidx_lt⟩)
        (show (⟨k, hk_lt⟩ : Fin sortedV.length) ≤ ⟨sortedV.idxOf v, hidx_lt⟩ from hk_le)
      grind
    have h_inj : (lower : Set α).InjOn (fun v => sortedV.idxOf v) := by
      intro a ha b hb h_eq; rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha_sorted : a ∈ sortedV := (h_mem_sorted_iff a).2 ha.1
      exact (List.idxOf_inj ha_sorted).1 h_eq
    simpa [lower, k, n] using
      Finset.card_le_card_of_injOn (fun v => sortedV.idxOf v) h_maps h_inj

/-- Lecture 2, Lemma 5, pp. 6–7: R(x + c1) ≤ R(x) when x is orthogonal to constants. -/
lemma median_shift_rayleigh_le (x : α → ℝ) (d : ℕ) (m : ℝ) (h_d_pos : d ≠ 0)
    (h_x_ne : ∃ v ∈ G.vertexFinset, x v ≠ 0)
    (h_orth : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    SimpleGraph.rayleighQuotient G (fun v => x v - m) ≤ SimpleGraph.rayleighQuotient G x := by
  -- Regularity converts degree-orthogonality to the x ⊥ 1 condition used in Lemma 5.
  have h_weight : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) =
      (d : ℝ) * G.vertexFinset.sum (fun v => x v) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; grind
  have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast h_d_pos
  -- Lemma 5, p. 6: orthogonality makes the cross term in the shifted norm vanish.
  have h_cross : G.vertexFinset.sum (fun v => 2 * x v * m) = 0 := by
    rw [← Finset.sum_mul]; rw [← Finset.mul_sum]; grind
  -- Lemma 5, p. 6: ||x + c1||² = ||x||² + ||c1||², so the denominator grows.
  have h_den : G.deg_norm x ≤ G.deg_norm (fun v => x v - m) := by
    rw [deg_norm_eq_sum_reg G x d h_reg, deg_norm_eq_sum_reg G (fun v => x v - m) d h_reg]
    rw [← Finset.mul_sum, ← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    simp only [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h_cross]
    simp only [sub_zero, le_add_iff_nonneg_right]
    positivity
  -- Lemma 5, p. 6: translating every coordinate leaves each edge difference unchanged.
  have h_num : G.energy (fun v => x v - m) = G.energy x := by
    unfold SimpleGraph.energy; apply Finset.sum_congr rfl; grind
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm, h_num]
  apply div_le_div_of_nonneg_left
  · exact energy_nonneg G x
  · exact deg_norm_pos_of_regular G d h_d_pos h_reg h_x_ne
  · exact h_den

/-- Lecture 2, Lemma 5, p. 7: at least one of x⁺ and x⁻ has R no larger than R(x′). -/
lemma shifted_part_rayleigh_le (x : α → ℝ) (m : ℝ)
    (h_shift_norm_pos : 0 < G.deg_norm (fun v => x v - m)) :
    ∃ y : α → ℝ, (y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0)) ∧
    (∀ v, 0 ≤ y v) ∧ (∃ v ∈ G.vertexFinset, 0 < y v) ∧
    SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G (fun v => x v - m) := by
  let z : α → ℝ := fun v => x v - m
  -- Lemma 5, p. 7: write the centered vector as x′ = x⁺ - x⁻.
  let parts : Bool → α → ℝ := fun b v => max (if b then z v else -(z v)) 0
  have hnonneg : ∀ b v, 0 ≤ parts b v := fun _ _ => le_max_right _ _
  -- Disjoint positive/negative supports give ||x′||² = ||x⁺||² + ||x⁻||².
  have hnorm : ∑ b : Bool, G.deg_norm (parts b) = G.deg_norm z := by
    simpa [parts, add_comm] using deg_norm_shifted_parts_add G z
  -- Lemma 5, p. 7: sum the edgewise inequality to bound the two parts' energies.
  have henergy : ∑ b : Bool, G.energy (parts b) ≤ G.energy z := by
    simpa [parts, add_comm] using energy_shifted_parts_add_le G z
  -- Lemma 5, p. 7: one ratio is at most the weighted average, hence at most R(x′).
  obtain ⟨b, _, hb_pos, hb_le⟩ := exists_ratio_le_of_sum_le Finset.univ
    (fun b => G.energy (parts b)) (fun b => G.deg_norm (parts b))
    (G.rayleighQuotient z) (fun b _ => energy_nonneg G (parts b))
    (fun b _ => deg_norm_nonneg G (parts b)) (by rwa [hnorm]) (by
      rw [hnorm, rQ_eq_energy_div_norm, div_mul_cancel₀ _ h_shift_norm_pos.ne']
      exact henergy)
  refine ⟨parts b, ?_, hnonneg b, ?_, hb_le⟩
  · cases b <;> simp [parts, z, neg_sub]
  -- Formal support: the chosen positive denominator ensures this part is nonzero.
  · obtain ⟨v, hv, hterm⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun v (_ : v ∈ G.vertexFinset) =>
        mul_nonneg (Nat.cast_nonneg (G.degree v)) (sq_nonneg (parts b v)))).1 hb_pos
    refine ⟨v, hv, ?_⟩
    by_contra h
    have : parts b v = 0 := le_antisymm (le_of_not_gt h) (hnonneg b v)
    simp [this] at hterm

/-- Lecture 2, Lemma 5, pp. 6–7: median splitting gives a nonnegative small-support vector
with R(y) ≤ R(x), whose threshold cuts are considered by Fiedler's algorithm on x. -/
lemma lemma_5_exists_median_split_witness (x : α → ℝ) (d : ℕ) (hV : 2 ≤ (G.vertexFinset).card)
    (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ G.vertexFinset, x v ≠ 0)
    (h_orth : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    ∃ y : α → ℝ, (∀ v, 0 ≤ y v) ∧ (∃ v ∈ G.vertexFinset, 0 < y v) ∧
      (2 * (G.vertexFinset.filter (fun v => y v > 0)).card ≤ G.vertexFinset.card) ∧
      SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G x ∧
      (∀ t > 0, ({v ∈ G.vertexFinset | y v ≥ t} : Finset α).Nonempty →
        {v ∈ G.vertexFinset | y v ≥ t} ∈ sweepCuts G x) := by
  -- Lemma 5, p. 7: center at a median so both strict sign supports have size ≤ |V|/2.
  obtain ⟨m, h_upper, h_lower⟩ := exists_balanced_median G x hV
  -- Formal support: a nonzero vector orthogonal to constants cannot become identically zero.
  have h_shift_ne : ∃ v ∈ G.vertexFinset, x v - m ≠ 0 := by
    by_contra h_no; push Not at h_no
    have h_sum_weight : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) =
        G.vertexFinset.sum (fun _ => (d : ℝ) * m) := by
      apply Finset.sum_congr rfl; grind
    have h_dm_zero : (d : ℝ) * m * (G.vertexFinset.card : ℝ) = 0 := by
      rw [h_sum_weight, Finset.sum_const] at h_orth; grind
    have hd_pos : (0 : ℝ) < d := mod_cast Nat.pos_of_ne_zero h_d_pos
    have hV_pos : (0 : ℝ) < (G.vertexFinset.card : ℝ) := mod_cast
        (by omega : 0 < G.vertexFinset.card)
    have hV_ne : ((G.vertexFinset.card : ℝ) ≠ 0) := ne_of_gt hV_pos
    grind
  -- Lemma 5, p. 7: choose the positive or negative part with the better Rayleigh quotient.
  obtain ⟨y, hy_side, hy_nonneg, hy_pos, hy_ray_shift⟩ :=
    shifted_part_rayleigh_le G x m (deg_norm_pos_of_regular G d h_d_pos h_reg h_shift_ne)
  -- Lemma 5, p. 7: the chosen part inherits the median's support bound.
  have hy_support : 2 * (G.vertexFinset.filter (fun v => y v > 0)).card ≤ G.vertexFinset.card := by
    rcases hy_side with rfl | rfl
    · have h_set : G.vertexFinset.filter (fun v => max (x v - m) 0 > 0) =
          G.vertexFinset.filter (fun v => x v > m) := by grind
      rw [h_set]
      omega
    · have h_set : G.vertexFinset.filter (fun v => max (m - x v) 0 > 0) =
          G.vertexFinset.filter (fun v => x v < m) := by grind
      rw [h_set]
      omega
  -- Lemma 5: combine R(y) ≤ R(x′) with the translation bound R(x′) ≤ R(x).
  have hy_ray_x : SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G x :=
    hy_ray_shift.trans (median_shift_rayleigh_le G x d m h_d_pos h_x_ne h_orth h_reg)
  refine ⟨y, hy_nonneg, hy_pos, hy_support, hy_ray_x, ?_⟩
  -- Lemma 5's furthermore clause, p. 7: recover a threshold of the original vector x.
  intro t ht h_nonempty
  have h_subset : ({v ∈ G.vertexFinset | y v ≥ t} : Finset α) ⊆
      G.vertexFinset.filter (fun v => y v > 0) := by grind
  have h_card_le := Finset.card_le_card h_subset
  have h_card : 2 * ({v ∈ G.vertexFinset | y v ≥ t} : Finset α).card ≤
      G.vertexFinset.card := by omega
  rcases hy_side with rfl | rfl
  · -- Lemma 5, p. 7: a positive-part threshold corresponds to x ≥ m + t.
    unfold sweepCuts
    simp only [Finset.mem_union]
    right; right
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, h_nonempty, h_card, m + t, ?_⟩
    ext v
    simp only [Finset.mem_filter, ge_iff_le, le_max_iff, not_le.mpr ht, or_false]
    constructor <;> rintro ⟨hv, h⟩ <;> exact ⟨hv, by linarith⟩
  · -- Lemma 5, p. 7: a negative-part threshold corresponds to x ≤ m - t.
    unfold sweepCuts
    simp only [Finset.mem_union]
    right; left
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, h_nonempty, h_card, m - t, ?_⟩
    ext v
    simp only [Finset.mem_filter, ge_iff_le, le_max_iff, not_le.mpr ht, or_false]
    constructor <;> rintro ⟨hv, h⟩ <;> exact ⟨hv, by linarith⟩

/-- Lecture 2, Lemma 4, p. 6, proved as Lecture 3, Lemma 1, pp. 1–2:
there is a nonempty positive threshold cut with expansion at most sqrt(2 R(y)). -/
lemma lemma_4_sweep_threshold_expansion_bound (d : ℕ) (y : α → ℝ) (h_d_pos : d ≠ 0)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    (h_pos : ∀ v, 0 ≤ y v) (h_y_pos : ∃ v ∈ G.vertexFinset, 0 < y v) :
    ∃ t > 0, let S_t := G.vertexFinset.filter (fun v => y v ≥ t)
      S_t.Nonempty ∧ edgeExpansion G d S_t ≤ Real.sqrt (2 * SimpleGraph.rayleighQuotient G y) := by
  -- Lecture 3, Lemma 1, p. 1: discretize the law in which t² is uniform.
  let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
  let w := coareaWeight levels
  -- Finite bookkeeping: distinct positive levels give strictly positive interval masses.
  have hw_pos : ∀ t ∈ levels, 0 < w t := by
    intro t ht
    have ht_pos := (Finset.mem_filter.mp ht).2
    unfold w coareaWeight previousLevel
    split_ifs with h
    · have hmem := Finset.max'_mem _ h
      have hpred_pos := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
      have hpred_lt := (Finset.mem_filter.mp hmem).2
      nlinarith
    · simpa using sq_pos_of_pos ht_pos
  have h_norm_pos : 0 < G.deg_norm y :=
    deg_norm_pos_of_regular G d h_d_pos h_reg (by grind)
  -- Lecture 3, p. 2: compute the expected denominator d|S_t|.
  have hvolume : ∑ t ∈ levels, w t * ((d * (G.vertexFinset.filter (y · ≥ t)).card : ℕ) : ℝ) =
      G.deg_norm y := level_coarea_volume_identity G d y h_reg h_pos
  -- Lecture 3, equation (1), pp. 1–2: the ratio of expectations is at most sqrt(2 R(y)).
  have h_sum_bound : ∑ t ∈ levels, w t * (Cut G (G.vertexFinset.filter (y · ≥ t))).card ≤
      Real.sqrt (2 * G.rayleighQuotient y) *
        ∑ t ∈ levels, w t * ((d * (G.vertexFinset.filter (y · ≥ t)).card : ℕ) : ℝ) := by
    rw [hvolume, rQ_eq_energy_div_norm]
    calc
      ∑ t ∈ levels, w t * (Cut G (G.vertexFinset.filter (y · ≥ t))).card
        ≤ Real.sqrt (2 * G.energy y * G.deg_norm y) :=
          (level_cut_sum_le_edge_abs_sq_diff_sum G y h_pos).trans
            (edge_abs_sq_diff_sum_le_sqrt_energy_deg_norm G y h_pos)
      -- The final algebra in Lecture 3, p. 2: divide the boundary bound by the degree norm.
      _ = Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y := by
        symm
        calc
          Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y =
              Real.sqrt (2 * (G.energy y / G.deg_norm y)) * Real.sqrt (G.deg_norm y ^ 2) := by
            rw [Real.sqrt_sq h_norm_pos.le]
          _ = Real.sqrt ((2 * (G.energy y / G.deg_norm y)) * G.deg_norm y ^ 2) :=
            (Real.sqrt_mul (mul_nonneg (by norm_num)
              (div_nonneg (energy_nonneg G y) h_norm_pos.le)) _).symm
          _ = Real.sqrt (2 * G.energy y * G.deg_norm y) := by
            congr 1
            field_simp
  -- Lecture 3, Fact 2, pp. 1–2: some threshold ratio is at most the ratio of expectations.
  obtain ⟨t, ht_mem, _, ht_ratio⟩ := exists_ratio_le_of_sum_le levels
    (fun t => w t * (Cut G (G.vertexFinset.filter (y · ≥ t))).card)
    (fun t => w t * ((d * (G.vertexFinset.filter (y · ≥ t)).card : ℕ) : ℝ))
    (Real.sqrt (2 * G.rayleighQuotient y))
    (by intro t ht; exact mul_nonneg (hw_pos t ht).le (Nat.cast_nonneg _))
    (by intro t ht; exact mul_nonneg (hw_pos t ht).le (Nat.cast_nonneg _))
    (by rwa [hvolume]) h_sum_bound
  -- Lecture 3, Lemma 1, p. 1: the selected threshold is positive and its cut is nonempty.
  refine ⟨t, (Finset.mem_filter.mp ht_mem).2, ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht_mem).1
    exact ⟨v, by simp [hv]⟩
  · simpa only [edgeExpansion, Nat.cast_mul,
      mul_div_mul_left _ _ (hw_pos t ht_mem).ne'] using ht_ratio

/-- Lecture 2, Lemma 3, pp. 5–6: Fiedler's cut on x ⊥ 1 has expansion ≤ sqrt(2 R(x)). -/
lemma lemma3 (d : ℕ) (x : α → ℝ) (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ G.vertexFinset, x v ≠ 0)
    (hV : 2 ≤ (G.vertexFinset).card) (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    (h_orth : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0) :
    let S_f := fiedlerCut G d x hV
    S_f.Nonempty ∧ S_f ⊆ G.vertexFinset ∧ 2 * S_f.card ≤ (G.vertexFinset).card ∧
      edgeExpansion G d S_f ≤ Real.sqrt (2 * G.rayleighQuotient x) := by
  intro S_f
  -- Proof of Lemma 3, p. 6: use Lemma 5 to obtain y with R(y) ≤ R(x).
  obtain ⟨y, hy_nonneg, hy_pos, _, hy_rayleigh, hy_sweep⟩ :=
    lemma_5_exists_median_split_witness G x d hV h_d_pos h_x_ne h_orth h_reg
  -- Apply Lemma 4 to choose a threshold cut of y with expansion ≤ sqrt(2 R(y)).
  obtain ⟨t, ht, hSt, hbound⟩ :=
    lemma_4_sweep_threshold_expansion_bound G d y h_d_pos h_reg hy_nonneg hy_pos
  -- Proof of Lemma 3, p. 6: Fiedler's minimum beats this same sweep cut of x.
  obtain ⟨h_ne, h_sub, h_card, h_min⟩ := fiedlerCut_spec G d x hV
  refine ⟨h_ne, h_sub, h_card, ?_⟩
  exact (h_min _ (hy_sweep t ht hSt)).trans
    (hbound.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hy_rayleigh (by norm_num))))

/-- Lecture 2, §4, p. 5: attain λ₂ = min_{x ⊥ 1} R(x).
The compactness argument below supplies the attainment implicit in that characterization. -/
lemma exists_eigenvector_lambda2 [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hV : 2 ≤ #G.vertexFinset) :
    ∃ x : α → ℝ, (∃ v ∈ G.vertexFinset, x v ≠ 0) ∧
      (∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * x v = 0) ∧
      G.rayleighQuotient x = lambda2 G := by
  -- Formal support for the variational minimum: the feasible set contains a nonzero vector.
  have hnonempty : (R_values G).Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < G.vertexFinset.card)
    let x : α → ℝ := fun v => (if v = a then 1 else 0) - (if v = b then 1 else 0)
    refine ⟨G.rayleighQuotient x, x, ⟨?_, a, ha, ?_⟩, rfl⟩
    · calc
        ∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * x v =
            (d : ℝ) * ∑ v ∈ G.vertexFinset, x v := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun v hv => by rw [h_reg v hv])
        _ = 0 := by simp [x, Finset.sum_sub_distrib, ha, hb]
    · simp [x, hab]
  -- Formal support for Lecture 2, p. 5: show that the feasible Rayleigh values are closed.
  have hclosed : IsClosed (R_values G) := by
    -- Formal support: handle d = 0 separately before normalizing the degree norm.
    by_cases h_d_pos : d = 0
    · have hzero : ∀ x : α → ℝ, G.rayleighQuotient x = 0 := by
        intro x
        rw [rQ_eq_energy_div_norm, deg_norm_eq_sum_reg G x 0 (by simpa [h_d_pos] using h_reg)]
        simp
      have hvalues : R_values G = {0} := by
        obtain ⟨r, hr⟩ := hnonempty
        ext s
        simp only [R_values, Set.mem_setOf_eq, Set.mem_singleton_iff, hzero] at hr ⊢
        grind
      rw [hvalues]
      exact isClosed_singleton
    -- Formal support for attainment: work with vectors of degree norm one.
    · let K : Set (α → ℝ) := {x | (∀ v, v ∉ G.vertexFinset → x v = 0) ∧
        x ∈ orthogonalVectors G ∧ G.deg_norm x = 1}
      -- Formal support: closedness and boundedness make the normalized feasible set compact.
      have hcompact : IsCompact K := by
        haveI := Fintype.ofFinite α
        haveI : ProperSpace (α → ℝ) := FiniteDimensional.proper ℝ (α → ℝ)
        have hsupport : IsClosed {x : α → ℝ | ∀ v, v ∉ G.vertexFinset → x v = 0} := by
          simp only [Set.setOf_forall]
          exact isClosed_iInter fun v => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply v) continuous_const
        have horthClosed :
            IsClosed {x : α → ℝ | G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0} := by
          apply isClosed_eq _ continuous_const; apply continuous_finsetSum
          intro v hv; exact continuous_const.mul (continuous_apply v)
        have hnormClosed : IsClosed {x : α → ℝ | G.deg_norm x = 1} := by
          apply isClosed_eq _ continuous_const
          unfold SimpleGraph.deg_norm
          apply continuous_finsetSum
          intro v hv; exact continuous_const.mul ((continuous_apply v).pow 2)
        -- Norm one implies nonzeroness, so the remaining constraints are closed equalities.
        have hK_eq : K = {x : α → ℝ | (∀ v, v ∉ G.vertexFinset → x v = 0)} ∩
            {x : α → ℝ | G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0} ∩
            {x : α → ℝ | G.deg_norm x = 1} := by
          ext x; constructor
          · intro hx; rcases hx with ⟨hsupp, ⟨horth, hne⟩, hnorm⟩; exact ⟨⟨hsupp, horth⟩, hnorm⟩
          · intro hx; rcases hx with ⟨⟨hsupp, horth⟩, hnorm⟩; refine ⟨hsupp, ⟨horth, ?_⟩, hnorm⟩
            by_contra hnone
            have hzero_norm : G.deg_norm x = 0 := by
              unfold SimpleGraph.deg_norm; apply Finset.sum_eq_zero; grind
            grind
        have hclosed : IsClosed K := by
          rw [hK_eq]; exact (hsupport.inter horthClosed).inter hnormClosed
        -- Positive regular degree bounds each coordinate of a norm-one feasible vector.
        have hbounded : Bornology.IsBounded K := by
          rw [Metric.isBounded_iff_subset_closedBall (0 : α → ℝ)]; refine ⟨1, ?_⟩; intro x hx
          rw [Metric.mem_closedBall, dist_zero_right, Pi.norm_def]
          change (Finset.univ.sup fun b => ‖x b‖₊) ≤ (1 : NNReal)
          apply Finset.sup_le_iff.mpr; intro v hv
          by_cases hvV : v ∈ G.vertexFinset
          · have hterm : (d : ℝ) * x v ^ 2 ≤ 1 := by
              have := Finset.single_le_sum
                (fun u (_ : u ∈ G.vertexFinset) =>
                  mul_nonneg (Nat.cast_nonneg (G.degree u)) (sq_nonneg (x u))) hvV
              change (G.degree v : ℝ) * x v ^ 2 ≤ G.deg_norm x at this
              simpa only [hx.2.2, h_reg v hvV] using this
            have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h_d_pos
            have hsq : x v ^ 2 ≤ 1 :=
              (le_mul_of_one_le_left (sq_nonneg _) hd).trans hterm
            exact NNReal.coe_le_coe.mp (by
              simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using
                (sq_le_one_iff_abs_le_one (x v)).1 hsq)
          · exact NNReal.coe_le_coe.mp (by simp [hx.1 v hvV])
        exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbounded⟩
      -- Formal support for Lecture 2, p. 5: normalization preserves all Rayleigh values.
      have himage : R_values G = (fun x : α → ℝ => G.rayleighQuotient x) '' K := by
        ext r; constructor
        · intro hr; rcases hr with ⟨x, hxorth, rfl⟩
          -- Restrict to graph vertices to match the lecture's ambient space ℝ^V.
          let y0 := restrictToVertexSet G x
          let n := G.deg_norm y0
          -- Scalar invariance of R (also used in Lecture 3, Lemma 1, p. 1) permits scaling.
          let c : ℝ := (Real.sqrt n)⁻¹
          let y : α → ℝ := fun v => c * y0 v
          have hn_pos : 0 < n := by
            dsimp [n, y0]
            rw [deg_norm_restrictToVertexSet]
            exact deg_norm_pos_of_regular G d h_d_pos h_reg hxorth.2
          have hy0orth : y0 ∈ orthogonalVectors G :=
            orthogonalVectors_restrictToVertexSet G x hxorth
          refine ⟨y, ?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · grind
            · rcases hy0orth with ⟨hy0_sum, hy0_ne⟩
              constructor
              · unfold y
                calc
                  ∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * (c * y0 v)
                    = c * ∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * y0 v := by
                      rw [Finset.mul_sum]
                      grind
                  _ = 0 := by rw [hy0_sum, mul_zero]
              · grind
            · grind [deg_norm_mul G y0 c]
          · calc
              G.rayleighQuotient y = G.rayleighQuotient (fun v => c * y0 v) := rfl
              _ = G.rayleighQuotient y0 := rayleighQuotient_mul G y0 (by grind)
              _ = G.rayleighQuotient x := rayleighQuotient_restrictToVertexSet G x
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx.2.1, rfl⟩
      -- Formal support: R is continuous where its denominator is fixed to one.
      have hcont : ContinuousOn (fun x : α → ℝ => G.rayleighQuotient x) K := by
        unfold SimpleGraph.rayleighQuotient
        apply ContinuousOn.div
        · apply Continuous.continuousOn
          apply continuous_finsetSum
          intro e he
          induction e using Sym2.ind with
          | h u v => simpa using ((continuous_apply u).sub (continuous_apply v)).pow 2
        · apply Continuous.continuousOn
          apply continuous_finsetSum
          intro v hv
          exact continuous_const.mul ((continuous_apply v).pow 2)
        · intro x hx
          change G.deg_norm x ≠ 0
          rw [hx.2.2]
          norm_num
      rw [himage]
      exact (hcompact.image_of_continuousOn hcont).isClosed
  -- Formal support for Lecture 2, p. 5: the closed nonempty value set contains its infimum.
  obtain ⟨x, hx, hvalue⟩ := hclosed.csInf_mem hnonempty
    (by simpa [R_values, orthogonalVectors, and_assoc] using lambda2_bounded_below G)
  exact ⟨x, hx.2, hx.1, hvalue.symm⟩

/-- Lecture 2, Theorem 1, p. 4 (hard direction): φ(G) ≤ sqrt(2 λ₂), using Lemma 3. -/
theorem cheeger_hard_direction [Finite α] (d : ℕ)
    (hV : 2 ≤ #G.vertexFinset)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    graphExpansion G d ≤ Real.sqrt (2 * lambda2 G) := by
  -- Formal support: the zero-degree case has zero expansion.
  by_cases hd : d = 0
  · rw [hd, graphExpansion_zero_degree]
    exact Real.sqrt_nonneg _
  -- Lecture 2, §4, p. 5: choose x ⊥ 1 with R(x) = λ₂.
  obtain ⟨x, hx, horth, h_lambda⟩ := exists_eigenvector_lambda2 G d h_reg hV
  -- Lecture 2, Lemma 3: Fiedler's cut then has expansion at most sqrt(2 λ₂).
  obtain ⟨hS_ne, hS_sub, hS_size, hS_phi⟩ := lemma3 G d x hd hx hV h_reg horth
  rw [← h_lambda]
  -- Theorem 1: graph expansion is bounded by the expansion of this valid cut.
  apply le_trans ?_ hS_phi
  unfold graphExpansion
  dsimp only
  rw [dif_pos (by
    simpa only [graphExpansionValidSubsets] using
      graphExpansionValidSubsets_nonempty_of_valid G _ hS_ne hS_sub hS_size)]
  exact Finset.min'_le _ _
    (edgeExpansion_mem_graphExpansion_image_of_valid G d _ hS_ne hS_sub hS_size)

end Spectral
end GraphLib
