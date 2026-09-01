import GraphLib.Theory.Spectral.Expansion
import GraphLib.Theory.Spectral.Coarea
import GraphLib.Theory.Spectral.Fiedler

namespace GraphLib
namespace Spectral

open Finset
open ProbabilityTheory MeasureTheory
open Cuts

variable {α : Type*} (G : SimpleGraph α)
  [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
/-- A median value for `x` whose strict upper and lower level sets both have
cardinality at most half of `G.vertexFinset`. -/
lemma exists_balanced_median (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) : ∃ m : ℝ,
    (G.vertexFinset.filter (fun v => x v > m)).card ≤ (G.vertexFinset).card / 2 ∧
    (G.vertexFinset.filter (fun v => x v < m)).card ≤ (G.vertexFinset).card / 2 := by
  classical
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
  have h_nodup : sortedV.Nodup := by
    simpa [sortedV] using (G.vertexFinset.nodup_toList.mergeSort (le := fun u v => x u ≤ x v))
  have h_mem_sorted_iff : ∀ v, v ∈ sortedV ↔ v ∈ G.vertexFinset := by
    intro v; simp [sortedV]
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

/-- Shifting by a balanced median does not increase the Rayleigh quotient for a
degree-regular graph when `x` is degree-orthogonal to constants. -/
lemma median_shift_rayleigh_le (x : α → ℝ) (d : ℕ) (m : ℝ) (h_d_pos : d ≠ 0)
    (h_x_ne : ∃ v ∈ G.vertexFinset, x v ≠ 0)
    (h_orth : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    SimpleGraph.rayleighQuotient G (fun v => x v - m) ≤ SimpleGraph.rayleighQuotient G x := by
  have h_weight : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) =
      (d : ℝ) * G.vertexFinset.sum (fun v => x v) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; grind
  have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast h_d_pos
  have h_cross : G.vertexFinset.sum (fun v => 2 * x v * m) = 0 := by
    rw [← Finset.sum_mul]; rw [← Finset.mul_sum]; grind
  have h_den : G.deg_norm x ≤ G.deg_norm (fun v => x v - m) := by
    rw [deg_norm_eq_sum_reg G x d h_reg, deg_norm_eq_sum_reg G (fun v => x v - m) d h_reg]
    rw [← Finset.mul_sum, ← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc
      G.vertexFinset.sum (fun v => x v ^ 2) ≤ G.vertexFinset.sum (fun v => (x v - m) ^ 2) := by
        simp only [sub_sq]; rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h_cross]
        simp only [sub_zero, sum_const, nsmul_eq_mul, le_add_iff_nonneg_right]; positivity
      _ = G.vertexFinset.sum (fun v => (x v - m) ^ 2) := rfl
  have h_num : G.energy (fun v => x v - m) = G.energy x := by
    unfold SimpleGraph.energy; apply Finset.sum_congr rfl; grind
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm, h_num]
  apply div_le_div_of_nonneg_left
  · exact energy_nonneg G x
  · rw [deg_norm_eq_sum_reg G x d h_reg, ← Finset.mul_sum]
    apply mul_pos
    · grind
    · exact sum_sq_pos G x h_x_ne
  · exact h_den

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
lemma exists_pos_of_deg_norm_pos (y : α → ℝ) (hy_nonneg : ∀ v, 0 ≤ y v)
    (h_norm_pos : 0 < G.deg_norm y) :
    ∃ v ∈ G.vertexFinset, 0 < y v := by
  unfold SimpleGraph.deg_norm at h_norm_pos
  have h_term_nonneg : ∀ v ∈ G.vertexFinset, 0 ≤ (↑(G.degree v) : ℝ) * y v ^ 2 := by
    intro v hv; exact mul_nonneg (by positivity) (sq_nonneg (y v))
  obtain ⟨v, hv, hv_pos⟩ := (Finset.sum_pos_iff_of_nonneg h_term_nonneg).1 h_norm_pos
  have hdeg_nonneg : (0 : ℝ) ≤ (G.degree v : ℝ) := by positivity
  have hy_sq_pos : 0 < y v ^ 2 := by nlinarith [hdeg_nonneg, sq_nonneg (y v), hv_pos]
  have hy_ne : y v ≠ 0 := by exact sq_pos_iff.mp hy_sq_pos
  grind

/-- From the positive and negative parts of a shifted vector, choose a nonzero
nonnegative side whose Rayleigh quotient is no larger than that of the shift. -/
lemma shifted_part_rayleigh_le (x : α → ℝ) (m : ℝ)
    (h_shift_norm_pos : 0 < G.deg_norm (fun v => x v - m)) :
    ∃ y : α → ℝ, (y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0)) ∧
    (∀ v, 0 ≤ y v) ∧ (∃ v ∈ G.vertexFinset, 0 < y v) ∧
    SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G (fun v => x v - m) := by
  let z : α → ℝ := fun v => x v - m; let p : α → ℝ := fun v => max (z v) 0
  let n : α → ℝ := fun v => max (-(z v)) 0
  let Ez := G.energy z; let Ep := G.energy p; let En := G.energy n
  let Cz := G.deg_norm z; let Cp := G.deg_norm p; let Cn := G.deg_norm n
  let Rz := Ez / Cz
  have hp_nonneg : ∀ v, 0 ≤ p v := by intro v; exact le_max_right _ _
  have hn_nonneg : ∀ v, 0 ≤ n v := by intro v; exact le_max_right _ _
  have hEp_nonneg : 0 ≤ Ep := by exact energy_nonneg G p
  have hEn_nonneg : 0 ≤ En := by exact energy_nonneg G n
  have hCn_nonneg : 0 ≤ Cn := by exact deg_norm_nonneg G n
  have hCz_pos : 0 < Cz := by simpa [Cz, z] using h_shift_norm_pos
  have h_norm_add : Cp + Cn = Cz := by
    simpa [Cp, Cn, Cz, p, n] using deg_norm_shifted_parts_add G z
  have h_energy_add : Ep + En ≤ Ez := by
    simpa [Ep, En, Ez, p, n] using energy_shifted_parts_add_le G z
  have h_avg : (Ep + En) / (Cp + Cn) ≤ Ez / Cz := by
    rw [h_norm_add]; exact div_le_div_of_nonneg_right h_energy_add (le_of_lt hCz_pos)
  have h_sum_le : Ep + En ≤ Rz * (Cp + Cn) := by
    have hCpCn_pos : 0 < Cp + Cn := by simpa [h_norm_add] using hCz_pos
    have := (div_le_iff₀ hCpCn_pos).1 h_avg
    simpa [Rz, mul_comm] using this
  have h_choose_p (hCp_pos : 0 < Cp) (hp_le : Ep / Cp ≤ Rz) :
      ∃ y : α → ℝ, (y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0)) ∧
      (∀ v, 0 ≤ y v) ∧ (∃ v ∈ G.vertexFinset, 0 < y v) ∧
      SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G (fun v => x v - m) := by
    refine ⟨p, ?_, hp_nonneg, exists_pos_of_deg_norm_pos G p hp_nonneg hCp_pos, ?_⟩
    all_goals grind
  have h_choose_n (hCn_pos : 0 < Cn) (hn_le : En / Cn ≤ Rz) : ∃ y : α → ℝ,
      (y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0)) ∧
      (∀ v, 0 ≤ y v) ∧ (∃ v ∈ G.vertexFinset, 0 < y v) ∧
      SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G (fun v => x v - m) := by
    refine ⟨n, ?_, hn_nonneg, exists_pos_of_deg_norm_pos G n hn_nonneg hCn_pos, ?_⟩
    all_goals grind
  by_cases hCp_pos : 0 < Cp
  · by_cases hp_le : Ep / Cp ≤ Rz
    · exact h_choose_p hCp_pos hp_le
    · have hp_gt : Rz < Ep / Cp := lt_of_not_ge hp_le
      have hCn_pos : 0 < Cn := by
        by_contra hCn_not
        have hCn_zero : Cn = 0 := by grind
        have hp_mul : Rz * Cp < Ep := (lt_div_iff₀ hCp_pos).1 hp_gt
        rw [hCn_zero, add_zero] at h_sum_le
        nlinarith
      have hn_le : En / Cn ≤ Rz := by
        by_contra hn_not
        have hn_gt : Rz < En / Cn := lt_of_not_ge hn_not
        have hp_mul : Rz * Cp < Ep := (lt_div_iff₀ hCp_pos).1 hp_gt
        have hn_mul : Rz * Cn < En := (lt_div_iff₀ hCn_pos).1 hn_gt
        nlinarith
      grind
  · have hCn_pos : 0 < Cn := by nlinarith [h_norm_add, hCz_pos]
    have hn_le : En / Cn ≤ Rz := by rw [div_le_iff₀ hCn_pos]; nlinarith
    grind

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
/-- A chosen positive or negative shifted part inherits the median support bound. -/
lemma shifted_part_support_le_half (x : α → ℝ) (m : ℝ)
    (y : α → ℝ) (hy_side : y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0))
    (h_upper : (G.vertexFinset.filter (fun v => x v > m)).card ≤ (G.vertexFinset).card / 2)
    (h_lower : (G.vertexFinset.filter (fun v => x v < m)).card ≤ (G.vertexFinset).card / 2) :
    2 * (G.vertexFinset.filter (fun v => y v > 0)).card ≤ (G.vertexFinset).card := by
  rcases hy_side with rfl | rfl
  · have h_set : G.vertexFinset.filter (fun v => max (x v - m) 0 > 0) =
      G.vertexFinset.filter (fun v => x v > m) := by grind
    rw [h_set]; omega
  · have h_set : G.vertexFinset.filter (fun v => max (m - x v) 0 > 0) =
      G.vertexFinset.filter (fun v => x v < m) := by grind
    rw [h_set]; omega

omit [DecidablePred (· ∈ G.edgeSet)] in
/-- Nonempty level sets of a chosen shifted part are bounded prefix/suffix sweep cuts. -/
lemma shifted_part_level_mem_sweepCuts (x : α → ℝ) (m : ℝ) (y : α → ℝ)
    (hy_side : y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0))
    (h_support : 2 * (G.vertexFinset.filter (fun v => y v > 0)).card ≤ (G.vertexFinset).card) :
    ∀ t > 0, ({v ∈ G.vertexFinset | y v ≥ t} : Finset α).Nonempty →
      {v ∈ G.vertexFinset | y v ≥ t} ∈ sweepCuts G x := by
  intro t ht h_nonempty
  have h_subset : ({v ∈ G.vertexFinset | y v ≥ t} : Finset α) ⊆
      G.vertexFinset.filter (fun v => y v > 0) := by grind
  have h_card_le : ({v ∈ G.vertexFinset | y v ≥ t} : Finset α).card ≤
      (G.vertexFinset.filter (fun v => y v > 0)).card := Finset.card_le_card h_subset
  have h_card : 2 * ({v ∈ G.vertexFinset | y v ≥ t} : Finset α).card ≤ (G.vertexFinset).card := by
    grind
  rcases hy_side with rfl | rfl
  · unfold sweepCuts; simp only [Finset.mem_union]; right; right
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by grind, h_nonempty, h_card, ⟨m + t, by grind⟩⟩
  · unfold sweepCuts; simp only [Finset.mem_union]; right; left
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by grind, h_nonempty, h_card, ⟨m - t, by grind⟩⟩

/-- Median-splitting lemma used by the sweep proof.
It produces a nonzero nonnegative vector with small support, no larger Rayleigh quotient,
and level sets that are valid sweep cuts of `x`. -/
-- exists_median_split_witness
lemma lemma_5_exists_median_split_witness (x : α → ℝ) (d : ℕ) (hV : 2 ≤ (G.vertexFinset).card)
    (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ G.vertexFinset, x v ≠ 0)
    (h_orth : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    ∃ y : α → ℝ, (∀ v, 0 ≤ y v) ∧ (∃ v ∈ G.vertexFinset, 0 < y v) ∧
      (2 * (G.vertexFinset.filter (fun v => y v > 0)).card ≤ G.vertexFinset.card) ∧
      SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G x ∧
      (∀ t > 0, ({v ∈ G.vertexFinset | y v ≥ t} : Finset α).Nonempty →
        {v ∈ G.vertexFinset | y v ≥ t} ∈ sweepCuts G x) := by
  obtain ⟨m, h_upper, h_lower⟩ := exists_balanced_median G x hV
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
  obtain ⟨y, hy_side, hy_nonneg, hy_pos, hy_ray_shift⟩ :=
    shifted_part_rayleigh_le G x m (by
      rw [deg_norm_eq_sum_reg G (fun v => x v - m) d h_reg, ← Finset.mul_sum]
      apply mul_pos
      · exact_mod_cast Nat.pos_of_ne_zero h_d_pos
      · exact sum_sq_pos G (fun v => x v - m) h_shift_ne)
  have hy_support : 2 * (G.vertexFinset.filter (fun v => y v > 0)).card ≤ G.vertexFinset.card :=
    shifted_part_support_le_half G x m y hy_side h_upper h_lower
  have hy_ray_x : SimpleGraph.rayleighQuotient G y ≤ SimpleGraph.rayleighQuotient G x :=
    hy_ray_shift.trans (median_shift_rayleigh_le G x d m h_d_pos h_x_ne h_orth h_reg)
  exact ⟨y, hy_nonneg, hy_pos, hy_support, hy_ray_x,
    shifted_part_level_mem_sweepCuts G x m y hy_side hy_support⟩

/-- Lemma 4: For a non-negative vector y, there exists a threshold t such that
    the expansion of the set S_t = {v : y_v ≥ t} is at most sqrt(2 * R_L(y)). -/
lemma lemma_4_sweep_threshold_expansion_bound (d : ℕ) (y : α → ℝ) (h_d_pos : d ≠ 0)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    (h_pos : ∀ v, 0 ≤ y v) (h_y_pos : ∃ v ∈ G.vertexFinset, 0 < y v) :
    ∃ t > 0, let S_t := G.vertexFinset.filter (fun v => y v ≥ t)
      S_t.Nonempty ∧ edgeExpansion G d S_t ≤ Real.sqrt (2 * SimpleGraph.rayleighQuotient G y) := by
  obtain ⟨levels, w, hlevels_ne, hlevels_pos, hw_pos, hlevel_sets_ne, hlevel_bound, hvolume_raw⟩ :=
    level_coarea_counting G d y h_reg h_pos h_y_pos
  have h_norm_pos : 0 < G.deg_norm y := by
    rw [deg_norm_eq_sum_reg G y d h_reg, ← Finset.mul_sum]
    apply mul_pos
    · exact_mod_cast Nat.pos_of_ne_zero h_d_pos
    · exact sum_sq_pos G y (by grind)
  have h_sum_bound : ∑ t ∈ levels, w t * (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card ≤
      Real.sqrt (2 * G.rayleighQuotient y) *
        ∑ t ∈ levels, w t * ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) :=
    coarea_bound_to_rayleigh G y d levels w h_norm_pos hlevel_bound hvolume_raw
  obtain ⟨t, ht_mem, ht_denom_pos, ht_ratio⟩ :=
    exists_ratio_le_of_sum_le levels
      (fun t => w t * (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card)
      (fun t => w t * ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ))
      (Real.sqrt (2 * G.rayleighQuotient y))
      hlevels_ne
      (by intro t ht; apply mul_pos (hw_pos t ht)
          exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero h_d_pos)
            (Finset.card_pos.mpr (hlevel_sets_ne t ht)))
      h_sum_bound
  have hw_ne : w t ≠ 0 := ne_of_gt (hw_pos t ht_mem)
  have hdcard_pos : 0 < ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) :=
    mod_cast Nat.mul_pos (Nat.pos_of_ne_zero h_d_pos)
      (Finset.card_pos.mpr (hlevel_sets_ne t ht_mem))
  have hdcard_ne : ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt hdcard_pos
  have hratio_eq : (w t * (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card) /
      (w t * ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ)) =
      ((Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card : ℝ) /
      ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) := by
    field_simp [hw_ne, hdcard_ne]
  grind

lemma lemma3 (d : ℕ) (x : α → ℝ) (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ G.vertexFinset, x v ≠ 0)
    (hV : 2 ≤ (G.vertexFinset).card) (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    (h_orth : G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0) :
    let S_f := fiedlerCut G d x hV
    S_f.Nonempty ∧ S_f ⊆ G.vertexFinset ∧ 2 * S_f.card ≤ (G.vertexFinset).card ∧
      edgeExpansion G d S_f ≤ Real.sqrt (2 * G.rayleighQuotient x) := by
  intro S_f; let R_x := G.rayleighQuotient x
  obtain ⟨y, h_pos, h_y_pos, h_supp, h_rayleigh, h_sweep_subset⟩ :=
    lemma_5_exists_median_split_witness G x d hV h_d_pos h_x_ne h_orth h_reg
  obtain ⟨t, ht_pos, hSt_ne, h_lem_4⟩ :=
    lemma_4_sweep_threshold_expansion_bound G d y h_d_pos h_reg h_pos h_y_pos
  let S_t := G.vertexFinset.filter (fun v => y v ≥ t)
  let expansion_vals := (sweepCuts G x).image (fun S => edgeExpansion G d S)
  let h_nonempty := sweepCuts_expansion_nonempty G d x hV
  have h_Sf_is_min : edgeExpansion G d (fiedlerCut G d x hV) = expansion_vals.min' h_nonempty := by
    grind
  have h_exp_bound : edgeExpansion G d S_f ≤ edgeExpansion G d S_t := by
    unfold S_f; rw [h_Sf_is_min]; apply Finset.min'_le; grind
  -- Algebraic Chain: ϕ(S_f)² ≤ ϕ(S_t)² ≤ 2R(y) ≤ 2R(x)
  have h_alg : edgeExpansion G d S_f ≤ Real.sqrt (2 * G.rayleighQuotient x) := by
    calc edgeExpansion G d S_f
      _ ≤ edgeExpansion G d S_t := by grind
      _ ≤ Real.sqrt (2 * G.rayleighQuotient y) := by grind
      _ ≤ Real.sqrt (2 * G.rayleighQuotient x) := by apply Real.sqrt_le_sqrt (by grind)
  exact ⟨fiedlerCut_nonempty G d x hV, fiedlerCut_is_subset G d x hV,
    fiedlerCut_card_le_half G d x hV, h_alg⟩

/-- Lemma: There exists a non-zero vector x orthogonal to the constant vector
    such that its Rayleigh quotient achieves λ₂. -/
lemma R_values_nonempty_of_regular_two_vertices [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hV : 2 ≤ #G.vertexFinset) :
    (R_values G).Nonempty := by
  have hcard : 1 < (G.vertexFinset).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  let x : α → ℝ := fun v => if v = a then (1 : ℝ) else if v = b then (-1 : ℝ) else 0
  refine ⟨G.rayleighQuotient x, ?_⟩; refine ⟨x, ?_, rfl⟩
  constructor
  · rw [show G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) =
      ∑ v ∈ G.vertexFinset, (d : ℝ) * x v by grind]
    rw [show (∑ v ∈ G.vertexFinset, (d : ℝ) * x v) = (d : ℝ) * ∑ v ∈ G.vertexFinset, x v by
      rw [Finset.mul_sum]]
    have hV_eq : G.vertexFinset = insert a (insert b ((G.vertexFinset.erase a).erase b)) := by grind
    have hrest : ∑ v ∈ (G.vertexFinset.erase a).erase b, x v = 0 := by
      apply Finset.sum_eq_zero; grind
    grind
  · grind

lemma R_values_bddBelow :
    BddBelow (R_values G) := by
  refine ⟨0, ?_⟩; intro r hr; rcases hr with ⟨x, hx, rfl⟩; exact rayleighQuotient_nonneg G x

/-- Compactness/closedness interface for the Rayleigh values on nonzero vectors
orthogonal to constants.  The proof is by normalizing to `deg_norm = 1`,
using finite-dimensional compactness of the normalized feasible set, and then
projecting the continuous SimpleGraph.energy function to `ℝ`. -/
lemma R_values_isClosed_of_regular_two_vertices [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hV : 2 ≤ #G.vertexFinset) :
    IsClosed (R_values G) := by
  by_cases h_d_pos : d = 0
  · have hreg0 : ∀ v ∈ G.vertexFinset, G.degree v = 0 := by grind
    rw [R_values_eq_singleton_zero_of_regular_zero G hreg0 hV]
    exact isClosed_singleton
  · rw [R_values_eq_rayleigh_image_normalizedSupportedOrthogonal G d h_d_pos h_reg]
    exact ((normalizedSupportedOrthogonal_isCompact G d h_d_pos h_reg).image_of_continuousOn
      (continuous_rayleighQuotient_on_normalizedSupportedOrthogonal G)).isClosed

lemma lambda2_mem_R_values_of_regular_two_vertices [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hV : 2 ≤ #G.vertexFinset) :
    lambda2 G ∈ R_values G := by
  unfold lambda2
  exact (R_values_isClosed_of_regular_two_vertices G d h_reg hV).csInf_mem
    (R_values_nonempty_of_regular_two_vertices G d h_reg hV) (R_values_bddBelow G)

lemma exists_eigenvector_lambda2 [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hV : 2 ≤ #G.vertexFinset) :
    ∃ x : α → ℝ, (∃ v ∈ G.vertexFinset, x v ≠ 0) ∧
      (∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * x v = 0) ∧
      G.rayleighQuotient x = lambda2 G := by
  obtain ⟨x, hx_orth, hx_rayleigh⟩ :=
    lambda2_mem_R_values_of_regular_two_vertices G d h_reg hV
  grind

/-- `graphExpansion` is no larger than the expansion of any valid nonempty subset. -/
lemma graphExpansion_le_of_valid (d : ℕ) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ G.vertexFinset)
    (hS_size : 2 * S.card ≤ (G.vertexFinset).card) :
    graphExpansion G d ≤ edgeExpansion G d S := by
  unfold graphExpansion; dsimp only
  rw [dif_pos (by
    simpa only [graphExpansionValidSubsets] using
      graphExpansionValidSubsets_nonempty_of_valid G S hS_ne hS_sub hS_size)]
  exact Finset.min'_le _ _
    (edgeExpansion_mem_graphExpansion_image_of_valid G d S hS_ne hS_sub hS_size)

/-- The Hard Direction of Cheeger's Inequality: h(G) ≤ √(2 * λ₂) -/
theorem cheeger_hard_direction [Finite α] (d : ℕ)
    (hV : 2 ≤ #G.vertexFinset)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    graphExpansion G d ≤ Real.sqrt (2 * lambda2 G) := by
  -- 1. Obtain the second eigenvector x with R(x) = λ₂
  obtain ⟨x, h_x_ne, h_orth, h_lambda2⟩ := exists_eigenvector_lambda2 G d h_reg hV
  -- 3. Handle the d = 0 case (isolated vertices)
  by_cases h_d_pos : d = 0
  · -- If d = 0, expansion is 0 and lambda2 is 0.
    rw [h_d_pos, graphExpansion_zero_degree]
    exact Real.sqrt_nonneg _
  -- 4. Apply Lemma 3 (The Sweep Cut Lemma)
  -- This provides a cut S_f (the Fiedler cut) from the level sets of x
  let S_f := fiedlerCut G d x hV
  obtain ⟨hS_ne, hS_sub, hS_size, hS_phi⟩ := lemma3 G d x h_d_pos h_x_ne hV h_reg  h_orth
  -- 5. Relate h(G) to the expansion of this specific Fiedler cut
  -- Since h(G) = min_{|S|≤n/2} ϕ(S), and Lemma 3 guarantees S_f is valid:
  have h_cheeger_le : graphExpansion G d ≤ edgeExpansion G d S_f := by
    exact graphExpansion_le_of_valid G d S_f hS_ne hS_sub hS_size
  -- 6. Final Chain of Inequalities
  calc
    graphExpansion G d ≤ edgeExpansion G d S_f := h_cheeger_le
    _ ≤ Real.sqrt (2 * G.rayleighQuotient x) := hS_phi
    _ = Real.sqrt (2 * lambda2 G) := by rw [h_lambda2]

end Spectral
end GraphLib
