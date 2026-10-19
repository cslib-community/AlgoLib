import GraphLib.Theory.Spectral.Expansion

-- Cheeger upper bound, finite coarea identities
-- Authors: Weixuan Yuan, Yuchen Zhong
-- LLM: Gemini, GPT-5.6, 6.1 Sol on codex

/-!
These finite sums formalize the expectations in Luca Trevisan's Lecture 3, §1, pp. 1–2:
https://lucatrevisan.github.io/41000-22/lecture03.pdf
Squared level gaps replace the intervals of the uniform squared-threshold distribution.
-/

namespace GraphLib
namespace Spectral

open Finset Cuts

variable {α : Type*} (G : SimpleGraph α)
  [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]

/-- Finite bookkeeping for Lecture 3, Lemma 1: the previous threshold interval endpoint. -/
@[grind] noncomputable def previousLevel (levels : Finset ℝ) (t : ℝ) : ℝ :=
  if h : (levels.filter (fun s => s < t)).Nonempty then
    (levels.filter (fun s => s < t)).max' h
  else 0

/-- Lecture 3, Lemma 1, p. 1: squared threshold gaps give unnormalized interval masses. -/
@[grind] noncomputable def coareaWeight (levels : Finset ℝ) (t : ℝ) : ℝ :=
  t ^ 2 - (previousLevel levels t) ^ 2

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
/-- Lecture 3, proof of Lemma 1, p. 2: the finite-sum version of P[v ∈ S_t] = y_v². -/
lemma sum_coareaWeight_initial_segment_eq_value_sq (y : α → ℝ) (h_pos : ∀ v, 0 ≤ y v) (v : α)
    (hv : v ∈ G.vertexFinset) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t = y v ^ 2 := by
  -- Finite bookkeeping for the threshold law: consecutive squared gaps telescope.
  have htelescope (s : Finset ℝ) : ∑ t ∈ s, coareaWeight s t =
      if h : s.Nonempty then (s.max' h) ^ 2 else 0 := by
    refine Finset.induction_on_max s ?_ ?_
    · simp
    · intro a s h_all_lt ih
      have h_weight_a : coareaWeight (insert a s) a =
          a ^ 2 - (if h : s.Nonempty then (s.max' h) ^ 2 else 0) := by
        unfold coareaWeight previousLevel
        rw [show (insert a s).filter (fun t => t < a) = s by grind]
        grind
      have h_sum_s :
          ∑ t ∈ s, coareaWeight (insert a s) t = ∑ t ∈ s, coareaWeight s t := by
        apply Finset.sum_congr rfl
        intro t ht
        unfold coareaWeight previousLevel
        rw [show (insert a s).filter (fun r => r < t) = s.filter (fun r => r < t) by grind]
      have hne := Finset.insert_nonempty a s
      have hmax : (insert a s).max' hne = a := by
        apply le_antisymm
        · exact Finset.max'_le _ _ _ (by grind)
        · exact Finset.le_max' _ a (by simp)
      grind
  intro levels
  by_cases hv_pos : 0 < y v
  · have hy_mem : y v ∈ levels := by grind
    -- The intervals ending at or below y_v have total mass y_v².
    let initial := levels.filter (fun t => t ≤ y v)
    have hne : initial.Nonempty := ⟨y v, Finset.mem_filter.mpr ⟨hy_mem, le_rfl⟩⟩
    have hmax : initial.max' hne = y v := by
      apply le_antisymm
      · exact Finset.max'_le _ _ _ (by grind)
      · exact Finset.le_max' initial (y v) (Finset.mem_filter.mpr ⟨hy_mem, le_rfl⟩)
    have hsum : ∑ t ∈ initial, coareaWeight levels t =
        ∑ t ∈ initial, coareaWeight initial t := by
      apply Finset.sum_congr rfl
      intro t ht
      unfold coareaWeight previousLevel
      rw [show initial.filter (fun r => r < t) = levels.filter (fun r => r < t) by grind]
    rw [hsum, htelescope initial, dif_pos hne, hmax]
  -- The same vertex-probability formula gives zero mass when y_v = 0.
  · have hy_zero : y v = 0 := by grind
    have hfilter_empty : levels.filter (fun t => t ≤ 0) = ∅ := by grind
    simp [hy_zero, hfilter_empty]

/-- Lecture 3, Lemma 1, p. 2: the finite version of P[{u,v} is cut] = |y_u² - y_v²|. -/
lemma edge_level_cut_weight_sum_le_abs_sq_sub (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) {u v : α} (he : s(u, v) ∈ G.edgeFinset) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (if s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) then (1 : ℝ) else 0)
      ≤ |y u ^ 2 - y v ^ 2| := by
  -- Lecture 3, p. 2: exchange endpoints so the cutting interval is y_u < t ≤ y_v.
  wlog huv : y u ≤ y v generalizing u v
  · simpa only [Sym2.eq_swap, abs_sub_comm] using
      this (by simpa only [Sym2.eq_swap] using he) (le_of_not_ge huv)
  intro levels
  have huV : u ∈ G.vertexFinset := by grind+suggestions
  have hvV : v ∈ G.vertexFinset := by grind+suggestions
  -- Identify exactly the thresholds that separate the two endpoints.
  have hfilter : levels.filter
      (fun t => s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))) =
      levels.filter (fun t => y u < t ∧ t ≤ y v) := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · intro ht
      grind [Cut]
    · rintro ⟨ht, hu, hv⟩
      refine ⟨ht, ?_⟩
      rw [Cut, Finset.mem_filter]
      refine ⟨he, v, ?_, Sym2.mem_mk_right u v, u, ?_, Sym2.mem_mk_left u v⟩
      · simp [hvV, hv]
      · simp [huV, not_le.mpr hu]
  -- Subtract the two vertex masses to obtain the edge cutting mass.
  have hinterval : ∑ t ∈ levels.filter (fun t => y u < t ∧ t ≤ y v),
      coareaWeight levels t = y v ^ 2 - y u ^ 2 := by
    have hsubset : levels.filter (fun t => t ≤ y u) ⊆ levels.filter (fun t => t ≤ y v) := by
      grind
    have hdiff : levels.filter (fun t => y u < t ∧ t ≤ y v) =
        levels.filter (fun t => t ≤ y v) \ levels.filter (fun t => t ≤ y u) := by grind
    rw [hdiff, Finset.sum_sdiff_eq_sub hsubset,
      sum_coareaWeight_initial_segment_eq_value_sq G y h_pos v hvV,
      sum_coareaWeight_initial_segment_eq_value_sq G y h_pos u huV]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hfilter, hinterval,
    abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ (h_pos u) huv 2))]
  linarith

omit G in
/-- Lecture 3, Lemma 1, p. 2: the edge cutting mass |y_u² - y_v²|. -/
@[grind] noncomputable def edgeAbsSqDiff {α : Type*} (y : α → ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u v => |y u ^ 2 - y v ^ 2|, by grind⟩

omit G in
/-- Lecture 3, Lemma 1, p. 2: the endpoint squares in the degree-counting identity. -/
@[grind] noncomputable def edgeEndpointSqSum {α : Type*} (y : α → ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u v => y u ^ 2 + y v ^ 2, by grind⟩

omit G in
/-- Lecture 3, Lemma 1, p. 2: the first factor |y_u - y_v| for Cauchy-Schwarz. -/
@[grind] noncomputable def edgeAbsDiff {α : Type*} (y : α → ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u v => |y u - y v|, by grind⟩

omit G in
/-- Lecture 3, Lemma 1, p. 2: the second factor y_u + y_v for Cauchy-Schwarz. -/
@[grind] noncomputable def edgeEndpointSum {α : Type*} (y : α → ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u v => y u + y v, by grind⟩

/-- Lecture 3, Lemma 1, p. 2: linearity gives E[|∂S_t|] = ∑_{uv ∈ E} P[uv is cut]. -/
lemma level_cut_sum_le_edge_abs_sq_diff_sum (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (Cut G (G.vertexFinset.filter (y · ≥ t))).card ≤
      ∑ e ∈ G.edgeFinset, edgeAbsSqDiff G y e := by
  intro levels
  -- Expand the cut into edge indicators and exchange the level and edge sums.
  calc
    ∑ t ∈ levels, coareaWeight levels t * (Cut G (G.vertexFinset.filter (y · ≥ t))).card
      = ∑ t ∈ levels, coareaWeight levels t * (∑ e ∈ G.edgeFinset,
          if e ∈ Cut G (G.vertexFinset.filter (y · ≥ t)) then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        congr 1
        rw [← Finset.sum_filter]
        have hfilter : {e ∈ G.edgeFinset |
            e ∈ Cut G (G.vertexFinset.filter (y · ≥ t))} =
            Cut G (G.vertexFinset.filter (y · ≥ t)) := by grind
        simp [hfilter]
    _ = ∑ t ∈ levels, ∑ e ∈ G.edgeFinset, coareaWeight levels t *
          (if e ∈ Cut G (G.vertexFinset.filter (y · ≥ t)) then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro t ht; rw [Finset.mul_sum]
    _ = ∑ e ∈ G.edgeFinset, ∑ t ∈ levels, coareaWeight levels t *
          (if e ∈ Cut G (G.vertexFinset.filter (y · ≥ t)) then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ ≤ ∑ e ∈ G.edgeFinset, edgeAbsSqDiff G y e := by
        apply Finset.sum_le_sum; intro e he; induction e using Sym2.ind
        case h u v => simpa [edgeAbsSqDiff, levels] using
            edge_level_cut_weight_sum_le_abs_sq_sub G y h_pos he

/-- Lecture 3, Lemma 1, p. 2: ∑_{uv ∈ E} (y_u + y_v)² ≤ 2d ∑_v y_v². -/
lemma edge_endpoint_sum_sq_le_two_deg_norm (y : α → ℝ) :
    ∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2 ≤ 2 * G.deg_norm y := by
  -- Lecture 3, p. 2: each y_v² occurs once per incident edge, hence degree(v) times.
  have h_endpoint : ∑ e ∈ G.edgeFinset, edgeEndpointSqSum y e = G.deg_norm y := by
    calc
      ∑ e ∈ G.edgeFinset, edgeEndpointSqSum y e
        = ∑ e ∈ G.edgeFinset, ∑ v ∈ G.vertexFinset, (if v ∈ e then y v ^ 2 else 0) := by
          apply Finset.sum_congr rfl; intro e he; induction e using Sym2.ind
          case h u v =>
            simp only [edgeEndpointSqSum, Sym2.lift_mk]
            have huv_ne : u ≠ v := ne_of_mem_edgeSet G u v he
            have huV : u ∈ G.vertexFinset := by grind+suggestions
            have hvV : v ∈ G.vertexFinset := by grind+suggestions
            have hfilter : G.vertexFinset.filter (fun x => x ∈ s(u, v)) = {u, v} := by grind
            symm
            rw [← Finset.sum_filter, hfilter, Finset.sum_pair huv_ne]
      _ = ∑ v ∈ G.vertexFinset, ∑ e ∈ G.edgeFinset, (if v ∈ e then y v ^ 2 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ v ∈ G.vertexFinset, ((G.degree v : ℕ) : ℝ) * y v ^ 2 := by
          apply Finset.sum_congr rfl; intro v hv
          calc
            ∑ e ∈ G.edgeFinset, (if v ∈ e then y v ^ 2 else 0)
              = ((G.edgeFinset.filter (fun e => v ∈ e)).card : ℝ) * y v ^ 2 := by
                rw [← Finset.sum_filter]; simp
            _ = ((G.degree v : ℕ) : ℝ) * y v ^ 2 := by
                have hcard : (G.edgeFinset.filter (fun e => v ∈ e)).card = G.degree v := by
                  rw [← card_incidenceFinset_eq_degree G v, ← Set.ncard_coe_finset]
                  congr 1; ext e; simp [SimpleGraph.incidenceSet]
                rw [hcard]
      _ = G.deg_norm y := by rfl
  -- The second Cauchy-Schwarz estimate is (a + b)² ≤ 2(a² + b²).
  calc
    ∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2
      ≤ ∑ e ∈ G.edgeFinset, 2 * edgeEndpointSqSum y e := by
        apply Finset.sum_le_sum; intro e he; induction e using Sym2.ind
        case h u v =>
          have hsq : (y u + y v) ^ 2 ≤ 2 * (y u ^ 2 + y v ^ 2) := by
            nlinarith [sq_nonneg (y u - y v)]
          simpa [edgeEndpointSum, edgeEndpointSqSum] using hsq
    _ = 2 * G.deg_norm y := by
        rw [← Finset.mul_sum, h_endpoint]

/-- Lecture 3, Lemma 1, p. 2: the Cauchy-Schwarz bound on the expected boundary. -/
lemma edge_abs_sq_diff_sum_le_sqrt_energy_deg_norm (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) :
    ∑ e ∈ G.edgeFinset, edgeAbsSqDiff G y e ≤
      Real.sqrt (2 * G.energy y * G.deg_norm y) := by
  -- The squared first factor is the numerator of the Rayleigh quotient.
  have h_energy : ∑ e ∈ G.edgeFinset, (edgeAbsDiff G y e) ^ 2 = G.energy y := by
    unfold SimpleGraph.energy
    apply Finset.sum_congr rfl
    intro e he
    induction e using Sym2.ind with
    | h u v => simp [edgeAbsDiff, sq_abs]
  -- Lecture 3, p. 2: factor |y_u² - y_v²| as |y_u - y_v|(y_u + y_v).
  calc
    ∑ e ∈ G.edgeFinset, edgeAbsSqDiff G y e
      ≤ ∑ e ∈ G.edgeFinset, edgeAbsDiff G y e * edgeEndpointSum y e := by
        apply Finset.sum_le_sum
        intro e he
        induction e using Sym2.ind with
        | h u v =>
          simp only [edgeAbsSqDiff, edgeAbsDiff, edgeEndpointSum, Sym2.lift_mk]
          rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (h_pos u) (h_pos v)), mul_comm]
    -- Apply the first Cauchy-Schwarz inequality to the two edge factors.
    _ ≤ Real.sqrt (∑ e ∈ G.edgeFinset, (edgeAbsDiff G y e) ^ 2) *
        Real.sqrt (∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    -- Substitute the energy and the second Cauchy-Schwarz/degree-counting estimate.
    _ ≤ Real.sqrt (G.energy y) * Real.sqrt (2 * G.deg_norm y) := by
      rw [h_energy]
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (edge_endpoint_sum_sq_le_two_deg_norm G y)) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * G.energy y * G.deg_norm y) := by
      rw [← Real.sqrt_mul (energy_nonneg G y)]
      ring_nf

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
/-- Lecture 3, Lemma 1, p. 2: the finite-sum version of E[d|S_t|] = d ∑_v y_v². -/
lemma level_coarea_volume_identity (d : ℕ) (y : α → ℝ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels, coareaWeight levels t *
    ((d * (G.vertexFinset.filter (y · ≥ t)).card : ℕ) : ℝ) = G.deg_norm y := by
  intro levels
  -- Lecture 3, p. 2: linearity of expectation, followed by P[v ∈ S_t] = y_v².
  calc
    ∑ t ∈ levels, coareaWeight levels t *
          ((d * (G.vertexFinset.filter (y · ≥ t)).card : ℕ) : ℝ)
      = ∑ t ∈ levels, coareaWeight levels t *
          (∑ v ∈ G.vertexFinset, if t ≤ y v then (d : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        congr 1
        rw [← Finset.sum_filter]
        simp [Nat.cast_mul, mul_comm]
    _ = ∑ t ∈ levels, ∑ v ∈ G.vertexFinset,
          coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro t ht; rw [Finset.mul_sum]
    _ = ∑ v ∈ G.vertexFinset, ∑ t ∈ levels,
          coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ v ∈ G.vertexFinset, (d : ℝ) * y v ^ 2 := by
        apply Finset.sum_congr rfl; intro v hv
        have hpoint := sum_coareaWeight_initial_segment_eq_value_sq G y h_pos v hv
        dsimp [levels] at hpoint
        calc
          ∑ t ∈ levels, coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0)
            = ∑ t ∈ levels, if t ≤ y v then coareaWeight levels t * (d : ℝ) else 0 := by grind
          _ = ∑ t ∈ levels.filter (fun t => t ≤ y v),
                coareaWeight levels t * (d : ℝ) := by rw [← Finset.sum_filter]
          _ = (∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t) * (d : ℝ) := by
              rw [Finset.sum_mul]
          _ = (d : ℝ) * y v ^ 2 := by rw [hpoint]; ring
    _ = G.deg_norm y := by rw [deg_norm_eq_sum_reg G y d h_reg]

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
/-- Formal support for the nonzero Rayleigh denominators in Lecture 2, §4 and Lecture 3, §1. -/
lemma deg_norm_pos_of_regular (d : ℕ) (hd : d ≠ 0)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    {x : α → ℝ} (hx : ∃ v ∈ G.vertexFinset, x v ≠ 0) : 0 < G.deg_norm x := by
  rw [deg_norm_eq_sum_reg G x d h_reg, ← Finset.mul_sum]
  apply mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hd)
  exact (Finset.sum_pos_iff_of_nonneg (fun v _ => sq_nonneg (x v))).2
    (by simpa only [sq_pos_iff] using hx)

end Spectral
end GraphLib
