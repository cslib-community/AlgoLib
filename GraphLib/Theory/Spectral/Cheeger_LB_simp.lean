import GraphLib.Theory.Spectral.Expansion

open Finset Cuts
namespace GraphLib
variable {α : Type*} [DecidableEq α]

@[grind] noncomputable def nG (G : SimpleGraph α) [Finite G.vertexSet] : ℝ := (#G.vertexFinset : ℝ)

@[grind] noncomputable def xS (G : SimpleGraph α) [Finite G.vertexSet] (S : Finset α) : α → ℝ :=
  let n : ℝ := nG G; let s : ℝ := #S; fun v => if v ∈ S then (n - s) else -s

lemma xS_orth (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (S : Finset α)
  (hS_nonempty : S.Nonempty) (hS_subset : S ⊆ G.vertexFinset)
  (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    ∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * (xS G S) v = 0 := by
  let n : ℝ := nG G; let s : ℝ := #S; let x : α → ℝ := xS G S
  have h_sum_zero : ∑ v ∈ G.vertexFinset, x v = 0 := by
    simp only [x]; let Sc := G.vertexFinset \ S
    have h_union : G.vertexFinset = S ∪ Sc := by grind
    have h1 : ∑ v ∈ S, x v = s * (n - s) := by
      unfold x xS; rw [Finset.sum_congr rfl (fun v hv => if_pos hv), Finset.sum_const]; grind
    have h2 : ∑ v ∈ Sc, x v = (n - s) * (-s) := by
      have h_sum : #G.vertexFinset = #S + #Sc := by grind
      have h_sum_R : (↑(nG G) : ℝ) = ↑(#S) + ↑(#Sc) := by unfold nG; norm_cast
      have h_card_Sc : ↑(#Sc) = n - s := by grind
      unfold x xS; rw [Finset.sum_congr rfl (fun v hv => if_neg (Finset.mem_sdiff.1 hv).2)]
      rw [Finset.sum_const]; grind
    rw [h_union, Finset.sum_union (Finset.disjoint_sdiff)]; grind
  rw [← mul_zero (d : ℝ), ← h_sum_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro v hv; simp [h_reg v hv]; grind

lemma lambda_le_rq (G : SimpleGraph α) [Finite G.vertexSet] (S : Finset α)
  (hS_nonempty : S.Nonempty) (hS_size : 2 * #S ≤ #G.vertexFinset) (hS_subset : S ⊆ G.vertexFinset)
  (h_orth : ∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * (xS G S) v = 0) :
    lambda2 G ≤ G.rayleighQuotient (xS G S) := by
  let n : ℝ := nG G; let s : ℝ := #S; let x : α → ℝ := xS G S
  unfold lambda2; apply csInf_le
  · use 0; intro r hr; rcases hr with ⟨w, _, rfl⟩
    exact rayleighQuotient_nonneg (G := G) w
  · have h_size_real : 2 * s ≤ n := by unfold n s nG; norm_cast
    have h_s_pos : 0 < s := by unfold s; norm_cast; grind
    have h_x_ne_zero : ∃ v ∈ G.vertexFinset, x v ≠ 0 := by grind
    refine ⟨x, ?_, rfl⟩; exact ⟨h_orth, h_x_ne_zero⟩

@[grind] noncomputable def edge_cut (G : SimpleGraph α) [Finite G.vertexSet] (S : Finset α) :
  Finset (Sym2 α) := G.edgeFinset.filter (
    fun e => ∃ u ∈ G.vertexFinset, u ∈ e ∧ u ∈ S ∧ ∃ v ∈ G.vertexFinset, v ∈ e ∧ v ∉ S
  )

@[grind] noncomputable def edge_diff_sq (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
  Sym2 α → ℝ := Sym2.lift ⟨fun u v => (x u - x v)^2, by intro u v; dsimp; ring⟩

lemma numerator_eq (G : SimpleGraph α) [Finite G.vertexSet] (S : Finset α)
  (hS_nonempty : S.Nonempty) :
    let n : ℝ := nG G; let x : α → ℝ := xS G S; let dS := edge_cut G S
    let edge_diff := edge_diff_sq G x
    ∑ e ∈ G.edgeFinset, edge_diff e = n^2 * ↑(#dS) := by
  intro n x dS edge_diff
  -- 1) dS is a subset of G.edgeFinset.
  have h_sub : dS ⊆ G.edgeFinset := by grind
  -- 2) Edges outside dS contribute 0, hence the full sum equals the dS-sum.
  have h_sum_is_dS : ∑ e ∈ G.edgeFinset, edge_diff e = ∑ e ∈ dS, edge_diff e := by
    rw [Finset.sum_subset h_sub]; intro e he_G he_ndS; by_contra h_nz
    have h_cross : ∃ u ∈ e, u ∈ S ∧ ∃ v ∈ e, v ∉ S := by
      obtain ⟨u, v⟩ := e; unfold edge_diff edge_diff_sq x at h_nz;
      simp only [Sym2.lift_mk, xS] at h_nz; split_ifs at h_nz with huS hvS <;> grind
    have he_in_dS : e ∈ dS := by
      unfold dS edge_cut; simp only [Finset.mem_filter]; use he_G
      rcases h_cross with ⟨u, hu_e, hu_S, v, hv_e, hv_nS⟩
      use u, G.mem_vertexFinset.mpr (G.incidence (G.mem_edgeFinset.mp he_G) hu_e), hu_e, hu_S
      use v, G.mem_vertexFinset.mpr (G.incidence (G.mem_edgeFinset.mp he_G) hv_e), hv_e, hv_nS
    exact he_ndS he_in_dS
  -- 3) Every edge in dS contributes exactly n^2.
  have h_const : ∀ e ∈ dS, edge_diff e = n^2 := by
    intro e he; simp only [dS, edge_cut, Finset.mem_filter] at he
    rcases he with ⟨he_G, u, hu_V, hu_e, hu_S, v, hv_V, hv_e, hv_nS⟩
    obtain ⟨u', v'⟩ := e; unfold edge_diff edge_diff_sq x; simp only [Sym2.lift_mk]; grind
  rw [h_sum_is_dS, Finset.sum_congr rfl h_const]; simp only [sum_const, nsmul_eq_mul]; grind

lemma denominator_eq (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (S : Finset α)
  (hS_size : 2 * #S ≤ #G.vertexFinset) (hS_subset : S ⊆ G.vertexFinset) :
    let n : ℝ := nG G; let s : ℝ := #S; let x : α → ℝ := xS G S
    (d : ℝ) * ∑ v ∈ G.vertexFinset, (x v)^2 = (d : ℝ) * n * s * (n - s) := by
  intro n s x
  have h_sum_S : ∑ v ∈ S, (x v)^2 = s * (n - s)^2 := by
    unfold x; rw [Finset.sum_congr rfl (fun v hv => by unfold xS; rw [if_pos hv])]
    rw [Finset.sum_const]; grind
  have h_sum_Sc : ∑ v ∈ G.vertexFinset \ S, (x v)^2 = (n - s) * s^2 := by
    unfold x; rw [Finset.sum_congr rfl (fun v hv => by
      have h_not_in_S : v ∉ S := (Finset.mem_sdiff.1 hv).2; unfold xS nG
      rw [if_neg h_not_in_S]), Finset.sum_const, Finset.card_sdiff]
    simp only [even_two, Even.neg_pow, nsmul_eq_mul]
    rw [Finset.inter_comm, Finset.inter_eq_right.mpr hS_subset, Nat.cast_sub]; repeat grind
  rw [← Finset.sum_sdiff hS_subset, h_sum_S, h_sum_Sc]; ring

lemma rq_le_two_phi (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (S : Finset α)
  (hS_nonempty : S.Nonempty) (hS_size : 2 * #S ≤ #G.vertexFinset) (hS_subset : S ⊆ G.vertexFinset)
  (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hd : d > 0) :
    G.rayleighQuotient (xS G S) ≤ 2 * edgeExpansion G d S := by
  -- We follow the lecture derivation in three layers:
  -- (1) exact numerator formula,
  -- (2) exact denominator formula,
  -- (3) scalar comparison n/(n-s) ≤ 2.
  let n : ℝ := nG G; let s : ℝ := #S; let x : α → ℝ := xS G S
  unfold SimpleGraph.rayleighQuotient edgeExpansion
  let dS := edge_cut G S; let edge_diff := edge_diff_sq G x
  -- Layer 1: numerator = n^2 * |dS|.
  have h_num_total := numerator_eq G S hS_nonempty
  -- Layer 2a: pull out regular degree in denominator.
  have h_den_match : ∑ v ∈ G.vertexFinset, ↑(G.degree v) * x v ^ 2 = ↑d * ∑ v ∈ G.vertexFinset,
      x v ^ 2 := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; grind
  -- Layer 2b: evaluate ∑ x(v)^2 explicitly.
  have h_denom := denominator_eq G d S hS_size hS_subset
  -- Convert |Cut G S| into |dS|.
  have h_cut_val : ↑(#(Cut G S)) = ↑(#dS) := by
    congr; ext e; constructor <;>
    · intro he; simp only [Cut, dS, Finset.mem_filter] at he ⊢; grind
  -- Rewrite Rayleigh quotient using the two formulas above.
  unfold edge_diff edge_diff_sq at h_num_total
  rw [h_num_total, h_den_match, h_denom, h_cut_val]
  -- Prepare non-vanishing side conditions for `field_simp`.
  unfold n at *
  have h_s_ne_zero : (↑(#S) : ℝ) ≠ 0 := by exact ne_of_gt (by exact_mod_cast (by grind))
  have h_d_ne_zero : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have h_size_real : (2 : ℝ) * ↑(#S) ≤ ↑(#G.vertexFinset) := by exact_mod_cast hS_size
  have h_ns_ne_zero : (↑(#G.vertexFinset) : ℝ) - ↑(#S) ≠ 0 := by grind
  -- Layer 3: pure scalar inequality after cancellation.
  field_simp [h_s_ne_zero, h_d_ne_zero, h_ns_ne_zero]
  -- Equivalent to n ≤ 2*(n-s), i.e. 2s ≤ n.
  have h_ratio_le_two : (↑(#G.vertexFinset) : ℝ) / ((↑(#G.vertexFinset) : ℝ) - ↑(#S)) ≤ 2 := by
    rw [div_le_iff₀ (by grind)]; grind
  have hmul :
      ((↑(#G.vertexFinset) : ℝ) / ((↑(#G.vertexFinset) : ℝ) - ↑(#S))) * ↑(#dS) ≤ 2 * ↑(#dS) :=
    mul_le_mul_of_nonneg_right h_ratio_le_two (by positivity)
  convert hmul using 1 <;> ring_nf; grind

/-- The "Easy Direction" of Cheeger's Inequality: For a d-regular graph, λ₂ / 2 ≤ ϕ(G). -/
theorem cheeger_easy_direction (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (S : Finset α)
  (hS_nonempty : S.Nonempty) (hS_size : 2 * #S ≤ #G.vertexFinset) (hS_subset : S ⊆ G.vertexFinset)
  (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hd : d > 0) :
    (lambda2 G) / 2 ≤ edgeExpansion G d S := by
  /-
    Proof Sketch from Lecture:
    1. Define a specific test vector x based on S.
    2. To satisfy x ⊥ D1, let:
         x_v = |V \ S| if v ∈ S
         x_v = -|S|     if v ∉ S
    3. Compute R_L(x).
    4. Show R_L(x) = |E(S, V \ S)| * |V| / (d * |S| * |V \ S|).
    5. Show this is ≤ 2 * ϕ(S) from |S| ≤ |V| / 2.
  -/
  let n : ℝ := nG G; let s : ℝ := #S; let x : α → ℝ := xS G S
  have h_orth := xS_orth G d S hS_nonempty hS_subset h_reg
  have h_lambda_le_rq := lambda_le_rq G S hS_nonempty hS_size hS_subset h_orth
  have h_rq_le_two_phi := rq_le_two_phi G d S hS_nonempty hS_size hS_subset h_reg hd
  grind

end GraphLib
