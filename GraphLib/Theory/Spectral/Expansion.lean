import Mathlib.Tactic

import GraphLib.Graph.Basic
import GraphLib.Graph.Finite
import GraphLib.Graph.Degree
import GraphLib.Theory.Spectral.Cuts
import GraphLib.Theory.Spectral.Helper

-- Cuts and contractions (undirected simple)
-- Authors: Yuchen Zhong, Weixuan Yuan
-- LLM: Gemini, GPT-5.5 on codex

open Finset
namespace GraphLib
namespace Spectral

open Cuts

variable {α : Type*} (G : SimpleGraph α)
  [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]

@[grind] lemma ne_of_mem_edgeSet (u v : α) (h : s(u, v) ∈ G.edgeFinset) : u ≠ v := by
  by_contra! huv; subst v
  apply G.loopless' s(u, u) (G.mem_edgeFinset.mp h); simp

@[grind] noncomputable def edgeExpansion (d : ℕ) (S : Finset α) : ℝ :=
    ( (Cut G S).card : ℝ ) / ( (d * S.card) : ℝ )

@[grind] noncomputable def graphExpansion (d : ℕ) : ℝ :=
  let validSubsets := (G.vertexFinset.powerset).filter (
      fun S => S.Nonempty ∧ 2 * S.card ≤ (G.vertexFinset).card
    )
  if h : validSubsets.Nonempty then
    (validSubsets.image (fun S => edgeExpansion G d S)).min' (by
      exact Finset.Nonempty.image h (fun S => edgeExpansion G d S)
    )
  else 0

@[grind] noncomputable def _root_.GraphLib.SimpleGraph.rayleighQuotient (x : α → ℝ) : ℝ :=
  let numerator := G.edgeFinset.sum (fun e => e.lift ⟨fun u v => (x u - x v) ^ 2, by grind⟩)
  let denominator := G.vertexFinset.sum (fun v => (G.degree v : ℝ) * (x v) ^ 2)
  numerator / denominator

lemma rayleighQuotient_nonneg (x : α → ℝ) :
    0 ≤ G.rayleighQuotient x := by
  unfold SimpleGraph.rayleighQuotient; apply div_nonneg
  · apply sum_nonneg; intro e _
    induction e using Sym2.inductionOn with
    | hf u v => dsimp; exact sq_nonneg (x u - x v)
  · apply sum_nonneg; intro v _; apply mul_nonneg
    · norm_cast; exact Nat.zero_le _
    · exact sq_nonneg (x v)

@[grind] def orthogonalVectors : Set (α → ℝ) :=
    { x | (G.vertexFinset.sum (
      fun v => (G.degree v ) * x v) = 0) ∧ (∃ v ∈ G.vertexFinset, x v ≠ 0) }

@[grind] def R_values : Set ℝ :=
  { r | ∃ x ∈ orthogonalVectors G, r = G.rayleighQuotient x }

@[grind] noncomputable def lambda2 : ℝ :=
    sInf (R_values G)

lemma lambda2_bounded_below :
  BddBelow { r : ℝ | ∃ x : α → ℝ, (G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0) ∧
    (∃ v ∈ G.vertexFinset, x v ≠ 0) ∧ r = G.rayleighQuotient x } := by
  use 0; intro r hr; simp only [Set.mem_setOf_eq] at hr
  rcases hr with ⟨x, _, _, rfl⟩; apply rayleighQuotient_nonneg

@[grind] noncomputable def _root_.GraphLib.SimpleGraph.energy (x : α → ℝ) : ℝ :=
    ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v ↦ (x u - x v) ^ 2, by grind⟩ e

lemma energy_nonneg (x : α → ℝ) :
    0 ≤ G.energy x := by
  unfold SimpleGraph.energy; apply Finset.sum_nonneg; intro e he
  induction e using Sym2.ind; case h => dsimp; apply sq_nonneg

lemma energy_mul (x : α → ℝ) (c : ℝ) :
    G.energy (fun v => c * x v) = c ^ 2 * G.energy x := by
  unfold SimpleGraph.energy; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
  intro e he; induction e using Sym2.ind; case h u => simp; ring_nf

@[grind] noncomputable def _root_.GraphLib.SimpleGraph.deg_norm (x : α → ℝ) : ℝ :=
    ∑ v ∈ G.vertexFinset, ↑(G.degree v) * x v ^ 2

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
lemma deg_norm_nonneg (x : α → ℝ) :
    0 ≤ G.deg_norm x := by
  unfold SimpleGraph.deg_norm; apply Finset.sum_nonneg
  intro v hv; apply mul_nonneg
  · norm_cast; exact Nat.zero_le _
  · exact sq_nonneg (x v)

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
lemma deg_norm_eq_sum_reg (x : α → ℝ) (d : ℕ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    G.deg_norm x = ∑ v ∈ G.vertexFinset, (d : ℝ) * x v ^ 2 := by
  unfold SimpleGraph.deg_norm; apply Finset.sum_congr rfl
  intro v hv; rw [h_reg v hv]

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
lemma deg_norm_mul (x : α → ℝ) (c : ℝ) :
    G.deg_norm (fun v => c * x v) = c ^ 2 * G.deg_norm x := by
  unfold SimpleGraph.deg_norm; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; grind

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
lemma deg_norm_shifted_parts_add (z : α → ℝ) :
    G.deg_norm (fun v => max (z v) 0) + G.deg_norm (fun v => max (-(z v)) 0) = G.deg_norm z := by
  unfold SimpleGraph.deg_norm; rw [← Finset.sum_add_distrib]; grind

lemma energy_shifted_parts_add_le (z : α → ℝ) :
    G.energy (fun v => max (z v) 0) + G.energy (fun v => max (-(z v)) 0) ≤ G.energy z := by
  unfold SimpleGraph.energy; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum
  intro e he; induction e using Sym2.ind
  case h => expose_names; dsimp; exact pos_neg_sub_sq_add_le (z x) (z y)

lemma rQ_eq_energy_div_norm (x : α → ℝ) :
    G.rayleighQuotient x = G.energy x / G.deg_norm x := by grind

lemma rayleighQuotient_mul (x : α → ℝ) {c : ℝ}
    (hc : c ≠ 0) : G.rayleighQuotient (fun v => c * x v) = G.rayleighQuotient x := by
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]; rw [energy_mul, deg_norm_mul]; grind

@[grind] noncomputable def restrictToVertexSet (x : α → ℝ) : α → ℝ :=
    fun v => if v ∈ G.vertexFinset then x v else 0

lemma energy_restrictToVertexSet (x : α → ℝ) : G.energy (restrictToVertexSet G x) = G.energy x := by
  unfold SimpleGraph.energy restrictToVertexSet; apply Finset.sum_congr rfl
  intro e he; induction e using Sym2.ind
  case h =>
    expose_names
    have huV : x_1 ∈ G.vertexFinset := by grind+suggestions
    have hvV : y ∈ G.vertexFinset := by grind+suggestions
    simp_all only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_vertexFinset,
      Sym2.lift_mk, ↓reduceIte]

omit [DecidablePred (· ∈ G.edgeSet)] in
lemma deg_norm_restrictToVertexSet (x : α → ℝ) :
    G.deg_norm (restrictToVertexSet G x) = G.deg_norm x := by
  unfold SimpleGraph.deg_norm restrictToVertexSet; apply Finset.sum_congr rfl; grind

lemma rayleighQuotient_restrictToVertexSet (x : α → ℝ) :
    G.rayleighQuotient (restrictToVertexSet G x) = G.rayleighQuotient x := by
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
  rw [energy_restrictToVertexSet, deg_norm_restrictToVertexSet]

omit [DecidablePred (· ∈ G.edgeSet)] in
lemma orthogonalVectors_restrictToVertexSet (x : α → ℝ) (horth : x ∈ orthogonalVectors G) :
    restrictToVertexSet G x ∈ orthogonalVectors G := by
  rcases horth with ⟨horth, hne⟩; constructor
  · unfold restrictToVertexSet
    rw [show (∑ v ∈ G.vertexFinset, ↑(G.degree v) * (if v ∈ G.vertexFinset then x v else 0)) =
        ∑ v ∈ G.vertexFinset, ↑(G.degree v) * x v by apply Finset.sum_congr rfl; grind]
    exact horth
  · rcases hne with ⟨v, hv, hxv⟩
    exact ⟨v, hv, by simpa [restrictToVertexSet, hv] using hxv⟩

@[grind] def graphExpansionValidSubsets :
    Finset (Finset α) :=
  (G.vertexFinset.powerset).filter (fun S => S.Nonempty ∧ 2 * S.card ≤ (G.vertexFinset).card)

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
lemma mem_graphExpansionValidSubsets_of_valid (S : Finset α) (hS_ne : S.Nonempty)
    (hS_sub : S ⊆ G.vertexFinset) (hS_size : 2 * S.card ≤ (G.vertexFinset).card) :
    S ∈ graphExpansionValidSubsets G := by
  simp [graphExpansionValidSubsets, hS_sub, hS_ne, hS_size]

omit [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] in
lemma graphExpansionValidSubsets_nonempty_of_valid (S : Finset α) (hS_ne : S.Nonempty)
    (hS_sub : S ⊆ G.vertexFinset) (hS_size : 2 * S.card ≤ (G.vertexFinset).card) :
    (graphExpansionValidSubsets G).Nonempty := by
  exact ⟨S, mem_graphExpansionValidSubsets_of_valid G S hS_ne hS_sub hS_size⟩

lemma edgeExpansion_mem_graphExpansion_image_of_valid (d : ℕ) (S : Finset α) (hS_ne : S.Nonempty)
    (hS_sub : S ⊆ G.vertexFinset) (hS_size : 2 * S.card ≤ (G.vertexFinset).card) :
    edgeExpansion G d S ∈ (graphExpansionValidSubsets G).image (fun T => edgeExpansion G d T) := by
  exact Finset.mem_image.mpr
    ⟨S, mem_graphExpansionValidSubsets_of_valid G S hS_ne hS_sub hS_size, rfl⟩

lemma edgeExpansion_zero_degree (S : Finset α) : edgeExpansion G 0 S = 0 := by grind

lemma graphExpansion_zero_degree :
    graphExpansion G 0 = 0 := by
  unfold graphExpansion; dsimp only; split_ifs with h
  · apply le_antisymm
    · obtain ⟨S, hS⟩ := h
      have hm : edgeExpansion G 0 S ∈ (Finset.image (fun S => edgeExpansion G 0 S)
        {S ∈ G.vertexFinset.powerset | S.Nonempty ∧ 2 * #S ≤ #G.vertexFinset}) := by grind
      have hz : edgeExpansion G 0 S = 0 := edgeExpansion_zero_degree G S
      simpa [hz] using Finset.min'_le _ _ hm
    · apply Finset.le_min'; grind
  · rfl

end Spectral
end GraphLib
