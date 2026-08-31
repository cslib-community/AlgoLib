import GraphLib.Theory.Spectral.Expansion

open Finset Cuts

namespace GraphLib

variable {α : Type*}

-- Generates the set of all prefix and suffix cuts (sweep cuts) for a vector x.
noncomputable def sweepCuts (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] (x : α → ℝ) :
    Finset (Finset α) := by
  classical
  let sortedV := (G.vertexFinset.toList).mergeSort (fun u v => x u ≤ x v)
  let n := (G.vertexFinset).card
  let indices := List.range (n / 2)
  let prefixes := indices.map (fun k => (sortedV.take (k + 1)).toFinset)
  let suffixes := indices.map (fun k => (sortedV.reverse.take (k + 1)).toFinset)
  let lowerLevels :=
    (G.vertexFinset.powerset).filter
      (fun S => S.Nonempty ∧ 2 * S.card ≤ n ∧ ∃ t : ℝ, S = G.vertexFinset.filter (fun v => x v ≤ t))
  let upperLevels :=
    (G.vertexFinset.powerset).filter
      (fun S => S.Nonempty ∧ 2 * S.card ≤ n ∧ ∃ t : ℝ, S = G.vertexFinset.filter (fun v => x v ≥ t))
  exact (prefixes ++ suffixes).toFinset ∪ (lowerLevels ∪ upperLevels)

lemma sweepCut_is_subset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, S ⊆ G.vertexFinset := by
  intro S hS; unfold sweepCuts at hS
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    Finset.mem_filter, Finset.mem_powerset] at hS
  intro v hv; rcases hS with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hLevels; any_goals
    rw [List.mem_toFinset] at hv
    have h_mem_sorted : v ∈ (G.vertexFinset.toList).mergeSort (fun u v => x u ≤ x v) := by grind
    rw [List.mem_mergeSort] at h_mem_sorted; rw [← Finset.mem_toList]; grind
  grind

lemma sweepCuts_are_nonempty (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    (hV : 2 ≤ (G.vertexFinset).card) (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, S.Nonempty := by
  intro S hS; unfold sweepCuts at hS
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    Finset.mem_filter, Finset.mem_powerset] at hS
  rcases hS with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hLevels
  · have h_list_len : 1 ≤ ((G.vertexFinset).toList.mergeSort (fun u v => x u ≤ x v)).length := by
      rw [List.length_mergeSort, Finset.length_toList]
      omega
    rw [Finset.nonempty_iff_ne_empty, ne_eq, List.toFinset_eq_empty_iff]; intro h_empty
    simp_all only [List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or,
      List.length_nil, nonpos_iff_eq_zero]
  · have h_list_len :
        1 ≤ (((G.vertexFinset).toList.mergeSort (fun u v => x u ≤ x v)).reverse).length := by
      rw [List.length_reverse, List.length_mergeSort, Finset.length_toList]; omega
    rw [Finset.nonempty_iff_ne_empty, ne_eq, List.toFinset_eq_empty_iff]; intro h_empty
    simp_all only [List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      false_or, List.length_nil, nonpos_iff_eq_zero]
  · grind

lemma sweepCuts_expansion_nonempty (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) :
    ((sweepCuts G x).image (fun S => edgeExpansion G d S)).Nonempty := by
  rw [Finset.image_nonempty]
  refine ⟨(List.take (0 + 1) ((G.vertexFinset).toList.mergeSort
    (fun u v => x u ≤ x v))).toFinset, ?_⟩
  unfold sweepCuts; simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map]
  grind

lemma sweepCut_card_le_half (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, 2 * S.card ≤ (G.vertexFinset).card := by
  intro S hS; unfold sweepCuts at hS
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    Finset.mem_filter, Finset.mem_powerset] at hS
  rcases hS with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hLevels
  · have h_card :
        ((List.take (k + 1) ((G.vertexFinset).toList.mergeSort
          (fun u v => x u ≤ x v))).toFinset).card ≤ k + 1 := by
      calc
        ((List.take (k + 1) ((G.vertexFinset).toList.mergeSort
          (fun u v => x u ≤ x v))).toFinset).card
            ≤ (List.take (k + 1) ((G.vertexFinset).toList.mergeSort
                (fun u v => x u ≤ x v))).length := by
              exact List.toFinset_card_le _
        _ ≤ k + 1 := by simp
    omega
  · have h_card :
        ((List.take (k + 1) ((G.vertexFinset).toList.mergeSort
          (fun u v => x u ≤ x v)).reverse).toFinset).card ≤ k + 1 := by
      calc
        ((List.take (k + 1) ((G.vertexFinset).toList.mergeSort
          (fun u v => x u ≤ x v)).reverse).toFinset).card
            ≤ (List.take (k + 1) ((G.vertexFinset).toList.mergeSort
                (fun u v => x u ≤ x v)).reverse).length := by
              exact List.toFinset_card_le _
        _ ≤ k + 1 := by simp
    omega
  · grind

/-- The expansion of the best cut found by Fiedler's algorithm.
    Requires |V| ≥ 2 to ensure at least one cut exists. -/
noncomputable def fiedlerExpansion (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (G.vertexFinset).card) : ℝ :=
  let cuts := sweepCuts G x
  (cuts.image (fun S => edgeExpansion G d S)).min' (by
    exact sweepCuts_expansion_nonempty G d x hV
  )

/-- The actual set of vertices (cut) that achieves the fiedlerExpansion. -/
noncomputable def fiedlerCut (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) : Finset α :=
  -- Pick a cut that attains the minimum expansion
  Classical.choose (Finset.mem_image.mp (Finset.min'_mem _ (sweepCuts_expansion_nonempty G d x hV)))

lemma fiedlerCut_mem_sweep (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) :
    fiedlerCut G d x hV ∈ sweepCuts G x := by
  unfold fiedlerCut; grind

lemma fiedlerCut_nonempty (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) : (fiedlerCut G d x hV).Nonempty := by
  let S_f := fiedlerCut G d x hV
  have hS_mem : S_f ∈ sweepCuts G x := fiedlerCut_mem_sweep G d x hV
  apply sweepCuts_are_nonempty G hV x; exact hS_mem

lemma fiedlerCut_is_subset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) :
    fiedlerCut G d x hV ⊆ G.vertexFinset := by
  apply sweepCut_is_subset G x; exact fiedlerCut_mem_sweep G d x hV

lemma fiedlerCut_card_le_half (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) :
    2 * (fiedlerCut G d x hV).card ≤ (G.vertexFinset).card := by
  apply sweepCut_card_le_half G x; exact fiedlerCut_mem_sweep G d x hV

end GraphLib
