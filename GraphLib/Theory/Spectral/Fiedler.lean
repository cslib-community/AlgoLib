import GraphLib.Theory.Spectral.Expansion

-- Cheeger upper bound, Fiedler's Algorithm (Sweep Cut)
-- Authors: Weixuan Yuan, Yuchen Zhong
-- LLM: Gemini, GPT-5.6, 6.1 Sol on codex

/-!
References are to Luca Trevisan, Lecture 2, §2 (Fiedler's algorithm) and §4 (Lemma 3):
https://lucatrevisan.github.io/41000-22/lecture02.pdf
-/

namespace GraphLib
namespace Spectral

open Finset Cuts

variable {α : Type*} (G : SimpleGraph α)
  [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]

-- Lecture 2, §2, pp. 3–4: sort x and consider the cuts along its vertex ordering.
@[grind] noncomputable def sweepCuts (x : α → ℝ) : Finset (Finset α) := by
  classical
  let sortedV := (G.vertexFinset.toList).mergeSort (fun u v => x u ≤ x v)
  let n := (G.vertexFinset).card
  let indices := List.range (n / 2)
  let prefixes := indices.map (fun k => (sortedV.take (k + 1)).toFinset)
  let suffixes := indices.map (fun k => (sortedV.reverse.take (k + 1)).toFinset)
  -- Formal support for Lemma 5's threshold cuts, including repeated coordinate values.
  let lowerLevels :=
    (G.vertexFinset.powerset).filter
      (fun S => S.Nonempty ∧ 2 * S.card ≤ n ∧ ∃ t : ℝ, S = G.vertexFinset.filter (fun v => x v ≤ t))
  let upperLevels :=
    (G.vertexFinset.powerset).filter
      (fun S => S.Nonempty ∧ 2 * S.card ≤ n ∧ ∃ t : ℝ, S = G.vertexFinset.filter (fun v => x v ≥ t))
  exact (prefixes ++ suffixes).toFinset ∪ (lowerLevels ∪ upperLevels)

/-- Formal support for Lecture 2, §2: Fiedler's minimum has a candidate when |V| ≥ 2. -/
lemma sweepCuts_expansion_nonempty (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (G.vertexFinset).card) :
    ((sweepCuts G x).image (fun S => edgeExpansion G d S)).Nonempty := by
  rw [Finset.image_nonempty]
  refine ⟨(List.take (0 + 1) ((G.vertexFinset).toList.mergeSort
    (fun u v => x u ≤ x v))).toFinset, ?_⟩
  unfold sweepCuts; simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map]
  grind

/-- Lecture 2, §2, pp. 3–4: minimize expansion over the cuts in the sorted order. -/
@[grind] noncomputable def fiedlerExpansion (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (G.vertexFinset).card) : ℝ :=
  let cuts := sweepCuts G x
  (cuts.image (fun S => edgeExpansion G d S)).min' (sweepCuts_expansion_nonempty G d x hV)

/-- Lecture 2, §2: the cut returned by Fiedler's expansion minimization. -/
@[grind] noncomputable def fiedlerCut (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (G.vertexFinset).card) : Finset α :=
  -- Formal support: choose a sweep cut attaining the finite minimum.
  Classical.choose (Finset.mem_image.mp (Finset.min'_mem _ (sweepCuts_expansion_nonempty G d x hV)))

/-- Lecture 2, proof of Lemma 3, p. 6: the returned cut is valid and beats any sweep cut. -/
lemma fiedlerCut_spec (d : ℕ) (x : α → ℝ) (hV : 2 ≤ G.vertexFinset.card) :
    let S := fiedlerCut G d x hV
    S.Nonempty ∧ S ⊆ G.vertexFinset ∧ 2 * S.card ≤ G.vertexFinset.card ∧
      ∀ T ∈ sweepCuts G x, edgeExpansion G d S ≤ edgeExpansion G d T := by
  -- Lecture 2, §2: represent each cut by its nonempty side of size at most |V|/2.
  have hvalid : ∀ T ∈ sweepCuts G x,
      T.Nonempty ∧ T ⊆ G.vertexFinset ∧ 2 * T.card ≤ G.vertexFinset.card := by
    intro T hT
    unfold sweepCuts at hT
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map,
      List.mem_range, Finset.mem_filter, Finset.mem_powerset] at hT
    rcases hT with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hLevels
    rotate_left 2
    · grind
    all_goals
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty, ne_eq, List.toFinset_eq_empty_iff]
        intro h_empty
        have h_len := congrArg List.length h_empty
        simp only [List.length_take, List.length_reverse, List.length_mergeSort,
          Finset.length_toList, List.length_nil] at h_len
        omega
      · intro v hv
        rw [List.mem_toFinset] at hv
        have h_mem : v ∈ G.vertexFinset.toList.mergeSort (fun u v => x u ≤ x v) := by grind
        simpa using h_mem
      · refine (Nat.mul_le_mul_left 2 (List.toFinset_card_le _)).trans ?_
        simp only [List.length_take]
        omega
  -- Lecture 2, proof of Lemma 3, p. 6: φ(S_F) ≤ φ(S_t) by the algorithm's minimum.
  have hspec := Classical.choose_spec (Finset.mem_image.mp
    (Finset.min'_mem _ (sweepCuts_expansion_nonempty G d x hV)))
  obtain ⟨h_ne, h_sub, h_card⟩ := hvalid _ hspec.1
  refine ⟨h_ne, h_sub, h_card, ?_⟩
  intro T hT
  rw [show edgeExpansion G d (fiedlerCut G d x hV) = _ from hspec.2]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hT)

end Spectral
end GraphLib
