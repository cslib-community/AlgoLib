/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Paper.InsertionSort
import AlgoLib.Experimental.RAM.Internal.InsertionInput

namespace AlgoLib.Experimental.RAM.Paper.Insertion

private theorem initially (xs : List Nat) : invariant xs (initial xs) := by
  simp [invariant, initial, List.reverse_perm]

/-- Takes an ordinary list; returns sorted values and actual RAM steps, without fuel. -/
def run (xs : List Nat) : Result (List Nat) := interface.run (correct xs) xs (initially xs)

theorem run_correct (xs : List Nat) : (run xs).value.Pairwise (· ≤ ·) ∧ (run xs).value.Perm xs := by
  obtain ⟨⟨g, ⟨empty, sorted, perm⟩, out⟩, _⟩ := interface.correct (correct xs) xs (initially xs)
  have he : (run xs).value = g.sorted := by simpa [interface, empty] using out
  rw [he]
  exact ⟨sorted, perm⟩

theorem time_bound (xs : List Nat) :
    (run xs).steps ≤ 50 * xs.length ^ 2 + 100 * xs.length + 55 := by
  have h := (interface.correct (correct xs) xs (initially xs)).2
  change (run xs).steps ≤ 5 + 50 * (potential (initial xs) + 1) at h
  simp only [potential, initial, List.length_reverse, List.length_nil, Nat.add_zero] at h
  nlinarith

theorem quadratic (xs : List Nat) (nonempty : xs ≠ []) : (run xs).steps ≤ 205 * xs.length ^ 2 := by
  have h := time_bound xs
  have : 0 < xs.length := List.length_pos_iff.mpr nonempty
  nlinarith [Nat.mul_self_le_mul_self this]

end AlgoLib.Experimental.RAM.Paper.Insertion
