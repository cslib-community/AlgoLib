/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.SortingAlgorithm
import AlgoLib.Experimental.RAM.Prototype.Frontend

/-!
# Default execution adapter for the pure insertion-sort algorithm

The complete program, annotations, and logical proof live in SortingAlgorithm.lean,
which imports no RAM code. This file selects the contiguous-array backend and
exports the familiar list runner and RAM corollaries. ArraySubstitution.lean reuses
the exact same specification and proof with pointer-indirected array storage.
-/
namespace AlgoLib.Experimental.RAM.Prototype.InsertionSort
open Authoring Frontend SortingFacts

/-- The default backend realizes the already verified logical specification. -/
def insertionSortVerified := Mutable.interface.realize insertionSort insertionSortCorrect

/-- The generated certificate packages the very body displayed above. -/
def certified : VerifiedMethod Mutable.interface := insertionSortVerified

/-- Execute compiled RAM, accepting an ordinary list and requiring no fuel. -/
def run (xs : List Nat) : Result (List Nat) :=
  let result := certified.run xs.toArray (by trivial)
  ⟨result.value.toList, result.steps⟩

/-- Correctness and quadratic RAM time for this same executable, including empty inputs. -/
theorem main (xs : List Nat) : SortedPermutation xs (run xs).value ∧
    (run xs).steps ≤ 300 * xs.length ^ 2 + 300 * xs.length + 360 := by
  have h := certified.correct xs.toArray (by trivial)
  change (SortedPermutation xs _ ∧ True) ∧ _ at h
  refine ⟨h.1.1, ?_⟩
  have bound := h.2
  have time_eq : certified.method.time xs.toArray =
      3 * (potential xs.toArray.size 0 + 20) := by
    simp only [certified, insertionSortVerified, Interface.realize, Method.time, insertionSort,
      Mutable.interface, Mutable.model,
      Nat.zero_add]
  rw [time_eq] at bound
  calc
    _ ≤ 3 * (potential xs.toArray.size 0 + 20) := bound
    _ = 300 * xs.length ^ 2 + 300 * xs.length + 360 := by
      simp [potential]
      ring

/-- A conventional big-O witness for nonempty inputs. -/
theorem quadratic (xs : List Nat) (nonempty : xs ≠ []) :
    (run xs).steps ≤ 960 * xs.length ^ 2 := by
  have h := (main xs).2
  have hn : 0 < xs.length := List.length_pos_iff.mpr nonempty
  nlinarith [Nat.mul_self_le_mul_self hn]

/-- An explicit certified program witnesses the sorting and time claim. -/
theorem exists_sort : ∃ p : VerifiedMethod Mutable.interface,
    p.method.body = insertionSort.body ∧ (∀ input, p.method.requires input) ∧
    ∀ xs (h : p.method.requires xs.toArray),
      SortedPermutation xs (p.run xs.toArray h).value.toList ∧
      (xs ≠ [] → (p.run xs.toArray h).steps ≤ 960 * xs.length ^ 2) := by
  exact ⟨certified, rfl, fun _ => by trivial, fun xs _ => ⟨(main xs).1, quadratic xs⟩⟩

/-- The generated conditions establish the actual upstream Loom WP. -/
theorem loom_correct (xs : Array Nat) :
    _root_.wp (denote insertionSort.body)
      (fun _ t _ => SortedPermutation xs.toList t.array.toList)
      (Mutable.initial xs) (insertionSort.credits xs) := by
  have h := (insertionSortVerification xs (by trivial))
  have observed := (insertionSortAnnotations xs).loom_sound _ _ _ h
  rw [loom_wp_eq] at observed ⊢
  exact Computation.wp_mono (fun _ t _ ht => (ht t.array rfl).1) observed

set_option linter.hashCommand false in
#eval (run [5, 2, 4, 1, 6]).value

end AlgoLib.Experimental.RAM.Prototype.InsertionSort
