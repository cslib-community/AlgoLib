/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Library.Insertion
import AlgoLib.Experimental.RAM.Authoring.Methods

/-!
# Sorting: specification → method → obligations → theorem

This is the canonical sorting program. Read `SortedPermutation` and `Claim`
first, then `insertionSort` for the input/output declaration and executable DSL.
The only algorithm proof is `loopProof`: insertion preserves the sorted suffix
and the multiset, while the potential pays for each scan. `verification` connects
that proof to the generated method VCs. `main` is the resulting RAM theorem.

`insertNext` is a certified array-library procedure, like a separately proved
INSERT operation in a textbook. Its implementation is backend code; this file
uses only its list effect and work contract. Processing is from right to left.
-/
namespace AlgoLib.Experimental.RAM.Programs.Sorting
open Authoring Authoring.Insertion

/-- Sortedness alone is insufficient: preserve duplicates and all input values. -/
def SortedPermutation (xs ys : List Nat) : Prop :=
  ys.Pairwise (· ≤ ·) ∧ ys.Perm xs

/-- The target statement, independent of how the algorithm will be proved.
The constant term covers empty-input initialization; the growth is quadratic. -/
def Claim (sort : List Nat → Result (List Nat)) : Prop :=
  ∀ xs, SortedPermutation xs (sort xs).value ∧
    (sort xs).steps ≤ 50 * xs.length ^ 2 + 100 * xs.length + 55

/-- The displayed body is the body compiled and executed. Input preparation
creates todo = reverse xs and sorted = []; the output is the final array. -/
def insertionSort : Method Insertion.interface :=
  ram_method (xs : List Nat) returns (ys : List Nat)
    using Insertion.interface;
    requires True;
    ensures SortedPermutation xs ys;
    credits (xs.length * (xs.length + 2) + 1);
    time (50 * xs.length ^ 2 + 100 * xs.length + 55);
  do {
    while (more) {
      call insertNext;
    }
  }

/-- A name for the declared body, useful when stating its loop contract. -/
def program : Program model := insertionSort.body

/-- The unprocessed values plus the sorted values permute the original input. -/
def invariant (input : List Nat) (s : State) : Prop :=
  s.sorted.Pairwise (· ≤ ·) ∧ (s.todo ++ s.sorted).Perm input

/-- Each remaining insertion can inspect at most the whole input, plus guards. -/
def potential (s : State) : Nat := s.todo.length * (s.todo.length + s.sorted.length + 2)

theorem loopProof (input : List Nat) : LoopProof more (.action insertNext)
    (invariant input) potential
    (fun s => s.todo = [] ∧ s.sorted.Pairwise (· ≤ ·) ∧ s.sorted.Perm input) where
  preservation := by
    intro s hs running
    cases ht : s.todo with
    | nil => simp [ht] at running
    | cons x xs =>
      have permutation := (List.perm_orderedInsert (· ≤ ·) x s.sorted).append_left xs
      have move : (xs ++ x :: s.sorted).Perm ((x :: xs) ++ s.sorted) := by
        exact List.perm_middle
      have sorted := hs.1.orderedInsert x s.sorted
      paper_steps []
      simp only [effect, ht, invariant, potential, List.length_cons, List.orderedInsert_length]
      refine ⟨by simp, by paper_credits, ⟨sorted, permutation.trans (move.trans (ht ▸ hs.2))⟩, ?_⟩
      paper_credits
  payment := by
    intro s _ running
    cases ht : s.todo with
    | nil => simp [ht] at running
    | cons x xs => simp only [potential, ht, List.length_cons]; paper_credits
  exit := by
    intro s hs stopped
    have empty : s.todo = [] := by simpa using stopped
    exact ⟨empty, by simpa [invariant, empty] using hs⟩

theorem correct (input : List Nat) : Correct program (invariant input)
    (fun _ s => s.todo = [] ∧ s.sorted.Pairwise (· ≤ ·) ∧ s.sorted.Perm input)
    (fun s => potential s + 1) :=
  (loopProof input).correct

/-- The prepared input has an empty sorted suffix and contains the input multiset. -/
private theorem initially (xs : List Nat) : invariant xs (initial xs) := by
  simp [invariant, initial, List.reverse_perm]

/-- Generated method obligations. Every goal here concerns lists or arithmetic.
The adapter's logical observation is used only to name the returned array. -/
theorem verification : insertionSort.VCs := by
  method_vc [insertionSort]
  intro xs _
  constructor
  · apply (correct xs).output_vc
    · exact initially xs
    · simp only [method_simps, potential, initial, List.length_reverse, List.length_nil,
        Nat.add_zero, Nat.le_refl]
    · intro t ht out view
      have eq : out = t.sorted := by
        simpa only [method_simps, ht.1, List.reverse_nil, List.nil_append] using view
      rw [eq]
      exact ht.2
  · method_time

/-- Packaging a checked method invokes the shared verified execution stack. -/
def certified : VerifiedMethod Insertion.interface := ⟨insertionSort, verification⟩

/-- Ordinary input, explicit output, actual RAM steps, and no fuel. -/
def run (xs : List Nat) : Result (List Nat) := certified.run xs (by trivial)

/-- Main theorem: the displayed method sorts every input within a quadratic bound. -/
theorem main : Claim run := fun xs => certified.correct xs (by trivial)

/-- Convenient functional projection of the main theorem. -/
theorem run_correct (xs : List Nat) :
    (run xs).value.Pairwise (· ≤ ·) ∧ (run xs).value.Perm xs := (main xs).1

/-- Exact advertised upper bound, including the empty-input constant. -/
theorem time_bound (xs : List Nat) :
    (run xs).steps ≤ 50 * xs.length ^ 2 + 100 * xs.length + 55 := (main xs).2

/-- For nonempty inputs the same algorithm takes at most 205 n² RAM steps. -/
theorem quadratic (xs : List Nat) (nonempty : xs ≠ []) :
    (run xs).steps ≤ 205 * xs.length ^ 2 := by
  have h := time_bound xs
  have : 0 < xs.length := List.length_pos_iff.mpr nonempty
  nlinarith [Nat.mul_self_le_mul_self this]

/-- An existence statement with a certified procedure witness, not an arbitrary
host-language function with an attached cost number. -/
theorem exists_quadratic_sort : ∃ p : VerifiedMethod Insertion.interface,
    p.method.requires = (fun _ => True) ∧
    ∀ xs (h : p.method.requires xs),
      SortedPermutation xs (p.run xs h).value ∧
      (xs ≠ [] → (p.run xs h).steps ≤ 205 * xs.length ^ 2) := by
  refine ⟨certified, rfl, ?_⟩
  intro xs h
  exact ⟨run_correct xs, quadratic xs⟩

end AlgoLib.Experimental.RAM.Programs.Sorting
