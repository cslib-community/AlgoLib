/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Verification
import AlgoLib.Experimental.RAM.Library.Insertion

/-!
# Insertion sort through the Loom-style observation and the RAM compiler

Start at `insertionSort`: ordinary list input/output, a fixed program, and its
functional/time specification. `annotations` supplies the paper invariant and
potential. `verification` solves the conditions generated FROM that program.
`run` executes compiled RAM without fuel; `main` proves its result and RAM bound.

The array is viewed as an unprocessed prefix and a sorted suffix. `insertNext`
inserts the rightmost remaining element into the suffix. Its contract states the
list effect and a linear charge; its existing certified RAM body performs the
inner scan. We reuse that LOCAL procedure certificate, not the existing complete
sorting theorem. This prototype demonstrates modular procedure calls, rather than
a new Velvet parser for explicit array assignments and nested inner loops.
-/
namespace AlgoLib.Experimental.RAM.Prototype.InsertionSort
open Authoring Authoring.Insertion

/-- Preserve multiplicities as well as ordering. -/
def SortedPermutation (xs ys : List Nat) : Prop := ys.Pairwise (· ≤ ·) ∧ ys.Perm xs

/-- One input-independent program for BOTH interpretations. -/
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

/-- The sorted suffix is ordered, and no input value has been lost or duplicated. -/
def invariant (xs : List Nat) (s : State) : Prop :=
  s.sorted.Pairwise (· ≤ ·) ∧ (s.todo ++ s.sorted).Perm xs

/-- Charge each remaining insertion enough for a scan and its guard. -/
def potential (s : State) : Nat := s.todo.length * (s.todo.length + s.sorted.length + 2)

/-- Annotations are proof data. Their type fixes the program they describe. -/
def annotations (xs : List Nat) : Plan insertionSort.body :=
  .loop more (fun s c => invariant xs s ∧ potential s + 1 ≤ c) (.action insertNext)

/-- The only algorithmic step: insertion preserves order/permutation and pays for its work. -/
theorem insertion_preserves (xs : List Nat) (s : State) (c : Nat)
    (hs : invariant xs s) (hc : potential s + 1 ≤ c) (running : more.test s = true) :
    (Plan.action insertNext).vc (fun t d => invariant xs t ∧ potential t + 1 ≤ d)
      s (c - 1) := by
  cases ht : s.todo with
  | nil => simp [ht] at running
  | cons x todo =>
    have permutation := (List.perm_orderedInsert (· ≤ ·) x s.sorted).append_left todo
    have move : (todo ++ x :: s.sorted).Perm ((x :: todo) ++ s.sorted) :=
      List.perm_middle
    have sorted := hs.1.orderedInsert x s.sorted
    prototype_steps []
    simp only [effect, ht, invariant, potential, List.orderedInsert_length]
    simp only [potential, ht, List.length_cons] at hc
    refine ⟨by simp, by paper_credits, ⟨sorted, permutation.trans (move.trans (ht ▸ hs.2))⟩,
      ?_⟩
    paper_credits

/-- Generated conditions: initialization, preservation/payment, exit, and total RAM budget. -/
theorem verification : Obligations insertionSort annotations := by
  intro xs _
  constructor
  · change (invariant xs (initial xs) ∧
        potential (initial xs) + 1 ≤ xs.length * (xs.length + 2) + 1) ∧ _
    constructor
    · simp [invariant, initial, potential, List.reverse_perm]
    · intro s c ⟨hs, hc⟩
      refine ⟨by omega, ?_⟩
      cases hq : more.test s with
      | true => simpa only [hq, ↓reduceIte] using insertion_preserves xs s c hs hc hq
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        intro out view
        have empty : s.todo = [] := by simpa using hq
        have result : out = s.sorted := by
          simpa only [method_simps, empty, List.reverse_nil, List.nil_append] using view
        change SortedPermutation xs out
        simpa [SortedPermutation, invariant, empty, result] using hs
  · change Insertion.interface.preparationCost xs +
      model.overhead * (xs.length * (xs.length + 2) + 1) ≤
        50 * xs.length ^ 2 + 100 * xs.length + 55
    method_time

/-- Reconstruction, lowering, and termination proofs are implementation responsibilities. -/
def certified : VerifiedMethod Insertion.interface := certify insertionSort verification

/-- Actual RAM execution; the argument is just the input list. -/
def run (xs : List Nat) : Result (List Nat) := certified.run xs (by trivial)

/-- Sorting correctness and quadratic time for the SAME executable. -/
theorem main (xs : List Nat) : SortedPermutation xs (run xs).value ∧
    (run xs).steps ≤ 50 * xs.length ^ 2 + 100 * xs.length + 55 :=
  certified.correct xs (by trivial)

/-- The familiar O(n²) form for nonempty inputs; `main` also covers the empty input. -/
theorem quadratic (xs : List Nat) (nonempty : xs ≠ []) :
    (run xs).steps ≤ 205 * xs.length ^ 2 := by
  have bound := (main xs).2
  have positive : 0 < xs.length := List.length_pos_iff.mpr nonempty
  nlinarith [Nat.mul_self_le_mul_self positive]

/-- Explicit witness: a certified program exists with both functional and cost guarantees. -/
theorem exists_sort : ∃ p : VerifiedMethod Insertion.interface,
    p.method.body = insertionSort.body ∧ p.method.requires = (fun _ => True) ∧
    ∀ xs (h : p.method.requires xs), SortedPermutation xs (p.run xs h).value ∧
      (xs ≠ [] → (p.run xs h).steps ≤ 205 * xs.length ^ 2) := by
  exact ⟨certified, rfl, rfl, fun xs _ => ⟨(main xs).1, quadratic xs⟩⟩

end AlgoLib.Experimental.RAM.Prototype.InsertionSort
