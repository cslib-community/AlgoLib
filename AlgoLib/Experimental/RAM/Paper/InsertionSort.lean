/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Paper.Array

/-! Insertion sort's paper proof: a sorted suffix and preservation of the
multiset of values. Insertion is a reusable, linear-time array procedure. -/
namespace AlgoLib.Experimental.RAM.Paper.Insertion


def program : Program model := paper {
  while (more) { call insertNext; }
}

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

end AlgoLib.Experimental.RAM.Paper.Insertion
