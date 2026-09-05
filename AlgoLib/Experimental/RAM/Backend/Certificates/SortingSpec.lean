/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

/-!
# Insertion mathematics for certificates

Collects sortedness, permutation, and insertion facts used to certify the machine implementation.

These list facts contain no new public executable. Programs/Sorting contains the canonical theorem
and algorithm-level proof.
-/
namespace AlgoLib.Experimental.RAM
abbrev Memory := Nat → Nat

/-- A mathematical view of a contiguous block, used only in specifications. -/
def contents (m : Memory) (base : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => m base :: contents m (base + 1) n

@[simp] theorem contents_length (m : Memory) (base n : Nat) :
    (contents m base n).length = n := by
  induction n generalizing base <;> simp [contents, *]

/-- Updating an earlier cell leaves a suffix view unchanged. -/
theorem contents_update_before (m : Memory) (base n a x : Nat) (h : a < base) :
    contents (Function.update m a x) base n = contents m base n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [contents, Function.update_of_ne (by omega : base ≠ a)]
    rw [ih (base + 1) (by omega)]

/-- Pure memory specification; no executable cost is asserted here. -/
structure MemoryResult where
  memory : Memory

def insert (base x : Nat) : Nat → Memory → MemoryResult
  | 0, m => ⟨Function.update m base x⟩
  | n + 1, m => if x ≤ m (base + 1) then ⟨Function.update m base x⟩
    else insert (base + 1) x n (Function.update m base (m (base + 1)))

def insertionSort (base : Nat) : Nat → Memory → MemoryResult
  | 0, m => ⟨m⟩
  | n + 1, m => insert base (m base) n (insertionSort (base + 1) n m).memory

@[simp] theorem insert_zero (m : Memory) (base x : Nat) :
    insert base x 0 m = ⟨Function.update m base x⟩ := rfl

theorem insert_succ (m : Memory) (base x n : Nat) :
    insert base x (n + 1) m =
      if x ≤ m (base + 1) then ⟨Function.update m base x⟩
      else insert (base + 1) x n (Function.update m base (m (base + 1))) := rfl

@[simp] theorem insertionSort_zero (m : Memory) (base : Nat) :
    insertionSort base 0 m = ⟨m⟩ := rfl

theorem insertionSort_succ (m : Memory) (base n : Nat) :
    insertionSort base (n + 1) m =
      insert base (m base) n (insertionSort (base + 1) n m).memory := rfl

/-- Insertion modifies only its `n + 1` output cells. -/
theorem insert_frame (m : Memory) (base x n a : Nat)
    (h : a < base ∨ base + n < a) :
    (insert base x n m).memory a = m a := by
  induction n generalizing base m with
  | zero =>
    simp only [insert_zero]
    exact Function.update_of_ne (by omega) ..
  | succ n ih =>
    rw [insert_succ]
    split
    · exact Function.update_of_ne (by omega) ..
    · rw [ih _ _ (by omega)]
      exact Function.update_of_ne (by omega) ..

/-- The key refinement: the imperative insertion has the familiar list meaning.
No sortedness precondition is needed to establish this equation. -/
theorem insert_contents (m : Memory) (base x n : Nat) :
    contents (insert base x n m).memory base (n + 1) =
      List.orderedInsert (· ≤ ·) x (contents m (base + 1) n) := by
  induction n generalizing base m with
  | zero => simp [contents]
  | succ n ih =>
    rw [insert_succ]
    split <;> rename_i h
    · simp only [contents, List.orderedInsert_cons, h, if_true]
      rw [Function.update_self]
      congr 1
      exact contents_update_before m (base + 1) (n + 1) base x (by omega)
    · rw [contents, insert_frame _ _ _ _ base (Or.inl (by omega))]
      rw [Function.update_self, ih, contents_update_before _ _ _ _ _ (by omega)]
      simp [contents, h]

/-- Sorting preserves every cell outside its input block. -/
theorem insertionSort_frame (m : Memory) (base n a : Nat)
    (h : a < base ∨ base + n ≤ a) :
    (insertionSort base n m).memory a = m a := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [insertionSort_succ]
    rw [insert_frame _ _ _ _ _ (by omega), ih _ (by omega)]

/-- Refinement removes the RAM implementation from subsequent functional proofs. -/
theorem insertionSort_contents (m : Memory) (base n : Nat) :
    contents (insertionSort base n m).memory base n =
      List.insertionSort (· ≤ ·) (contents m base n) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [insertionSort_succ]
    rw [insert_contents, ih]
    rfl

def ofList (xs : List Nat) : Memory := fun a => xs[a]?.getD 0

end AlgoLib.Experimental.RAM
