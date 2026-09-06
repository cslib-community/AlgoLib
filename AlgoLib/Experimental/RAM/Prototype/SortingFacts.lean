/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.ArrayFacts

/-!
# The mathematical argument for adjacent-swap insertion sort

These facts talk only about arrays and indices. A sorted prefix becomes a prefix
with one possible out-of-order position; comparing adjacent elements moves that
position left. There is no machine state, compiler, or verification-condition API here.
The frontend can use these ordinary lemmas when it reaches an annotated loop.
-/
namespace AlgoLib.Experimental.RAM.Prototype.SortingFacts
open Authoring.ArrayFacts

/-- Positions strictly before `i` are in nondecreasing order. -/
def Prefix (a : Array Nat) (i : Nat) : Prop :=
  ∀ p q, p < q → q < i → a[p]! ≤ a[q]!

/-- In the prefix through `i`, only position `j` may violate the ordering. -/
def Hole (a : Array Nat) (i j : Nat) : Prop :=
  ∀ p q, p < q → q ≤ i → q ≠ j → a[p]! ≤ a[q]!

/-- Open the insertion loop at the end of an already sorted prefix. -/
theorem enter (a : Array Nat) (i : Nat) (h : Prefix a i) : Hole a i i := by
  intro p q hp hq hn
  exact h p q hp (by omega)

/-- At position zero there is no remaining exception to ordering. -/
theorem exit (a : Array Nat) (i : Nat) (h : Hole a i 0) : Prefix a (i + 1) := by
  intro p q hp hq
  exact h p q hp (by omega) (by omega)

/-- An already ordered adjacent pair needs no swap. -/
theorem keep (a : Array Nat) (i j : Nat) (hj : 0 < j) (hji : j ≤ i)
    (h : Hole a i j) (ordered : a[j - 1]! ≤ a[j]!) : Hole a i (j - 1) := by
  intro p q hp hq hn
  by_cases eq : q = j
  · subst q
    by_cases eq : p = j - 1
    · simpa [eq] using ordered
    · exact Nat.le_trans (h p (j - 1) (by omega) (by omega) (by omega)) ordered
  · exact h p q hp hq eq

/-- Swapping the inverted adjacent pair moves the exceptional position left. -/
theorem swap (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : 0 < j)
    (hji : j ≤ i) (h : Hole a i j) (inverted : a[j]! < a[j - 1]!) :
    Hole ((a.set! j a[j - 1]!).set! (j - 1) a[j]!) i (j - 1) := by
  intro p q hp hq hn
  simp only [Array.set!_eq_setIfInBounds]
  rw [get_set _ (j - 1) q _ (by simpa using (show q < a.size by omega)),
    get_set _ (j - 1) p _ (by simpa using (show p < a.size by omega)),
    get_set a j q _ (by omega), get_set a j p _ (by omega)]
  split_ifs <;> subst_vars <;> first
    | exact Nat.le_of_lt inverted
    | exact h _ _ (by omega) (by omega) (by omega)

/-- A swap preserves every multiplicity, including duplicate keys. -/
theorem swap_perm (a : Array Nat) (j : Nat) (hj : 0 < j) (hb : j < a.size) :
    ((a.set! j a[j - 1]!).set! (j - 1) a[j]!).toList.Perm a.toList := by
  have hb' : j - 1 < a.size := by omega
  simpa [Array.perm_iff_toList_perm, Array.swap, Array.setIfInBounds, hb, hb', getElem!_pos] using
    (Array.swap_perm (xs := a) (i := j) (j := j - 1) hb hb')

/-- Adjacent exchange preserves the input multiset, composed with an earlier permutation. -/
theorem swap_preserves_permutation (a : Array Nat) (xs : List Nat) (j : Nat)
    (hj : 0 < j) (hb : j < a.size) (perm : a.toList.Perm xs) :
    ((a.toList.set j a[j - 1]!).set (j - 1) a[j]!).Perm xs := by
  simpa only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] using
    (swap_perm a j hj hb).trans perm

/-- The index-based invariant gives the conventional list sorting specification. -/
theorem sorted (a : Array Nat) (h : Prefix a a.size) : a.toList.Pairwise (· ≤ ·) := by
  rw [List.pairwise_iff_getElem]
  intro p q hp hq hpq
  have hp' : p < a.size := by simpa using hp
  have hq' : q < a.size := by simpa using hq
  simpa only [getElem!_pos a p hp', getElem!_pos a q hq', Array.getElem_toList] using h p q hpq hq'

end AlgoLib.Experimental.RAM.Prototype.SortingFacts
