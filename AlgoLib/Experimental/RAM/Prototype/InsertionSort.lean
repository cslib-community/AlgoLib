/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Frontend
import AlgoLib.Experimental.RAM.Prototype.SortingFacts

/-!
# Insertion sort with mutable arrays and inline loop invariants

Read `insertionSort` as pseudocode. Both loops and every array read/write are visible.
`Prefix` and `Hole` express the textbook argument; `remaining` is the available
credit budget. `prove_ram` generates safety, correctness, termination, and time
conditions from this very body. The same body has the actual Loom interpretation
and compiles to RAM. There is no `insertNext` action or algorithm-specific lowering.

`run` is the familiar list convenience interface to the compiled executable.
-/
namespace AlgoLib.Experimental.RAM.Prototype.InsertionSort
open Authoring Frontend SortingFacts

/-- Preserve multiplicities as well as ordering. -/
def SortedPermutation (xs ys : List Nat) : Prop := ys.Pairwise (· ≤ ·) ∧ ys.Perm xs

/-- Reserve one linear insertion allowance for each remaining prefix extension. -/
def potential (n i : Nat) : Nat := 100 * (n - i) * (n + 1) + 100

/-- Each loop test is paid for, including its final unsuccessful test. -/
theorem potential_positive (n i : Nat) : 100 ≤ potential n i := by
  unfold potential
  omega

/-- A prefix extension pays for one complete inner scan and its scalar bookkeeping. -/
theorem insertion_allowance (n i : Nat) (hi : i < n) :
    potential n (i + 1) + 100 * i + 36 ≤ potential n i := by
  have eq : n - i = n - (i + 1) + 1 := by omega
  simp only [potential, eq, Nat.mul_add, Nat.add_mul, Nat.mul_one]
  omega

ram method insertionSort (mut arr : Array Nat) return (u : Unit)
  require True
  ensures SortedPermutation arrOld.toList arr.toList
  credits potential arr.size 0 + 20
  do
    let mut i := 0
    while i < arr.size
      invariant i ≤ arr.size
      invariant Prefix arr i
      invariant arr.toList.Perm arrOld.toList
      invariant arr.size = arrOld.size
      invariant potential arr.size i ≤ remaining
      decreasing arr.size - i
      do
        let mut j := i
        while 0 < j
          invariant j ≤ i
          invariant i < arr.size
          invariant Hole arr i j
          invariant arr.toList.Perm arrOld.toList
          invariant arr.size = arrOld.size
          invariant potential arr.size (i + 1) + 100 * j + 20 ≤ remaining
          decreasing j
          do
            let x := arr[j]!
            let y := arr[j - 1]!
            if x < y then
              arr[j] := y
              arr[j - 1] := x
            j := j - 1
        i := i + 1
    return

prove_ram insertionSort by
  ram_solve [potential_positive, insertion_allowance, SortedPermutation,
    Prefix, Hole, enter, exit, keep, swap, swap_perm, sorted, List.Perm.trans]

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
    simp only [certified, insertionSortVerified, certify, Method.time, insertionSort,
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
