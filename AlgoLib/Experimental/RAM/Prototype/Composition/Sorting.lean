/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend
import AlgoLib.Experimental.RAM.Prototype.SortingFacts

/-!
# Insertion sort with mutable arrays and inline loop invariants

Read `insertionSort` as pseudocode. Both loops and every array read/write are visible.
`Prefix` and `Hole` express the textbook argument; `remaining` is the available
credit budget. `prove_algorithm` generates safety, correctness, termination, and logical credit
conditions from this very body. The same body has the actual Loom interpretation
and compiles to RAM. There is no `insertNext` action or algorithm-specific lowering.

This file imports no RAM backend. SortingExecution.lean supplies the default list
runner. This is the owned-language
version; historical array-substitution regressions remain in the compatibility layer.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
open Frontend SortingFacts

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
  credits potential arr.size 0 + 60
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

set_option maxHeartbeats 400000 in
-- Both nested loop invariants are normalized and checked in one generated proof.
prove_algorithm insertionSort by
  contract_solve [potential_positive, insertion_allowance, SortedPermutation,
    Prefix, Hole, enter, exit, keep, swap, swap_perm, sorted, List.Perm.trans]

/- A caller can combine an array procedure with direct indexing and a scalar result.
The callee is used through its public contract, including the permutation fact. -/
ram method minimumAfterSort (mut arr : Array Nat) (mut smallest : Nat)
    return (result : Array Nat × Nat)
  require 0 < arr.size
  ensures SortedPermutation arrOld.toList arr.toList
  ensures smallest = arr[0]!
  credits insertionSort.credits arr + 5
  do
    arr := insertionSortProcedure
    smallest := arr[0]!

/-- Permutation preserves length, also when used through a procedure summary. -/
theorem sorted_size {a b : Array Nat} (h : SortedPermutation a.toList b.toList) :
    b.size = a.size := by simpa using h.2.length_eq

prove_algorithm minimumAfterSort by
  contract_solve [SortedPermutation, sorted_size]

end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
