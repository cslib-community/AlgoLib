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
`Prefix` and `Hole` express the textbook argument. Remaining iteration bounds
replace manual credit invariants and bookkeeping constants. `prove_algorithm` generates
named safety, invariant, and iteration-bound obligations from this very body.
The same body has the actual Loom interpretation
and compiles to RAM. There is no `insertNext` action or algorithm-specific lowering.

This file imports no RAM backend. SortingExecution.lean supplies the default list
runner. This is the owned-language
version; historical array-substitution regressions remain in the compatibility layer.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
open Frontend SortingFacts

/-- Preserve multiplicities as well as ordering. -/
def SortedPermutation (xs ys : List Nat) : Prop := ys.Pairwise (· ≤ ·) ∧ ys.Perm xs

ram method insertionSort (mut arr : Array Nat) return (u : Unit)
  require True
  ensures SortedPermutation arrOld.toList arr.toList
  do
    let mut i := 0
    while i < arr.size named outer
      invariant "index" i ≤ arr.size
      invariant "prefix" Prefix arr i
      invariant "permutation" arr.toList.Perm arrOld.toList
      invariant "size" arr.size = arrOld.size
      iterations_at_most arr.size - i
      do
        let mut j := i
        while 0 < j named inner
          invariant "index" j ≤ i
          invariant "bounds" i < arr.size
          invariant "hole" Hole arr i j
          invariant "permutation" arr.toList.Perm arrOld.toList
          invariant "size" arr.size = arrOld.size
          iterations_at_most j
          do
            let x := arr[j]!
            let y := arr[j - 1]!
            if x < y then
              arr[j] := y
              arr[j - 1] := x
            j := j - 1
        i := i + 1
    return

-- During authoring: #named_goals insertionSort only outer.inner.preserve
prove_algorithm insertionSort where
  case outer.initialize.prefix => by simp [Prefix]
  case outer.inner.initialize.hole => by grind only [enter]
  case outer.inner.preserve.hole => by
    first
    | apply swap <;> first | assumption | omega
    | apply keep <;> first | assumption | omega
  case outer.inner.preserve.permutation => by
    grind only [swap_preserves_permutation]
  case outer.preserve.prefix => by grind only [exit]
  case outer.terminate => by omega
  case outer.account => by omega
  case outer.inner.account => by omega
  case outer.exit => by grind only [SortedPermutation, sorted]

/- A caller can combine an array procedure with direct indexing and a scalar result.
The callee is used through its public contract, including the permutation fact. -/
ram method minimumAfterSort (mut arr : Array Nat) (mut smallest : Nat)
    return (result : Array Nat × Nat)
  require 0 < arr.size
  ensures SortedPermutation arrOld.toList arr.toList
  ensures smallest = arr[0]!
  do
    arr := insertionSortProcedure
    smallest := arr[0]!

/-- Permutation preserves length, also when used through a procedure summary. -/
theorem sorted_size {a b : Array Nat} (h : SortedPermutation a.toList b.toList) :
    b.size = a.size := by simpa using h.2.length_eq

prove_algorithm minimumAfterSort where
  case method.safety => by grind only [sorted_size]

end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
