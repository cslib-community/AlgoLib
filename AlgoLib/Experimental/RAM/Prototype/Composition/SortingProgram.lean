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


end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
