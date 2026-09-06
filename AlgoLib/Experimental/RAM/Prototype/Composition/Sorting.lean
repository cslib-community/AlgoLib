/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.SortingProofs

/-!
# Verified sorting and a modular caller

The paper program lives in `SortingProgram`, its generated API in `SortingSpec`;
edit algorithmic proofs in
`SortingProofs`. `SortingBackend` depends only on the specification, so proof edits
reuse its instruction certificates. `SortingExecution` connects proofs to that backend.
This module adds a caller using the sorting procedure's public contract.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
open Frontend SortingFacts

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
