/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.SortingAlgorithm
import AlgoLib.Experimental.RAM.Prototype.ZeroAlgorithm
import AlgoLib.Experimental.RAM.Prototype.IndirectArrays

/-!
# Unchanged algorithms and proofs across two array implementations

SortingAlgorithm and ZeroAlgorithm are pure frontend modules: neither imports RAM.
This file attaches contiguous or pointer-indirected array storage. Each pair below
passes exactly the same Specification and the same logical proof to Interface.realize.
There are no repeated invariants, credit arguments, or algorithm-specific compilation rules.

Both backends use the existing unit-cost RAM, but they have different memory
representations and access algorithms: direct loads/stores versus pointer-table
loads followed by payload access. This is data-structure substitution, not extra
scratch instructions. Table non-aliasing and write framing are proved in IndirectArrays.
-/
namespace AlgoLib.Experimental.RAM.Prototype.ArraySubstitution
open Authoring InsertionSort ZeroAlgorithm

/-- The same insertion-sort declaration and proof, with contiguous array storage. -/
def denseSort := Mutable.interface.realize insertionSort insertionSortCorrect

/-- The exact same declaration and proof, with indirect array storage. -/
def indirectSort := IndirectArrays.interface.realize insertionSort insertionSortCorrect

/-- Reuse a second, linear-time algorithm through both implementations. -/
def denseZero := Mutable.interface.realize zeroArray zeroArrayCorrect

def indirectZero := IndirectArrays.interface.realize zeroArray zeroArrayCorrect

/-- Backend selection cannot change the algorithm body being proved. -/
theorem sorting_body : denseSort.method.body = indirectSort.method.body := rfl

theorem zeroing_body : denseZero.method.body = indirectZero.method.body := rfl

/-- Each implementation obtains its output and RAM bound from the same logical proof. -/
theorem sorting_correct (xs : Array Nat) :
    (SortedPermutation xs.toList (denseSort.run xs (by trivial)).value.toList ∧
      (denseSort.run xs (by trivial)).steps ≤ denseSort.method.time xs) ∧
    (SortedPermutation xs.toList (indirectSort.run xs (by trivial)).value.toList ∧
      (indirectSort.run xs (by trivial)).steps ≤ indirectSort.method.time xs) := by
  have dense := denseSort.correct xs (by trivial)
  have indirect := indirectSort.correct xs (by trivial)
  exact ⟨⟨dense.1.1, dense.2⟩, ⟨indirect.1.1, indirect.2⟩⟩

/-- Implementation substitution preserves the exact returned list on every input. -/
theorem sorting_outputs_equal (xs : Array Nat) :
    (denseSort.run xs (by trivial)).value.toList =
      (indirectSort.run xs (by trivial)).value.toList := by
  have dense := (sorting_correct xs).1.1
  have indirect := (sorting_correct xs).2.1
  exact List.Perm.eq_of_pairwise' dense.1 indirect.1 (dense.2.trans indirect.2.symm)

/-- No RAM conversion is part of the zeroing algorithm's proof. -/
theorem zeroing_correct (xs : Array Nat) :
    zeroArray.ensures xs (denseZero.run xs (by trivial)).value ∧
    zeroArray.ensures xs (indirectZero.run xs (by trivial)).value ∧
    (denseZero.run xs (by trivial)).steps ≤ denseZero.method.time xs ∧
    (indirectZero.run xs (by trivial)).steps ≤ indirectZero.method.time xs :=
  ⟨(denseZero.correct xs (by trivial)).1, (indirectZero.correct xs (by trivial)).1,
    (denseZero.correct xs (by trivial)).2, (indirectZero.correct xs (by trivial)).2⟩

end AlgoLib.Experimental.RAM.Prototype.ArraySubstitution
