/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Ordinary lists through the unified frontend and verified RAM compiler

`Sorting.insertionSort` supplies all algorithmic reasoning. This adapter chooses
resident array storage and reconstructs private local registers from the generated
local type. It contains no algorithm-specific simulation or loop proof.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting

-- This one command assembles the resident backend, executable, and joint theorem.
compile_array_method insertionSort

/-- A normal Lean list goes in and a normal Lean list comes out; execution needs no fuel. -/
def run (xs : List Nat) : Result (List Nat) := insertionSortRun xs

/-- The bound is generated from the program and its iteration annotations. -/
theorem main (xs : List Nat) : SortedPermutation xs (run xs).value ∧
    (run xs).steps ≤ insertionSortBound xs := by
  have h := insertionSortCorrect xs (by trivial)
  exact ⟨by simpa using h.1.1, h.2⟩

/-- A readable polynomial form of the automatically generated bound. -/
theorem bound_eq (xs : List Nat) :
    insertionSortBound xs = 912 * xs.length ^ 2 + 384 * xs.length + 648 := by
  simp [insertionSortBound, Value.credits, Locals.credits]
  ring

/-- The inferred bound establishes quadratic RAM time. -/
theorem quadratic (xs : List Nat) : (run xs).steps ≤ 1944 * (xs.length + 1)^2 := by
  have h := (main xs).2
  rw [bound_eq] at h
  nlinarith

private abbrev minimumEncoder (n : Nat) := (insertionSortEncoder n).sep (scalarEncoder ⟨"minimum"⟩)
  (by simp [insertionSortEncoder, Encoder.hide, arrayEncoder, insertionSortLayout,
    Storage.ArrayLayout.footprint,
    insertionSortScratch, Encoder.sep, scalarEncoder, Finset.disjoint_left])

private instance (n : Nat) : Linked 24 (minimumEncoder n).representation
    minimumAfterSortProcedure.body (minimumEncoder n).representation := by ram_link

/-- Calls the sorter, then executes a scalar read through the same owned array interface. -/
def minimum (xs : List Nat) (nonempty : 0 < xs.length) :=
  runEncoded (rate := 24) (Q := (minimumEncoder xs.length).representation)
    minimumAfterSortProcedure (minimumEncoder xs.length) (xs.toArray, 0)
    ⟨by simpa using nonempty, trivial⟩
    (by simp [Encoder.sep, Encoder.hide, arrayEncoder, scalarEncoder, insertionSortLayout])

set_option linter.hashCommand false in
#eval show IO Unit from do
  let r := minimum [5, 3, 8, 1] (by decide)
  unless r.value == (#[1, 3, 5, 8], 1) do
    throw <| IO.userError "array procedure followed by direct indexing"

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 6 do
    for mask in List.range (3^n) do
      let xs := (List.range n).map (fun i => mask / 3^i % 3)
      let result := run xs
      unless result.value == xs.mergeSort (· ≤ ·) do
        throw <| IO.userError s!"unified sorting: {xs}"
      unless result.steps ≤ insertionSortBound xs do
        throw <| IO.userError "unified sorting cost"

end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
