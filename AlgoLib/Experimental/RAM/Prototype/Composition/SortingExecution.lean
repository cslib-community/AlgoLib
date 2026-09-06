/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
import AlgoLib.Experimental.RAM.Prototype.Composition.Encoding

/-!
# Ordinary lists through the unified frontend and verified RAM compiler

`Sorting.insertionSort` supplies all algorithmic reasoning. This adapter chooses
resident array storage and reconstructs private local registers from the generated
local type. It contains no algorithm-specific simulation or loop proof.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting

private abbrev scratch := local_storage% "sort" : insertionSortLocals
private abbrev layout (n : Nat) : Storage.ArrayLayout := ⟨⟨"array.size"⟩, 0, n⟩
private abbrev encoder (n : Nat) := (arrayEncoder (layout n)).hide scratch
  (by simp [scratch, Encoder.sep, scalarEncoder])
  (by simp [arrayEncoder, layout, Storage.ArrayLayout.footprint, scratch, Encoder.sep,
    scalarEncoder, Finset.disjoint_left])

private abbrev representation (n : Nat) := (encoder n).representation

private instance (n : Nat) : Linked 24 (representation n) insertionSortProcedure.body
    (representation n) := by ram_link

/-- No fuel, scratch values, addresses, or compiler knowledge in the caller interface. -/
def run (xs : List Nat) : Result (List Nat) :=
  let r := runEncoded (rate := 24) (Q := representation xs.length) insertionSortProcedure
    (encoder xs.length) xs.toArray
    (by trivial) (by simp [Encoder.hide, arrayEncoder, layout])
  ⟨r.value.toList, r.steps⟩

/-- Correctness and a derived quadratic bound for the very executable above. -/
theorem main (xs : List Nat) : SortedPermutation xs (run xs).value ∧
    (run xs).steps ≤ 3840 * (xs.length + 1)^2 := by
  have h := runEncoded_correct (rate := 24) (Q := representation xs.length) insertionSortProcedure
    (encoder xs.length) xs.toArray
    (by trivial) (by simp [Encoder.hide, arrayEncoder, layout])
  constructor
  · exact h.1.1
  · have bound := h.2
    change (run xs).steps ≤ _ at bound
    simp [potential,
      encoder, Encoder.hide, scratch, Encoder.sep, scalarEncoder, arrayEncoder] at bound
    nlinarith

private abbrev minimumEncoder (n : Nat) := (encoder n).sep (scalarEncoder ⟨"minimum"⟩)
  (by simp [encoder, Encoder.hide, arrayEncoder, layout, Storage.ArrayLayout.footprint,
    scratch, Encoder.sep, scalarEncoder, Finset.disjoint_left])

private instance (n : Nat) : Linked 24 (minimumEncoder n).representation
    minimumAfterSortProcedure.body (minimumEncoder n).representation := by ram_link

/-- Calls the sorter, then executes a scalar read through the same owned array interface. -/
def minimum (xs : List Nat) (nonempty : 0 < xs.length) :=
  runEncoded (rate := 24) (Q := (minimumEncoder xs.length).representation)
    minimumAfterSortProcedure (minimumEncoder xs.length) (xs.toArray, 0)
    ⟨by simpa using nonempty, trivial⟩
    (by simp [Encoder.sep, Encoder.hide, arrayEncoder, scalarEncoder, layout])

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
      unless result.steps ≤ 3840*(n+1)^2 do
        throw <| IO.userError "unified sorting cost"

end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
