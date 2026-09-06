/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend
import AlgoLib.Experimental.RAM.Authoring.ArrayFacts

/-!
# A linear array algorithm proved without selecting a backend

The program overwrites every element with zero. Its one invariant and logical
credit proof are reused with contiguous and indirect arrays in ArraySubstitution.
This file has no transitive RAM import. The same frontend and VCG used by sorting
handle this algorithm; there is no specialized zeroing compiler or proof tactic.
-/
namespace AlgoLib.Experimental.RAM.Prototype.ZeroAlgorithm
open Authoring Frontend

/-- Extending a zero prefix is the sole algorithm-specific preservation fact. -/
theorem zero_prefix (a : Array Nat) (i : Nat) (hi : i < a.size)
    (hprefix : ∀ j, j < i → a[j]! = 0) :
    ∀ j, j < i + 1 → (a.setIfInBounds i 0)[j]! = 0 := by
  intro j hj
  have hb : j < a.size := by omega
  rw [ArrayFacts.get_set a i j 0 hb]
  split_ifs with equal
  · rfl
  · exact hprefix j (by omega)

ram method zeroArray (mut arr : Array Nat) return (u : Unit)
  ensures arr.size = arrOld.size
  ensures ∀ j, j < arr.size → arr[j]! = 0
  credits 100 * arr.size + 110
  do
    let mut i := 0
    while i < arr.size
      invariant i ≤ arr.size
      invariant arr.size = arrOld.size
      invariant ∀ j, j < i → arr[j]! = 0
      invariant 100 * (arr.size - i) + 100 ≤ remaining
      decreasing arr.size - i
      do
        arr[i] := 0
        i := i + 1
    return

prove_algorithm zeroArray by
  ram_solve [zero_prefix]

end AlgoLib.Experimental.RAM.Prototype.ZeroAlgorithm
