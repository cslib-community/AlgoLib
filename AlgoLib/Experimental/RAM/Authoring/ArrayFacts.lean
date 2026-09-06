/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Reusable mathematical array substitution

This is a fact about ordinary Lean arrays. Both sorting and zeroing reuse it when
proving invariant preservation; it contains no backend representation or cost model.
-/
namespace AlgoLib.Experimental.RAM.Authoring.ArrayFacts

/-- An array read after an update: a reusable mathematical substitution rule. -/
theorem get_set (a : Array Nat) (i j v : Nat) (hj : j < a.size) :
    (a.setIfInBounds i v)[j]! = if j = i then v else a[j]! := by
  by_cases hi : i < a.size
  · simp [Array.setIfInBounds, hi, getElem!_pos, hj, Array.getElem_set, eq_comm]
  · have hji : j ≠ i := by omega
    simp [Array.setIfInBounds, hi, hji]

end AlgoLib.Experimental.RAM.Authoring.ArrayFacts
