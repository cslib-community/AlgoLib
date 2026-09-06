/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Frontend

/-!
# Multiple-array frontend and frame regressions

The two mutable parameters are independent Lean values, including when the same
input array value is supplied for both. Their RAM lanes are disjoint. Verification
must establish both the intended write and preservation of the other array.
-/
namespace AlgoLib.Experimental.RAM.Prototype.MultipleArrayTests
open Authoring Frontend

ram method exchangeHeads (mut left : Array Nat) (mut right : Array Nat) return (u : Unit)
  require 0 < left.size
  require 0 < right.size
  ensures left = leftOld.set! 0 rightOld[0]!
  ensures right = rightOld.set! 0 leftOld[0]!
  credits 50
  do
    let x := left[0]!
    let y := right[0]!
    left[0] := y
    right[0] := x
    return

prove_ram exchangeHeads by
  ram_solve []

/-- The inputs and outputs are ordinary Lean arrays. -/
def exchange (left right : Array Nat) (hl : 0 < left.size) (hr : 0 < right.size) :
    Result (Fin 2 → Array Nat) :=
  exchangeHeadsVerified.run ![left, right] ⟨hl, hr, trivial⟩

set_option linter.hashCommand false in
/-- info: (#[8, 2], #[1, 9, 10]) -/
#guard_msgs in
#eval let result := exchange #[1, 2] #[8, 9, 10] (by decide) (by decide)
      (result.value 0, result.value 1)

/-- Updating one array frames the other even for arbitrary lengths and values. -/
example (s : MultipleArrays.State 2) (i v : Nat) :
    (s.write 0 i v).arrays 1 = s.arrays 1 :=
  MultipleArrays.write_other s 0 1 i v (by decide)

/- Loop framing keeps the second array available without an adjacency-style frame proof. -/
ram method clearLeft (mut left : Array Nat) (mut right : Array Nat) return (u : Unit)
  ensures right = rightOld
  ensures left.size = leftOld.size
  credits 100 * left.size + 100
  do
    let mut i := 0
    while i < left.size
      invariant i ≤ left.size
      invariant left.size = leftOld.size
      invariant 30 * (left.size - i) + 20 ≤ remaining
      decreasing left.size - i
      do
        left[i] := 0
        i := i + 1
    return

prove_ram clearLeft by
  ram_solve [Array.size_setIfInBounds]

ram method touchThree (mut a : Array Nat) (mut b : Array Nat) (mut c : Array Nat)
  return (u : Unit)
  require 0 < a.size ∧ 0 < b.size ∧ 0 < c.size
  ensures a = aOld.set! 0 bOld[0]!
  ensures b = bOld
  ensures c = cOld.set! 0 aOld[0]!
  credits 100
  do
    let first := a[0]!
    a[0] := b[0]!
    c[0] := first
    return

prove_ram touchThree by
  ram_solve []

set_option linter.hashCommand false in
#eval show IO Unit from do
  let cleared := (clearLeftVerified.run ![#[9, 8, 7], #[6, 5]] trivial).value
  unless cleared 0 == #[0, 0, 0] && cleared 1 == #[6, 5] do
    throw <| IO.userError "multiple-array loop frame"
  let empty := (clearLeftVerified.run ![#[], #[6]] trivial).value
  unless empty 0 == #[] && empty 1 == #[6] do
    throw <| IO.userError "empty first array"
  let shared := #[9, 8]
  let independent := (clearLeftVerified.run ![shared, shared] trivial).value
  unless independent 0 == #[0, 0] && independent 1 == shared do
    throw <| IO.userError "value parameters must occupy independent lanes"
  let three := (touchThreeVerified.run ![#[7], #[8, 9], #[10, 11, 12]]
    ⟨⟨by decide, by decide, by decide⟩, trivial⟩).value
  unless three 0 == #[8] && three 1 == #[8, 9] && three 2 == #[7, 11, 12] do
    throw <| IO.userError "three independent arrays"

/-- An empty array is unsafe even when another parameter has a cell at that index. -/
example (c : Nat) : ¬ (Plan.action (MultipleArrays.read "x" (0 : Fin 2) (.literal 0))).vc
    (fun _ _ => True) (MultipleArrays.initial ![#[], #[1]]) c := by
  simp [Plan.vc, MultipleArrays.read, MultipleArrays.Value.eval, MultipleArrays.initial]

set_option linter.hashCommand false in
/-- error: RAM inputs must be declared mutable arrays -/
#guard_msgs in
ram method rejectFunction (mut a : Array Nat) (f : Nat → Nat) return (u : Unit)
  credits 100
  do
    return

set_option linter.hashCommand false in
/-- error: Unsupported RAM expression: Nat.succ 0 -/
#guard_msgs in
ram method rejectUncompiledCall (mut a : Array Nat) (mut b : Array Nat) return (u : Unit)
  credits 100
  do
    let x := Nat.succ 0
    return

set_option linter.hashCommand false in
/-- error: Reserve output, old-array, and remaining-credit names -/
#guard_msgs in
ram method rejectGhostCollision (mut a : Array Nat) (mut b : Array Nat) return (aOld : Unit)
  credits 100
  do
    return

end AlgoLib.Experimental.RAM.Prototype.MultipleArrayTests
