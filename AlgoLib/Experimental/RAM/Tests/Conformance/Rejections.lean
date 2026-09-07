/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Rejected source programs

Unsupported lexical aliasing, escaped locals, mutation of immutable locals, and host
arithmetic outside the accepted syntax must fail at elaboration. Unsafe indexing
must fail verification, even though a mathematical array lookup has a default value.
-/
namespace AlgoLib.Experimental.RAM.Tests.Conformance.Rejections
open Prototype.Composition Prototype.Frontend

/-- error: Local name already used; shadowing is not supported -/
#guard_msgs in
ram method shadow (mut arr : Array Nat) return (u : Unit)
  do
    let mut x := 0
    if 0 < arr.size then
      let x := 1
      arr[0] := x

/-- error: Local 'x' is not in scope -/
#guard_msgs in
ram method escaped (mut arr : Array Nat) return (u : Unit)
  do
    if 0 < arr.size then
      let x := 1
    arr[0] := x

/-- error: Immutable local; use 'let mut' -/
#guard_msgs in
ram method immutable (mut arr : Array Nat) return (u : Unit)
  do
    let x := 0
    x := 1

/-- error: Supported expressions are Nat variables, constants, array indexing, array size, and +, -, *. Use a verified procedure for other computations -/
#guard_msgs in
ram method hostDivision (mut arr : Array Nat) return (u : Unit)
  do
    let x := arr.size / 2

ram method unsafeStore (mut arr : Array Nat) return (u : Unit)
  do
    arr[0] := 1

example : ¬ unsafeStore.Obligations := by
  intro verified
  have bad := verified #[] trivial
  dsimp [unsafeStore] at bad
  contract_vc

end AlgoLib.Experimental.RAM.Tests.Conformance.Rejections
