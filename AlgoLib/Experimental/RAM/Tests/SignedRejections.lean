/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Signed typing and safety rejection regressions

Explicit truncation and a checked signed index have different contracts. A negative
checked index cannot obtain a certificate, even though Int.toNat would yield zero.
-/
namespace AlgoLib.Experimental.RAM.Tests.SignedRejections
open Prototype.Composition Prototype.Frontend

/-- error: Signed arithmetic requires Int; use Int.ofNat for a Nat variable -/
#guard_msgs in
ram method implicitWidening (mut x : Int) (mut n : Nat) return (u : Unit)
  do
    x := x + n

/-- error: A scalar expression requires Nat -/
#guard_msgs in
ram method implicitNarrowing (mut x : Int) (mut n : Nat) return (u : Unit)
  do
    n := x

ram method negativeIndex (mut arr : Array Int) return (u : Unit)
  do
    arr[-1] := 2

example : ¬negativeIndex.Obligations := by
  intro h
  have bad := h #[0] trivial
  dsimp [negativeIndex] at bad
  contract_vc

ram method beyondEnd (mut arr : Array Int) return (u : Unit)
  do
    arr[arr.size] := 2

example : ¬beyondEnd.Obligations := by
  intro h
  have bad := h #[0] trivial
  dsimp [beyondEnd] at bad
  contract_vc

end AlgoLib.Experimental.RAM.Tests.SignedRejections
