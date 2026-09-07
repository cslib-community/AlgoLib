/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Composition of separately owned signed arrays

The source proof is independent of the two heap bases. This backend fixture puts
both arrays away from address zero and composes their encoders with signed scratch.
No array operation may overwrite its neighbor or the private local representation.
-/
namespace AlgoLib.Experimental.RAM.Tests.SignedOwnership
open Prototype.Composition Prototype.Frontend

ram method swapFirst (mut left : Array Int) (mut right : Array Int) return (u : Unit)
  require 0 < left.size ∧ 0 < right.size
  ensures left = leftOld.set! 0 rightOld[0]! ∧ right = rightOld.set! 0 leftOld[0]!
  do
    let x : Int := left[0]!
    left[0] := right[0]!
    right[0] := x

generate_obligations swapFirst
complete_algorithm swapFirst

private abbrev leftLayout : SignedArrays.Layout :=
  ⟨SignedStorageImpl.Layout.named "twins.left", 10, 2⟩
private abbrev rightLayout : SignedArrays.Layout :=
  ⟨SignedStorageImpl.Layout.named "twins.right", 100, 2⟩
private abbrev scratch := local_storage% "twins.scratch" : swapFirstLocals
private abbrev encoder :=
  ((SignedArrays.encoder leftLayout).sep (SignedArrays.encoder rightLayout) (by decide)).hide
    scratch (by trivial) (by decide)

private instance : Linked 24 encoder.representation swapFirst.body encoder.representation := by
  ram_link

set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  for k in List.range 11 do
    let a : Int := (k : Int) - 5
    let input := (#[a, -9], #[-a, 7])
    let result := runEncoded (rate := 24) (Q := encoder.representation)
      swapFirstProcedure encoder input (by simp [input]) (by simp [encoder, input,
        Encoder.hide, Encoder.sep, SignedArrays.encoder, leftLayout, rightLayout])
    unless result.value == (#[-a, -9], #[a, 7]) do
      throw <| IO.userError "signed ownership/layout composition"

end AlgoLib.Experimental.RAM.Tests.SignedOwnership
