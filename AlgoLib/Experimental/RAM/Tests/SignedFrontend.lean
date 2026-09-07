/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Signed source arithmetic on the certified Int-RAM runner

These methods use the public frontend, generated obligations, and assembled
execution. Their mathematical inputs and outputs are ordinary Lean integers.
-/
namespace AlgoLib.Experimental.RAM.Tests.SignedFrontend
open Prototype.Composition Prototype.Frontend

ram method subtractFive (mut x : Int) return (result : Int)
  ensures result = xOld - 5
  do
    x := x - 5

generate_obligations subtractFive
complete_algorithm subtractFive
compile_scalar_method subtractFive

ram method signedLocals (mut x : Int) return (result : Int)
  ensures result = -(xOld - 3) * 2
  do
    let mut y : Int := x - 3
    y := -y
    x := y * 2

generate_obligations signedLocals
complete_algorithm signedLocals
compile_scalar_method signedLocals

ram method absolute (mut x : Int) return (result : Int)
  ensures result = |xOld|
  do
    if x < 0 then
      x := -x

generate_obligations absolute
prove_obligation absolute.ObligationAPI.result by
  simp_all [abs_of_neg, abs_of_nonneg]
complete_algorithm absolute
compile_scalar_method absolute

ram method countdown (mut x : Int) return (result : Int)
  require 0 ≤ x
  ensures result = 0
  do
    while 0 < x named count
      invariant "nonnegative" 0 ≤ x
      iterations_at_most x.toNat
      do
        x := x - 1

generate_obligations countdown
complete_algorithm countdown
compile_scalar_method countdown

ram method shiftArray (mut arr : Array Int) return (result : Unit)
  ensures arr.size = arrOld.size
  do
    let mut i : Nat := 0
    while i < arr.size named scan
      invariant "position" i ≤ arr.size
      invariant "length" arr.size = arrOld.size
      iterations_at_most arr.size - i
      do
        let mut x : Int := arr[i]!
        x.subtractFiveProcedure()
        arr[i] := x
        i := i + 1

generate_obligations shiftArray
complete_algorithm shiftArray
compile_array_method shiftArray

ram method conversion (mut x : Int) return (result : Int)
  ensures result = Int.ofNat xOld.toNat - 2
  do
    let n : Nat := x.toNat
    x := Int.ofNat n - 2

generate_obligations conversion
complete_algorithm conversion
compile_scalar_method conversion

ram method negateFirst (mut arr : Array Int) return (u : Unit)
  require 0 < arr.size
  ensures arr = arrOld.set! 0 (-arrOld[0]!)
  do
    arr[0] := -arr[0]!

generate_obligations negateFirst
complete_algorithm negateFirst
compile_array_method negateFirst

ram method signedIndex (mut arr : Array Nat) return (u : Unit)
  require 0 < arr.size
  ensures arr[0]! = 7
  do
    let i : Int := 0
    arr[i] := 7

generate_obligations signedIndex
complete_algorithm signedIndex
compile_array_method signedIndex

ram method notEqual (mut x : Int) return (result : Int)
  ensures result = (if xOld = -2 then 9 else -7)
  do
    if x != -2 then
      x := -7
    else
      x := 9

generate_obligations notEqual
complete_algorithm notEqual
compile_scalar_method notEqual

ram method natSubtractFive (mut x : Nat) return (result : Nat)
  ensures result = xOld - 5
  do
    x := x - 5

generate_obligations natSubtractFive
complete_algorithm natSubtractFive
compile_scalar_method natSubtractFive

ram method addTo (mut x : Int) (mut delta : Int) return (u : Unit)
  ensures x = xOld + deltaOld ∧ delta = deltaOld
  do
    x := x + delta

generate_obligations addTo
complete_algorithm addTo

/-- Runtime-argument contract following the existing receiver From convention. -/
abbrev addToProcedureFrom := addToProcedure

ram method runtimeArgument (mut x : Int) return (result : Int)
  ensures result = xOld - 3
  do
    let delta : Int := -3
    x.addToProcedure(delta)

generate_obligations runtimeArgument
complete_algorithm runtimeArgument
compile_scalar_method runtimeArgument

ram method localCountdown (mut x : Int) return (result : Int)
  require 0 ≤ x
  ensures result = 0
  do
    let mut y : Int := x
    while 0 < y named count
      invariant "nonnegative" 0 ≤ y
      iterations_at_most y.toNat
      do
        y := y - 1
    x := y

generate_obligations localCountdown
complete_algorithm localCountdown
compile_scalar_method localCountdown

ram method compoundConversion (mut x : Int) return (result : Int)
  ensures result = Int.ofNat (xOld - 3).toNat
  do
    let n := (x - 3).toNat
    x := Int.ofNat n

generate_obligations compoundConversion
complete_algorithm compoundConversion
compile_scalar_method compoundConversion

set_option linter.hashCommand false in
set_option profiler false in
#guard_msgs in
#eval show IO Unit from do
  for k in List.range 21 do
    let x : Int := (k : Int) - 10
    let a := subtractFiveRun x
    unless a.value == x - 5 && a.steps ≤ subtractFiveBound x do
      throw <| IO.userError "signed subtraction"
    let b := signedLocalsRun x
    unless b.value == -(x - 3) * 2 && b.steps ≤ signedLocalsBound x do
      throw <| IO.userError "signed locals"
    unless (absoluteRun x).value == |x| do
      throw <| IO.userError "signed comparison"
    unless (conversionRun x).value == Int.ofNat x.toNat - 2 do
      throw <| IO.userError "explicit conversion"
    unless (countdownRun (k : Int) (by simp)).value == 0 do
      throw <| IO.userError "signed loop"
    let xs := [x, 0, -x, x - 5]
    let r := shiftArrayRun xs
    unless r.value == xs.map (· - 5) && r.steps ≤ shiftArrayBound xs do
      throw <| IO.userError "signed array and procedure call"
    unless (negateFirstRun [x] (by simp)).value == [-x] do
      throw <| IO.userError "self-referential signed array write"
    unless (signedIndexRun [k] (by simp)).value == [7] do
      throw <| IO.userError "checked signed index into Nat array"
    unless (notEqualRun x).value == (if x = -2 then 9 else -7) do
      throw <| IO.userError "signed negated comparison"
    unless (natSubtractFiveRun k).value == k - 5 do
      throw <| IO.userError "Nat scalar subtraction remains saturating"
    unless (runtimeArgumentRun x).value == x - 3 do
      throw <| IO.userError "signed runtime procedure argument"
    unless (localCountdownRun (k : Int) (by simp)).value == 0 do
      throw <| IO.userError "signed local loop counting"
    unless (compoundConversionRun x).value == Int.ofNat (x - 3).toNat do
      throw <| IO.userError "compound conversion type inference"

end AlgoLib.Experimental.RAM.Tests.SignedFrontend
