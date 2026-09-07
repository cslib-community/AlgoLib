/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Native array storage through ordinary frontend assembly

The same source program, generated proof, and executable interface use consecutive
integer cells. Inspecting the raw certified execution rules out a hidden paired
representation. The second element is negative and must remain exactly unchanged.
-/
namespace AlgoLib.Experimental.RAM.Tests.NativeArrays
open Prototype.Composition Prototype.Frontend

ram method negateHead (mut a : Array Int) return (result : Unit)
  require 0 < a.size
  ensures a.size = aOld.size
  do
    a[0] := -a[0]

generate_obligations negateHead
complete_algorithm negateHead
compile_array_method negateHead

private def rawInput : Array Int := #[-3, -7, 11]

private theorem terminates : ∃ k t,
    Native.Eval (negateHeadLinked 3).supported.compile.code
      ((negateHeadEncoder 3).store rawInput) k t := by
  obtain ⟨k, b, source, _, _⟩ := negateHeadProcedure.correct rawInput (by decide)
  obtain ⟨steps, t, left, he, _, _, _⟩ := (negateHeadLinked 3).supported.compile.sound source
    _ _ _ ((negateHeadEncoder 3).correct rawInput (by
      simp [negateHeadEncoder, Native.arrayEncoder, negateHeadLayout, rawInput]))
  exact ⟨steps, t, he⟩

private def rawResult : Nat × Native.Store :=
  Native.run (negateHeadLinked 3).supported.compile.code
    ((negateHeadEncoder 3).store rawInput) terminates

set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  let r := rawResult
  unless r.2.heap 0 == 3 && r.2.heap 1 == -7 && r.2.heap 2 == 11 do
    throw <| IO.userError "signed arrays must occupy consecutive native integer cells"
  let result :=  negateHeadRun [-3, -7, 11] (by decide)
  unless result.value == [3, -7, 11] && result.steps == r.1 do
    throw <| IO.userError "public array execution disagrees with certified native execution"

end AlgoLib.Experimental.RAM.Tests.NativeArrays
