/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Default frontend executes integer instructions

A source-level Nat subtraction must saturate even though its target machine has
signed subtraction. Pin the actual count to distinguish this default runner from
the old one-instruction natural machine. No migration command or proof appears in
the algorithm. The existing conformance corpus exercises the same default runner.
-/
namespace AlgoLib.Experimental.RAM.Tests.IntegerFrontend
open Prototype.Composition Prototype.Frontend

ram method subtractFive (mut arr : Array Nat) return (result : Unit)
  require 0 < arr.size
  ensures True
  do
    arr[0] := arr[0] - 5

generate_obligations subtractFive
complete_algorithm subtractFive
compile_array_method subtractFive

-- Ten IR instructions gain two native clamps: one Nat load and one subtraction.
set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  for n in List.range 11 do
    let result := subtractFiveRun [n] (by simp)
    unless result.value == [n - 5] && result.steps == 12 do
      throw <| IO.userError "default frontend did not execute Int-RAM Nat subtraction"

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Checked.Language.Method.integerRun_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Checked.Language.Method.integerRun_exec

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Checked.Language.Method.integerCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Checked.Language.Method.integerCorrect

end AlgoLib.Experimental.RAM.Tests.IntegerFrontend
