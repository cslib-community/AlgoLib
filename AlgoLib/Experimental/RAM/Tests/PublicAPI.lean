/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language
import AlgoLib.Experimental.RAM.Verification
import AlgoLib.Experimental.RAM.Library
import AlgoLib.Experimental.RAM.Implementations
import AlgoLib.Experimental.RAM.Compiler
import AlgoLib.Experimental.RAM.Machine
import AlgoLib.Experimental.RAM.Examples

/-!
# Public layer imports and canonical names

This client uses no historical namespace or internal import. The generated proof
API, signed executable, library contract, and complete examples work together.
-/
namespace AlgoLib.Experimental.RAM.Tests.PublicAPI

ram method decrement (mut x : Int) return (result : Int)
  ensures result = xOld - 1
  do
    x := x - 1

generate_obligations decrement
complete_algorithm decrement
compile_scalar_method decrement

example : Language.Program Nat Nat := .identity
example : (Library.Queue.enqueue 4).credits ([], 0) = 10 := rfl
example : Verification.Algorithm Int Int := decrement

set_option linter.hashCommand false in
#eval show IO Unit from do
  unless (decrementRun 0).value == -1 do
    throw <| IO.userError "canonical public signed method"
  unless (Examples.InsertionSort.run [3, 1, 2]).value == [1, 2, 3] do
    throw <| IO.userError "canonical public sorting runner"
  let graph := Examples.BFS.Inputs.diamond
  let result := Examples.BFS.search .circular graph ⟨0, by decide⟩
  unless result.value == Finset.range 4 do
    throw <| IO.userError "canonical public BFS runner"

#check Language.Contract.implement
#check Verification.Plan.sound
#check Verification.Algorithm.certify
#check Implementations.Encoder
#check Compiler.runEncoded_correct
#check Machine.run_correct
#check Examples.InsertionSort.insertionSort
#check Examples.InsertionSort.main
#check Examples.BFS.bfs
#check Examples.BFS.connected
#check Examples.BFS.linear

end AlgoLib.Experimental.RAM.Tests.PublicAPI
