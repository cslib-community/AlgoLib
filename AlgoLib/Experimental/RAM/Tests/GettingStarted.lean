/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language
import AlgoLib.Experimental.RAM.Verification
import AlgoLib.Experimental.RAM.Compiler
import AlgoLib.Experimental.RAM.Examples

/-!
# Getting started: from a source method to a certified RAM execution

This is the complete executable companion to `docs/GETTING-STARTED.md`.
It uses public imports and needs no historical namespaces, user-supplied fuel,
or backend proof. The inspection commands deliberately display their results.
-/
namespace AlgoLib.Experimental.RAM.Tests.GettingStarted

set_option linter.hashCommand false

-- Start by running the two complete public examples.
/-- info: [1, 1, 2, 3] -/
#guard_msgs in
#eval (Examples.InsertionSort.run [3, 1, 2, 1]).value
/-- info: {0, 1, 2, 3} -/
#guard_msgs in
#eval (Examples.BFS.search .circular Examples.BFS.Inputs.diamond ⟨0, by decide⟩).value

#check Examples.InsertionSort.main
#check Examples.BFS.search_correct
#check Examples.BFS.linear

-- A new source method, with ordinary integer arithmetic and a mathematical contract.
ram method magnitude (mut x : Int) return (result : Int)
  ensures result = |xOld|
  do
    if x < 0 then
      x := -x

-- Generate propositions before supplying the mathematical proof.
generate_obligations magnitude

#check magnitude.ObligationAPI.result
#named_goals magnitude only result
#proof_template magnitude only result

-- Both branches are covered by this one generated responsibility.
prove_obligation magnitude.ObligationAPI.result by
  simp_all [abs_of_neg, abs_of_nonneg]

#named_goals magnitude only result

-- Assemble the checked source procedure, then its integer RAM execution.
complete_algorithm magnitude
compile_scalar_method magnitude

#check magnitudeVerification
#check magnitudeProcedure
#check magnitudeCorrect

-- The generated theorem contains both functional correctness and the step bound.
theorem magnitude_correct (x : Int) :
    (magnitudeRun x).value = |x| ∧ (magnitudeRun x).steps ≤ magnitudeBound x := by
  simpa using magnitudeCorrect x (by trivial)

/-- A client can use the theorem without unfolding the program or the compiler. -/
theorem magnitude_nonnegative (x : Int) : 0 ≤ (magnitudeRun x).value := by
  rw [(magnitude_correct x).1]
  exact abs_nonneg x

/-- info: 7 -/
#guard_msgs in
#eval (magnitudeRun (-7)).value
/-- info: 0 -/
#guard_msgs in
#eval (magnitudeRun 0).value
/-- info: 9 -/
#guard_msgs in
#eval (magnitudeRun 9).value
/-- info: (15, 2256) -/
#guard_msgs in
#eval ((magnitudeRun (-7)).steps, magnitudeBound (-7))
/-- info: 47 -/
#guard_msgs in
#eval (magnitude.credits (-7))

-- Executable checks supplement the universal theorem above.
#eval show IO Unit from do
  for x in [-7, 0, 9] do
    let result := magnitudeRun x
    unless result.value == |x| && result.steps ≤ magnitudeBound x do
      throw <| IO.userError "getting-started magnitude execution"

end AlgoLib.Experimental.RAM.Tests.GettingStarted
