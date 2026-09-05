/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.InsertionSort

/-!
# Executable and negative-contract tests for the prototype

The exhaustive small-input test runs compiled RAM, comparing its output with an
independent reference and checking the advertised bound. The examples also reject
unpaid calls, invalid call preconditions, and mismatched program annotations.
These tests supplement the universal theorems; they are not correctness certificates.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Tests
open Authoring Authoring.Insertion

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 6 do
    for mask in List.range (3 ^ n) do
      let xs := (List.range n).map (fun i => mask / 3 ^ i % 3)
      let r := InsertionSort.run xs
      unless r.value == xs.mergeSort (· ≤ ·) do
        throw <| IO.userError s!"prototype sorting: {xs}"
      unless r.steps ≤ 50 * n * n + 100 * n + 55 do
        throw <| IO.userError s!"prototype budget: {xs}"
  for xs in [List.range 16, (List.range 16).reverse, List.replicate 20 7] do
    let r := InsertionSort.run xs
    unless r.value == xs.mergeSort (· ≤ ·) do
      throw <| IO.userError s!"prototype larger input: {xs}"
    unless r.steps ≤ 205 * xs.length * xs.length do
      throw <| IO.userError s!"prototype larger budget: {xs}"

set_option linter.hashCommand false in
/-- info: [1, 1, 3, 4] -/
#guard_msgs in
#eval (InsertionSort.run [3, 1, 4, 1]).value

/-- Credits cannot be silently omitted at a procedure call. -/
example (s : State) : ¬ (Plan.action insertNext).vc (fun _ _ => True) s 0 := by
  simp [Plan.vc, insert_work]

/-- An insertion is not callable on an empty unprocessed prefix, even with ample credit. -/
example (c : Nat) : ¬ (Plan.action insertNext).vc (fun _ _ => True) (initial []) c := by
  simp [Plan.vc, insert_requires, initial]

/-- An invariant that forgets guard payments cannot certify a loop. -/
example : ¬ (Plan.loop more (fun _ _ => True) (.action insertNext)).vc
    (fun _ _ => True) (initial [1]) 0 := by
  intro h
  have unpaid := (h.2 (initial []) 0 trivial).1
  omega

/-- A proof plan for skip cannot be substituted for an insertion program's plan. -/
example : True := by
  fail_if_success
    have wrong : Plan (.action insertNext) := (Plan.skip : Plan (.skip : Program model))
  trivial

/-- Exercise sequencing and the false branch without relying on the sorting loop. -/
example : (Plan.seq Plan.skip (Plan.branch more (.action insertNext) Plan.skip)).vc
    (fun s _ => s = initial []) (initial []) 1 := by
  simp [Plan.vc, initial]

/-- The true branch propagates the procedure's effect and its cost. -/
example : (Plan.branch more (.action insertNext) Plan.skip).vc
    (fun s _ => s.sorted = [2]) (initial [2]) 2 := by
  simp [Plan.vc, insert_requires, insert_work, insert_effect, initial, effect]

end AlgoLib.Experimental.RAM.Prototype.Tests
