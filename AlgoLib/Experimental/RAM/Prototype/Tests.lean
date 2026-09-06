/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.InsertionSort

/-!
# Executable and negative-contract tests for the mutable frontend

The exhaustive small-input test executes compiled RAM, compares with an independent
reference, and checks the advertised bound. `fill` exercises the same frontend on a
different algorithm. Negative obligations reject unsafe reads/writes, unpaid work,
false assertions, false decreasing measures, and certificates for a different body.
The universal correctness theorems remain the evidence for all inputs.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Tests
open Authoring Frontend

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 6 do
    for mask in List.range (3 ^ n) do
      let xs := (List.range n).map (fun i => mask / 3 ^ i % 3)
      let r := InsertionSort.run xs
      unless r.value == xs.mergeSort (· ≤ ·) do
        throw <| IO.userError s!"mutable sorting: {xs}"
      unless r.steps ≤ 300 * n * n + 300 * n + 360 do
        throw <| IO.userError s!"mutable budget: {xs}"
  for xs in [List.range 16, (List.range 16).reverse, List.replicate 20 7] do
    let r := InsertionSort.run xs
    unless r.value == xs.mergeSort (· ≤ ·) do
      throw <| IO.userError s!"mutable larger input: {xs}"
    unless r.steps ≤ 960 * xs.length * xs.length do
      throw <| IO.userError s!"mutable larger budget: {xs}"

ram method fill (mut arr : Array Nat) return (u : Unit)
  require True
  ensures arr.size = arrOld.size
  ensures ∀ i, i < arr.size → arr[i]! = 0
  credits 100 * arr.size + 100
  do
    let mut i := 0
    while i < arr.size
      invariant i ≤ arr.size
      invariant arr.size = arrOld.size
      invariant ∀ j, j < i → arr[j]! = 0
      invariant 20 * (arr.size - i) + 20 ≤ remaining
      decreasing arr.size - i
      do
        arr[i] := 0
        i := i + 1
    return

prove_ram fill by
  ram_solve [ArrayFacts.get_set, Array.size_setIfInBounds]

set_option linter.hashCommand false in
/-- info: #[0, 0, 0] -/
#guard_msgs in
#eval (fillVerified.run #[3, 2, 1] (by trivial)).value

/-- Scalar writes cannot be hidden as uncharged Lean computations. -/
example (s : Mutable.State) :
    ¬ (Plan.action (Mutable.assign "x" (.literal 1))).vc (fun _ _ => True) s 0 := by
  simp [Plan.vc, Mutable.assign, Mutable.Value.credits]

/-- Total Lean array indexing does not make out-of-bounds RAM reads safe. -/
example (c : Nat) : ¬ (Plan.action (Mutable.read "x" (.literal 0))).vc
    (fun _ _ => True) (Mutable.initial #[]) c := by
  simp [Plan.vc, Mutable.read, Mutable.Value.eval, Mutable.initial]

/-- Writes beyond the represented allocation are also rejected. -/
example (c : Nat) : ¬ (Plan.action (Mutable.write (.literal 1) (.literal 7))).vc
    (fun _ _ => True) (Mutable.initial #[0]) c := by
  simp [Plan.vc, Mutable.write, Mutable.Value.eval, Mutable.initial]

/-- An assertion is an obligation, never an axiom introduced by the parser. -/
example (s : Mutable.State) (c : Nat) :
    ¬ (Plan.assert (State := Mutable.State) (fun _ => False)).vc (fun _ _ => True) s c := by
  simp [Plan.vc]

/-- A supplied constant variant cannot justify a taken loop iteration. -/
example (c : Nat) :
    ¬ (Plan.loopVariant (Mutable.compare .eq "x" "x") (fun _ _ => True)
      (fun _ => 0) Plan.skip).vc (fun _ _ => True) (Mutable.initial #[]) c := by
  intro h
  have step := h.2 (Mutable.initial #[]) c trivial
  simpa [Plan.vc, Mutable.compare, Mutable.Comparison.eval] using step.2

/-- Proof annotations cannot be substituted for a different program. -/
example : True := by
  fail_if_success
    have wrong : Plan (.action (Mutable.assign "x" (.literal 1))) :=
      (Plan.skip : Plan (.skip : Program Mutable.State))
  trivial

/- A host-language function call is outside the supported RAM expression grammar. -/
set_option linter.hashCommand false in
/-- error: Unsupported RAM expression: Nat.succ 0 -/
#guard_msgs in
ram method rejectHostCall (mut arr : Array Nat) return (u : Unit)
  credits 100
  do
    let x := Nat.succ 0
    return

/- A logical credit counter cannot be read by executable code. -/
set_option linter.hashCommand false in
/-- error: Unknown RAM local 'remaining'; ghost terms cannot occur in executable code -/
#guard_msgs in
ram method rejectGhostRead (mut arr : Array Nat) return (u : Unit)
  credits 100
  do
    let x := remaining
    return

/- Early returns must not be accidentally compiled as skip. -/
set_option linter.hashCommand false in
/-- error: RAM return is supported only at method exit -/
#guard_msgs in
ram method rejectEarlyReturn (mut arr : Array Nat) return (u : Unit)
  credits 100
  do
    if 0 = 0 then
      return
    return

/- Lexical shadowing must not silently change which array an indexing expression uses. -/
set_option linter.hashCommand false in
/-- error: This name belongs to the array interface or proof context; choose a fresh local -/
#guard_msgs in
ram method rejectArrayShadow (mut arr : Array Nat) return (u : Unit)
  credits 100
  do
    let mut arr := 0
    return

/- A caller cannot replace the inferred RAM bound with an arbitrary number. -/
set_option linter.hashCommand false in
/-- error: RAM time is inferred from logical credits; remove the time clause -/
#guard_msgs in
ram method rejectTimeOverride (mut arr : Array Nat) return (u : Unit)
  credits 0
  time 0
  do
    return

end AlgoLib.Experimental.RAM.Prototype.Tests
