/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Machine.Integer.NatEmbedding

/-!
# Signed execution and natural-number migration regressions

Execute signed arithmetic without fuel; reject negative addresses; check saturating
subtraction for every register-alias pattern and small natural inputs. The migration
proof is generic over all code, including loops, rather than these test instances.
-/
namespace AlgoLib.Experimental.RAM.Tests.IntegerRAM
open Checked (Reg)
open Integer

def empty : State := ⟨fun _ => 0, fun _ => 0⟩

/-- Signed subtraction and negative heap contents are ordinary machine operations. -/
def signed : Code := .block [
  .bin .sub .key (.lit 3) (.lit 5),
  .store (.lit 0) (.reg .key),
  .load .temp (.lit 0)]

theorem signed_exec : Exec signed empty 3 (empty.set .key (-2) |>.set .temp (-2) |>
    fun s => { s with memory := Function.update s.memory 0 (-2) }) := by
  apply Exec.block
  rfl

def signedRun := Integer.run signed empty ⟨_, _, signed_exec⟩

theorem signed_correct : signedRun.2.regs .temp = -2 ∧ signedRun.1 = 3 := by
  rw [signedRun, Integer.run_eq signed_exec]
  exact ⟨rfl, rfl⟩

/-- Invalid signed addresses cannot alias zero. -/
example : (Instr.store (.lit (-1)) (.lit 42)).eval empty = none := by decide
example : (Instr.load .key (.lit (-1))).eval empty = none := by decide

/-- The faulting instruction cannot have a successful execution derivation. -/
example : ¬ ∃ k t, Exec (.block [.load .key (.lit (-1))]) empty k t := by
  rintro ⟨k, t, h⟩
  cases h with
  | block h => simp [blockEval, Instr.eval, address, Operand.eval] at h

private def subtraction (dst : Reg) : Checked.Code :=
  .block [.bin .sub dst (.reg .key) (.reg .temp)]

private def initial (a b : Nat) : Checked.State :=
  ⟨fun r => if r = .key then a else if r = .temp then b else 0, fun _ => 0⟩

private def countdown : Checked.Code :=
  .while (.lt (.lit 0) (.reg .key))
    (.block [.bin .sub .key (.reg .key) (.lit 1)])

private theorem countdown_terminates : Checked.Terminates countdown (initial 3 0) := by
  exact ⟨7, _, .whileTrue rfl (.block _ _)
    (.whileTrue rfl (.block _ _) (.whileTrue rfl (.block _ _) (.whileFalse rfl)))⟩

set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  unless signedRun.2.regs .temp == -2 && signedRun.1 == 3 do
    throw <| IO.userError "signed execution"
  let loopResult := Migration.run countdown (initial 3 0) countdown_terminates
  unless loopResult.2.regs .key == 0 && loopResult.1 == 10 do
    throw <| IO.userError "loop migration cost"
  for a in List.range 9 do
    for b in List.range 9 do
      for dst in [Reg.key, Reg.temp, Reg.next] do
        let c := subtraction dst
        let s := initial a b
        let h : Checked.Terminates c s := ⟨_, _, .block _ _⟩
        let result := Migration.run c s h
        unless result.2.regs dst == (a - b : Nat) && result.1 == 2 do
          throw <| IO.userError s!"Nat subtraction migration: {a}, {b}"

end AlgoLib.Experimental.RAM.Tests.IntegerRAM

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Integer.Migration.preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Integer.Migration.preserves

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Integer.Migration.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Integer.Migration.run_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Integer.run_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Integer.run_correct
