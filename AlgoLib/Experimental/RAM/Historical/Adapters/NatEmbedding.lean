/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Historical.NatMachine.Runner
import AlgoLib.Experimental.RAM.Machine.Integer.Runner

/-!
# Migration of natural-number RAM to integer RAM

One fixed translation preserves every terminating execution, including loops.
Natural subtraction expands into signed subtraction followed by max with zero.
The translated program executes at most twice as many instructions. No assumption
on runtime input size is needed; this remains an unbounded unit-cost model.
-/
namespace AlgoLib.Experimental.RAM.Integer.Migration
open Checked (Reg)

/-- Natural values are represented by nonnegative integers at instruction boundaries. -/
def state (s : Checked.State) : Integer.State :=
  ⟨fun r => s.regs r, fun a => s.memory a⟩

def operand : Checked.Operand → Integer.Operand
  | .reg r => .reg r
  | .lit n => .lit n

@[simp] theorem operand_eval (x : Checked.Operand) (s : Checked.State) :
    (operand x).eval (state s) = (x.eval s : Int) := by cases x <;> rfl

@[simp] theorem state_set (s : Checked.State) (r : Reg) (n : Nat) :
    state (s.set r n) = (state s).set r n := by
  apply congrArg₂ Integer.State.mk
  · funext q; simp only [state, Checked.State.set, Function.update_apply]; split_ifs <;> rfl
  · rfl

/-- Saturating subtraction is an explicit two-instruction implementation. -/
def instruction : Checked.Instr → List Integer.Instr
  | .mov r x => [.mov r (operand x)]
  | .load r a => [.load r (operand a)]
  | .store a x => [.store (operand a) (operand x)]
  | .bin .add r x y => [.bin .add r (operand x) (operand y)]
  | .bin .mul r x y => [.bin .mul r (operand x) (operand y)]
  | .bin .sub r x y => [.bin .sub r (operand x) (operand y),
      .bin .max r (.reg r) (.lit 0)]

@[simp] theorem address_nat (n : Nat) : Integer.address n = some n := by
  simp [Integer.address]

private theorem nat_sub (a b : Nat) : ((a - b : Nat) : Int) = max ((a : Int) - b) 0 := by
  omega

theorem instruction_correct (i : Checked.Instr) (s : Checked.State) :
    Integer.blockEval (instruction i) (state s) = some (state (i.eval s)) := by
  cases i with
  | mov r x => simp [instruction, Integer.blockEval, Integer.Instr.eval, Checked.Instr.eval]
  | load r a =>
    simp only [instruction, Integer.blockEval, Integer.Instr.eval, operand_eval, address_nat,
      Option.map_some, Option.bind_some, Checked.Instr.eval, state_set]
    rfl
  | store a x =>
    simp only [instruction, Integer.blockEval, Integer.Instr.eval, operand_eval, address_nat,
      Option.map_some, Option.bind_some]
    congr 1
    apply congrArg₂ Integer.State.mk
    · rfl
    · funext p; simp only [state, Checked.Instr.eval, Function.update_apply]; split_ifs <;> rfl
  | bin op r x y =>
    cases op <;>
      simp only [instruction, Integer.blockEval, Integer.Instr.eval, operand_eval,
        Option.bind_some, Checked.Instr.eval, Checked.BinOp.eval, state_set,
        Integer.BinOp.eval, Int.natCast_add, Int.natCast_mul, nat_sub]
    simp [Integer.Operand.eval, Integer.State.set, Function.update_idem]

def block (is : List Checked.Instr) : List Integer.Instr := is.flatMap instruction

theorem block_append (a b : List Integer.Instr) (s : Integer.State) :
    Integer.blockEval (a ++ b) s = (Integer.blockEval a s).bind (Integer.blockEval b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, Integer.blockEval]
    cases i.eval s <;> simp_all

theorem block_correct (is : List Checked.Instr) (s : Checked.State) :
    Integer.blockEval (block is) (state s) = some (state (Checked.blockEval is s)) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simpa [block, List.flatMap_cons, block_append, instruction_correct, Checked.blockEval]
      using ih (i.eval s)

theorem block_cost (is : List Checked.Instr) : (block is).length ≤ 2 * is.length := by
  induction is with
  | nil => simp [block]
  | cons i is ih =>
    have hi : (instruction i).length ≤ 2 := by
      cases i with
      | bin op _ _ _ => cases op <;> simp [instruction]
      | _ => simp [instruction]
    simp only [block, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

def test : Checked.Test → Integer.Test
  | .lt x y => .lt (operand x) (operand y)
  | .le x y => .le (operand x) (operand y)
  | .eq x y => .eq (operand x) (operand y)

@[simp] theorem test_eval (q : Checked.Test) (s : Checked.State) :
    (test q).eval (state s) = q.eval s := by
  cases q <;> simp [test, Integer.Test.eval, Checked.Test.eval, Int.natCast_inj]

/-- Translation depends on code only, never on the input or its execution proof. -/
def code : Checked.Code → Integer.Code
  | .block is => .block (block is)
  | .seq a b => .seq (code a) (code b)
  | .ite q a b => .ite (test q) (code a) (code b)
  | .while q b => .while (test q) (code b)

/-- Generic semantic and cost preservation for every terminating natural RAM program. -/
theorem preserves {c : Checked.Code} {s t : Checked.State} {k : Nat}
    (h : Checked.Exec c s k t) :
    ∃ j, Integer.Exec (code c) (state s) j (state t) ∧ j ≤ 2 * k := by
  induction h with
  | block is s => exact ⟨_, .block (block_correct is s), block_cost is⟩
  | seq ha hb iha ihb =>
    obtain ⟨i, hi, hci⟩ := iha
    obtain ⟨j, hj, hcj⟩ := ihb
    exact ⟨_, .seq hi hj, by omega⟩
  | ifTrue hq ha ih =>
    obtain ⟨i, hi, hc⟩ := ih
    exact ⟨_, .ifTrue (by simpa using hq) hi, by omega⟩
  | ifFalse hq ha ih =>
    obtain ⟨i, hi, hc⟩ := ih
    exact ⟨_, .ifFalse (by simpa using hq) hi, by omega⟩
  | whileFalse hq => exact ⟨1, .whileFalse (by simpa using hq), by omega⟩
  | whileTrue hq ha hb iha ihb =>
    obtain ⟨i, hi, hci⟩ := iha
    obtain ⟨j, hj, hcj⟩ := ihb
    exact ⟨_, .whileTrue (by simpa using hq) hi hj, by omega⟩

/-- Existing termination proofs suffice to run migrated code without fuel. -/
theorem terminates {c : Checked.Code} {s : Checked.State}
    (h : ∃ k t, Checked.Exec c s k t) : Integer.Terminates (code c) (state s) := by
  obtain ⟨k, t, hx⟩ := h
  obtain ⟨j, hj, _⟩ := preserves hx
  exact ⟨j, state t, hj⟩

/-- Execute translated instructions on integer registers using the existing termination proof. -/
def run (c : Checked.Code) (s : Checked.State) (h : Checked.Terminates c s) :
    Nat × Integer.State := Integer.run (code c) (state s) (terminates h)

/-- The migration runner agrees with the old result and derives its own instruction count. -/
theorem run_correct (c : Checked.Code) (s : Checked.State) (h : Checked.Terminates c s) :
    (run c s h).2 = state (Checked.run c s h).2 ∧
      (run c s h).1 ≤ 2 * (Checked.run c s h).1 := by
  obtain ⟨j, hj, hc⟩ := preserves (Checked.run_correct c s h)
  unfold run
  rw [Integer.run_eq hj]
  exact ⟨rfl, hc⟩

end AlgoLib.Experimental.RAM.Integer.Migration
