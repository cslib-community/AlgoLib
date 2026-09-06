/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.VelvetWP
import AlgoLib.Experimental.RAM.Prototype.NondeterministicRunner
import AlgoLib.Experimental.RAM.Authoring.Interface

/-!
# A recursive ordinary Velvet procedure and its recursive RAM translation

This example exercises genuine target calls, not depth-bounded unrolling or a host
recursion oracle. Each activation tests the argument, decrements it, recursively
calls the same fixed procedure, and increments the returned value. The callee
clobbers the argument register; no caller-local data is live across the call.

The exact bound includes each call, return, branch, and arithmetic instruction.
This is a reconstructed per-method translation certificate. A general compiler
must additionally allocate and save caller-local data; that ABI is not supplied
by this example, and `ram method` does not yet accept recursive calls.
-/
namespace AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation
open Checked VelvetSemantics Nondeterministic

method countBack (n : Nat) return (result : Nat)
  do
    match n with
    | 0 => return 0
    | k + 1 =>
      let r ← countBack k
      return r + 1

/-- The ordinary source procedure is a terminating recursive computation. -/
theorem countBack_pure (n : Nat) : countBack n = .pure n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countBack, ih, bind, NonDetT.bind, pure]

def argument : Reg := .user 0 "argument"
def result : Reg := .user 0 "result"

def body : Nondeterministic.Code :=
  .branch (.eq (.reg argument) (.lit 0))
    (.deterministic (.block [.mov result (.lit 0)]))
    (.seq (.deterministic (.block [.bin .sub argument (.reg argument) (.lit 1)]))
      (.seq (.call 0)
        (.deterministic (.block [.bin .add result (.reg result) (.lit 1)]))))

def procedures : List Nondeterministic.Code := [body]

def initial (n : Nat) : Checked.State :=
  ⟨fun r => if r = argument then n else 0, fun _ => 0⟩

private theorem execution (n : Nat) (s : Checked.State) (input : s.regs argument = n) :
    ∃ t, ExecIn procedures (.call 0) s (5 * n + 4) t ∧ t.regs result = n := by
  induction n generalizing s with
  | zero =>
    refine ⟨_, .call (body := body) rfl
      (.ifTrue ?_ (.deterministic (.block [.mov result (.lit 0)] s))), ?_⟩
    · simp [Test.eval, Operand.eval, input]
    · simp [blockEval, Instr.eval, Operand.eval, State.set]
  | succ n ih =>
    let middle := blockEval [.bin .sub argument (.reg argument) (.lit 1)] s
    have value : middle.regs argument = n := by
      simp [middle, blockEval, Instr.eval, BinOp.eval, Operand.eval, State.set, input]
    obtain ⟨t, run, output⟩ := ih middle value
    have whole := ExecIn.call (procedures := procedures) (index := 0) rfl
      (ExecIn.ifFalse (a := .deterministic (.block [.mov result (.lit 0)]))
        (by simp [Test.eval, Operand.eval, input])
        (.seq (.deterministic (.block _ s))
          (.seq run (.deterministic (.block [.bin .add result (.reg result) (.lit 1)] t)))))
    refine ⟨blockEval [.bin .add result (.reg result) (.lit 1)] t, ?_, ?_⟩
    · convert whole using 1
      simp only [List.length_cons, List.length_nil]
      omega
    · simp [blockEval, Instr.eval, BinOp.eval, Operand.eval, State.set, output]

/-- Both the result and exact cost hold for every execution of the recursive code. -/
private theorem outcome (n : Nat) (s : Checked.State) (input : s.regs argument = n)
    {k : Nat} {t : Checked.State} (run : ExecIn procedures (.call 0) s k t) :
    k = 5 * n + 4 ∧ t.regs result = n := by
  induction n generalizing s t k with
  | zero =>
    cases run with
    | call lookup run =>
      simp only [procedures, List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst_vars
      cases run with
      | ifTrue guard run =>
        cases run with
        | deterministic run =>
          cases run
          simp [blockEval, Instr.eval, Operand.eval, State.set]
      | ifFalse guard run => simp [Test.eval, Operand.eval, input] at guard
  | succ n ih =>
    cases run with
    | call lookup run =>
      simp only [procedures, List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst_vars
      cases run with
      | ifTrue guard run => simp [Test.eval, Operand.eval, input] at guard
      | ifFalse guard run =>
        cases run with
        | seq subtract rest =>
          cases subtract with
          | deterministic subtract =>
            cases subtract
            cases rest with
            | seq recursive increment =>
              have nextInput : (blockEval
                  [.bin .sub argument (.reg argument) (.lit 1)] s).regs argument = n := by
                simp [blockEval, Instr.eval, BinOp.eval, Operand.eval, State.set, input]
              have h := ih _ nextInput recursive
              cases increment with
              | deterministic increment =>
                cases increment
                constructor
                · simp only [List.length_cons, List.length_nil] at *
                  omega
                · simp [blockEval, Instr.eval, BinOp.eval, Operand.eval, State.set, h.2]

/-- One finite recursive program preserves and reflects every ordinary source outcome. -/
def translation : Translation countBack where
  code := .call 0
  procedures := procedures
  encode := initial
  decode s := s.regs result
  valid _ := True
  equivalent n _ output := by
    rw [countBack_pure, returns_pure]
    have input : (initial n).regs argument = n := by simp [initial]
    constructor
    · intro same
      subst output
      obtain ⟨t, run, value⟩ := execution n (initial n) input
      exact ⟨_, t, run, value⟩
    · rintro ⟨k, t, run, value⟩
      exact value.symm.trans (outcome n (initial n) input run).2

/-- Recursive calls and returns are paid for, including at the base case. -/
theorem budget : translation.Within (fun n => 5 * n + 4) := by
  intro n _ k t run
  exact (outcome n (initial n) (by simp [initial]) run).1.le

private theorem noChoice : ∀ code ∈ procedures, code.ChoiceFree := by
  simp [procedures, body, Code.ChoiceFree]

private theorem terminates (n : Nat) :
    Nondeterministic.Terminates procedures (fun _ => 0) (.call 0) (initial n) := by
  obtain ⟨t, execution, _⟩ := execution n (initial n) (by simp [initial])
  exact ⟨_, t, execution.trace noChoice trivial (.done t 0)⟩

/-- Execute the recursive RAM procedure; callers supply only the natural-number input. -/
def run (n : Nat) : Authoring.Result Nat :=
  let execution := Nondeterministic.run procedures (fun _ => 0) (.call 0) (initial n)
    (terminates n)
  ⟨execution.2.regs result, execution.1⟩

/-- The executable result and step count agree with the ordinary Velvet method. -/
theorem run_correct (n : Nat) : (run n).value = n ∧ (run n).steps = 5 * n + 4 := by
  obtain ⟨t, execution, value⟩ := execution n (initial n) (by simp [initial])
  have trace := execution.trace (schedule := fun _ => 0) noChoice trivial (.done t 0)
  have eq := Nondeterministic.run_eq trace (terminates n)
  simpa [run, eq] using And.intro value (Eq.refl (5 * n + 4))

set_option linter.hashCommand false in
/-- info: (10, 54) -/
#guard_msgs in
#eval let r := run 10; (r.value, r.steps)

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 100 do
    let r := run n
    unless r.value == n && r.steps == 5 * n + 4 do
      throw <| IO.userError s!"recursive RAM execution at {n}"

end AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation
