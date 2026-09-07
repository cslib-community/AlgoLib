/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Machine.Registers
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Int.Basic

/-!
# Integer-valued RAM

Registers and heap cells store unbounded signed integers. Addresses and operation
counts remain natural numbers. Loads/stores reject negative addresses. Arithmetic,
including max, costs one instruction; this is not a bit-complexity model.

This independent target is the first migration layer. Existing Nat frontend
semantics will be preserved by a checked translation, not by changing subtraction.
-/
namespace AlgoLib.Experimental.RAM.Integer
open Checked (Reg)

/-- There is no time field in the machine state. -/
structure State where
  regs : Reg → Int
  memory : Nat → Int

/-- Atomic operands prohibit hiding computation inside expression evaluation. -/
inductive Operand where
  | reg (r : Reg)
  | lit (n : Int)
  deriving DecidableEq, Repr

def Operand.eval (s : State) : Operand → Int
  | .reg r => s.regs r
  | .lit n => n

inductive BinOp where
  | add | sub | mul | max
  deriving DecidableEq, Repr

def BinOp.eval : BinOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .max => Max.max

/-- Each instruction has a constant number of atomic operands. -/
inductive Instr where
  | mov (dst : Reg) (src : Operand)
  | load (dst : Reg) (addr : Operand)
  | store (addr value : Operand)
  | bin (op : BinOp) (dst : Reg) (x y : Operand)
  deriving DecidableEq, Repr

def State.set (s : State) (r : Reg) (v : Int) : State :=
  { s with regs := Function.update s.regs r v }

/-- Negative addresses are invalid, rather than truncated to address zero. -/
def address (i : Int) : Option Nat := if 0 ≤ i then some i.toNat else none

/-- One instruction either executes or rejects an invalid address. -/
def Instr.eval (i : Instr) (s : State) : Option State :=
  match i with
  | .mov r x => some (s.set r (x.eval s))
  | .load r a => (address (a.eval s)).map fun p => s.set r (s.memory p)
  | .store a x => (address (a.eval s)).map fun p =>
      { s with memory := Function.update s.memory p (x.eval s) }
  | .bin op r x y => some (s.set r (op.eval (x.eval s) (y.eval s)))

/-- Failure propagates; successful blocks charge their instruction count. -/
def blockEval : List Instr → State → Option State
  | [], s => some s
  | i :: is, s => (i.eval s).bind (blockEval is)

inductive Test where
  | lt (x y : Operand)
  | le (x y : Operand)
  | eq (x y : Operand)
  deriving DecidableEq, Repr

def Test.eval (s : State) : Test → Bool
  | .lt x y => decide (x.eval s < y.eval s)
  | .le x y => decide (x.eval s ≤ y.eval s)
  | .eq x y => decide (x.eval s = y.eval s)

/-- Finite structured code, including potentially nonterminating loops. -/
inductive Code where
  | block (is : List Instr)
  | seq (first second : Code)
  | ite (test : Test) (yes no : Code)
  | while (test : Test) (body : Code)
  deriving DecidableEq, Repr

/-- Terminating execution in exactly the indicated number of machine operations.
There is no rule allowing arbitrary computation or an arbitrary time charge. -/
inductive Exec : Code → State → Nat → State → Prop where
  | block {is : List Instr} {s t : State} :
      blockEval is s = some t → Exec (.block is) s is.length t
  | seq {a b : Code} {s u t : State} {i j : Nat} :
      Exec a s i u → Exec b u j t → Exec (.seq a b) s (i + j) t
  | ifTrue {q : Test} {a b : Code} {s t : State} {i : Nat} :
      q.eval s = true → Exec a s i t → Exec (.ite q a b) s (1 + i) t
  | ifFalse {q : Test} {a b : Code} {s t : State} {i : Nat} :
      q.eval s = false → Exec b s i t → Exec (.ite q a b) s (1 + i) t
  | whileFalse {q : Test} {b : Code} {s : State} :
      q.eval s = false → Exec (.while q b) s 1 s
  | whileTrue {q : Test} {b : Code} {s u t : State} {i j : Nat} :
      q.eval s = true → Exec b s i u → Exec (.while q b) u j t →
      Exec (.while q b) s (1 + i + j) t

/-- A proved execution fixes both the result and the cost. -/
theorem Exec.deterministic {c : Code} {s t : State} {i : Nat} (h : Exec c s i t) :
    ∀ {j u}, Exec c s j u → i = j ∧ t = u := by
  induction h with
  | block hs =>
    intro j u h
    cases h with
    | block ht => exact ⟨rfl, Option.some.inj (hs.symm.trans ht)⟩
  | seq ha hb iha ihb =>
    intro j u h
    cases h with
    | seq ha' hb' =>
      obtain ⟨rfl, rfl⟩ := iha ha'
      obtain ⟨rfl, rfl⟩ := ihb hb'
      exact ⟨rfl, rfl⟩
  | ifTrue hq ha ih =>
    intro j u h
    cases h with
    | ifTrue _ ha' => obtain ⟨rfl, rfl⟩ := ih ha'; exact ⟨rfl, rfl⟩
    | ifFalse hq' _ => simp_all
  | ifFalse hq ha ih =>
    intro j u h
    cases h with
    | ifTrue hq' _ => simp_all
    | ifFalse _ ha' => obtain ⟨rfl, rfl⟩ := ih ha'; exact ⟨rfl, rfl⟩
  | whileFalse hq =>
    intro j u h
    cases h with
    | whileFalse _ => exact ⟨rfl, rfl⟩
    | whileTrue hq' _ _ => simp_all
  | whileTrue hq ha hb iha ihb =>
    intro j u h
    cases h with
    | whileFalse hq' => simp_all
    | whileTrue _ ha' hb' =>
      obtain ⟨rfl, rfl⟩ := iha ha'
      obtain ⟨rfl, rfl⟩ := ihb hb'
      exact ⟨rfl, rfl⟩

/-- No zero-step execution can change even one register or memory cell. -/
theorem Exec.zero {c : Code} {s t : State} (h : Exec c s 0 t) : t = s := by
  generalize hz : 0 = n at h
  induction h with
  | @block is s t hs =>
    have : is = [] := List.length_eq_zero_iff.mp hz.symm
    subst is
    simpa [blockEval] using hs.symm
  | seq ha hb iha ihb =>
    have hi : _ = 0 := Nat.eq_zero_of_add_eq_zero_left hz.symm
    have hj : _ = 0 := Nat.eq_zero_of_add_eq_zero_right hz.symm
    exact (ihb hi.symm).trans (iha hj.symm)
  | ifTrue | ifFalse | whileFalse | whileTrue => omega

end AlgoLib.Experimental.RAM.Integer
