/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Runner

/-!
# Typed RAM input and output interfaces

A procedure has a typed input encoder, one fixed code body, and a restricted
output descriptor. Outputs can read registers or expose a bitmap view; there
is no arbitrary Lean result transformer that could hide an algorithm in decoding.
Encoding supplies the initial input representation, outside the body cost.
-/
namespace AlgoLib.Experimental.RAM.Checked

/-- A returned bitmap view, without copying or enumerating its cells. -/
structure Bitmap where
  length : Nat
  memory : Nat → Nat
  stride : Nat
  offset : Nat

def Bitmap.contains (b : Bitmap) (v : Nat) : Bool :=
  decide (v < b.length) && (b.memory (b.stride * v + b.offset) == 1)

/-- Host-side display/serialization, separate from the procedure's RAM count. -/
def Bitmap.toList (b : Bitmap) : List Nat := (List.range b.length).filter b.contains

/-- Restricted, static output descriptors. No arbitrary result computation. -/
inductive Output : Type → Type 1 where
  | word (r : Reg) : Output Nat
  | bitmap (length : Reg) (stride offset : Nat) : Output Bitmap
  | pair {α β} (left : Output α) (right : Output β) : Output (α × β)

def Output.read {α : Type} : Output α → State → α
  | .word r, s => s.regs r
  | .bitmap r stride offset, s => ⟨s.regs r, s.memory, stride, offset⟩
  | .pair a b, s => (a.read s, b.read s)

structure Execution (α : Type) where
  output : α
  steps : Nat

/-- Input and output types are part of the program's public signature. -/
structure Procedure (Input : Type*) (OutputType : Type) where
  encode : Input → State
  body : Code
  output : Output OutputType
  terminates : ∀ input, Terminates body (encode input)

def Procedure.run {I : Type*} {O : Type} (p : Procedure I O) (input : I) : Execution O :=
  let result := Checked.run p.body (p.encode input) (p.terminates input)
  ⟨p.output.read result.2, result.1⟩

theorem Procedure.correct {I : Type*} {O : Type} (p : Procedure I O) (input : I) :
    ∃ final, Exec p.body (p.encode input) (p.run input).steps final ∧
      (p.run input).output = p.output.read final :=
  ⟨_, Checked.run_correct _ _ _, rfl⟩

/-- Syntactic register footprint, useful for proving output lengths and frames. -/
def Instr.writes (r : Reg) : Instr → Bool
  | .mov dst _ | .load dst _ | .bin _ dst _ _ => dst == r
  | .store _ _ => false

def Code.writes (r : Reg) : Code → Bool
  | .block is => is.any (Instr.writes r)
  | .seq a b | .ite _ a b => a.writes r || b.writes r
  | .while _ b => b.writes r

private theorem block_frame (r : Reg) (is : List Instr) (s : State)
    (h : is.any (Instr.writes r) = false) : (blockEval is s).regs r = s.regs r := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    have hi : i.writes r = false := by simpa using (Bool.or_eq_false_iff.mp h).1
    have ht : is.any (Instr.writes r) = false := (Bool.or_eq_false_iff.mp h).2
    have he : (i.eval s).regs r = s.regs r := by
      cases i with
      | store => rfl
      | mov dst x =>
        have hn : dst ≠ r := by simpa [Instr.writes] using hi
        exact Function.update_of_ne hn.symm _ _
      | load dst x =>
        have hn : dst ≠ r := by simpa [Instr.writes] using hi
        exact Function.update_of_ne hn.symm _ _
      | bin op dst x y =>
        have hn : dst ≠ r := by simpa [Instr.writes] using hi
        exact Function.update_of_ne hn.symm _ _
    exact (ih (i.eval s) ht).trans he

theorem Exec.frame_register {c : Code} {s t : State} {k : Nat} (hx : Exec c s k t)
    (r : Reg) (h : c.writes r = false) : t.regs r = s.regs r := by
  induction hx with
  | block is s => exact block_frame r is s h
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ (Bool.or_eq_false_iff.mp h).2).trans (ih₁ (Bool.or_eq_false_iff.mp h).1)
  | ifTrue _ _ ih => exact ih (Bool.or_eq_false_iff.mp h).1
  | ifFalse _ _ ih => exact ih (Bool.or_eq_false_iff.mp h).2
  | whileFalse => rfl
  | whileTrue _ _ _ ih₁ ih₂ => exact (ih₂ h).trans (ih₁ h)

end AlgoLib.Experimental.RAM.Checked
