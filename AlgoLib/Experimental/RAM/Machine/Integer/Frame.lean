/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Machine.Integer.Machine

/-!
# Integer RAM register framing

Successful execution preserves every register outside the syntactic write set.
The statement accounts for checked memory addresses: faulting instructions do not
supply an execution certificate. This supports private procedure temporaries and
saved local variables in the native compiler.
-/
namespace AlgoLib.Experimental.RAM.Integer
open Checked (Reg)

def Instr.writes (r : Reg) : Instr → Bool
  | .mov dst _ | .load dst _ | .bin _ dst _ _ => dst == r
  | .store _ _ => false

def Code.writes (r : Reg) : Code → Bool
  | .block is => is.any (Instr.writes r)
  | .seq a b | .ite _ a b => a.writes r || b.writes r
  | .while _ b => b.writes r

theorem Instr.frame_register (i : Instr) (s t : State) (r : Reg)
    (hw : i.writes r = false) (he : i.eval s = some t) : t.regs r = s.regs r := by
  cases i with
  | mov dst x | bin op dst x y =>
    simp only [Instr.eval, Option.some.injEq] at he
    subst t
    have hn : dst ≠ r := by simpa [Instr.writes] using hw
    exact Function.update_of_ne hn.symm _ _
  | load dst a =>
    have hn : dst ≠ r := by simpa [Instr.writes] using hw
    cases ha : address (a.eval s) with
    | none => simp [Instr.eval, ha] at he
    | some p =>
      simp only [Instr.eval, ha, Option.map_some, Option.some.injEq] at he
      subst t
      exact Function.update_of_ne hn.symm _ _
  | store a x =>
    cases ha : address (a.eval s) with
    | none => simp [Instr.eval, ha] at he
    | some p =>
      simp only [Instr.eval, ha, Option.map_some, Option.some.injEq] at he
      subst t
      rfl

private theorem block_frame (r : Reg) (is : List Instr) (s t : State)
    (hw : is.any (Instr.writes r) = false) (he : blockEval is s = some t) :
    t.regs r = s.regs r := by
  induction is generalizing s with
  | nil => simpa [blockEval] using congrArg (fun x => x.map (fun z => z.regs r)) he.symm
  | cons i is ih =>
    have hi : i.writes r = false := (Bool.or_eq_false_iff.mp hw).1
    have ht : is.any (Instr.writes r) = false := (Bool.or_eq_false_iff.mp hw).2
    cases hx : i.eval s with
    | none => simp [blockEval, hx] at he
    | some u =>
      have hu : blockEval is u = some t := by simpa [blockEval, hx] using he
      exact (ih u ht hu).trans (i.frame_register s u r hi hx)

theorem Exec.frame_register {c : Code} {s t : State} {k : Nat} (hx : Exec c s k t)
    (r : Reg) (h : c.writes r = false) : t.regs r = s.regs r := by
  induction hx with
  | block he => exact block_frame r _ _ _ h he
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ (Bool.or_eq_false_iff.mp h).2).trans (ih₁ (Bool.or_eq_false_iff.mp h).1)
  | ifTrue _ _ ih => exact ih (Bool.or_eq_false_iff.mp h).1
  | ifFalse _ _ ih => exact ih (Bool.or_eq_false_iff.mp h).2
  | whileFalse => rfl
  | whileTrue _ _ _ ih₁ ih₂ => exact (ih₂ h).trans (ih₁ h)

end AlgoLib.Experimental.RAM.Integer
