/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Historical.NatMachine.Runner
import AlgoLib.Experimental.RAM.Machine.Output

/-!
# Shared output views and historical register framing

`Bitmap` and `Execution` are mathematical output containers used by the native
method interfaces. Turning a bitmap into a list is a host-side observation,
separate from the charged algorithm execution.

The remaining register-frame lemmas support historical instruction certificates.
The obsolete Nat-machine `Output`/`Procedure` executable wrappers are removed;
use the native typed method input/output interface or `Integer.TotalProgram`.
-/
namespace AlgoLib.Experimental.RAM.Checked

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
