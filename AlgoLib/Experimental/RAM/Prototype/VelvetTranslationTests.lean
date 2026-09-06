/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.ExecutableTranslation

/-!
# Translation of an ordinary Velvet choice and an ordinary procedure call

These declarations use the unmodified upstream `method` frontend. The equivalence
certificates quantify over all natural-number outcomes, not the single outcome
selected by executable extraction. The RAM budget is established for every
execution. The examples are small semantic regressions, not a full compiler.
-/
namespace AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests
open Checked VelvetSemantics Nondeterministic

method chooseWord return (result : Nat)
  do
    let value ← pick Nat
    return value

method relay return (result : Nat)
  do
    let value ← chooseWord
    return value

/-- Every natural number is a possible result of the ordinary Velvet method. -/
theorem chooseWord_returns (n : Nat) : Returns chooseWord n := by
  unfold chooseWord
  exact .pick (x := n) trivial (.pure n)

/-- The same outcome is propagated through an ordinary Velvet procedure call. -/
theorem relay_returns (n : Nat) : Returns relay n := by
  unfold relay chooseWord
  exact .pick (x := n) trivial (.pure n)

def resultRegister : Reg := .user 0 "result"
def inputState : Checked.State := ⟨fun _ => 0, fun _ => 0⟩

/-- An actual source/target equivalence, with preservation and reflection. -/
def chooseWordTranslation : Translation (fun (_ : Unit) => chooseWord) where
  code := .choose resultRegister
  encode _ := inputState
  decode s := s.regs resultRegister
  valid _ := True
  equivalent _ _ n := by
    constructor
    · intro _
      exact ⟨1, _, .choose _ _ n, by simp [Checked.State.set]⟩
    · intro _; exact chooseWord_returns n

/-- The ordinary call is preserved as a charged target call through a finite table. -/
def relayTranslation : Translation (fun (_ : Unit) => relay) where
  code := .call 0
  procedures := [.choose resultRegister]
  encode _ := inputState
  decode s := s.regs resultRegister
  valid _ := True
  equivalent _ _ n := by
    constructor
    · intro _
      exact ⟨3, _, .call rfl (.choose _ _ n), by simp [Checked.State.set]⟩
    · intro _; exact relay_returns n

/-- A universal cost bound, not a bound on one favorable nondeterministic run. -/
theorem chooseWord_budget : chooseWordTranslation.Within (fun _ => 1) := by
  intro _ _ k final run
  change Nondeterministic.Exec (.choose resultRegister) inputState k final at run
  cases run
  exact Nat.le_refl _

/-- Deterministic RAM cannot preserve all the outcomes of this ordinary Velvet method. -/
theorem choice_needs_nondeterministic_RAM (code : Checked.Code) (input : Checked.State)
    (decode : Checked.State → Nat) :
    ¬ (∀ n, Returns chooseWord n ↔ ∃ k t, Checked.Exec code input k t ∧ decode t = n) :=
  deterministic_target_impossible chooseWord 0 1 (chooseWord_returns 0) (chooseWord_returns 1)
    (by decide) code input decode

/-- Every schedule gives a terminating one-instruction choice execution. -/
def chooseWordExecutable : ExecutableTranslation (fun (_ : Unit) => chooseWord) where
  toTranslation := chooseWordTranslation
  terminates _ _ schedule :=
    ⟨1, _, .next rfl (.done (inputState.set resultRegister (schedule 0)) 1)⟩

set_option linter.hashCommand false in
/-- info: (42, 1) -/
#guard_msgs in
#eval let r := chooseWordExecutable.run () trivial (fun _ => 42); (r.value, r.steps)

/-- The external schedule can select any outcome, including values not selected by extraction. -/
theorem every_word_executable (n : Nat) :
    (chooseWordExecutable.run () trivial (fun _ => n)).value = n := by
  have trace : Trace [] (fun _ => n) ⟨[.code (.choose resultRegister)], inputState, 0⟩
      1 (inputState.set resultRegister n) := .next rfl (.done _ 1)
  have eq := Nondeterministic.run_eq trace
    (chooseWordExecutable.terminates () trivial (fun _ => n))
  change (Nondeterministic.run [] (fun _ => n) (.choose resultRegister) inputState _).2.regs
    resultRegister = n
  rw [eq]
  simp [State.set]

end AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests
