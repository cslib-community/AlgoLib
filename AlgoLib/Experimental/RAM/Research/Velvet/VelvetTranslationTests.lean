/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Research.Velvet.ExecutableTranslation

/-!
# Translation of an ordinary Velvet choice and an ordinary procedure call

These declarations use the unmodified upstream `method` frontend. The equivalence
certificates quantify over all natural-number outcomes, not the single outcome
selected by executable extraction. The RAM budget is established for every
execution. The examples are small semantic regressions, not a full compiler.
-/
namespace AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests
open Integer
open Checked (Reg)
open VelvetSemantics Nondeterministic

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
def inputState : Integer.State := ⟨fun _ => 0, fun _ => 0⟩

/-- An actual source/target equivalence, with preservation and reflection. -/
def chooseWordTranslation : Translation (fun (_ : Unit) => chooseWord) where
  code := .choose resultRegister
  encode _ := inputState
  decode s := (s.regs resultRegister).toNat
  valid _ := True
  equivalent _ _ n := by
    constructor
    · intro _
      exact ⟨1, _, .choose _ _ n, by simp [Integer.State.set]⟩
    · intro _; exact chooseWord_returns n

/-- The ordinary call is preserved as a charged target call through a finite table. -/
def relayTranslation : Translation (fun (_ : Unit) => relay) where
  code := .call 0
  procedures := [.choose resultRegister]
  encode _ := inputState
  decode s := (s.regs resultRegister).toNat
  valid _ := True
  equivalent _ _ n := by
    constructor
    · intro _
      exact ⟨3, _, .call rfl (.choose _ _ n), by simp [Integer.State.set]⟩
    · intro _; exact relay_returns n

/-- A universal cost bound, not a bound on one favorable nondeterministic run. -/
theorem chooseWord_budget : chooseWordTranslation.Within (fun _ => 1) := by
  intro _ _ k final run
  change Nondeterministic.Exec (.choose resultRegister) inputState k final at run
  cases run
  exact Nat.le_refl _

/-- Deterministic RAM cannot preserve all the outcomes of this ordinary Velvet method. -/
theorem choice_needs_nondeterministic_RAM (code : Integer.Code) (input : Integer.State)
    (decode : Integer.State → Nat) :
    ¬ (∀ n, Returns chooseWord n ↔ ∃ k t, Integer.Exec code input k t ∧ decode t = n) :=
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
  change ((Nondeterministic.run [] (fun _ => n) (.choose resultRegister) inputState _).2.regs
    resultRegister).toNat = n
  rw [eq]
  simp [State.set]

/-- An invalid signed address cannot become a successful interpreter trace. -/
example : ¬ Terminates [] (fun _ => 0)
    (.deterministic (.block [.load resultRegister (.lit (-1))])) inputState := by
  rintro ⟨k, t, trace⟩
  have run := trace.exec
  cases run with
  | deterministic run =>
    cases run with
    | block success => simp [blockEval, Instr.eval, Operand.eval, address] at success

private def signedCode : Nondeterministic.Code := .deterministic (.block [
  .bin .sub resultRegister (.lit 3) (.lit 5),
  .store (.lit 0) (.reg resultRegister),
  .load resultRegister (.lit 0)])

private theorem signed_terminates : Terminates [] (fun _ => 0) signedCode inputState := by
  have execution : ∃ t, ExecIn [] signedCode inputState 3 t :=
    ⟨_, .deterministic (.block rfl)⟩
  obtain ⟨t, execution⟩ := execution
  exact ⟨_, t, execution.trace (by simp) trivial (.done t 0)⟩

/- Negative values survive both memory operations in the scheduled integer runner. -/
set_option linter.hashCommand false in
#eval show IO Unit from do
  let r := Nondeterministic.run [] (fun _ => 0) signedCode inputState signed_terminates
  unless r.1 == 3 && r.2.regs resultRegister == -2 && r.2.memory 0 == -2 do
    throw <| IO.userError "native nondeterministic runner: signed memory regression"

end AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests
