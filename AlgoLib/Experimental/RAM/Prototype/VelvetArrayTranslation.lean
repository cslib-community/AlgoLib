/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.MultipleArrayTests
import AlgoLib.Experimental.RAM.Prototype.ExecutionBridge
import AlgoLib.Experimental.RAM.Prototype.Nondeterministic

/-!
# Two-way equivalence for an ordinary Velvet multiple-array method

Unlike a theorem about `denote p`, this certificate relates the actual upstream
`method` value below to compiled RAM executions. It uses the independent Velvet
outcome semantics and the compiled execution witness. The frontend currently
requires this bridge to be reconstructed per method; this example is not a claim
that arbitrary ordinary methods are automatically reified by the compiler.
-/
namespace AlgoLib.Experimental.RAM.Prototype.VelvetArrayTranslation
open Authoring Checked.Language VelvetSemantics Nondeterministic

method exchangeHeads (mut left : Array Nat) (mut right : Array Nat) return (u : Unit)
  require 0 < left.size
  require 0 < right.size
  do
    let x := left[0]!
    let y := right[0]!
    left[0] := y
    right[0] := x
    return

abbrev Inputs := Array Nat × Array Nat
abbrev Outputs := Unit × Array Nat × Array Nat

def source (input : Inputs) : VelvetM Outputs := exchangeHeads input.1 input.2

def answer (input : Inputs) : Outputs :=
  ((), input.1.set! 0 input.2[0]!, input.2.set! 0 input.1[0]!)

/-- The operational meaning of the actual ordinary Velvet source declaration. -/
theorem source_outcomes (input : Inputs) (output : Outputs) :
    Returns (source input) output ↔ output = answer input := by
  change Returns (.pure (answer input)) output ↔ _
  exact returns_pure

private def inputs (input : Inputs) : Fin 2 → Array Nat := ![input.1, input.2]
private def pack (arrays : Fin 2 → Array Nat) : Outputs := ((), arrays 0, arrays 1)

private abbrev executable := MultipleArrayTests.exchangeHeadsVerified

def machineCode : Checked.Code :=
  (Cmd.seq (MultipleArrays.interface 2).prepare executable.method.body.source).compile

def machineInput (input : Inputs) : Checked.State :=
  encode ((MultipleArrays.interface 2).encode (inputs input))

def decode (state : Checked.State) : Outputs :=
  pack ((MultipleArrays.interface 2).decode (fun _ => #[]) (observe state))

private theorem result_eq (input : Inputs) (hl : 0 < input.1.size) (hr : 0 < input.2.size) :
    pack (executable.run (inputs input) ⟨hl, hr, trivial⟩).value = answer input := by
  have h := (executable.correct (inputs input) ⟨hl, hr, trivial⟩).1
  change _ = _ ∧ _ = _ ∧ True at h
  exact Prod.ext rfl (Prod.ext h.1 h.2.1)

/-- One fixed RAM code preserves and reflects all source outcomes on valid inputs. -/
def translation : Translation source where
  code := .deterministic machineCode
  encode := machineInput
  decode := decode
  valid input := 0 < input.1.size ∧ 0 < input.2.size
  equivalent input valid output := by
    obtain ⟨final, run, result⟩ := method_execution executable (inputs input)
      ⟨valid.1, valid.2, trivial⟩
    have decoded : decode final = answer input := by
      change pack ((MultipleArrays.interface 2).decode (inputs input) (observe final)) = _
      rw [result]
      exact result_eq input valid.1 valid.2
    rw [source_outcomes]
    constructor
    · rintro rfl
      exact ⟨_, final, .deterministic run, decoded⟩
    · rintro ⟨k, other, execution, ho⟩
      cases execution with
      | deterministic execution =>
        have eq := (run.deterministic execution).2
        subst other
        exact ho.symm.trans decoded

/-- Source correctness is now transportable to every execution of the RAM translation. -/
theorem correct (input : Inputs) (valid : translation.valid input)
    {steps : Nat} {final : Checked.State}
    (run : Nondeterministic.ExecIn translation.procedures translation.code
      (translation.encode input) steps final) :
    translation.decode final = answer input :=
  translation.correct input valid (· = answer input)
    (fun output h => (source_outcomes input output).mp h) run

end AlgoLib.Experimental.RAM.Prototype.VelvetArrayTranslation
