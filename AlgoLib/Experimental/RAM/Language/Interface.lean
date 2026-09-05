/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.VC
import AlgoLib.Experimental.RAM.Core.Output

/-! # Explicit input/output entry points for verified source programs -/
namespace AlgoLib.Experimental.RAM.Checked.Language

/-- A uniform source program, a typed input encoder, and one word output.
Input validation can be expressed in the input type. Encoding is outside cost. -/
structure Function (Input : Type*) where
  body : Cmd
  input : Input → Store
  output : Var .word
  ensures : Input → Nat → Prop
  budget : Input → Nat
  verification : ∀ x, ∃ k t, Eval body (input x) k t ∧
    ensures x (t.vars .word output.name) ∧ k ≤ budget x

def Function.machine {Input : Type*} (p : Function Input) : Checked.Procedure Input Nat where
  encode x := encode (p.input x)
  body := p.body.compile
  output := .word p.output.reg
  terminates x := by
    obtain ⟨k, t, hx, _, _⟩ := p.verification x
    obtain ⟨u, hu, _⟩ := hx.compile _ (observe_encode _)
    exact ⟨k, u, hu⟩

def Function.run {Input : Type*} (p : Function Input) (x : Input) : Execution Nat :=
  p.machine.run x

theorem Function.correct {Input : Type*} (p : Function Input) (x : Input) :
    p.ensures x (p.run x).output ∧ (p.run x).steps ≤ p.budget x := by
  obtain ⟨k, t, hx, hQ, hk⟩ := p.verification x
  obtain ⟨u, hu, ht⟩ := hx.compile _ (observe_encode _)
  have hv : u.regs p.output.reg = t.vars .word p.output.name :=
    congrArg (fun s : Store => s.vars .word p.output.name) ht
  simp only [Function.run, Function.machine, Checked.Procedure.run, Checked.run_eq hu,
    Output.read, hv]
  exact ⟨hQ, hk⟩

end AlgoLib.Experimental.RAM.Checked.Language
