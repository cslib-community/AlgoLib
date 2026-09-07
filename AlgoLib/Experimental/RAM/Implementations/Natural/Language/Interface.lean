/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Natural.Language.VC
import AlgoLib.Experimental.RAM.Machine.Output

/-!
# Lower implementation interfaces

Packages typed procedure inputs, outputs, and verification contracts at the implementation layer.

Authoring/Interface adds the logical state and observation boundary needed by the public method
workflow.

## Further details

# Explicit input/output entry points for verified source programs
-/
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

/-- The lower entry point shares the native method runner. Its contract is still
stated in source credits; lowering supplies the machine bound. -/
def Function.machine {Input : Type*} (p : Function Input) (x : Input) : Method where
  body := p.body
  requires s := s = p.input x
  ensures _ t := p.ensures x (t.vars .word p.output.name)
  budget _ := p.budget x
  verification s hs := by
    subst s
    exact p.verification x

def Function.run {Input : Type*} (p : Function Input) (x : Input) : Execution Nat :=
  let result := (p.machine x).run (p.input x) rfl
  ⟨result.2.vars .word p.output.name, result.1⟩

theorem Function.correct {Input : Type*} (p : Function Input) (x : Input) :
    p.ensures x (p.run x).output ∧ (p.run x).steps ≤ 2 * p.budget x := by
  have h := (p.machine x).correct (p.input x) rfl
  exact ⟨h.2.1, h.2.2⟩

end AlgoLib.Experimental.RAM.Checked.Language
