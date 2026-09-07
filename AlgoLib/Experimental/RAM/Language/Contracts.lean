/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.Program

/-!
# Public mathematical procedure contracts

Preconditions, postconditions and logical allowances describe the library interface.
Uniform allowances and borrowing queries compose without proof-plan machinery.
Annotated verification lives in Verification; the public frontend imports it for authors.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- A public contract can be fixed before any implementation body is selected. -/
structure Contract (A B : Type) where
  requires : A → Prop
  ensures : A → B → Prop
  credits : A → Nat

/-- A body realizes a public contract, with no change to its client-facing fields. -/
@[reducible] def Contract.implement (contract : Contract A B) (body : Program A B)
    (proof : ∀ a, contract.requires a → ∃ k b,
      Run body a k b ∧ contract.ensures a b ∧ k ≤ contract.credits a) : Procedure A B :=
  ⟨body, contract.requires, contract.ensures, contract.credits, proof⟩

/-- A library advertises a constant public allowance for automatic straight-line budgets.
State-dependent contracts remain supported through explicit logical loop/method budgets. -/
class UniformCredits (proc : Procedure A B) where
  amount : Nat
  bound : ∀ a, proc.credits a ≤ amount

/-- Reserve a uniform allowance; correctness still comes from the original summary. -/
@[reducible] def Procedure.uniform (proc : Procedure A B)
    [cost : UniformCredits proc] : Procedure A B where
  body := proc.body
  requires := proc.requires
  ensures := proc.ensures
  credits _ := cost.amount
  correct a h := by
    obtain ⟨k, b, run, post, bound⟩ := proc.correct a h
    exact ⟨k, b, run, post, bound.trans (cost.bound a)⟩

/-- Queries borrow one component of a separating product. -/
def testLeft (test : A → Bool) (s : A × B) : Bool := test s.1

def testRight (test : B → Bool) (s : A × B) : Bool := test s.2

end AlgoLib.Experimental.RAM.Prototype.Composition
