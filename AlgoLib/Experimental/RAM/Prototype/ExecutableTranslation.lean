/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.NondeterministicRunner
import AlgoLib.Experimental.RAM.Prototype.VelvetWP
import AlgoLib.Experimental.RAM.Authoring.Interface

/-!
# Public execution of a certified ordinary-Velvet translation

A translation certificate relates all successful source and target outcomes.
`ExecutableTranslation` additionally requires target termination for every input
satisfying the precondition and every external choice schedule. Neither outcome
equivalence nor an upper bound on terminating runs can replace that obligation.

The public runner hides the control stack, raw state, and termination proof.
`run_correct_and_cost` combines an ordinary Loom WP and a universal RAM cost bound
for exactly the execution that returned the observed Lean value. This packages
certificates; it does not automatically construct a compiler for arbitrary methods.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Nondeterministic
open TotalCorrectness TotalCorrectness.DemonicChoice

/-- A translation whose execution is total under every choice schedule. -/
structure ExecutableTranslation {Input Output : Type} (source : Input → VelvetM Output)
    extends Translation source where
  terminates : ∀ input, valid input → ∀ schedule,
    Terminates procedures schedule code (encode input)

/-- Run with an optional external choice schedule, never a fuel argument. -/
def ExecutableTranslation.run {Input Output : Type} {source : Input → VelvetM Output}
    (translation : ExecutableTranslation source) (input : Input) (valid : translation.valid input)
    (schedule : Nat → Nat := fun _ => 0) : Authoring.Result Output :=
  let execution := Nondeterministic.run translation.procedures schedule translation.code
    (translation.encode input) (translation.terminates input valid schedule)
  ⟨translation.decode execution.2, execution.1⟩

/-- The returned value has source correctness and the advertised RAM time bound. -/
theorem ExecutableTranslation.run_correct_and_cost {Input Output : Type}
    {source : Input → VelvetM Output} (translation : ExecutableTranslation source)
    (budget : Input → Nat) (cost : translation.toTranslation.Within budget)
    (input : Input) (valid : translation.valid input) (post : Output → Prop)
    (proof : wp (source input) post) (schedule : Nat → Nat := fun _ => 0) :
    post (translation.run input valid schedule).value ∧
      (translation.run input valid schedule).steps ≤ budget input := by
  exact translation.toTranslation.correct_and_cost budget cost input valid post
    (fun _ outcome => outcome.satisfies_wp post proof)
    (Nondeterministic.run_correct _ _ _ _ (translation.terminates input valid schedule))

end AlgoLib.Experimental.RAM.Prototype.Nondeterministic
