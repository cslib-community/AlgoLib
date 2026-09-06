/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Methods

/-!
# Public execution witness for compiled method interfaces

Exposes the checked machine execution behind `VerifiedMethod.run`. Translation
certificates can now relate an ordinary Velvet method to that execution, instead
of merely proving another weakest precondition for the authoring representation.
This bridge contains no algorithm-specific facts or host evaluation oracle.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring Checked.Language

variable {State Input Output : Type} {M : Model State}

/-- The public result is decoded from a genuine execution of the displayed body. -/
theorem interface_execution (api : Interface M Input Output) {p : Program State} [Compilation M p]
    {P : State → Prop} {Q : State → State → Prop} {budget : State → Nat}
    (proof : Correct p P Q budget) (input : Input) (valid : P (api.initial input)) :
    ∃ final, Checked.Exec (Cmd.seq api.prepare (p.source M)).compile (encode (api.encode input))
      (api.run proof input valid).steps final ∧
      api.decode input (observe final) = (api.run proof input valid).value := by
  have h := ((api.method proof input valid).correct (api.encode input) rfl).1
  obtain ⟨final, run, observation⟩ := h.compile _ (observe_encode _)
  exact ⟨final, run, by simp only [Interface.run, observation]⟩

/-- The program and input encoder do not depend on a particular proof or result. -/
theorem method_execution {api : Interface M Input Output} (p : VerifiedMethod api)
    (input : Input) (valid : p.method.requires input) :
    ∃ final, Checked.Exec (Cmd.seq api.prepare p.compilation.source).compile
      (encode (api.encode input)) (p.run input valid).steps final ∧
      api.decode input (observe final) = (p.run input valid).value := by
  letI := p.compilation
  unfold VerifiedMethod.run
  apply interface_execution

end AlgoLib.Experimental.RAM.Prototype
