/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Execution
import AlgoLib.Experimental.RAM.Machine.Integer.NatEmbedding

/-!
# Existing owned procedure contracts transported to integer execution

Every currently linked procedure inherits integer execution and a derived bound
without changing its client proof. The old natural-valued representation is an
intermediate migration witness, embedded in the actual integer machine state.
Default assembly uses Backend.Language.IntegerExecution. This theorem exposes
whole-contract transport for backend authors; signed source types are still pending.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

/-- Uniform transport of the existing owned procedure linking theorem to Int-RAM.
Initial private potential is scaled with the instruction simulation overhead. -/
theorem integer_procedure_linking {A B : Type} {rate : Nat} {P : Representation A}
    {Q : Representation B} (proc : Procedure A B)
    (supported : Supported rate P Q proc.body) (a : A) (valid : proc.requires a)
    (r : Footprint) (machine : Checked.State) (saved : Nat)
    (rep : P.holds a r (observe machine) saved) :
    ∃ steps final b left,
      Integer.Exec (Integer.Migration.code supported.compile.code.compile)
        (Integer.Migration.state machine) steps (Integer.Migration.state final) ∧
      Q.holds b r (observe final) left ∧ proc.ensures a b ∧
      Writes r (observe machine) (observe final) ∧
      steps + 2 * left ≤ 2 * (rate * proc.credits a + saved) := by
  obtain ⟨steps, final, b, left, exec, represented, post, frame, paid⟩ :=
    procedure_linking proc supported a valid r machine saved rep
  obtain ⟨actual, run, overhead⟩ := Integer.Migration.preserves exec
  exact ⟨actual, final, b, left, run, represented, post, frame, by omega⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
