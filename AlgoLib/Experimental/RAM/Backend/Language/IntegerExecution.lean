/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Verification
import AlgoLib.Experimental.RAM.Machine.Integer.NatEmbedding

/-!
# Default execution of natural-valued compiler IR on Int-RAM

The existing typed command language is an intermediate representation. Execution
uses integer instructions, including explicit clamping for Nat subtraction. The
natural observation is used only on states certified to represent natural values.
No old interpreter is called to compute the result. Logical contracts retain their
original budgets; the final machine bound includes the verified lowering overhead.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

/-- Observation for the currently natural-valued source types, not address conversion. -/
def integerObserve (s : Integer.State) : Store :=
  observe ⟨fun r => (s.regs r).toNat, fun a => (s.memory a).toNat⟩

@[simp] theorem integerObserve_embed (s : Checked.State) :
    integerObserve (Integer.Migration.state s) = observe s := by
  simp [integerObserve, Integer.Migration.state]

/-- The code interpreted by the default owned frontend runner. -/
def Method.integerCode (p : Method) : Integer.Code := Integer.Migration.code p.body.compile

private theorem Method.integerTerminates (p : Method) (s : Store) (hs : p.requires s) :
    Integer.Terminates p.integerCode (Integer.Migration.state (encode s)) := by
  apply Integer.Migration.terminates
  obtain ⟨k, t, hx, _, _⟩ := p.verification s hs
  obtain ⟨u, hu, _⟩ := hx.compile (encode s) (observe_encode s)
  exact ⟨k, u, hu⟩

/-- Actual integer-machine result and exact instruction count, with no fuel. -/
def Method.integerRun (p : Method) (s : Store) (hs : p.requires s) : Nat × Store :=
  let result := Integer.run p.integerCode (Integer.Migration.state (encode s))
    (p.integerTerminates s hs)
  (result.1, integerObserve result.2)

/-- The returned count belongs to actual integer instructions, not the old IR semantics. -/
theorem Method.integerRun_exec (p : Method) (s : Store) (hs : p.requires s) :
    ∃ final, Integer.Exec p.integerCode (Integer.Migration.state (encode s))
      (p.integerRun s hs).1 final ∧ (p.integerRun s hs).2 = integerObserve final :=
  ⟨_, Integer.run_correct _ _ (p.integerTerminates s hs), rfl⟩

/-- Automatic transport: source postconditions are unchanged, machine counts are derived. -/
theorem Method.integerCorrect (p : Method) (s : Store) (hs : p.requires s) :
    (∃ k, Eval p.body s k (p.integerRun s hs).2) ∧
      p.ensures s (p.integerRun s hs).2 ∧ (p.integerRun s hs).1 ≤ 2 * p.budget s := by
  obtain ⟨k, t, hx, post, paid⟩ := p.verification s hs
  obtain ⟨u, hu, observed⟩ := hx.compile (encode s) (observe_encode s)
  obtain ⟨j, hj, cost⟩ := Integer.Migration.preserves hu
  simp only [Method.integerRun, Method.integerCode, Integer.run_eq hj,
    integerObserve_embed, observed]
  exact ⟨⟨k, hx⟩, post, by omega⟩

end AlgoLib.Experimental.RAM.Checked.Language
