/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LoomObservation
import AlgoLib.Experimental.RAM.Backend.Realization

/-!
# Every supported program: actual Loom correctness to actual RAM execution

This generic theorem uses Loom's actual WP, the existing logical interpretation,
and the total structural compiler for Supported. It does not assume a separately
proved whole-program translation or an algorithm-specific RAM theorem.

The scope is the deterministic Authoring.Program language and its implemented
primitives. Ordinary Velvet's nondeterministic/recursive extension has a different
semantics and is not silently covered by this theorem.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring

/-- A single theorem covers skip, primitive calls, sequences, both branch arms,
unbounded loops, and nested, nonrecursive verified procedure bodies. -/
theorem loom_to_supported_ram {State : Type} {M : Model State} {p : Program State}
    (supported : Supported M p) (post : State → Prop) (s : State) (credits : Nat)
    (proof : _root_.wp (denote p) (fun _ t _ => post t) s credits)
    (machine : Checked.State) (rep : M.Represents s (Checked.Language.observe machine)) :
    ∃ steps final t, Checked.Exec supported.compile.source.compile machine steps final ∧
      M.Represents t (Checked.Language.observe final) ∧ post t ∧
      steps ≤ M.overhead * credits := by
  rw [loom_wp_eq] at proof
  obtain ⟨k, t, u, run, cost, result⟩ := proof
  cases u
  obtain ⟨steps, final, execution, represents, time⟩ :=
    supported.sound (denote_run _ run) machine rep
  exact ⟨steps, final, t, execution, represents, result,
    time.trans (Nat.mul_le_mul_left _ cost)⟩

end AlgoLib.Experimental.RAM.Prototype
