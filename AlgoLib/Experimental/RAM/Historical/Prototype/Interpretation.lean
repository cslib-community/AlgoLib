/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Verification.Semantics.LogicalInterpretation
import AlgoLib.Experimental.RAM.Historical.Backend.Realization

/-!
# RAM compilation of the independently defined logical interpretation

LogicalInterpretation imports no RAM backend. This adapter connects its executions
to the verified compiler and concrete instruction costs through realization certificates.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring
variable {State : Type} {M : Model State}

/-- The compiler receives exactly the syntax inspected by `denote`. -/
def compile (M : Model State) (p : Program State)
    (c : Compilation M p := by ram_compile) : Integer.Code :=
  (Native.Natural.command (p.source M c)).compile

/-- A symbolic execution certifies the same compiled program, with bounded RAM work. -/
theorem compilation_sound {p : Program State} [Compilation M p] {s t : State} {k : Nat}
    (h : denote p s k t ()) (r : Checked.Language.Store)
    (hr : M.Represents s r) :
    ∃ j u, Integer.Exec (compile M p) (Checked.Language.integerEncode r) j u ∧
      M.Represents t (Checked.Language.integerObserve u) ∧ j ≤ 2 * (M.overhead * k) := by
  obtain ⟨j, v, hv, ht, hj⟩ := (denote_run p h).refines _ hr
  obtain ⟨nativeSteps, native, lowering⟩ := Native.Natural.preserves hv
  obtain ⟨u, hu, observed⟩ := native.compile _ (Native.observe_encode _)
  refine ⟨nativeSteps, u, hu, ?_, by omega⟩
  simpa only [Checked.Language.integerObserve, observed, Native.Natural.project_store] using ht

end AlgoLib.Experimental.RAM.Prototype
