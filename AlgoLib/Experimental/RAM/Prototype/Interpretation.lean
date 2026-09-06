/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalInterpretation
import AlgoLib.Experimental.RAM.Backend.Realization

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
    (c : Compilation M p := by ram_compile) : Checked.Code :=
  (p.source M c).compile

/-- A symbolic execution certifies the same compiled program, with bounded RAM work. -/
theorem compilation_sound {p : Program State} [Compilation M p] {s t : State} {k : Nat}
    (h : denote p s k t ()) (r : Checked.State)
    (hr : M.Represents s (Checked.Language.observe r)) :
    ∃ j u, Checked.Exec (compile M p) r j u ∧
      M.Represents t (Checked.Language.observe u) ∧ j ≤ M.overhead * k := by
  obtain ⟨j, v, hv, ht, hj⟩ := (denote_run p h).refines _ hr
  obtain ⟨u, hu, he⟩ := hv.compile r rfl
  exact ⟨j, u, hu, he ▸ ht, hj⟩

end AlgoLib.Experimental.RAM.Prototype
