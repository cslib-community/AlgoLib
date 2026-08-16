module

public import Benchmarks.Hierholzer.Mathlib.Correctness

/-!
# Logical auxiliary-space bound

The count follows the frozen word model: one word per used flag and cursor, two payload words plus
one list-cell word per stack frame and output step, and five constant words for the core-state and
four container headers.  The bottom frame is included.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Benchmarks.Hierholzer.Common

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

/-- Logical words simultaneously owned by the algorithm in a core state. -/
def auxiliaryWords (state : CoreState R.n R.m) : Nat :=
  5 + R.m + R.n + 3 * state.stack.length + 3 * state.output.length

theorem StackPath.stack_length_eq {start current : Fin R.n}
    {stack : List (Frame R.n R.m)} (h : R.StackPath start stack current) :
    stack.length = (R.frameSteps stack).length + 1 := by
  induction h with
  | bottom => simp
  | @push stack x y e _ _ ih =>
      simp [frameSteps, ih]

theorem RunInvariant.combined_length_le {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state) :
    (R.combinedSteps state).length ≤ R.m := by
  have hcard := h.edgesNodup.length_le_card
  simpa only [List.length_map, Fintype.card_fin] using hcard

theorem RunInvariant.stack_length_le {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state) :
    state.stack.length ≤ R.m + 1 := by
  rcases h.stackShape with hempty | ⟨current, hpath⟩
  · simp [hempty]
  · have hlen := hpath.stack_length_eq (R := R)
    have hcombined := h.combined_length_le (R := R)
    simp only [combinedSteps, List.length_append] at hcombined
    omega

theorem RunInvariant.stack_add_output_length_le {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state) :
    state.stack.length + state.output.length ≤ R.m + 1 := by
  rcases h.stackShape with hempty | ⟨current, hpath⟩
  · have ho := h.output_length_le (R := R)
    simp [hempty]
    omega
  · have hlen := hpath.stack_length_eq (R := R)
    have hcombined := h.combined_length_le (R := R)
    simp only [combinedSteps, List.length_append] at hcombined
    omega

/-- Peak algorithm-owned storage at every state satisfying the executable loop invariant. -/
theorem RunInvariant.auxiliaryWords_le {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state) :
    R.auxiliaryWords state ≤ R.n + 4 * R.m + 8 := by
  have hso := h.stack_add_output_length_le (R := R)
  simp only [auxiliaryWords]
  omega

end CertifiedIncidenceRepresentation

end Benchmarks.Hierholzer.Mathlib
