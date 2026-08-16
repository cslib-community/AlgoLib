module

public import Benchmarks.Hierholzer.Mathlib.Correctness

/-!
# Bounded-word obligations

The timed core uses dense IDs, cursor/fuel values, and an optional incoming-edge sentinel.  These
lemmas make explicit that all such values fit below the frozen capacity `n + I + 1`, and therefore
below `2^w` whenever the protocol's word-width assumption supplies that capacity inequality.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open scoped BigOperators

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

/-- The largest ordinary one-past-end capacity required by the frozen word model. -/
def wordCapacity : Nat := R.n + R.incidenceCount + 1

/-- Canonical one-word encoding: actual IDs use `0,...,m-1`, and `none` uses sentinel `m`. -/
def encodeIncoming : Option (Fin R.m) → Nat
  | none => R.m
  | some edge => edge.1

theorem edgeCount_le_incidenceCount : R.m ≤ R.incidenceCount := by
  rw [R.incidenceCount_eq_two_mul_m]
  omega

theorem vertexId_lt_wordCapacity (x : Fin R.n) : x.1 < R.wordCapacity := by
  have hx := x.2
  simp only [wordCapacity]
  omega

theorem edgeId_lt_wordCapacity (start : Fin R.n) (e : Fin R.m) :
    e.1 < R.wordCapacity := by
  have hn := start.2
  have he := e.2
  have hm := R.edgeCount_le_incidenceCount
  simp only [wordCapacity]
  omega

theorem incoming_lt_wordCapacity (start : Fin R.n) (incoming : Option (Fin R.m)) :
    R.encodeIncoming incoming < R.wordCapacity := by
  have hn := start.2
  have hm := R.edgeCount_le_incidenceCount
  cases incoming with
  | none =>
      simp only [encodeIncoming, wordCapacity]
      omega
  | some edge => exact R.edgeId_lt_wordCapacity start edge

theorem RunInvariant.scanFuel_lt_wordCapacity {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state) :
    scanFuel < R.wordCapacity := by
  have hn := start.2
  have hb := h.scanBalance
  simp only [wordCapacity]
  omega

theorem RunInvariant.cursor_lt_wordCapacity {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state)
    (x : Fin R.n) : state.cursor.get x < R.wordCapacity := by
  have hn := start.2
  have hb := h.scanBalance
  have hx : state.cursor.get x ≤ ∑ y : Fin R.n, state.cursor.get y := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
  simp only [wordCapacity]
  omega

theorem RunInvariant.popFuel_lt_wordCapacity {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state)
    (hne : state.stack ≠ []) : popFuel < R.wordCapacity := by
  have hn := start.2
  have hp := h.popBalance hne
  have hm := R.edgeCount_le_incidenceCount
  simp only [wordCapacity]
  omega

theorem initialScanFuel_lt_wordCapacity (start : Fin R.n) :
    R.m + R.m < R.wordCapacity := by
  have hn := start.2
  simp only [wordCapacity]
  rw [R.incidenceCount_eq_two_mul_m]
  omega

theorem initialPopFuel_lt_wordCapacity (start : Fin R.n) :
    R.m + 1 < R.wordCapacity := by
  have hn := start.2
  have hm := R.edgeCount_le_incidenceCount
  simp only [wordCapacity]
  omega

/-- Any proved capacity bound supplies the literal `2^w` word-width conclusions. -/
theorem lt_two_pow_of_lt_wordCapacity {value w : Nat}
    (hvalue : value < R.wordCapacity) (hwidth : R.wordCapacity ≤ 2 ^ w) :
    value < 2 ^ w :=
  lt_of_lt_of_le hvalue hwidth

end CertifiedIncidenceRepresentation

end Benchmarks.Hierholzer.Mathlib
