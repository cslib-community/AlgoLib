module

public import Benchmarks.Hierholzer.Mathlib.Core
public import Benchmarks.Hierholzer.Mathlib.Counting

/-!
# Componentwise and scalar abstract-RAM bounds
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Cslib.Algorithms.Lean
open Benchmarks.Hierholzer.Common

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace Core

/-- Uniform componentwise bounds for the hot loop from its two decreasing budgets. -/
structure RunBounds (cost : Cost) (scanFuel popFuel : Nat) : Prop where
  initWrite : cost.initWrite = 0
  incidenceRead : cost.incidenceRead ≤ 4 * scanFuel + 2 * popFuel + 2
  endpointRead : cost.endpointRead ≤ 2 * scanFuel
  usedRead : cost.usedRead ≤ scanFuel
  usedWrite : cost.usedWrite ≤ scanFuel
  cursorRead : cost.cursorRead ≤ scanFuel + popFuel + 1
  cursorWrite : cost.cursorWrite ≤ scanFuel
  indexOp : cost.indexOp ≤ 2 * scanFuel + popFuel + 1
  stackControl : cost.stackControl ≤ 3 * scanFuel + 3 * popFuel + 2
  stackRead : cost.stackRead ≤ 2 * scanFuel + 4 * popFuel + 2
  stackWrite : cost.stackWrite ≤ 2 * scanFuel
  outputControl : cost.outputControl ≤ popFuel
  outputRead : cost.outputRead = 0
  outputWrite : cost.outputWrite ≤ 2 * popFuel

theorem run_bounds (R : CertifiedIncidenceRepresentation G) :
    ∀ (scanFuel popFuel : Nat) (state : CoreState R.n R.m),
      RunBounds (run R scanFuel popFuel state).time scanFuel popFuel
  | scanFuel, popFuel, state => by
      rw [run]
      cases hstack : state.stack with
      | nil =>
          simp [hstack]
          constructor <;> simp <;> omega
      | cons top rest =>
          simp only [Event.ret_stackCheck, hstack, Event.ret_stackPeek,
            Event.ret_incidenceRead, Event.ret_cursorRead, Event.ret_indexLt]
          let bucket := R.buckets.get top.vertex
          let cursor := state.cursor.get top.vertex
          cases hget : bucket[cursor]? with
          | none =>
              cases popFuel with
              | zero =>
                  simp [bucket, cursor, hget]
                  constructor <;> simp <;> omega
              | succ popFuel =>
                  cases hin : top.incoming with
                  | none =>
                      have ih := run_bounds R scanFuel popFuel (popState state rest none)
                      rcases ih with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                        h12, h13⟩
                      simp [bucket, cursor, hget, hin]
                      constructor <;> simp_all <;> omega
                  | some edge =>
                      have ih := run_bounds R scanFuel popFuel
                        (popState state rest (some (edge, top.vertex)))
                      rcases ih with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                        h12, h13⟩
                      simp [bucket, cursor, hget, hin]
                      constructor <;> simp_all <;> omega
          | some dart =>
              cases scanFuel with
              | zero =>
                  simp [bucket, cursor, hget]
                  constructor <;> simp <;> omega
              | succ scanFuel =>
                  cases hused : state.used.get dart.edge with
                  | false =>
                      have ih := run_bounds R scanFuel popFuel
                        (pushState state (setFin state.used dart.edge true)
                          (setFin state.cursor top.vertex (state.cursor.get top.vertex + 1))
                          ({ incoming := some dart.edge
                             vertex := otherEndpoint dart.role
                               (R.ends.get dart.edge).1 (R.ends.get dart.edge).2 } :: top :: rest))
                      rcases ih with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                        h12, h13⟩
                      simp [bucket, cursor, hget, hused]
                      constructor <;> simp_all <;> omega
                  | true =>
                      have ih := run_bounds R scanFuel popFuel
                        (skipState state
                          (setFin state.cursor top.vertex (state.cursor.get top.vertex + 1)))
                      rcases ih with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                        h12, h13⟩
                      simp [bucket, cursor, hget, hused]
                      constructor <;> simp_all <;> omega
termination_by scanFuel popFuel _state => scanFuel + popFuel

@[simp] theorem initState_time (n m : Nat) (start : Fin n) :
    (initState n m start).time =
      { (0 : Cost) with initWrite := n + m, stackControl := 1, stackWrite := 2 } := by
  simp [initState]
  ext <;> simp <;> omega

/-- The fourteen public componentwise bounds, with total incidence size left explicit. -/
structure HierholzerBounds (cost : Cost) (n m incidence : Nat) : Prop where
  initWrite : cost.initWrite ≤ n + m
  incidenceRead : cost.incidenceRead ≤ 4 * incidence + 2 * m + 4
  endpointRead : cost.endpointRead ≤ 2 * incidence
  usedRead : cost.usedRead ≤ incidence
  usedWrite : cost.usedWrite ≤ incidence
  cursorRead : cost.cursorRead ≤ incidence + m + 2
  cursorWrite : cost.cursorWrite ≤ incidence
  indexOp : cost.indexOp ≤ 2 * incidence + m + 4
  stackControl : cost.stackControl ≤ 3 * incidence + 3 * m + 6
  stackRead : cost.stackRead ≤ 2 * incidence + 4 * m + 6
  stackWrite : cost.stackWrite ≤ 2 * incidence + 2
  outputControl : cost.outputControl ≤ m + 1
  outputRead : cost.outputRead = 0
  outputWrite : cost.outputWrite ≤ 2 * m + 3

/-- Unconditional componentwise resource theorem for every certified representation and start. -/
theorem hierholzer_bounds (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    HierholzerBounds (hierholzer R start).time R.n R.m R.incidenceCount := by
  have bounds := run_bounds R (R.m + R.m) (R.m + 1) (initState R.n R.m start).ret
  rcases bounds with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  have hinc : R.m + R.m = R.incidenceCount := by
    rw [R.incidenceCount_eq_two_mul_m]
    omega
  simp [hierholzer]
  constructor <;> simp_all <;> omega

/-! Named concrete coefficients required by the frozen affine theorem. -/

def c0 : Nat := 28
def cV : Nat := 1
def cE : Nat := 15
def cI : Nat := 19

/-- Concrete affine scalar bound with all four frozen coefficients exposed. -/
theorem hierholzer_total_affine (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤
      c0 + cV * R.n + cE * R.m + cI * R.incidenceCount := by
  rcases hierholzer_bounds R start with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13⟩
  simp only [Cost.total, c0, cV, cE, cI]
  omega

/-- The same affine theorem stated with the official mathematical cardinalities. -/
theorem hierholzer_total_affine_math (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤
      c0 + cV * R.vertexCount + cE * R.edgeCount + cI * R.incidenceCount := by
  simpa [R.n_eq_vertexCount, R.m_eq_edgeCount] using hierholzer_total_affine R start

/-- Substitution of the two-darts theorem: `28 + n + 53m`. -/
theorem hierholzer_total_edges (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤
      c0 + cV * R.n + (cE + 2 * cI) * R.m := by
  have h := hierholzer_total_affine R start
  rw [R.incidenceCount_eq_two_mul_m] at h
  simp [c0, cV, cE, cI] at h ⊢
  omega

def linearC : Nat := 53

/-- Frozen pointwise textbook `O(n+m)` theorem with concrete `C = 53`. -/
theorem hierholzer_linear (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤ linearC * (R.n + R.m + 1) := by
  have h := hierholzer_total_edges R start
  simp only [c0, cV, cE, cI, linearC] at h ⊢
  omega

/-- Textbook theorem in the official mathematical vertex/actual-edge cardinalities. -/
theorem hierholzer_linear_math (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤
      linearC * (R.vertexCount + R.edgeCount + 1) := by
  simpa [← R.n_eq_vertexCount, ← R.m_eq_edgeCount] using hierholzer_linear R start

end Core

end Benchmarks.Hierholzer.Mathlib
