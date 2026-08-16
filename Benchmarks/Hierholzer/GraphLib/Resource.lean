import Benchmarks.Hierholzer.GraphLib.Algorithm

/-!
# Abstract-RAM resource analysis

The proof threads the global dart fuel as a potential.  Each inspected dart consumes one unit of
that potential, so the sum of all cursor scans is linear even when the stack revisits a vertex.
-/

set_option autoImplicit false

namespace Benchmarks.Hierholzer.GraphLib

open Cslib.Algorithms.Lean
open Benchmarks.Hierholzer.Common
open scoped _root_.GraphLib

universe u v

variable {α : Type u} {β : Type v}

structure ScanBudget (cost : Cost) (remaining initial : Nat) : Prop where
  remaining_le : remaining ≤ initial
  initWrite : cost.initWrite = 0
  incidenceRead : cost.incidenceRead + 2 * remaining ≤ 2 * initial
  endpointRead : cost.endpointRead = 0
  usedRead : cost.usedRead + remaining ≤ initial
  usedWrite : cost.usedWrite = 0
  cursorRead : cost.cursorRead = 0
  cursorWrite : cost.cursorWrite + remaining ≤ initial
  indexOp : cost.indexOp + 2 * remaining ≤ 2 * initial + 1
  stackControl : cost.stackControl = 0
  stackRead : cost.stackRead = 0
  stackWrite : cost.stackWrite = 0
  outputControl : cost.outputControl = 0
  outputRead : cost.outputRead = 0
  outputWrite : cost.outputWrite = 0

theorem scanBucket_budget {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]
    (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (bucket : BucketView R.m)
    (dartFuel position : Nat) (state : CoreState R.n R.m) :
    let result := scanBucket R vertexId bucket dartFuel position state
    ScanBudget result.time result.ret.2.2 dartFuel := by
  induction dartFuel generalizing position state with
  | zero =>
      simp [scanBucket]
      constructor <;> simp <;> omega
  | succ dartFuel ih =>
      rw [scanBucket]
      split
      next hBounds =>
        simp
        constructor <;> simp <;> omega
      next hBounds =>
        have hpos : position < bucket.entries.size := by
          have : position < bucket.size := by
            simpa [Event.indexLt] using of_decide_eq_true hBounds
          simpa [bucket.size_eq] using this
        let dart := bucket.entries[position]'hpos
        by_cases hused :
            (state.setCursor vertexId (position + 1)).usedAt dart.1 = true
        ·
          have hrec := ih (position := position + 1)
            (state := state.setCursor vertexId (position + 1))
          dsimp [dart] at hused hrec ⊢
          simp [hused]
          rcases hrec with ⟨hremain, hinit, hincidence, hendpoint, husedRead, husedWrite,
            hcursorRead, hcursorWrite, hindex, hstackControl, hstackRead, hstackWrite,
            houtputControl, houtputRead, houtputWrite⟩
          constructor <;> simp at * <;> omega
        · have hfalse :
              (state.setCursor vertexId (position + 1)).usedAt dart.1 = false := by
            cases hvalue : (state.setCursor vertexId (position + 1)).usedAt dart.1
            · rfl
            · exact (hused hvalue).elim
          dsimp [dart] at hfalse ⊢
          simp [hfalse]
          constructor <;> simp <;> omega

structure NextBudget (cost : Cost) (remaining initial : Nat) : Prop where
  remaining_le : remaining ≤ initial
  initWrite : cost.initWrite = 0
  incidenceRead : cost.incidenceRead + 2 * remaining ≤ 2 * initial + 2
  endpointRead : cost.endpointRead = 0
  usedRead : cost.usedRead + remaining ≤ initial
  usedWrite : cost.usedWrite = 0
  cursorRead : cost.cursorRead ≤ 1
  cursorWrite : cost.cursorWrite + remaining ≤ initial
  indexOp : cost.indexOp + 2 * remaining ≤ 2 * initial + 1
  stackControl : cost.stackControl = 0
  stackRead : cost.stackRead = 0
  stackWrite : cost.stackWrite = 0
  outputControl : cost.outputControl = 0
  outputRead : cost.outputRead = 0
  outputWrite : cost.outputWrite = 0

theorem nextIncident_budget {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]
    (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (dartFuel : Nat) (state : CoreState R.n R.m) :
    let result := nextIncident R vertexId dartFuel state
    NextBudget result.time result.ret.2.2 dartFuel := by
  simp only [nextIncident, TimeM.time_bind, TimeM.ret_bind, Event.ret_incidenceRead,
    Event.time_incidenceRead, Event.ret_cursorRead, Event.time_cursorRead]
  let entries := R.bucket vertexId
  let bucket : BucketView R.m := ⟨entries, entries.size, rfl⟩
  have hscan := scanBucket_budget R vertexId bucket
    dartFuel (state.cursorAt vertexId) state
  dsimp at hscan ⊢
  rcases hscan with ⟨hremain, hinit, hincidence, hendpoint, husedRead, husedWrite,
    hcursorRead, hcursorWrite, hindex, hstackControl, hstackRead, hstackWrite,
    houtputControl, houtputRead, houtputWrite⟩
  constructor <;> simp [bucket, entries] at * <;> omega

/-- A potential bound for the main loop.  The two potentials are the remaining global dart
budget and the remaining structural step budget. -/
structure LoopBudget (cost : Cost) (remaining initialD initialS : Nat) : Prop where
  remaining_le : remaining ≤ initialD
  initWrite : cost.initWrite = 0
  incidenceRead : cost.incidenceRead + 2 * remaining ≤ 2 * initialD + 2 * initialS
  endpointRead : cost.endpointRead ≤ 2 * initialS
  usedRead : cost.usedRead + remaining ≤ initialD
  usedWrite : cost.usedWrite ≤ initialS
  cursorRead : cost.cursorRead ≤ initialS
  cursorWrite : cost.cursorWrite + remaining ≤ initialD
  indexOp : cost.indexOp + 2 * remaining ≤ 2 * initialD + initialS
  stackControl : cost.stackControl ≤ 3 * initialS
  stackRead : cost.stackRead ≤ 6 * initialS
  stackWrite : cost.stackWrite ≤ 3 * initialS
  outputControl : cost.outputControl ≤ initialS
  outputRead : cost.outputRead = 0
  outputWrite : cost.outputWrite ≤ 2 * initialS

theorem runLoop_budget {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]
    (R : CertifiedIncidenceRepresentation G) (stepFuel dartFuel : Nat)
    (state : CoreState R.n R.m) :
    let result := runLoop R stepFuel dartFuel state
    LoopBudget result.time result.ret.2 dartFuel stepFuel := by
  induction stepFuel generalizing dartFuel state with
  | zero =>
      simp [runLoop]
      constructor <;> simp <;> omega
  | succ stepFuel ih =>
      rw [runLoop]
      cases hstack : state.stack with
      | nil =>
          simp [hstack]
          constructor <;> simp <;> omega
      | cons frame rest =>
          simp only [Event.ret_stackCheck, hstack, Event.ret_stackPeek]
          dsimp
          simp only [Event.ret_stackPeek]
          generalize hscan : nextIncident R frame.vertex dartFuel state = scan
          have hnext := nextIncident_budget R frame.vertex dartFuel state
          rw [hscan] at hnext
          cases hoption : scan.ret.1 with
          | some dart =>
              have hrec := ih (dartFuel := scan.ret.2.2)
                (state :=
                  { (scan.ret.2.1.setUsed dart.1 true) with
                    stack :=
                      { vertex := if dart.2 then (R.ends dart.1).1 else (R.ends dart.1).2,
                        incoming := some dart.1 } ::
                      (scan.ret.2.1.setUsed dart.1 true).stack })
              dsimp at hnext hrec ⊢
              simp [hoption] at ⊢
              rcases hnext with ⟨hnRemain, hnInit, hnIncidence, hnEndpoint, hnUsedRead,
                hnUsedWrite, hnCursorRead, hnCursorWrite, hnIndex, hnStackControl,
                hnStackRead, hnStackWrite, hnOutputControl, hnOutputRead, hnOutputWrite⟩
              rcases hrec with ⟨hrRemain, hrInit, hrIncidence, hrEndpoint, hrUsedRead,
                hrUsedWrite, hrCursorRead, hrCursorWrite, hrIndex, hrStackControl,
                hrStackRead, hrStackWrite, hrOutputControl, hrOutputRead, hrOutputWrite⟩
              constructor <;> simp at * <;> omega
          | none =>
              cases hincoming : frame.incoming with
              | none =>
                  have hrec := ih (dartFuel := scan.ret.2.2)
                    (state := { scan.ret.2.1 with stack := rest })
                  dsimp at hnext hrec ⊢
                  simp [hoption, hincoming] at ⊢
                  rcases hnext with ⟨hnRemain, hnInit, hnIncidence, hnEndpoint, hnUsedRead,
                    hnUsedWrite, hnCursorRead, hnCursorWrite, hnIndex, hnStackControl,
                    hnStackRead, hnStackWrite, hnOutputControl, hnOutputRead, hnOutputWrite⟩
                  rcases hrec with ⟨hrRemain, hrInit, hrIncidence, hrEndpoint, hrUsedRead,
                    hrUsedWrite, hrCursorRead, hrCursorWrite, hrIndex, hrStackControl,
                    hrStackRead, hrStackWrite, hrOutputControl, hrOutputRead, hrOutputWrite⟩
                  constructor <;> simp at * <;> omega
              | some edgeId =>
                  have hrec := ih (dartFuel := scan.ret.2.2)
                    (state :=
                      { scan.ret.2.1 with
                        stack := rest
                        outputSteps := (edgeId, frame.vertex) :: scan.ret.2.1.outputSteps })
                  dsimp at hnext hrec ⊢
                  simp [hoption, hincoming] at ⊢
                  rcases hnext with ⟨hnRemain, hnInit, hnIncidence, hnEndpoint, hnUsedRead,
                    hnUsedWrite, hnCursorRead, hnCursorWrite, hnIndex, hnStackControl,
                    hnStackRead, hnStackWrite, hnOutputControl, hnOutputRead, hnOutputWrite⟩
                  rcases hrec with ⟨hrRemain, hrInit, hrIncidence, hrEndpoint, hrUsedRead,
                    hrUsedWrite, hrCursorRead, hrCursorWrite, hrIndex, hrStackControl,
                    hrStackRead, hrStackWrite, hrOutputControl, hrOutputRead, hrOutputWrite⟩
                  constructor <;> simp at * <;> omega

@[simp] theorem time_initializeState {n m : Nat} (start : Fin n) :
    (initializeState (m := m) start).time =
      { (0 : Cost) with initWrite := m + n, stackControl := 1, stackWrite := 3 } := by
  simp [initializeState]
  ext <;> simp <;> omega

/-- All fourteen public component bounds, stated before scalarization. -/
structure HierholzerComponentBounds {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (cost : Cost) : Prop where
  initWrite : cost.initWrite ≤ R.n + R.m
  incidenceRead : cost.incidenceRead ≤ 2 * R.incidenceCount + 4 * R.m + 4
  endpointRead : cost.endpointRead ≤ 4 * R.m + 4
  usedRead : cost.usedRead ≤ R.incidenceCount
  usedWrite : cost.usedWrite ≤ 2 * R.m + 2
  cursorRead : cost.cursorRead ≤ 2 * R.m + 2
  cursorWrite : cost.cursorWrite ≤ R.incidenceCount
  indexOp : cost.indexOp ≤ 2 * R.incidenceCount + 2 * R.m + 4
  stackControl : cost.stackControl ≤ 6 * R.m + 7
  stackRead : cost.stackRead ≤ 12 * R.m + 12
  stackWrite : cost.stackWrite ≤ 6 * R.m + 9
  outputControl : cost.outputControl ≤ 2 * R.m + 2
  outputRead : cost.outputRead = 0
  outputWrite : cost.outputWrite ≤ 4 * R.m + 5

theorem hierholzer_component_bounds {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : HierholzerComponentBounds R (hierholzer R start).time := by
  have hloop := runLoop_budget R (R.m + R.m + 1) (R.m + R.m)
    (initializeState (m := R.m) start).ret
  dsimp at hloop ⊢
  rcases hloop with ⟨hremain, hinit, hincidence, hendpoint, husedRead, husedWrite,
    hcursorRead, hcursorWrite, hindex, hstackControl, hstackRead, hstackWrite,
    houtputControl, houtputRead, houtputWrite⟩
  have hI := R.incidenceCount_eq_twice_edgeCount
  constructor <;> simp [hierholzer] at * <;> omega

theorem hierholzer_initWrite_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.initWrite ≤ R.n + R.m :=
  (hierholzer_component_bounds R start).initWrite

theorem hierholzer_incidenceRead_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    (hierholzer R start).time.incidenceRead ≤ 2 * R.incidenceCount + 4 * R.m + 4 :=
  (hierholzer_component_bounds R start).incidenceRead

theorem hierholzer_endpointRead_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.endpointRead ≤ 4 * R.m + 4 :=
  (hierholzer_component_bounds R start).endpointRead

theorem hierholzer_usedRead_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.usedRead ≤ R.incidenceCount :=
  (hierholzer_component_bounds R start).usedRead

theorem hierholzer_usedWrite_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.usedWrite ≤ 2 * R.m + 2 :=
  (hierholzer_component_bounds R start).usedWrite

theorem hierholzer_cursorRead_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.cursorRead ≤ 2 * R.m + 2 :=
  (hierholzer_component_bounds R start).cursorRead

theorem hierholzer_cursorWrite_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.cursorWrite ≤ R.incidenceCount :=
  (hierholzer_component_bounds R start).cursorWrite

theorem hierholzer_indexOp_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    (hierholzer R start).time.indexOp ≤ 2 * R.incidenceCount + 2 * R.m + 4 :=
  (hierholzer_component_bounds R start).indexOp

theorem hierholzer_stackControl_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.stackControl ≤ 6 * R.m + 7 :=
  (hierholzer_component_bounds R start).stackControl

theorem hierholzer_stackRead_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.stackRead ≤ 12 * R.m + 12 :=
  (hierholzer_component_bounds R start).stackRead

theorem hierholzer_stackWrite_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.stackWrite ≤ 6 * R.m + 9 :=
  (hierholzer_component_bounds R start).stackWrite

theorem hierholzer_outputControl_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.outputControl ≤ 2 * R.m + 2 :=
  (hierholzer_component_bounds R start).outputControl

theorem hierholzer_outputRead_eq_zero {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.outputRead = 0 :=
  (hierholzer_component_bounds R start).outputRead

theorem hierholzer_outputWrite_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).time.outputWrite ≤ 4 * R.m + 5 :=
  (hierholzer_component_bounds R start).outputWrite

def c0 : Nat := 51
def cV : Nat := 1
def cE : Nat := 45
def cI : Nat := 6

theorem hierholzer_total_affine {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤
      c0 + cV * R.n + cE * R.m + cI * R.incidenceCount := by
  have h := hierholzer_component_bounds R start
  rcases h with ⟨hinit, hincidence, hendpoint, husedRead, husedWrite, hcursorRead,
    hcursorWrite, hindex, hstackControl, hstackRead, hstackWrite, houtputControl,
    houtputRead, houtputWrite⟩
  simp only [Cost.total, c0, cV, cE, cI]
  omega

theorem hierholzer_total_edge_bound {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤ c0 + cV * R.n + (cE + 2 * cI) * R.m := by
  have h := hierholzer_total_affine R start
  rw [R.incidenceCount_eq_twice_edgeCount] at h
  simp only [c0, cV, cE, cI] at h ⊢
  omega

def C : Nat := 57

theorem C_eq_protocol_max : C = max c0 (max cV (cE + 2 * cI)) := by decide

theorem hierholzer_total_linear {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤ C * (R.n + R.m + 1) := by
  have h := hierholzer_total_edge_bound R start
  simp only [c0, cV, cE, cI, C] at h ⊢
  omega

theorem hierholzer_total_linear_mathematical {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    Cost.total (hierholzer R start).time ≤ C * (vertexCount G + edgeCount G + 1) := by
  simpa [← R.n_eq, ← R.m_eq] using hierholzer_total_linear R start

end Benchmarks.Hierholzer.GraphLib
