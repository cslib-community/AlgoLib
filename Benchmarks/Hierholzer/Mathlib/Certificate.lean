module

public import Benchmarks.Hierholzer.Mathlib.Correctness

/-!
# Public Euler-tour certificate and mandatory corollaries
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Set
open scoped Graph
open Benchmarks.Hierholzer.Common

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

def denseVertices (start : Fin R.n) (steps : List (Fin R.m × Fin R.n)) : List (Fin R.n) :=
  start :: steps.map Prod.snd

theorem denseLink_inc_vertex {e : Fin R.m} {a b x : Fin R.n}
    (hl : R.DenseLink e a b) (hi : R.DenseInc e x) : x = a ∨ x = b := by
  rcases hl with hl | hl <;> rcases hi with hi | hi <;> aesop

theorem DenseTrail.inc_vertex_mem {start finish x : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)} {e : Fin R.m}
    (ht : R.DenseTrail start steps finish)
    (he : e ∈ steps.map Prod.fst) (hi : R.DenseInc e x) :
    x ∈ R.denseVertices start steps := by
  induction ht with
  | nil => simp at he
  | @cons a b finish edge rest hlink htail ih =>
      simp only [denseVertices, List.map_cons, Prod.snd, List.mem_cons]
      simp only [List.map_cons, Prod.fst, List.mem_cons] at he
      rcases he with rfl | he
      · rcases R.denseLink_inc_vertex hlink hi with rfl | rfl <;> simp
      · exact Or.inr (by simpa [denseVertices] using ih he)

theorem DenseTrail.links {start finish : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)}
    (ht : R.DenseTrail start steps finish) :
    List.Forall₂ (fun step endpoints ↦ R.DenseLink step.1 endpoints.1 endpoints.2)
      steps ((R.denseVertices start steps).zip (R.denseVertices start steps).tail) := by
  induction ht with
  | nil => simp [denseVertices]
  | cons hlink htail ih =>
      simp only [denseVertices, List.map_cons, List.tail_cons, List.zip_cons_cons,
        Prod.snd, List.forall₂_cons]
      exact ⟨hlink, by simpa [denseVertices] using ih⟩

theorem DenseTrail.getLast?_vertices {start finish : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)}
    (ht : R.DenseTrail start steps finish) :
    (R.denseVertices start steps).getLast? = some finish := by
  induction ht with
  | nil => simp [denseVertices]
  | @cons a b finish edge rest hlink htail ih =>
      simpa [denseVertices] using ih

theorem DenseTrail.decodedLinks {start finish : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)}
    (ht : R.DenseTrail start steps finish) :
    List.Forall₂ (fun (edge : Edge G) (endpoints : Vertex G × Vertex G) ↦
        Link G edge endpoints.1 endpoints.2)
      (steps.map (fun step ↦ R.decodeEdge step.1))
      (((R.denseVertices start steps).map R.decodeVertex).zip
        ((R.denseVertices start steps).map R.decodeVertex).tail) := by
  induction ht with
  | nil => simp [denseVertices]
  | cons hlink htail ih =>
      simp only [denseVertices, List.map_cons, List.tail_cons, List.zip_cons_cons,
        List.forall₂_cons]
      exact ⟨(R.link_decode_iff _ _ _).2 hlink, by simpa [denseVertices] using ih⟩

theorem validEulerTour_of_dense (start : Fin R.n) (steps : List (Fin R.m × Fin R.n))
    (htrail : R.DenseTrail start steps start)
    (hnodup : (steps.map Prod.fst).Nodup)
    (hcomplete : ∀ e : Fin R.m, e ∈ steps.map Prod.fst) :
    ValidEulerTour (Link G) (R.decodeVertex start)
      (R.decodeTour ({ start := start, steps := steps } : IndexedTour R.n R.m)) := by
  constructor
  · simp [decodeTour]
  · simp [decodeTour]
  · have hlast := htrail.getLast?_vertices (R := R)
    have hmap : ((R.denseVertices start steps).map R.decodeVertex).getLast? =
        some (R.decodeVertex start) := by
      rw [List.getLast?_map, hlast]
      rfl
    simpa [decodeTour, IndexedTour.decode, denseVertices] using hmap
  · simpa [decodeTour, IndexedTour.decode, denseVertices] using
      htrail.decodedLinks (R := R)
  · exact (IndexedTour.decode_edges_nodup_iff
      ({ start := start, steps := steps } : IndexedTour R.n R.m)
      R.decodeVertex R.decodeEdge).2 hnodup
  · exact (IndexedTour.decode_edges_complete_iff
      ({ start := start, steps := steps } : IndexedTour R.n R.m)
      R.decodeVertex R.decodeEdge).2 hcomplete

def DenseStep (x y : Fin R.n) : Prop := ∃ e : Fin R.m, R.DenseLink e x y

theorem reachable_dense {start x : Fin R.n}
    (h : Reachable G (R.decodeVertex start) (R.decodeVertex x)) :
    Relation.ReflTransGen R.DenseStep start x := by
  classical
  have hlift := Relation.ReflTransGen.lift R.decodeVertex.symm (p := R.DenseStep)
    (fun a b hab ↦ by
      obtain ⟨edge, hedge⟩ := hab
      let edgeId := R.encodeEdge edge
      refine ⟨edgeId, ?_⟩
      rw [← R.link_decode_iff]
      simpa [edgeId, encodeEdge]) h
  simpa using hlift

theorem RunInvariant.final_edge_complete {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m}
    (h : R.RunInvariant start scanFuel popFuel state) (hempty : state.stack = [])
    (hconn : ∀ x : Vertex G, (∃ e : Edge G, Inc G e x) → Reachable G (R.decodeVertex start) x) :
    ∀ e : Fin R.m, e ∈ state.output.map Prod.fst := by
  classical
  have htrail : R.DenseTrail start state.output start := h.emptyTrail hempty
  have hvertexExhausted : ∀ x ∈ R.denseVertices start state.output,
      R.Exhausted state.used x := by
    intro x hx
    simp only [denseVertices, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨step, hstep, rfl⟩
    · exact h.emptyExhausted hempty
    · exact h.outputExhausted step hstep
  have husedOutput : ∀ e : Fin R.m,
      state.used.get e = true ↔ e ∈ state.output.map Prod.fst := by
    intro e
    simpa [combinedSteps, hempty] using h.used_iff e
  have hreachableMem : ∀ y : Fin R.n,
      Relation.ReflTransGen R.DenseStep start y → y ∈ R.denseVertices start state.output := by
    intro y hy
    induction hy with
    | refl => simp [denseVertices]
    | @tail a b hab hbc ih =>
        obtain ⟨edge, hlink⟩ := hbc
        have hincA : R.DenseInc edge a :=
          Or.elim hlink (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
        have hused := hvertexExhausted a ih edge hincA
        have hedge := (husedOutput edge).1 hused
        exact htrail.inc_vertex_mem (R := R) hedge
          (Or.elim hlink (fun h ↦ Or.inr h.2) (fun h ↦ Or.inl h.2))
  intro e
  let x := (R.ends.get e).1
  have hinc : R.DenseInc e x := Or.inl rfl
  have hmathInc : Inc G (R.decodeEdge e) (R.decodeVertex x) :=
    (R.inc_decode_iff e x).2 hinc
  have hreachMath := hconn (R.decodeVertex x) ⟨R.decodeEdge e, hmathInc⟩
  have hreach := R.reachable_dense hreachMath
  have hmem : x ∈ R.denseVertices start state.output := hreachableMem x hreach
  exact (husedOutput e).1 (hvertexExhausted x hmem e hinc)

theorem hierholzer_finalInvariant (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    (heven : ∀ x : Fin R.n, Even (R.fullDenseDegree x)) :
    ∃ scanFuel popFuel state,
      R.RunInvariant start scanFuel popFuel state ∧ state.stack = [] ∧
      (hierholzer R start).ret = { start := start, steps := state.output } := by
  have hinc : R.m + R.m = R.incidenceCount := by
    rw [R.incidenceCount_eq_two_mul_m]
    omega
  have hi : R.RunInvariant start (R.m + R.m) (R.m + 1)
      (Core.initState R.n R.m start).ret := by
    simpa [hinc] using RunInvariant.initial R start
  obtain ⟨scanFuel, popFuel, hf, hempty⟩ :=
    R.run_final heven (R.m + R.m) (R.m + 1) (Core.initState R.n R.m start).ret start hi
  exact ⟨scanFuel, popFuel, _, hf, hempty, by simp [hierholzer]⟩

/-- The exact frozen six-clause correctness contract. -/
theorem hierholzer_correct [Finite (Vertex G)] [Finite (Edge G)]
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (heven : ∀ x : Vertex G, Even (degree G x))
    (hconn : ∀ x : Vertex G, (∃ e : Edge G, Inc G e x) → Reachable G s x) :
    ValidEulerTour (Link G) s
      (R.decodeTour (hierholzer R (R.encodeVertex s)).ret) := by
  classical
  let start := R.encodeVertex s
  have hstart : R.decodeVertex start = s := by simp [start, encodeVertex]
  have hdenseEven : ∀ x : Fin R.n, Even (R.fullDenseDegree x) := by
    intro x
    rw [R.fullDenseDegree_eq_bucket_size, ← R.degree_decode_eq_bucket_size]
    exact heven (R.decodeVertex x)
  obtain ⟨scanFuel, popFuel, state, hf, hempty, htour⟩ :=
    R.hierholzer_finalInvariant start hdenseEven
  have hn : (state.output.map Prod.fst).Nodup := by
    simpa [combinedSteps, hempty] using hf.edgesNodup
  have hconn' : ∀ x : Vertex G, (∃ e : Edge G, Inc G e x) →
      Reachable G (R.decodeVertex start) x := by
    simpa [hstart] using hconn
  have hc : ∀ e : Fin R.m, e ∈ state.output.map Prod.fst :=
    hf.final_edge_complete (R := R) hempty hconn'
  rw [htour]
  simpa [hstart] using R.validEulerTour_of_dense start state.output
    (hf.emptyTrail hempty) hn hc

/-- Mandatory exact indexed and decoded lengths. -/
theorem hierholzer_exact_lengths [Finite (Vertex G)] [Finite (Edge G)]
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (heven : ∀ x : Vertex G, Even (degree G x))
    (hconn : ∀ x : Vertex G, (∃ e : Edge G, Inc G e x) → Reachable G s x) :
    (R.decodeTour (hierholzer R (R.encodeVertex s)).ret).edges.length = R.m ∧
    (R.decodeTour (hierholzer R (R.encodeVertex s)).ret).vertices.length = R.m + 1 := by
  classical
  have valid := R.hierholzer_correct s heven hconn
  letI := Fintype.ofFinite (Edge G)
  let edges := (R.decodeTour (hierholzer R (R.encodeVertex s)).ret).edges
  have hfin : edges.toFinset = Finset.univ := by
    ext e
    simp [edges, valid.edges_complete]
  have hlenCard : edges.length = Fintype.card (Edge G) := by
    have hc := congrArg Finset.card hfin
    simpa [edges, List.toFinset_card_of_nodup valid.edges_nodup] using hc
  have hcard : Fintype.card (Edge G) = R.m := by
    simpa using (Fintype.card_congr R.decodeEdge).symm
  have hedges : (R.decodeTour (hierholzer R (R.encodeVertex s)).ret).edges.length = R.m := by
    simpa [edges, hcard] using hlenCard
  exact ⟨hedges, by rw [valid.length_eq, hedges]⟩

/-- Mandatory edgeless result shape. -/
theorem hierholzer_edgeless [Finite (Vertex G)] [Finite (Edge G)]
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G) (hm : R.m = 0) :
    (R.decodeTour (hierholzer R (R.encodeVertex s)).ret).edges = [] ∧
    (R.decodeTour (hierholzer R (R.encodeVertex s)).ret).vertices = [s] := by
  let tour := (hierholzer R (R.encodeVertex s)).ret
  have hsteps : tour.steps = [] := by
    cases hs : tour.steps with
    | nil => rfl
    | cons step rest =>
        have impossible : Fin 0 := hm ▸ step.1
        exact Fin.elim0 impossible
  have hstart : tour.start = R.encodeVertex s := by
    simp [tour, hierholzer]
  constructor
  · change (R.decodeTour tour).edges = []
    simp [decodeTour, IndexedTour.decode, hsteps]
  · change (R.decodeTour tour).vertices = [s]
    simp [decodeTour, IndexedTour.decode, hsteps, hstart, encodeVertex]

/-- Positive-edge form of the common certificate. -/
theorem hierholzer_positive_edge_circuit [Finite (Vertex G)] [Finite (Edge G)]
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (heven : ∀ x : Vertex G, Even (degree G x))
    (hconn : ∀ x : Vertex G, (∃ e : Edge G, Inc G e x) → Reachable G s x)
    (hm : 0 < R.m) :
    ValidEulerTour (Link G) s
        (R.decodeTour (hierholzer R (R.encodeVertex s)).ret) ∧
      0 < (R.decodeTour (hierholzer R (R.encodeVertex s)).ret).edges.length := by
  refine ⟨R.hierholzer_correct s heven hconn, ?_⟩
  rw [(R.hierholzer_exact_lengths s heven hconn).1]
  exact hm

end CertifiedIncidenceRepresentation

end Benchmarks.Hierholzer.Mathlib
