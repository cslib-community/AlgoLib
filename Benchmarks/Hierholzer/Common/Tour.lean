module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Equiv.Defs

/-!
# Frozen graph-neutral Euler-tour certificate

The semantic decoder in this module is pointwise relabeling only: it preserves the indexed step
order and performs no graph query, search, endpoint reconstruction, append, or reversal.  A later
executable materialization of its two lists is not free and must be charged under the protocol.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Common

/-- The frozen logical certificate carrier. -/
structure TourData (V E : Type*) where
  vertices : List V
  edges : List E
deriving DecidableEq, Repr

/-- The frozen canonical executable result.  A step stores an edge ID and its destination ID. -/
structure IndexedTour (n m : Nat) where
  start : Fin n
  steps : List (Fin m × Fin n)
deriving DecidableEq, Repr

namespace IndexedTour

/-- Decode an indexed tour by pointwise application of the two frozen dense-ID equivalences. -/
def decode {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) : TourData V E :=
  { vertices := decodeVertex tour.start :: tour.steps.map (fun step => decodeVertex step.2)
    edges := tour.steps.map (fun step => decodeEdge step.1) }

@[simp] theorem decode_vertices {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) :
    (tour.decode decodeVertex decodeEdge).vertices =
      decodeVertex tour.start :: tour.steps.map (fun step => decodeVertex step.2) := rfl

@[simp] theorem decode_edges {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) :
    (tour.decode decodeVertex decodeEdge).edges =
      tour.steps.map (fun step => decodeEdge step.1) := rfl

@[simp] theorem decode_vertices_length {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) :
    (tour.decode decodeVertex decodeEdge).vertices.length = tour.steps.length + 1 := by
  simp [decode]

@[simp] theorem decode_edges_length {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) :
    (tour.decode decodeVertex decodeEdge).edges.length = tour.steps.length := by
  simp [decode]

@[simp] theorem decode_vertices_head? {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) :
    (tour.decode decodeVertex decodeEdge).vertices.head? = some (decodeVertex tour.start) := rfl

/-- Decoding through an edge equivalence preserves and reflects edge-ID uniqueness. -/
theorem decode_edges_nodup_iff {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) :
    (tour.decode decodeVertex decodeEdge).edges.Nodup ↔
      (tour.steps.map Prod.fst).Nodup := by
  simpa only [decode_edges, List.map_map, Function.comp_def] using
    (List.nodup_map_iff (l := tour.steps.map Prod.fst) decodeEdge.injective)

/-- Decoded edge coverage is exactly dense edge-ID coverage. -/
theorem decode_edges_complete_iff {n m : Nat} {V E : Type*} (tour : IndexedTour n m)
    (decodeVertex : Fin n ≃ V) (decodeEdge : Fin m ≃ E) :
    (∀ edge : E, edge ∈ (tour.decode decodeVertex decodeEdge).edges) ↔
      ∀ edgeId : Fin m, edgeId ∈ tour.steps.map Prod.fst := by
  constructor
  · intro complete edgeId
    have decodedMem := complete (decodeEdge edgeId)
    simpa [decode, List.mem_map, decodeEdge.injective.eq_iff] using decodedMem
  · intro complete edge
    obtain ⟨edgeId, rfl⟩ := decodeEdge.surjective edge
    simpa [decode, List.mem_map, decodeEdge.injective.eq_iff] using complete edgeId

end IndexedTour

/--
The six frozen semantic clauses for an edge-aware closed Euler tour.

The `links` field pairs each edge with the corresponding consecutive vertex pair.  Together with
`length_eq`, `List.Forall₂` has exactly one such pair for every edge position.
-/
structure ValidEulerTour {V E : Type*} (Link : E → V → V → Prop) (start : V)
    (tour : TourData V E) : Prop where
  length_eq : tour.vertices.length = tour.edges.length + 1
  head_eq : tour.vertices.head? = some start
  last_eq : tour.vertices.getLast? = some start
  links : List.Forall₂ (fun edge endpoints => Link edge endpoints.1 endpoints.2) tour.edges
    (tour.vertices.zip tour.vertices.tail)
  edges_nodup : tour.edges.Nodup
  edges_complete : ∀ edge : E, edge ∈ tour.edges

end Benchmarks.Hierholzer.Common
