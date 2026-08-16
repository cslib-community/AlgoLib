import Benchmarks.Hierholzer.GraphLib.Adapter
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Vector.Basic

/-!
# Frozen executable incidence representation

The executable payload is an endpoint vector and a vector of incidence arrays.  A dart is a pair
of a dense actual-edge ID and a Boolean endpoint role.  The laws permit every bucket ordering and
state that a bucket contains exactly the canonical darts whose selected endpoint is its vertex.
-/

set_option autoImplicit false

namespace Benchmarks.Hierholzer.GraphLib

open scoped _root_.GraphLib BigOperators

universe u v

variable {α : Type u} {β : Type v}

/-- Constant-time dense access to the array-backed core `Vector`. -/
def vectorGet {γ : Type*} {n : Nat} (xs : Vector γ n) (i : Fin n) : γ :=
  xs[i.1]

@[simp] theorem vectorGet_ofFn {γ : Type*} {n : Nat} (f : Fin n → γ) (i : Fin n) :
    vectorGet (Vector.ofFn f) i = f i := by
  simp [vectorGet]

/-- A dart stores an actual-edge ID and one of its two endpoint roles. -/
abbrev Dart (m : Nat) := Fin m × Bool

/-- The benchmark-local array-backed incidence enumeration. -/
structure IncidenceEnumeration (n m : Nat) where
  /-- Two stored dense endpoint IDs per actual edge. -/
  endpoints : Vector (Fin n × Fin n) m
  /-- One array pointer per vertex; every entry is a two-word dart. -/
  buckets : Vector (Array (Dart m)) n

namespace IncidenceEnumeration

/-- The endpoint selected by a dart's Boolean role. -/
def dartVertex {n m : Nat} (data : IncidenceEnumeration n m) (dart : Dart m) : Fin n :=
  if dart.2 then (vectorGet data.endpoints dart.1).2 else (vectorGet data.endpoints dart.1).1

/-- Representation refinement to the full bundled-edge GraphLib semantics. -/
structure Represents (G : _root_.GraphLib.Graph α β)
    {n m : Nat} (data : IncidenceEnumeration n m)
    (decodeVertex : Fin n ≃ Vertex G)
    (decodeEdge : Fin m ≃ ActualEdge G) : Prop where
  endpoint_sound : ∀ edgeId,
    let ends := vectorGet data.endpoints edgeId
    Link G (decodeEdge edgeId) (decodeVertex ends.1) (decodeVertex ends.2)
  bucket_nodup : ∀ vertexId, (vectorGet data.buckets vertexId).toList.Nodup
  dart_mem_bucket_iff : ∀ vertexId dart,
    dart ∈ (vectorGet data.buckets vertexId).toList ↔ data.dartVertex dart = vertexId

end IncidenceEnumeration

/-- A supplied executable incidence enumeration certified to represent exactly `G`. -/
structure CertifiedIncidenceRepresentation (G : _root_.GraphLib.Graph α β)
    [Finite V(G)] [Finite E(G)] where
  n : Nat
  m : Nat
  data : IncidenceEnumeration n m
  decodeVertex : Fin n ≃ Vertex G
  decodeEdge : Fin m ≃ ActualEdge G
  represents : data.Represents G decodeVertex decodeEdge
  n_eq : n = vertexCount G
  m_eq : m = edgeCount G

namespace CertifiedIncidenceRepresentation

variable {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]

/-- The excluded mathematical-start-to-dense-ID lookup.  The mandatory existence construction
is noncomputable, so this lookup is not advertised as an end-to-end executable preprocessing step.
-/
def encodeVertex (R : CertifiedIncidenceRepresentation G) : Vertex G → Fin R.n :=
  R.decodeVertex.symm

/-- Constant-time abstract endpoint-vector lookup. -/
def ends (R : CertifiedIncidenceRepresentation G) (edgeId : Fin R.m) : Fin R.n × Fin R.n :=
  vectorGet R.data.endpoints edgeId

/-- Constant-time abstract outer-vector lookup of an incidence-array pointer. -/
def bucket (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n) :
    Array (Dart R.m) :=
  vectorGet R.data.buckets vertexId

/-- The endpoint selected by a dart role. -/
def dartVertex (R : CertifiedIncidenceRepresentation G) (dart : Dart R.m) : Fin R.n :=
  R.data.dartVertex dart

/-- The other endpoint reached by traversing a dart's edge from its selected endpoint. -/
def dartOther (R : CertifiedIncidenceRepresentation G) (dart : Dart R.m) : Fin R.n :=
  if dart.2 then (R.ends dart.1).1 else (R.ends dart.1).2

@[simp] theorem dartVertex_false (R : CertifiedIncidenceRepresentation G)
    (edgeId : Fin R.m) : R.dartVertex (edgeId, false) = (R.ends edgeId).1 := rfl

@[simp] theorem dartVertex_true (R : CertifiedIncidenceRepresentation G)
    (edgeId : Fin R.m) : R.dartVertex (edgeId, true) = (R.ends edgeId).2 := rfl

@[simp] theorem dartOther_false (R : CertifiedIncidenceRepresentation G)
    (edgeId : Fin R.m) : R.dartOther (edgeId, false) = (R.ends edgeId).2 := rfl

@[simp] theorem dartOther_true (R : CertifiedIncidenceRepresentation G)
    (edgeId : Fin R.m) : R.dartOther (edgeId, true) = (R.ends edgeId).1 := rfl

theorem endpoint_sound (R : CertifiedIncidenceRepresentation G) (edgeId : Fin R.m) :
    Link G (R.decodeEdge edgeId) (R.decodeVertex (R.ends edgeId).1)
      (R.decodeVertex (R.ends edgeId).2) :=
  R.represents.endpoint_sound edgeId

theorem bucket_nodup (R : CertifiedIncidenceRepresentation G)
    (vertexId : Fin R.n) : (R.bucket vertexId).toList.Nodup :=
  R.represents.bucket_nodup vertexId

@[simp] theorem dart_mem_bucket_iff (R : CertifiedIncidenceRepresentation G)
    (vertexId : Fin R.n) (dart : Dart R.m) :
    dart ∈ (R.bucket vertexId).toList ↔ R.dartVertex dart = vertexId :=
  R.represents.dart_mem_bucket_iff vertexId dart

theorem dart_link (R : CertifiedIncidenceRepresentation G) (dart : Dart R.m) :
    Link G (R.decodeEdge dart.1) (R.decodeVertex (R.dartVertex dart))
      (R.decodeVertex (R.dartOther dart)) := by
  cases hrole : dart.2 <;> simp only [dartVertex, IncidenceEnumeration.dartVertex,
    dartOther, hrole, Bool.false_eq_true, ↓reduceIte]
  · exact R.endpoint_sound dart.1
  · exact (R.endpoint_sound dart.1).symm

/-- Total number of stored incidence occurrences. -/
def incidenceCount (R : CertifiedIncidenceRepresentation G) : Nat :=
  ∑ vertexId : Fin R.n, (R.bucket vertexId).size

/-- Logical executable representation words under the frozen codebook: the two supplied size
words, a structure pointer and container header for each top-level array, two endpoint words per
edge, one pointer plus one inner-array header per vertex, and two words per dart.  Proofs and
mathematical decoding equivalences are erased.
-/
def repWords (R : CertifiedIncidenceRepresentation G) : Nat :=
  6 + 2 * R.n + 2 * R.m + 2 * R.incidenceCount

def r0 : Nat := 6
def rV : Nat := 2
def rE : Nat := 2
def rI : Nat := 2

theorem repWords_bound (R : CertifiedIncidenceRepresentation G) :
    R.repWords ≤ r0 + rV * R.n + rE * R.m + rI * R.incidenceCount := by
  rfl

private theorem bucket_size_eq_filter_card (R : CertifiedIncidenceRepresentation G)
    (vertexId : Fin R.n) :
    (R.bucket vertexId).size =
      (Finset.univ.filter fun dart : Dart R.m => R.dartVertex dart = vertexId).card := by
  classical
  rw [← Array.length_toList, ← List.toFinset_card_of_nodup (R.bucket_nodup vertexId)]
  congr 1
  ext dart
  simp [R.dart_mem_bucket_iff]

/-- The representation laws imply exactly two stored darts per actual edge, independent of every
bucket ordering. -/
theorem incidenceCount_eq_twice_edgeCount (R : CertifiedIncidenceRepresentation G) :
    R.incidenceCount = 2 * R.m := by
  classical
  rw [incidenceCount]
  simp_rw [bucket_size_eq_filter_card]
  have hmap : Set.MapsTo R.dartVertex
      (Finset.univ : Finset (Dart R.m))
      (Finset.univ : Finset (Fin R.n)) := by simp
  rw [← Finset.card_eq_sum_card_fiberwise hmap]
  simp [Fintype.card_prod, Nat.mul_comm]

/-- Total stored darts equal the sum of the frozen loop-counting degrees. -/
theorem incidenceCount_eq_sum_degree (R : CertifiedIncidenceRepresentation G) :
    R.incidenceCount = degreeSum G := by
  rw [R.incidenceCount_eq_twice_edgeCount, degreeSum_eq_twice_edgeCount, ← R.m_eq]

end CertifiedIncidenceRepresentation

private noncomputable def denseEquiv (S : Set α) [Finite S] : Fin S.ncard ≃ S := by
  letI : Fintype S := Fintype.ofFinite S
  have hcard : S.ncard = Fintype.card S := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Set.ncard_univ]
    simpa using (Set.ncard_subtype (fun x : α => x ∈ S) (Set.univ : Set α)).symm
  exact (finCongr hcard).trans (Fintype.equivFin S).symm

private theorem exists_link_endpoints (G : _root_.GraphLib.Graph α β) (e : ActualEdge G) :
    ∃ x y : Vertex G, Link G e x y := by
  obtain ⟨⟨x, y⟩, hxy⟩ := Sym2.mk_surjective e.1.endpoints
  have hx : x ∈ V(G) := G.endpoints_mem e.1 e.2 x (by rw [← hxy]; simp)
  have hy : y ∈ V(G) := G.endpoints_mem e.1 e.2 y (by rw [← hxy]; simp)
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, e.2, hxy.symm⟩

private noncomputable def chosenEndpoints (G : _root_.GraphLib.Graph α β)
    (e : ActualEdge G) : Vertex G × Vertex G :=
  let x := Classical.choose (exists_link_endpoints G e)
  let y := Classical.choose (Classical.choose_spec (exists_link_endpoints G e))
  (x, y)

private theorem chosenEndpoints_spec (G : _root_.GraphLib.Graph α β) (e : ActualEdge G) :
    Link G e (chosenEndpoints G e).1 (chosenEndpoints G e).2 := by
  exact Classical.choose_spec (Classical.choose_spec (exists_link_endpoints G e))

/-- Every finite GraphLib mathematical graph admits a fully certified dense incidence
representation.  This mandatory constructor is noncomputable because it chooses finite
enumerations and an orientation for each unordered endpoint pair; the timed core itself does not.
-/
theorem representation_exists (G : _root_.GraphLib.Graph α β) [Finite V(G)] [Finite E(G)] :
    Nonempty (CertifiedIncidenceRepresentation G) := by
  classical
  let decodeVertex : Fin (vertexCount G) ≃ Vertex G := denseEquiv V(G)
  let decodeEdge : Fin (edgeCount G) ≃ ActualEdge G := denseEquiv E(G)
  let endpointFn : Fin (edgeCount G) → Fin (vertexCount G) × Fin (vertexCount G) :=
    fun edgeId =>
      (decodeVertex.symm (chosenEndpoints G (decodeEdge edgeId)).1,
        decodeVertex.symm (chosenEndpoints G (decodeEdge edgeId)).2)
  let endpoints : Vector (Fin (vertexCount G) × Fin (vertexCount G)) (edgeCount G) :=
    Vector.ofFn endpointFn
  let vertexOf : Dart (edgeCount G) → Fin (vertexCount G) := fun dart =>
    if dart.2 then (endpointFn dart.1).2 else (endpointFn dart.1).1
  let bucketFn : Fin (vertexCount G) → Array (Dart (edgeCount G)) := fun vertexId =>
    (Finset.univ.filter fun dart => vertexOf dart = vertexId).toList.toArray
  let data : IncidenceEnumeration (vertexCount G) (edgeCount G) :=
    { endpoints := endpoints, buckets := Vector.ofFn bucketFn }
  refine ⟨⟨vertexCount G, edgeCount G, data, decodeVertex, decodeEdge, ?_, rfl, rfl⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edgeId
    simpa [data, endpoints, endpointFn] using
      chosenEndpoints_spec G (decodeEdge edgeId)
  · intro vertexId
    simpa [data, bucketFn, List.toList_toArray] using
      (Finset.nodup_toList
        (Finset.univ.filter fun dart : Dart (edgeCount G) => vertexOf dart = vertexId))
  · intro vertexId dart
    simp [bucketFn, data, IncidenceEnumeration.dartVertex, vertexOf, endpoints, endpointFn,
      List.toList_toArray]

end Benchmarks.Hierholzer.GraphLib
