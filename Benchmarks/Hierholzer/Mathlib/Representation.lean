module

public import Benchmarks.Hierholzer.Common
public import Benchmarks.Hierholzer.Mathlib.Adapter
public import Mathlib.Data.Finite.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Vector.Basic
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn

/-!
# Frozen Mathlib-side executable incidence representation

The executable payload is array-backed.  `ends` is a dense edge endpoint table and `buckets` is a
dense vertex table of incidence arrays.  A dart stores two logical words: an actual dense edge ID
and a Boolean endpoint role.  The two roles remain distinct for loops.

The decode equivalences and all laws are erased specification data.  Construction below is
noncomputable and outside the primary Hierholzer clock.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Set
open scoped Graph

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

@[simp] theorem vector_get_ofFn {k : Nat} {γ : Type*} (f : Fin k → γ) (i : Fin k) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

/-- One canonical incidence occurrence. `false` is endpoint role 0 and `true` is role 1. -/
structure Dart (m : Nat) where
  edge : Fin m
  role : Bool
deriving DecidableEq, Repr

def dartEquiv (m : Nat) : Fin m × Bool ≃ Dart m where
  toFun p := ⟨p.1, p.2⟩
  invFun d := ⟨d.edge, d.role⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (m : Nat) : Fintype (Dart m) :=
  Fintype.ofEquiv (Fin m × Bool) (dartEquiv m)

namespace Dart

/-- The bucket in which a dart canonically belongs. -/
def vertex {n m : Nat} (ends : Vector (Fin n × Fin n) m) (d : Dart m) : Fin n :=
  if d.role then (ends.get d.edge).2 else (ends.get d.edge).1

@[simp] theorem vertex_role0 {n m : Nat} (ends : Vector (Fin n × Fin n) m) (e : Fin m) :
    vertex ends ⟨e, false⟩ = (ends.get e).1 := rfl

@[simp] theorem vertex_role1 {n m : Nat} (ends : Vector (Fin n × Fin n) m) (e : Fin m) :
    vertex ends ⟨e, true⟩ = (ends.get e).2 := rfl

end Dart

/--
An array-backed, actual-edge-indexed incidence representation certified to represent exactly `G`.

`bucket_nodup` and `mem_bucket_iff` jointly state the exact-two-darts law, including no junk,
omission, or duplication.  They deliberately constrain only bucket contents, not their order.
-/
structure CertifiedIncidenceRepresentation (G : Graph α ε) where
  n : Nat
  m : Nat
  decodeVertex : Fin n ≃ Vertex G
  decodeEdge : Fin m ≃ Edge G
  ends : Vector (Fin n × Fin n) m
  buckets : Vector (Array (Dart m)) n
  endpoint_sound : ∀ e : Fin m,
    Link G (decodeEdge e) (decodeVertex (ends.get e).1) (decodeVertex (ends.get e).2)
  bucket_nodup : ∀ x : Fin n, (buckets.get x).toList.Nodup
  mem_bucket_iff : ∀ (x : Fin n) (d : Dart m),
    d ∈ (buckets.get x).toList ↔ Dart.vertex ends d = x

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

/-- Mathematical vertex to dense ID.  This is proof/construction-side and may be noncomputable. -/
noncomputable def encodeVertex (x : Vertex G) : Fin R.n := R.decodeVertex.symm x

/-- Mathematical edge to dense ID.  This is proof/construction-side and may be noncomputable. -/
noncomputable def encodeEdge (e : Edge G) : Fin R.m := R.decodeEdge.symm e

/-- Pointwise logical decoding through the frozen Common decoder. -/
def decodeTour (tour : Common.IndexedTour R.n R.m) : Common.TourData (Vertex G) (Edge G) :=
  tour.decode R.decodeVertex R.decodeEdge

/-- The official mathematical vertex count. -/
noncomputable def vertexCount (_R : CertifiedIncidenceRepresentation G) : Nat := Set.ncard V(G)

/-- The official mathematical actual-edge count. -/
noncomputable def edgeCount (_R : CertifiedIncidenceRepresentation G) : Nat := Set.ncard E(G)

/-- Total stored incidence occurrences. -/
def incidenceCount : Nat :=
  ∑ x : Fin R.n, (R.buckets.get x).size

theorem n_eq_vertexCount : R.n = R.vertexCount := by
  simpa [vertexCount] using Nat.card_congr R.decodeVertex

theorem m_eq_edgeCount : R.m = R.edgeCount := by
  simpa [edgeCount] using Nat.card_congr R.decodeEdge

/-- The two endpoint roles of one edge are distinct darts, even for a loop. -/
theorem role0_ne_role1 (e : Fin R.m) : Dart.mk e false ≠ Dart.mk e true := by
  simp

/-- Endpoint role 0 occurs exactly once, in its first endpoint bucket. -/
theorem role0_mem_iff (x : Fin R.n) (e : Fin R.m) :
    Dart.mk e false ∈ (R.buckets.get x).toList ↔ x = (R.ends.get e).1 := by
  rw [R.mem_bucket_iff]
  simp [eq_comm]

/-- Endpoint role 1 occurs exactly once, in its second endpoint bucket. -/
theorem role1_mem_iff (x : Fin R.n) (e : Fin R.m) :
    Dart.mk e true ∈ (R.buckets.get x).toList ↔ x = (R.ends.get e).2 := by
  rw [R.mem_bucket_iff]
  simp [eq_comm]

/-- Logical representation word count under the frozen codebook. -/
def repWords : Nat :=
  5 + 2 * R.n + 2 * R.m + 2 * R.incidenceCount

def repR0 : Nat := 5
def repRV : Nat := 2
def repRE : Nat := 2
def repRI : Nat := 2

theorem repWords_bound :
    R.repWords ≤ repR0 + repRV * R.n + repRE * R.m + repRI * R.incidenceCount := by
  rfl

end CertifiedIncidenceRepresentation

/-! ## Total noncomputable existence -/

namespace RepresentationConstruction

variable (G : Graph α ε) [Finite (Vertex G)] [Finite (Edge G)]

noncomputable def vertexEquiv : Fin (Nat.card (Vertex G)) ≃ Vertex G :=
  (Finite.equivFin (Vertex G)).symm

noncomputable def edgeEquiv : Fin (Nat.card (Edge G)) ≃ Edge G :=
  (Finite.equivFin (Edge G)).symm

noncomputable def chosenLink (e : Edge G) :
    {p : Vertex G × Vertex G // Link G e p.1 p.2} := by
  let h : ∃ p : Vertex G × Vertex G, Link G e p.1 p.2 := by
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
    exact ⟨⟨⟨x, hxy.left_mem⟩, ⟨y, hxy.right_mem⟩⟩, hxy⟩
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

noncomputable def endpointFn (e : Fin (Nat.card (Edge G))) :
    Fin (Nat.card (Vertex G)) × Fin (Nat.card (Vertex G)) :=
  let p := (chosenLink G (edgeEquiv G e)).val
  ⟨(vertexEquiv G).symm p.1, (vertexEquiv G).symm p.2⟩

noncomputable def ends :
    Vector (Fin (Nat.card (Vertex G)) × Fin (Nat.card (Vertex G))) (Nat.card (Edge G)) :=
  Vector.ofFn (endpointFn G)

noncomputable def bucket (x : Fin (Nat.card (Vertex G))) : Array (Dart (Nat.card (Edge G))) :=
  (((Finset.univ : Finset (Dart (Nat.card (Edge G)))).filter
    (fun d ↦ Dart.vertex (ends G) d = x)).toList).toArray

noncomputable def buckets :
    Vector (Array (Dart (Nat.card (Edge G)))) (Nat.card (Vertex G)) :=
  Vector.ofFn (bucket G)

theorem endpoint_sound (e : Fin (Nat.card (Edge G))) :
    Link G (edgeEquiv G e)
      (vertexEquiv G ((ends G).get e).1) (vertexEquiv G ((ends G).get e).2) := by
  simp only [ends, vector_get_ofFn, endpointFn]
  simpa only [Equiv.apply_symm_apply] using (chosenLink G (edgeEquiv G e)).2

theorem bucket_nodup (x : Fin (Nat.card (Vertex G))) :
    ((buckets G).get x).toList.Nodup := by
  simp only [buckets, vector_get_ofFn, bucket, List.toList_toArray]
  exact Finset.nodup_toList _

theorem mem_bucket_iff (x : Fin (Nat.card (Vertex G))) (d : Dart (Nat.card (Edge G))) :
    d ∈ ((buckets G).get x).toList ↔ Dart.vertex (ends G) d = x := by
  simp only [buckets, vector_get_ofFn, bucket, List.toList_toArray]
  rw [Finset.mem_toList]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

noncomputable def build : CertifiedIncidenceRepresentation G where
  n := Nat.card (Vertex G)
  m := Nat.card (Edge G)
  decodeVertex := vertexEquiv G
  decodeEdge := edgeEquiv G
  ends := ends G
  buckets := buckets G
  endpoint_sound := endpoint_sound G
  bucket_nodup := bucket_nodup G
  mem_bucket_iff := mem_bucket_iff G

end RepresentationConstruction

/-- Every finite Mathlib multigraph admits the full frozen certified incidence representation. -/
theorem representation_exists (G : Graph α ε) [Finite (Vertex G)] [Finite (Edge G)] :
    Nonempty (CertifiedIncidenceRepresentation G) :=
  ⟨RepresentationConstruction.build G⟩

end Benchmarks.Hierholzer.Mathlib
