module

public import Benchmarks.Hierholzer.Mathlib.Counting
public import Mathlib.Data.Finite.Sum

/-!
# Dense endpoint semantics and degree bridge
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Set
open scoped Graph

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

def DenseLink (e : Fin R.m) (x y : Fin R.n) : Prop :=
  let ends := R.ends.get e
  (x = ends.1 ∧ y = ends.2) ∨ (x = ends.2 ∧ y = ends.1)

def DenseInc (e : Fin R.m) (x : Fin R.n) : Prop :=
  x = (R.ends.get e).1 ∨ x = (R.ends.get e).2

def DenseLoop (e : Fin R.m) (x : Fin R.n) : Prop :=
  x = (R.ends.get e).1 ∧ x = (R.ends.get e).2

theorem link_decode_iff (e : Fin R.m) (x y : Fin R.n) :
    Link G (R.decodeEdge e) (R.decodeVertex x) (R.decodeVertex y) ↔ R.DenseLink e x y := by
  have h := R.endpoint_sound e
  change G.IsLink (R.decodeEdge e).1 (R.decodeVertex x).1 (R.decodeVertex y).1 ↔ _
  have hi := h.isLink_iff (x' := (R.decodeVertex x).1) (y' := (R.decodeVertex y).1)
  have hdecode (a b : Fin R.n) :
      (R.decodeVertex a).1 = (R.decodeVertex b).1 ↔ a = b := by
    constructor
    · intro hab
      apply R.decodeVertex.injective
      exact Subtype.ext hab
    · rintro rfl
      rfl
  simp_rw [hdecode] at hi
  simpa [DenseLink, eq_comm, and_comm] using hi

theorem denseLink_symm {e : Fin R.m} {x y : Fin R.n} (h : R.DenseLink e x y) :
    R.DenseLink e y x := by
  rcases h with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem inc_decode_iff (e : Fin R.m) (x : Fin R.n) :
    Inc G (R.decodeEdge e) (R.decodeVertex x) ↔ R.DenseInc e x := by
  constructor
  · rintro ⟨y, hxy⟩
    obtain ⟨yId, rfl⟩ := R.decodeVertex.surjective y
    rw [R.link_decode_iff] at hxy
    rcases hxy with hxy | hxy
    · exact Or.inl hxy.1
    · exact Or.inr hxy.1
  · intro h
    rcases h with hx | hx
    · refine ⟨R.decodeVertex (R.ends.get e).2, ?_⟩
      rw [R.link_decode_iff]
      exact Or.inl ⟨hx, rfl⟩
    · refine ⟨R.decodeVertex (R.ends.get e).1, ?_⟩
      rw [R.link_decode_iff]
      exact Or.inr ⟨hx, rfl⟩

theorem loop_decode_iff (e : Fin R.m) (x : Fin R.n) :
    Loop G (R.decodeEdge e) (R.decodeVertex x) ↔ R.DenseLoop e x := by
  rw [Loop, R.link_decode_iff]
  simp only [DenseLink, DenseLoop]
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2⟩
    · exact ⟨h.2, h.1⟩
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨h1, h2⟩

/-- Predicate subtypes are transported exactly through the dense edge equivalence. -/
def edgePredEquiv (P : Edge G → Prop) :
    {e : Fin R.m // P (R.decodeEdge e)} ≃ {e : Edge G // P e} where
  toFun e := ⟨R.decodeEdge e.1, e.2⟩
  invFun e := ⟨R.decodeEdge.symm e.1, by simpa using e.2⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

theorem ncard_edge_pred (P : Edge G → Prop) :
    Set.ncard {e : Edge G | P e} = Set.ncard {e : Fin R.m | P (R.decodeEdge e)} := by
  exact (Set.ncard_congr' (R.edgePredEquiv P)).symm

/-- Darts at `x` are the disjoint role-0/role-1 endpoint occurrences. -/
def dartAtEquiv (x : Fin R.n) :
    {d : Dart R.m // Dart.vertex R.ends d = x} ≃
      Sum {e : Fin R.m // (R.ends.get e).1 = x}
        {e : Fin R.m // (R.ends.get e).2 = x} where
  toFun d := by
    rcases d with ⟨⟨e, role⟩, h⟩
    cases role with
    | false => exact Sum.inl ⟨e, h⟩
    | true => exact Sum.inr ⟨e, h⟩
  invFun s := by
    cases s with
    | inl e => exact ⟨⟨e.1, false⟩, e.2⟩
    | inr e => exact ⟨⟨e.1, true⟩, e.2⟩
  left_inv d := by
    rcases d with ⟨⟨e, role⟩, h⟩
    cases role <;> rfl
  right_inv s := by
    cases s <;> rfl

theorem bucket_size_eq_endpoint_ncards (x : Fin R.n) :
    (R.buckets.get x).size =
      Set.ncard {e : Fin R.m | (R.ends.get e).1 = x} +
        Set.ncard {e : Fin R.m | (R.ends.get e).2 = x} := by
  rw [R.bucket_size_eq_dartFiber_card]
  have h := Nat.card_congr (R.dartAtEquiv x)
  rw [Nat.card_sum] at h
  have h' : Set.ncard {d : Dart R.m | Dart.vertex R.ends d = x} =
      Set.ncard {e : Fin R.m | (R.ends.get e).1 = x} +
        Set.ncard {e : Fin R.m | (R.ends.get e).2 = x} := h
  rw [Set.ncard_eq_toFinset_card'] at h'
  simpa [dartFiber] using h'

theorem degree_decode_eq_bucket_size (x : Fin R.n) :
    degree G (R.decodeVertex x) = (R.buckets.get x).size := by
  classical
  let left : Set (Fin R.m) := {e | (R.ends.get e).1 = x}
  let right : Set (Fin R.m) := {e | (R.ends.get e).2 = x}
  have hinc : {e : Fin R.m | Inc G (R.decodeEdge e) (R.decodeVertex x)} = left ∪ right := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_union, left, right]
    rw [R.inc_decode_iff]
    simp [DenseInc, eq_comm]
  have hloop : {e : Fin R.m | Loop G (R.decodeEdge e) (R.decodeVertex x)} = left ∩ right := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, left, right]
    rw [R.loop_decode_iff]
    simp [DenseLoop, eq_comm]
  rw [degree, R.ncard_edge_pred (fun e ↦ Inc G e (R.decodeVertex x)),
    R.ncard_edge_pred (fun e ↦ Loop G e (R.decodeVertex x)), hinc, hloop]
  rw [Set.ncard_union_add_ncard_inter]
  simpa [left, right, eq_comm] using (R.bucket_size_eq_endpoint_ncards x).symm

/-- The mandatory representation incidence/adapter-degree equality. -/
theorem incidenceCount_eq_sum_degree :
    R.incidenceCount = ∑ x : Fin R.n, degree G (R.decodeVertex x) := by
  rw [incidenceCount]
  congr 1
  funext x
  exact (R.degree_decode_eq_bucket_size x).symm

/-- Mathematical handshaking, indexed through the certified dense vertex equivalence. -/
theorem sum_degree_eq_two_mul_edgeCount :
    (∑ x : Fin R.n, degree G (R.decodeVertex x)) = 2 * R.edgeCount := by
  rw [← R.incidenceCount_eq_sum_degree, R.incidenceCount_eq_two_mul_edgeCount]

end CertifiedIncidenceRepresentation

end Benchmarks.Hierholzer.Mathlib
