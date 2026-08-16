module

public import Benchmarks.Hierholzer.Mathlib.Representation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!
# Incidence counting bridges

These lemmas count the frozen representation payload.  The graph-theoretic degree bridge is kept
separate below so the executable two-darts theorem is independently visible.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open scoped BigOperators

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

def dartFiber (x : Fin R.n) : Finset (Dart R.m) :=
  Finset.univ.filter (fun d ↦ Dart.vertex R.ends d = x)

theorem bucket_size_eq_dartFiber_card (x : Fin R.n) :
    (R.buckets.get x).size = (R.dartFiber x).card := by
  let l := (R.buckets.get x).toList
  have hn : l.Nodup := R.bucket_nodup x
  have hs : l.toFinset = R.dartFiber x := by
    ext d
    simp only [List.mem_toFinset, dartFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact R.mem_bucket_iff x d
  calc
    (R.buckets.get x).size = l.length := by simp [l]
    _ = l.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ = (R.dartFiber x).card := by rw [hs]

theorem fintype_card_dart : Fintype.card (Dart R.m) = 2 * R.m := by
  have h := Fintype.card_congr (dartEquiv R.m)
  simpa [Nat.mul_comm] using h.symm

/-- Every certified representation stores exactly two darts per actual dense edge ID. -/
theorem incidenceCount_eq_two_mul_m : R.incidenceCount = 2 * R.m := by
  rw [incidenceCount]
  simp_rw [R.bucket_size_eq_dartFiber_card]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Dart R.m)))
    (t := (Finset.univ : Finset (Fin R.n)))
    (f := Dart.vertex R.ends) (by simp)
  have hsum : (∑ x : Fin R.n, (R.dartFiber x).card) = Fintype.card (Dart R.m) := by
    simpa [dartFiber] using h.symm
  rw [hsum, R.fintype_card_dart]

/-- The representation incidence count is twice the official mathematical edge count. -/
theorem incidenceCount_eq_two_mul_edgeCount :
    R.incidenceCount = 2 * R.edgeCount := by
  rw [R.incidenceCount_eq_two_mul_m, R.m_eq_edgeCount]

end CertifiedIncidenceRepresentation

end Benchmarks.Hierholzer.Mathlib
