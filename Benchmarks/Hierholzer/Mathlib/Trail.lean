module

public import Benchmarks.Hierholzer.Mathlib.Dense
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Dense edge-aware trail algebra used by the correctness proof
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open scoped BigOperators

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

/-- A positional dense trail: each stored edge links the current vertex to its destination. -/
inductive DenseTrail : Fin R.n → List (Fin R.m × Fin R.n) → Fin R.n → Prop where
  | nil (x : Fin R.n) : DenseTrail x [] x
  | cons {x y z : Fin R.n} {e : Fin R.m} {steps : List (Fin R.m × Fin R.n)} :
      R.DenseLink e x y → DenseTrail y steps z → DenseTrail x ((e, y) :: steps) z

namespace DenseTrail

theorem append {R : CertifiedIncidenceRepresentation G} {x y z : Fin R.n}
    {left right : List (Fin R.m × Fin R.n)}
    (hleft : R.DenseTrail x left y) (hright : R.DenseTrail y right z) :
    R.DenseTrail x (left ++ right) z := by
  induction hleft with
  | nil => simpa using hright
  | cons hlink _ ih => exact .cons hlink (ih hright)

theorem snoc {R : CertifiedIncidenceRepresentation G} {x y z : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)} {e : Fin R.m}
    (hsteps : R.DenseTrail x steps y) (hlink : R.DenseLink e y z) :
    R.DenseTrail x (steps ++ [(e, z)]) z :=
  hsteps.append (.cons hlink (.nil z))

theorem edges_length_le {R : CertifiedIncidenceRepresentation G} {x y : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)}
    (hn : (steps.map Prod.fst).Nodup) : steps.length ≤ R.m := by
  simpa only [List.length_map, Fintype.card_fin] using hn.length_le_card

end DenseTrail

def vertexIndicator (x y : Fin R.n) : Nat := if x = y then 1 else 0

def edgeDegree (x : Fin R.n) (e : Fin R.m) : Nat :=
  vertexIndicator R x (R.ends.get e).1 + vertexIndicator R x (R.ends.get e).2

def degreeOn (x : Fin R.n) (steps : List (Fin R.m × Fin R.n)) : Nat :=
  (steps.map (fun step ↦ R.edgeDegree x step.1)).sum

@[simp] theorem degreeOn_nil (x : Fin R.n) : R.degreeOn x [] = 0 := rfl

@[simp] theorem degreeOn_cons (x : Fin R.n) (step : Fin R.m × Fin R.n)
    (steps : List (Fin R.m × Fin R.n)) :
    R.degreeOn x (step :: steps) = R.edgeDegree x step.1 + R.degreeOn x steps := rfl

theorem degreeOn_append (x : Fin R.n) (left right : List (Fin R.m × Fin R.n)) :
    R.degreeOn x (left ++ right) = R.degreeOn x left + R.degreeOn x right := by
  simp [degreeOn, List.sum_append]

theorem edgeDegree_of_denseLink {e : Fin R.m} {x y z : Fin R.n}
    (h : R.DenseLink e y z) :
    R.edgeDegree x e = R.vertexIndicator x y + R.vertexIndicator x z := by
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    rfl
  · rcases h with ⟨rfl, rfl⟩
    simp [edgeDegree, vertexIndicator, Nat.add_comm]

/-- Endpoint parity for a dense trail, with loops contributing two. -/
theorem DenseTrail.even_degreeOn_endpoints {x y z : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)} (h : R.DenseTrail y steps z) :
    Even (R.degreeOn x steps + R.vertexIndicator x y + R.vertexIndicator x z) := by
  induction h with
  | nil y =>
      by_cases hxy : x = y
      · refine ⟨1, ?_⟩
        simp [vertexIndicator, hxy]
      · refine ⟨0, ?_⟩
        simp [vertexIndicator, hxy]
  | @cons y w z e steps hlink htrail ih =>
      rcases ih with ⟨k, hk⟩
      have hedge := R.edgeDegree_of_denseLink (x := x) hlink
      refine ⟨k + R.vertexIndicator x y, ?_⟩
      simp only [degreeOn_cons]
      omega

def fullDenseDegree (x : Fin R.n) : Nat :=
  ∑ e : Fin R.m, R.edgeDegree x e

theorem edgeDegree_eq_zero_of_not_inc {x : Fin R.n} {e : Fin R.m}
    (h : ¬ R.DenseInc e x) : R.edgeDegree x e = 0 := by
  simp only [DenseInc] at h
  rw [not_or] at h
  simp [edgeDegree, vertexIndicator, h.1, h.2]

theorem fullDenseDegree_eq_bucket_size (x : Fin R.n) :
    R.fullDenseDegree x = (R.buckets.get x).size := by
  rw [R.bucket_size_eq_endpoint_ncards]
  simp only [fullDenseDegree, edgeDegree, Finset.sum_add_distrib]
  have hleft : Set.ncard {e : Fin R.m | (R.ends.get e).1 = x} =
      ∑ e : Fin R.m, R.vertexIndicator x (R.ends.get e).1 := by
    rw [Set.ncard_eq_toFinset_card']
    have hs : {e : Fin R.m | (R.ends.get e).1 = x}.toFinset =
        Finset.univ.filter (fun e ↦ (R.ends.get e).1 = x) := by
      ext e
      simp
    rw [hs]
    simpa [vertexIndicator, eq_comm] using
      (Finset.card_filter (p := fun e : Fin R.m ↦ (R.ends.get e).1 = x) Finset.univ)
  have hright : Set.ncard {e : Fin R.m | (R.ends.get e).2 = x} =
      ∑ e : Fin R.m, R.vertexIndicator x (R.ends.get e).2 := by
    rw [Set.ncard_eq_toFinset_card']
    have hs : {e : Fin R.m | (R.ends.get e).2 = x}.toFinset =
        Finset.univ.filter (fun e ↦ (R.ends.get e).2 = x) := by
      ext e
      simp
    rw [hs]
    simpa [vertexIndicator, eq_comm] using
      (Finset.card_filter (p := fun e : Fin R.m ↦ (R.ends.get e).2 = x) Finset.univ)
  omega

/-- A noduplicated edge list covering every edge incident to `x` has the full degree at `x`. -/
theorem degreeOn_eq_fullDenseDegree {x : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)}
    (hn : (steps.map Prod.fst).Nodup)
    (hcover : ∀ e : Fin R.m, R.DenseInc e x → e ∈ steps.map Prod.fst) :
    R.degreeOn x steps = R.fullDenseDegree x := by
  classical
  let ids := steps.map Prod.fst
  have hid : ids.Nodup := hn
  have hsum : R.degreeOn x steps = ∑ e ∈ ids.toFinset, R.edgeDegree x e := by
    have hfin := List.sum_toFinset (R.edgeDegree x) hid
    simpa [degreeOn, ids, List.map_map, Function.comp_def] using hfin.symm
  rw [hsum, fullDenseDegree]
  apply Finset.sum_subset (by simp)
  intro e _ he
  apply R.edgeDegree_eq_zero_of_not_inc
  intro hinc
  exact he (by simpa [ids] using hcover e hinc)

end CertifiedIncidenceRepresentation

end Benchmarks.Hierholzer.Mathlib
