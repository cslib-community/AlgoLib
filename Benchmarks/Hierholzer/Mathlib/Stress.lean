module

public import Benchmarks.Hierholzer.Mathlib.Certificate
public meta import Benchmarks.Hierholzer.Mathlib.Representation
public meta import Benchmarks.Hierholzer.Mathlib.Core

/-!
# Executable supplied representations and mandatory stress cases
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib.Stress

open Set
open scoped Graph
open Benchmarks.Hierholzer.Common
open Benchmarks.Hierholzer.Mathlib

/-- A finite multigraph whose actual edge values are dense IDs and whose endpoint table is given. -/
def graphOfEnds (n m : Nat) (ends : Vector (Fin n × Fin n) m) : Graph (Fin n) (Fin m) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y :=
    (x = (ends.get e).1 ∧ y = (ends.get e).2) ∨
      (x = (ends.get e).2 ∧ y = (ends.get e).1)
  isLink_symm := by
    intro e _ x y h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h h'
    rcases h with h | h <;> rcases h' with h' | h' <;> aesop
  edge_mem_iff_exists_isLink := by
    intro e
    simp only [Set.mem_univ, true_iff]
    exact ⟨(ends.get e).1, (ends.get e).2, Or.inl ⟨rfl, rfl⟩⟩
  left_mem_of_isLink := by simp

instance {n m : Nat} {ends : Vector (Fin n × Fin n) m}
    (edge : Edge (graphOfEnds n m ends)) (x y : Vertex (graphOfEnds n m ends)) :
    Decidable (Link (graphOfEnds n m ends) edge x y) := by
  unfold Link graphOfEnds
  infer_instance

def vertexEquiv (n m : Nat) (ends : Vector (Fin n × Fin n) m) :
    Fin n ≃ Vertex (graphOfEnds n m ends) where
  toFun x := ⟨x, Set.mem_univ x⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

def edgeEquiv (n m : Nat) (ends : Vector (Fin n × Fin n) m) :
    Fin m ≃ Edge (graphOfEnds n m ends) where
  toFun e := ⟨e, Set.mem_univ e⟩
  invFun e := e.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

def supplied {n m : Nat} (ends : Vector (Fin n × Fin n) m)
    (buckets : Vector (Array (Dart m)) n)
    (bucket_nodup : ∀ x : Fin n, (buckets.get x).toList.Nodup)
    (mem_bucket_iff : ∀ (x : Fin n) (d : Dart m),
      d ∈ (buckets.get x).toList ↔ Dart.vertex ends d = x) :
    CertifiedIncidenceRepresentation (graphOfEnds n m ends) where
  n := n
  m := m
  decodeVertex := vertexEquiv n m ends
  decodeEdge := edgeEquiv n m ends
  ends := ends
  buckets := buckets
  endpoint_sound := by
    intro e
    exact Or.inl ⟨rfl, rfl⟩
  bucket_nodup := bucket_nodup
  mem_bucket_iff := mem_bucket_iff

def ends0 : Vector (Fin 1 × Fin 1) 0 := Vector.ofFn (fun e ↦ Fin.elim0 e)
def endsLoop1 : Vector (Fin 1 × Fin 1) 1 := Vector.ofFn ![(0, 0)]
def endsLoop2 : Vector (Fin 1 × Fin 1) 2 := Vector.ofFn ![(0, 0), (0, 0)]
def endsParallel2 : Vector (Fin 2 × Fin 2) 2 := Vector.ofFn ![(0, 1), (0, 1)]
def endsIsolated : Vector (Fin 3 × Fin 3) 2 := Vector.ofFn ![(0, 1), (0, 1)]
def endsTriangle : Vector (Fin 3 × Fin 3) 3 := Vector.ofFn ![(0, 1), (1, 2), (2, 0)]
def endsIdentity4 : Vector (Fin 2 × Fin 2) 4 :=
  Vector.ofFn ![(0, 1), (0, 1), (0, 1), (0, 1)]

def buckets0 : Vector (Array (Dart 0)) 1 := Vector.ofFn ![#[]]
def bucketsLoop1 : Vector (Array (Dart 1)) 1 :=
  Vector.ofFn ![#[⟨0, false⟩, ⟨0, true⟩]]
def bucketsLoop2 : Vector (Array (Dart 2)) 1 :=
  Vector.ofFn ![#[⟨0, false⟩, ⟨0, true⟩, ⟨1, false⟩, ⟨1, true⟩]]
def bucketsParallel2 : Vector (Array (Dart 2)) 2 :=
  Vector.ofFn ![#[⟨0, false⟩, ⟨1, false⟩], #[⟨0, true⟩, ⟨1, true⟩]]
def bucketsIsolated : Vector (Array (Dart 2)) 3 :=
  Vector.ofFn ![#[⟨0, false⟩, ⟨1, false⟩], #[⟨0, true⟩, ⟨1, true⟩], #[]]
def bucketsTriangle : Vector (Array (Dart 3)) 3 :=
  Vector.ofFn ![#[⟨0, false⟩, ⟨2, true⟩], #[⟨0, true⟩, ⟨1, false⟩],
    #[⟨1, true⟩, ⟨2, false⟩]]
def bucketsIdentity4 : Vector (Array (Dart 4)) 2 :=
  Vector.ofFn ![#[⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩, ⟨3, false⟩],
    #[⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]]

def r0 := supplied ends0 buckets0 (by native_decide) (by native_decide)
def rLoop1 := supplied endsLoop1 bucketsLoop1 (by native_decide) (by native_decide)
def rLoop2 := supplied endsLoop2 bucketsLoop2 (by native_decide) (by native_decide)
def rParallel2 := supplied endsParallel2 bucketsParallel2 (by native_decide) (by native_decide)
def rIsolated := supplied endsIsolated bucketsIsolated (by native_decide) (by native_decide)
def rTriangle := supplied endsTriangle bucketsTriangle (by native_decide) (by native_decide)
def rIdentity4 := supplied endsIdentity4 bucketsIdentity4 (by native_decide) (by native_decide)

def start0 : Fin r0.n := ⟨0, by native_decide⟩
def startLoop1 : Fin rLoop1.n := ⟨0, by native_decide⟩
def startLoop2 : Fin rLoop2.n := ⟨0, by native_decide⟩
def startParallel2 : Fin rParallel2.n := ⟨0, by native_decide⟩
def startIsolated : Fin rIsolated.n := ⟨0, by native_decide⟩
def startTriangle : Fin rTriangle.n := ⟨0, by native_decide⟩
def startIdentity4 : Fin rIdentity4.n := ⟨0, by native_decide⟩

def edgeLoop10 : Fin rLoop1.m := ⟨0, by native_decide⟩
def edgeLoop20 : Fin rLoop2.m := ⟨0, by native_decide⟩
def edgeLoop21 : Fin rLoop2.m := ⟨1, by native_decide⟩
def edgeParallel20 : Fin rParallel2.m := ⟨0, by native_decide⟩
def edgeParallel21 : Fin rParallel2.m := ⟨1, by native_decide⟩
def vertexParallel21 : Fin rParallel2.n := ⟨1, by native_decide⟩
def edgeIsolated0 : Fin rIsolated.m := ⟨0, by native_decide⟩
def edgeIsolated1 : Fin rIsolated.m := ⟨1, by native_decide⟩
def vertexIsolated1 : Fin rIsolated.n := ⟨1, by native_decide⟩
def edgeTriangle0 : Fin rTriangle.m := ⟨0, by native_decide⟩
def edgeTriangle1 : Fin rTriangle.m := ⟨1, by native_decide⟩
def edgeTriangle2 : Fin rTriangle.m := ⟨2, by native_decide⟩
def vertexTriangle1 : Fin rTriangle.n := ⟨1, by native_decide⟩
def vertexTriangle2 : Fin rTriangle.n := ⟨2, by native_decide⟩
def edgeIdentity0 : Fin rIdentity4.m := ⟨0, by native_decide⟩
def edgeIdentity1 : Fin rIdentity4.m := ⟨1, by native_decide⟩
def edgeIdentity2 : Fin rIdentity4.m := ⟨2, by native_decide⟩
def edgeIdentity3 : Fin rIdentity4.m := ⟨3, by native_decide⟩
def vertexIdentity1 : Fin rIdentity4.n := ⟨1, by native_decide⟩

def withinBound (n m incidence : Nat) (cost : Cost) : Bool :=
  cost.initWrite ≤ n + m &&
  cost.incidenceRead ≤ 4 * incidence + 2 * m + 4 &&
  cost.endpointRead ≤ 2 * incidence && cost.usedRead ≤ incidence &&
  cost.usedWrite ≤ incidence && cost.cursorRead ≤ incidence + m + 2 &&
  cost.cursorWrite ≤ incidence && cost.indexOp ≤ 2 * incidence + m + 4 &&
  cost.stackControl ≤ 3 * incidence + 3 * m + 6 &&
  cost.stackRead ≤ 2 * incidence + 4 * m + 6 &&
  cost.stackWrite ≤ 2 * incidence + 2 && cost.outputControl ≤ m + 1 &&
  cost.outputRead = 0 && cost.outputWrite ≤ 2 * m + 3

-- Representation validity is witnessed by the seven closed certified values above.
example : r0.incidenceCount = 0 := by native_decide
example : rLoop1.incidenceCount = 2 := by native_decide
example : rLoop2.incidenceCount = 4 := by native_decide
example : rParallel2.incidenceCount = 4 := by native_decide
example : rIsolated.incidenceCount = 4 := by native_decide
example : rTriangle.incidenceCount = 6 := by native_decide
example : rIdentity4.incidenceCount = 8 := by native_decide

-- Traversal-ordered indexed tours.
#eval (hierholzer r0 start0).ret
#eval (hierholzer rLoop1 startLoop1).ret
#eval (hierholzer rLoop2 startLoop2).ret
#eval (hierholzer rParallel2 startParallel2).ret
#eval (hierholzer rIsolated startIsolated).ret
#eval (hierholzer rTriangle startTriangle).ret
#eval (hierholzer rIdentity4 startIdentity4).ret

-- Full fourteen-component cost vectors.
#eval (hierholzer r0 start0).time
#eval (hierholzer rLoop1 startLoop1).time
#eval (hierholzer rLoop2 startLoop2).time
#eval (hierholzer rParallel2 startParallel2).time
#eval (hierholzer rIsolated startIsolated).time
#eval (hierholzer rTriangle startTriangle).time
#eval (hierholzer rIdentity4 startIdentity4).time

-- Concrete componentwise resource checks.
#eval withinBound r0.n r0.m r0.incidenceCount (hierholzer r0 start0).time
#eval withinBound rLoop1.n rLoop1.m rLoop1.incidenceCount (hierholzer rLoop1 startLoop1).time
#eval withinBound rLoop2.n rLoop2.m rLoop2.incidenceCount (hierholzer rLoop2 startLoop2).time
#eval withinBound rParallel2.n rParallel2.m rParallel2.incidenceCount
  (hierholzer rParallel2 startParallel2).time
#eval withinBound rIsolated.n rIsolated.m rIsolated.incidenceCount
  (hierholzer rIsolated startIsolated).time
#eval withinBound rTriangle.n rTriangle.m rTriangle.incidenceCount
  (hierholzer rTriangle startTriangle).time
#eval withinBound rIdentity4.n rIdentity4.m rIdentity4.incidenceCount
  (hierholzer rIdentity4 startIdentity4).time

-- Full decoded common certificates, including loops, parallel identity, and isolation.
example : ValidEulerTour (Link (graphOfEnds 1 0 ends0)) (r0.decodeVertex start0)
    (r0.decodeTour (hierholzer r0 start0).ret) := by
  have hret : (hierholzer r0 start0).ret =
      ({ start := start0, steps := [] } : IndexedTour r0.n r0.m) := by native_decide
  rw [hret]
  apply r0.validEulerTour_of_dense
  · exact .nil start0
  · native_decide
  · native_decide
example : ValidEulerTour (Link (graphOfEnds 1 1 endsLoop1)) (rLoop1.decodeVertex startLoop1)
    (rLoop1.decodeTour (hierholzer rLoop1 startLoop1).ret) := by
  have hret : (hierholzer rLoop1 startLoop1).ret =
      ({ start := startLoop1, steps := [(edgeLoop10, startLoop1)] } :
        IndexedTour rLoop1.n rLoop1.m) := by
    native_decide
  rw [hret]
  apply rLoop1.validEulerTour_of_dense
  · exact .cons (Or.inl ⟨by native_decide, by native_decide⟩) (.nil startLoop1)
  · native_decide
  · native_decide
example : ValidEulerTour (Link (graphOfEnds 1 2 endsLoop2)) (rLoop2.decodeVertex startLoop2)
    (rLoop2.decodeTour (hierholzer rLoop2 startLoop2).ret) := by
  have hret : (hierholzer rLoop2 startLoop2).ret =
      ({ start := startLoop2,
          steps := [(edgeLoop20, startLoop2), (edgeLoop21, startLoop2)] } :
        IndexedTour rLoop2.n rLoop2.m) := by
    native_decide
  rw [hret]
  apply rLoop2.validEulerTour_of_dense
  · exact .cons (Or.inl ⟨by native_decide, by native_decide⟩)
      (.cons (Or.inl ⟨by native_decide, by native_decide⟩) (.nil startLoop2))
  · native_decide
  · native_decide
example : ValidEulerTour (Link (graphOfEnds 2 2 endsParallel2)) (rParallel2.decodeVertex startParallel2)
    (rParallel2.decodeTour (hierholzer rParallel2 startParallel2).ret) := by
  have hret : (hierholzer rParallel2 startParallel2).ret =
      ({ start := startParallel2,
          steps := [(edgeParallel20, vertexParallel21), (edgeParallel21, startParallel2)] } :
        IndexedTour rParallel2.n rParallel2.m) := by native_decide
  rw [hret]
  apply rParallel2.validEulerTour_of_dense
  · exact .cons (Or.inl ⟨by native_decide, by native_decide⟩)
      (.cons (Or.inr ⟨by native_decide, by native_decide⟩) (.nil startParallel2))
  · native_decide
  · native_decide
example : ValidEulerTour (Link (graphOfEnds 3 2 endsIsolated)) (rIsolated.decodeVertex startIsolated)
    (rIsolated.decodeTour (hierholzer rIsolated startIsolated).ret) := by
  have hret : (hierholzer rIsolated startIsolated).ret =
      ({ start := startIsolated,
          steps := [(edgeIsolated0, vertexIsolated1), (edgeIsolated1, startIsolated)] } :
        IndexedTour rIsolated.n rIsolated.m) := by native_decide
  rw [hret]
  apply rIsolated.validEulerTour_of_dense
  · exact .cons (Or.inl ⟨by native_decide, by native_decide⟩)
      (.cons (Or.inr ⟨by native_decide, by native_decide⟩) (.nil startIsolated))
  · native_decide
  · native_decide
example : ValidEulerTour (Link (graphOfEnds 3 3 endsTriangle)) (rTriangle.decodeVertex startTriangle)
    (rTriangle.decodeTour (hierholzer rTriangle startTriangle).ret) := by
  have hret : (hierholzer rTriangle startTriangle).ret =
      ({ start := startTriangle,
          steps := [(edgeTriangle0, vertexTriangle1), (edgeTriangle1, vertexTriangle2),
            (edgeTriangle2, startTriangle)] } :
        IndexedTour rTriangle.n rTriangle.m) := by native_decide
  rw [hret]
  apply rTriangle.validEulerTour_of_dense
  · exact .cons (Or.inl ⟨by native_decide, by native_decide⟩)
      (.cons (Or.inl ⟨by native_decide, by native_decide⟩)
        (.cons (Or.inl ⟨by native_decide, by native_decide⟩) (.nil startTriangle)))
  · native_decide
  · native_decide
example : ValidEulerTour (Link (graphOfEnds 2 4 endsIdentity4)) (rIdentity4.decodeVertex startIdentity4)
    (rIdentity4.decodeTour (hierholzer rIdentity4 startIdentity4).ret) := by
  have hret : (hierholzer rIdentity4 startIdentity4).ret =
      ({ start := startIdentity4,
          steps := [(edgeIdentity0, vertexIdentity1), (edgeIdentity1, startIdentity4),
            (edgeIdentity2, vertexIdentity1), (edgeIdentity3, startIdentity4)] } :
        IndexedTour rIdentity4.n rIdentity4.m) := by native_decide
  rw [hret]
  apply rIdentity4.validEulerTour_of_dense
  · exact .cons (Or.inl ⟨by native_decide, by native_decide⟩)
      (.cons (Or.inr ⟨by native_decide, by native_decide⟩)
        (.cons (Or.inl ⟨by native_decide, by native_decide⟩)
          (.cons (Or.inr ⟨by native_decide, by native_decide⟩) (.nil startIdentity4))))
  · native_decide
  · native_decide

end Benchmarks.Hierholzer.Mathlib.Stress
