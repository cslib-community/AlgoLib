import Benchmarks.Hierholzer.GraphLib.Correctness
import Benchmarks.Hierholzer.GraphLib.Resource
import Mathlib.Logic.Equiv.Fintype

/-!
# Mandatory supplied-representation stress cases

The fixtures below build small GraphLib graphs from bundled actual edges and supply explicit
filtered dart arrays.  Representation construction is outside the timed boundary.
-/

set_option autoImplicit false

namespace Benchmarks.Hierholzer.GraphLib.Stress

open Cslib.Algorithms.Lean
open Benchmarks.Hierholzer.Common
open scoped _root_.GraphLib

/-- Bundled edge used by a finite supplied fixture. -/
def suppliedEdge {n m : Nat} {tagType : Type*} (tag : Fin m → tagType)
    (ends : Fin m → Fin n × Fin n) (edgeId : Fin m) :
    _root_.GraphLib.Edge (Fin n) tagType :=
  { tag := tag edgeId, endpoints := s((ends edgeId).1, (ends edgeId).2) }

/-- Mathematical GraphLib graph underlying a supplied fixture. -/
def suppliedGraph {n m : Nat} {tagType : Type*} (tag : Fin m → tagType)
    (ends : Fin m → Fin n × Fin n) : _root_.GraphLib.Graph (Fin n) tagType where
  vertexSet := Set.univ
  edgeSet := Set.range (suppliedEdge tag ends)
  endpoints_mem := by simp

def suppliedEdgeEmbedding {n m : Nat} {tagType : Type*} [DecidableEq tagType]
    (tag : Fin m → tagType) (ends : Fin m → Fin n × Fin n)
    (hinjective : Function.Injective (suppliedEdge tag ends)) :
    Fin m ↪ _root_.GraphLib.Edge (Fin n) tagType :=
  ⟨suppliedEdge tag ends, hinjective⟩

instance suppliedFiniteEdges {n m : Nat} {tagType : Type*}
    (tag : Fin m → tagType) (ends : Fin m → Fin n × Fin n) :
    Finite (ActualEdge (suppliedGraph tag ends)) := by
  apply Finite.of_surjective
    (fun edgeId : Fin m =>
      ⟨suppliedEdge tag ends edgeId, Set.mem_range_self edgeId⟩)
  rintro ⟨edge, edgeId, rfl⟩
  exact ⟨edgeId, rfl⟩

def suppliedDecodeVertex {n m : Nat} {tagType : Type*} (tag : Fin m → tagType)
    (ends : Fin m → Fin n × Fin n) :
    Fin n ≃ Vertex (suppliedGraph tag ends) :=
  (Equiv.Set.univ _).symm

def suppliedDecodeEdge {n m : Nat} {tagType : Type*} [DecidableEq tagType]
    (tag : Fin m → tagType) (ends : Fin m → Fin n × Fin n)
    (hinjective : Function.Injective (suppliedEdge tag ends)) :
    Fin m ≃ ActualEdge (suppliedGraph tag ends) :=
  (suppliedEdgeEmbedding tag ends hinjective).toEquivRange

def allDarts (m : Nat) : List (Dart m) :=
  (List.finRange m).flatMap fun edgeId => [(edgeId, false), (edgeId, true)]

def suppliedDartVertex {n m : Nat} (ends : Fin m → Fin n × Fin n)
    (dart : Dart m) : Fin n :=
  if dart.2 then (ends dart.1).2 else (ends dart.1).1

def suppliedData {n m : Nat} (ends : Fin m → Fin n × Fin n) :
    IncidenceEnumeration n m where
  endpoints := Vector.ofFn ends
  buckets := Vector.ofFn fun vertexId =>
    ((allDarts m).filter fun dart => suppliedDartVertex ends dart = vertexId).toArray

theorem supplied_endpoint_sound {n m : Nat} {tagType : Type*} [DecidableEq tagType]
    (tag : Fin m → tagType) (ends : Fin m → Fin n × Fin n)
    (hinjective : Function.Injective (suppliedEdge tag ends)) (edgeId : Fin m) :
    let storedEnds := vectorGet (suppliedData ends).endpoints edgeId
    Link (suppliedGraph tag ends) (suppliedDecodeEdge tag ends hinjective edgeId)
      (suppliedDecodeVertex tag ends storedEnds.1)
      (suppliedDecodeVertex tag ends storedEnds.2) := by
  dsimp
  constructor
  · exact Set.mem_range_self edgeId
  · have hend :
        ((suppliedEdgeEmbedding tag ends hinjective).toEquivRange edgeId).val.endpoints =
          (suppliedEdge tag ends edgeId).endpoints := by
      exact congrArg (fun edge : ActualEdge (suppliedGraph tag ends) => edge.val.endpoints)
        (Function.Embedding.toEquivRange_apply
          (f := suppliedEdgeEmbedding tag ends hinjective) edgeId)
    exact hend.trans (by
      have hvertex (vertexId : Fin n) :
          (suppliedDecodeVertex tag ends vertexId).val = vertexId := rfl
      have hstored : vectorGet (suppliedData ends).endpoints edgeId = ends edgeId := by
        simp [suppliedData]
      rw [hstored]
      change s((ends edgeId).1, (ends edgeId).2) =
        s((suppliedDecodeVertex tag ends (ends edgeId).1).val,
          (suppliedDecodeVertex tag ends (ends edgeId).2).val)
      rw [hvertex, hvertex])

def suppliedRepresentation {n m : Nat} {tagType : Type*} [DecidableEq tagType]
    (tag : Fin m → tagType) (ends : Fin m → Fin n × Fin n)
    (hinjective : Function.Injective (suppliedEdge tag ends))
    (hrep : (suppliedData ends).Represents (suppliedGraph tag ends)
      (suppliedDecodeVertex tag ends) (suppliedDecodeEdge tag ends hinjective)) :
    CertifiedIncidenceRepresentation (suppliedGraph tag ends) where
  n := n
  m := m
  data := suppliedData ends
  decodeVertex := suppliedDecodeVertex tag ends
  decodeEdge := suppliedDecodeEdge tag ends hinjective
  represents := hrep
  n_eq := by
    rw [← natCard_vertex]
    simpa using Nat.card_congr (suppliedDecodeVertex tag ends)
  m_eq := by
    rw [edgeCount]
    change m = Set.ncard (Set.range (suppliedEdge tag ends))
    rw [Set.ncard_range_of_injective hinjective]
    simp

def uniqueTags {m : Nat} : Fin m → Fin m := id

theorem uniqueTags_edge_injective {n m : Nat} (ends : Fin m → Fin n × Fin n) :
    Function.Injective (suppliedEdge uniqueTags ends) := by
  intro left right heq
  exact congrArg _root_.GraphLib.Edge.tag heq

def endsEmpty : Fin 0 → Fin 1 × Fin 1 := Fin.elim0
def endsOneLoop : Fin 1 → Fin 1 × Fin 1 := fun _ => (0, 0)
def endsTwoLoops : Fin 2 → Fin 1 × Fin 1 := fun _ => (0, 0)
def endsParallel : Fin 2 → Fin 2 × Fin 2 := fun _ => (0, 1)
def endsComponentIsolate : Fin 2 → Fin 3 × Fin 3 := fun _ => (0, 1)
def endsTriangle : Fin 3 → Fin 3 × Fin 3 := fun edgeId =>
  Fin.cases (0, 1) (Fin.cases (1, 2) (fun _ => (2, 0))) edgeId
def reusedTag : Fin 3 → Unit := fun _ => ()

theorem reusedTag_edge_injective :
    Function.Injective (suppliedEdge reusedTag endsTriangle) := by decide

def repEmpty : CertifiedIncidenceRepresentation (suppliedGraph uniqueTags endsEmpty) :=
  suppliedRepresentation uniqueTags endsEmpty (uniqueTags_edge_injective endsEmpty) (by
    exact ⟨supplied_endpoint_sound _ _ _, by decide, by decide⟩)

def repOneLoop : CertifiedIncidenceRepresentation (suppliedGraph uniqueTags endsOneLoop) :=
  suppliedRepresentation uniqueTags endsOneLoop (uniqueTags_edge_injective endsOneLoop)
    (by exact ⟨supplied_endpoint_sound _ _ _, by decide, by decide⟩)

def repTwoLoops : CertifiedIncidenceRepresentation (suppliedGraph uniqueTags endsTwoLoops) :=
  suppliedRepresentation uniqueTags endsTwoLoops (uniqueTags_edge_injective endsTwoLoops)
    (by exact ⟨supplied_endpoint_sound _ _ _, by decide, by decide⟩)

def repParallel : CertifiedIncidenceRepresentation (suppliedGraph uniqueTags endsParallel) :=
  suppliedRepresentation uniqueTags endsParallel (uniqueTags_edge_injective endsParallel)
    (by exact ⟨supplied_endpoint_sound _ _ _, by decide, by decide⟩)

def repComponentIsolate :
    CertifiedIncidenceRepresentation (suppliedGraph uniqueTags endsComponentIsolate) :=
  suppliedRepresentation uniqueTags endsComponentIsolate
    (uniqueTags_edge_injective endsComponentIsolate)
    (by exact ⟨supplied_endpoint_sound _ _ _, by decide, by decide⟩)

def repTriangle : CertifiedIncidenceRepresentation (suppliedGraph uniqueTags endsTriangle) :=
  suppliedRepresentation uniqueTags endsTriangle (uniqueTags_edge_injective endsTriangle)
    (by exact ⟨supplied_endpoint_sound _ _ _, by decide, by decide⟩)

def repReusedTag : CertifiedIncidenceRepresentation (suppliedGraph reusedTag endsTriangle) :=
  suppliedRepresentation reusedTag endsTriangle reusedTag_edge_injective
    (by exact ⟨supplied_endpoint_sound _ _ _, by decide, by decide⟩)

def startEmpty : Fin repEmpty.n := ⟨0, by simp [repEmpty, suppliedRepresentation]⟩
def startOneLoop : Fin repOneLoop.n := ⟨0, by simp [repOneLoop, suppliedRepresentation]⟩
def startTwoLoops : Fin repTwoLoops.n := ⟨0, by simp [repTwoLoops, suppliedRepresentation]⟩
def startParallel : Fin repParallel.n := ⟨0, by simp [repParallel, suppliedRepresentation]⟩
def startComponentIsolate : Fin repComponentIsolate.n :=
  ⟨0, by simp [repComponentIsolate, suppliedRepresentation]⟩
def startTriangle : Fin repTriangle.n := ⟨0, by simp [repTriangle, suppliedRepresentation]⟩
def startReusedTag : Fin repReusedTag.n :=
  ⟨0, by simp [repReusedTag, suppliedRepresentation]⟩

/-! ## Kernel-checked semantic certificates -/

/-- A closed dense walk that is duplicate-free and covers every dense edge ID decodes to the
frozen six-clause certificate.  This fixture helper does not use Eulerian assumptions: the three
finite lists below are checked directly. -/
theorem valid_of_dense_closed {α β : Type*} {G : _root_.GraphLib.Graph α β}
    [Finite V(G)] [Finite E(G)] (R : CertifiedIncidenceRepresentation G)
    (tour : IndexedTour R.n R.m)
    (hwalk : DenseWalkSteps R tour.start tour.steps tour.start)
    (hnodup : (tour.steps.map Prod.fst).Nodup)
    (hcomplete : ∀ edgeId : Fin R.m, edgeId ∈ tour.steps.map Prod.fst) :
    ValidEulerTour (Link G) (R.decodeVertex tour.start)
      (tour.decode R.decodeVertex R.decodeEdge) := by
  constructor
  · simp
  · simp
  · rw [show (tour.decode R.decodeVertex R.decodeEdge).vertices =
        (tour.start :: tour.steps.map Prod.snd).map R.decodeVertex by
      simp [IndexedTour.decode]]
    rw [List.getLast?_map, DenseWalkSteps.vertices_getLast hwalk]
    rfl
  · exact hwalk.decoded_links
  · exact (IndexedTour.decode_edges_nodup_iff tour R.decodeVertex R.decodeEdge).mpr hnodup
  · exact (IndexedTour.decode_edges_complete_iff tour R.decodeVertex R.decodeEdge).mpr hcomplete

def expectedEmpty : IndexedTour 1 0 :=
  { start := 0, steps := [] }

def expectedOneLoop : IndexedTour 1 1 :=
  { start := 0, steps := [(0, 0)] }

def expectedTwoLoops : IndexedTour 1 2 :=
  { start := 0, steps := [(0, 0), (1, 0)] }

def expectedParallel : IndexedTour 2 2 :=
  { start := 0, steps := [(0, 1), (1, 0)] }

def expectedComponentIsolate : IndexedTour 3 2 :=
  { start := 0, steps := [(0, 1), (1, 0)] }

def expectedTriangle : IndexedTour 3 3 :=
  { start := 0, steps := [(0, 1), (1, 2), (2, 0)] }

def expectedReusedTag : IndexedTour 3 3 :=
  { start := 0, steps := [(0, 1), (1, 2), (2, 0)] }

theorem empty_representation_valid :
    repEmpty.data.Represents (suppliedGraph uniqueTags endsEmpty)
      repEmpty.decodeVertex repEmpty.decodeEdge := repEmpty.represents

theorem oneLoop_representation_valid :
    repOneLoop.data.Represents (suppliedGraph uniqueTags endsOneLoop)
      repOneLoop.decodeVertex repOneLoop.decodeEdge := repOneLoop.represents

theorem twoLoops_representation_valid :
    repTwoLoops.data.Represents (suppliedGraph uniqueTags endsTwoLoops)
      repTwoLoops.decodeVertex repTwoLoops.decodeEdge := repTwoLoops.represents

theorem parallel_representation_valid :
    repParallel.data.Represents (suppliedGraph uniqueTags endsParallel)
      repParallel.decodeVertex repParallel.decodeEdge := repParallel.represents

theorem componentIsolate_representation_valid :
    repComponentIsolate.data.Represents (suppliedGraph uniqueTags endsComponentIsolate)
      repComponentIsolate.decodeVertex repComponentIsolate.decodeEdge :=
  repComponentIsolate.represents

theorem triangle_representation_valid :
    repTriangle.data.Represents (suppliedGraph uniqueTags endsTriangle)
      repTriangle.decodeVertex repTriangle.decodeEdge := repTriangle.represents

theorem reusedTag_representation_valid :
    repReusedTag.data.Represents (suppliedGraph reusedTag endsTriangle)
      repReusedTag.decodeVertex repReusedTag.decodeEdge := repReusedTag.represents

theorem empty_result : (hierholzer repEmpty startEmpty).ret = expectedEmpty := by decide
theorem oneLoop_result : (hierholzer repOneLoop startOneLoop).ret = expectedOneLoop := by decide
theorem twoLoops_result : (hierholzer repTwoLoops startTwoLoops).ret = expectedTwoLoops := by decide
theorem parallel_result : (hierholzer repParallel startParallel).ret = expectedParallel := by decide
theorem componentIsolate_result :
    (hierholzer repComponentIsolate startComponentIsolate).ret = expectedComponentIsolate := by decide
theorem triangle_result : (hierholzer repTriangle startTriangle).ret = expectedTriangle := by decide
theorem reusedTag_result :
    (hierholzer repReusedTag startReusedTag).ret = expectedReusedTag := by decide

theorem empty_walk : DenseWalkSteps repEmpty expectedEmpty.start expectedEmpty.steps
    expectedEmpty.start := by exact .nil _

theorem oneLoop_walk : DenseWalkSteps repOneLoop expectedOneLoop.start expectedOneLoop.steps
    expectedOneLoop.start := by
  exact .cons (by simpa [DenseLink, expectedOneLoop, startOneLoop, repOneLoop,
    suppliedRepresentation, suppliedData, endsOneLoop] using repOneLoop.dart_link ((0 : Fin 1), false))
    (.nil _)

theorem twoLoops_walk : DenseWalkSteps repTwoLoops expectedTwoLoops.start expectedTwoLoops.steps
    expectedTwoLoops.start := by
  exact .cons (by simpa [DenseLink, expectedTwoLoops, startTwoLoops, repTwoLoops,
    suppliedRepresentation, suppliedData, endsTwoLoops] using repTwoLoops.dart_link ((0 : Fin 2), false))
    (.cons (by simpa [DenseLink, expectedTwoLoops, startTwoLoops, repTwoLoops,
      suppliedRepresentation, suppliedData, endsTwoLoops] using
        repTwoLoops.dart_link ((1 : Fin 2), false)) (.nil _))

theorem parallel_walk : DenseWalkSteps repParallel expectedParallel.start expectedParallel.steps
    expectedParallel.start := by
  exact .cons (by simpa [DenseLink, expectedParallel, startParallel, repParallel,
    suppliedRepresentation, suppliedData, endsParallel] using
      repParallel.dart_link ((0 : Fin 2), false))
    (.cons (by simpa [DenseLink, expectedParallel, startParallel, repParallel,
      suppliedRepresentation, suppliedData, endsParallel] using
        repParallel.dart_link ((1 : Fin 2), true)) (.nil _))

theorem componentIsolate_walk :
    DenseWalkSteps repComponentIsolate expectedComponentIsolate.start
      expectedComponentIsolate.steps expectedComponentIsolate.start := by
  exact .cons (by simpa [DenseLink, expectedComponentIsolate, startComponentIsolate,
    repComponentIsolate, suppliedRepresentation, suppliedData, endsComponentIsolate] using
      repComponentIsolate.dart_link ((0 : Fin 2), false))
    (.cons (by simpa [DenseLink, expectedComponentIsolate, startComponentIsolate,
      repComponentIsolate, suppliedRepresentation, suppliedData, endsComponentIsolate] using
        repComponentIsolate.dart_link ((1 : Fin 2), true)) (.nil _))

theorem triangle_walk : DenseWalkSteps repTriangle expectedTriangle.start expectedTriangle.steps
    expectedTriangle.start := by
  exact .cons (by simpa [DenseLink, expectedTriangle, startTriangle, repTriangle,
    suppliedRepresentation, suppliedData, endsTriangle] using
      repTriangle.dart_link ((0 : Fin 3), false))
    (.cons (by simpa [DenseLink, expectedTriangle, startTriangle, repTriangle,
      suppliedRepresentation, suppliedData, endsTriangle] using
        repTriangle.dart_link ((1 : Fin 3), false))
      (.cons (by simpa [DenseLink, expectedTriangle, startTriangle, repTriangle,
        suppliedRepresentation, suppliedData, endsTriangle] using
          repTriangle.dart_link ((2 : Fin 3), false)) (.nil _)))

theorem reusedTag_walk : DenseWalkSteps repReusedTag expectedReusedTag.start
    expectedReusedTag.steps expectedReusedTag.start := by
  exact .cons (by simpa [DenseLink, expectedReusedTag, startReusedTag, repReusedTag,
    suppliedRepresentation, suppliedData, endsTriangle] using
      repReusedTag.dart_link ((0 : Fin 3), false))
    (.cons (by simpa [DenseLink, expectedReusedTag, startReusedTag, repReusedTag,
      suppliedRepresentation, suppliedData, endsTriangle] using
        repReusedTag.dart_link ((1 : Fin 3), false))
      (.cons (by simpa [DenseLink, expectedReusedTag, startReusedTag, repReusedTag,
        suppliedRepresentation, suppliedData, endsTriangle] using
          repReusedTag.dart_link ((2 : Fin 3), false)) (.nil _)))

theorem empty_decoded_valid :
    ValidEulerTour (Link (suppliedGraph uniqueTags endsEmpty))
      (repEmpty.decodeVertex startEmpty)
      ((hierholzer repEmpty startEmpty).ret.decode repEmpty.decodeVertex repEmpty.decodeEdge) := by
  rw [empty_result]
  exact valid_of_dense_closed repEmpty expectedEmpty empty_walk (by decide) (by decide)

theorem oneLoop_decoded_valid :
    ValidEulerTour (Link (suppliedGraph uniqueTags endsOneLoop))
      (repOneLoop.decodeVertex startOneLoop)
      ((hierholzer repOneLoop startOneLoop).ret.decode
        repOneLoop.decodeVertex repOneLoop.decodeEdge) := by
  rw [oneLoop_result]
  exact valid_of_dense_closed repOneLoop expectedOneLoop oneLoop_walk (by decide) (by decide)

theorem twoLoops_decoded_valid :
    ValidEulerTour (Link (suppliedGraph uniqueTags endsTwoLoops))
      (repTwoLoops.decodeVertex startTwoLoops)
      ((hierholzer repTwoLoops startTwoLoops).ret.decode
        repTwoLoops.decodeVertex repTwoLoops.decodeEdge) := by
  rw [twoLoops_result]
  exact valid_of_dense_closed repTwoLoops expectedTwoLoops twoLoops_walk (by decide) (by decide)

theorem parallel_decoded_valid :
    ValidEulerTour (Link (suppliedGraph uniqueTags endsParallel))
      (repParallel.decodeVertex startParallel)
      ((hierholzer repParallel startParallel).ret.decode
        repParallel.decodeVertex repParallel.decodeEdge) := by
  rw [parallel_result]
  exact valid_of_dense_closed repParallel expectedParallel parallel_walk (by decide) (by decide)

theorem componentIsolate_decoded_valid :
    ValidEulerTour (Link (suppliedGraph uniqueTags endsComponentIsolate))
      (repComponentIsolate.decodeVertex startComponentIsolate)
      ((hierholzer repComponentIsolate startComponentIsolate).ret.decode
        repComponentIsolate.decodeVertex repComponentIsolate.decodeEdge) := by
  rw [componentIsolate_result]
  exact valid_of_dense_closed repComponentIsolate expectedComponentIsolate
    componentIsolate_walk (by decide) (by decide)

theorem triangle_decoded_valid :
    ValidEulerTour (Link (suppliedGraph uniqueTags endsTriangle))
      (repTriangle.decodeVertex startTriangle)
      ((hierholzer repTriangle startTriangle).ret.decode
        repTriangle.decodeVertex repTriangle.decodeEdge) := by
  rw [triangle_result]
  exact valid_of_dense_closed repTriangle expectedTriangle triangle_walk (by decide) (by decide)

theorem reusedTag_decoded_valid :
    ValidEulerTour (Link (suppliedGraph reusedTag endsTriangle))
      (repReusedTag.decodeVertex startReusedTag)
      ((hierholzer repReusedTag startReusedTag).ret.decode
        repReusedTag.decodeVertex repReusedTag.decodeEdge) := by
  rw [reusedTag_result]
  exact valid_of_dense_closed repReusedTag expectedReusedTag reusedTag_walk (by decide) (by decide)

/-! ## Exact full cost vectors and concrete scalar bounds -/

def costEmpty : Cost :=
  { initWrite := 1, incidenceRead := 2, endpointRead := 0, usedRead := 0,
    usedWrite := 0, cursorRead := 1, cursorWrite := 0, indexOp := 2,
    stackControl := 4, stackRead := 6, stackWrite := 3, outputControl := 0,
    outputRead := 0, outputWrite := 1 }

def costOneLoop : Cost :=
  { initWrite := 2, incidenceRead := 10, endpointRead := 2, usedRead := 2,
    usedWrite := 1, cursorRead := 3, cursorWrite := 2, indexOp := 6,
    stackControl := 10, stackRead := 15, stackWrite := 6, outputControl := 1,
    outputRead := 0, outputWrite := 3 }

def costTwoLoops : Cost :=
  { initWrite := 3, incidenceRead := 18, endpointRead := 4, usedRead := 4,
    usedWrite := 2, cursorRead := 5, cursorWrite := 4, indexOp := 10,
    stackControl := 16, stackRead := 24, stackWrite := 9, outputControl := 2,
    outputRead := 0, outputWrite := 5 }

def costParallel : Cost :=
  { costTwoLoops with initWrite := 4 }

def costComponentIsolate : Cost :=
  { costTwoLoops with initWrite := 5 }

def costTriangle : Cost :=
  { initWrite := 6, incidenceRead := 26, endpointRead := 6, usedRead := 6,
    usedWrite := 3, cursorRead := 7, cursorWrite := 6, indexOp := 14,
    stackControl := 22, stackRead := 33, stackWrite := 12, outputControl := 3,
    outputRead := 0, outputWrite := 7 }

theorem empty_cost : (hierholzer repEmpty startEmpty).time = costEmpty := by rfl
theorem oneLoop_cost : (hierholzer repOneLoop startOneLoop).time = costOneLoop := by rfl
theorem twoLoops_cost : (hierholzer repTwoLoops startTwoLoops).time = costTwoLoops := by rfl
theorem parallel_cost : (hierholzer repParallel startParallel).time = costParallel := by rfl
theorem componentIsolate_cost :
    (hierholzer repComponentIsolate startComponentIsolate).time = costComponentIsolate := by rfl
theorem triangle_cost : (hierholzer repTriangle startTriangle).time = costTriangle := by rfl
theorem reusedTag_cost : (hierholzer repReusedTag startReusedTag).time = costTriangle := by rfl

theorem empty_concrete_bound : Cost.total (hierholzer repEmpty startEmpty).time = 20 ∧
    Cost.total (hierholzer repEmpty startEmpty).time ≤
      C * (repEmpty.n + repEmpty.m + 1) := by decide
theorem oneLoop_concrete_bound : Cost.total (hierholzer repOneLoop startOneLoop).time = 63 ∧
    Cost.total (hierholzer repOneLoop startOneLoop).time ≤
      C * (repOneLoop.n + repOneLoop.m + 1) := by decide
theorem twoLoops_concrete_bound : Cost.total (hierholzer repTwoLoops startTwoLoops).time = 106 ∧
    Cost.total (hierholzer repTwoLoops startTwoLoops).time ≤
      C * (repTwoLoops.n + repTwoLoops.m + 1) := by decide
theorem parallel_concrete_bound : Cost.total (hierholzer repParallel startParallel).time = 107 ∧
    Cost.total (hierholzer repParallel startParallel).time ≤
      C * (repParallel.n + repParallel.m + 1) := by decide
theorem componentIsolate_concrete_bound :
    Cost.total (hierholzer repComponentIsolate startComponentIsolate).time = 108 ∧
      Cost.total (hierholzer repComponentIsolate startComponentIsolate).time ≤
        C * (repComponentIsolate.n + repComponentIsolate.m + 1) := by decide
theorem triangle_concrete_bound : Cost.total (hierholzer repTriangle startTriangle).time = 151 ∧
    Cost.total (hierholzer repTriangle startTriangle).time ≤
      C * (repTriangle.n + repTriangle.m + 1) := by decide
theorem reusedTag_concrete_bound :
    Cost.total (hierholzer repReusedTag startReusedTag).time = 151 ∧
      Cost.total (hierholzer repReusedTag startReusedTag).time ≤
        C * (repReusedTag.n + repReusedTag.m + 1) := by decide

#eval (hierholzer repEmpty startEmpty).ret
#eval (hierholzer repOneLoop startOneLoop).ret
#eval (hierholzer repTwoLoops startTwoLoops).ret
#eval (hierholzer repParallel startParallel).ret
#eval (hierholzer repComponentIsolate startComponentIsolate).ret
#eval (hierholzer repTriangle startTriangle).ret
#eval (hierholzer repReusedTag startReusedTag).ret

#eval (hierholzer repEmpty startEmpty).time
#eval (hierholzer repOneLoop startOneLoop).time
#eval (hierholzer repTwoLoops startTwoLoops).time
#eval (hierholzer repParallel startParallel).time
#eval (hierholzer repComponentIsolate startComponentIsolate).time
#eval (hierholzer repTriangle startTriangle).time
#eval (hierholzer repReusedTag startReusedTag).time

end Benchmarks.Hierholzer.GraphLib.Stress
