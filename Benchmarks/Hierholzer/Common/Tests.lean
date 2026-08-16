module

public import Benchmarks.Hierholzer.Common.Cost
public import Benchmarks.Hierholzer.Common.Tour

/-!
# Graph-free checks for the frozen Common layer
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Common.Tests

open Cslib.Algorithms.Lean
open Benchmarks.Hierholzer.Common

-- Cost ledger: zero, every primitive basis event, scalar totals, and bind addition.
example : Cost.total 0 = 0 := by simp

example : (Event.initWrite 0).time = { (0 : Cost) with initWrite := 1 } := by simp
example : (Event.incidenceRead 0).time = { (0 : Cost) with incidenceRead := 1 } := by simp
example : (Event.endpointRead 0).time = { (0 : Cost) with endpointRead := 1 } := by simp
example : (Event.usedRead 0).time = { (0 : Cost) with usedRead := 1 } := by simp
example : (Event.usedWrite 0).time = { (0 : Cost) with usedWrite := 1 } := by simp
example : (Event.cursorRead 0).time = { (0 : Cost) with cursorRead := 1 } := by simp
example : (Event.cursorWrite 0).time = { (0 : Cost) with cursorWrite := 1 } := by simp
example : (Event.stackControl 0).time = { (0 : Cost) with stackControl := 1 } := by simp
example : (Event.stackRead 0).time = { (0 : Cost) with stackRead := 1 } := by simp
example : (Event.stackWrite 0).time = { (0 : Cost) with stackWrite := 1 } := by simp
example : (Event.outputControl 0).time = { (0 : Cost) with outputControl := 1 } := by simp
example : (Event.outputRead 0).time = { (0 : Cost) with outputRead := 1 } := by simp
example : (Event.outputWrite 0).time = { (0 : Cost) with outputWrite := 1 } := by simp

example : (Event.indexEq 2 2).ret = true := by decide
example : (Event.indexLt 2 3).ret = true := by decide
example : (Event.indexSucc 2).ret = 3 := by decide
example : (Event.indexAdd 2 3).ret = 5 := by decide
example : (Event.indexEq 2 2).time = { (0 : Cost) with indexOp := 1 } := by simp
example : (Event.indexLt 2 3).time = { (0 : Cost) with indexOp := 1 } := by simp
example : (Event.indexSucc 2).time = { (0 : Cost) with indexOp := 1 } := by simp
example : (Event.indexAdd 2 3).time = { (0 : Cost) with indexOp := 1 } := by simp
example : Cost.total (Event.indexEq 2 2).time = 1 := by simp [Cost.total]
example : Cost.total (Event.indexLt 2 3).time = 1 := by simp [Cost.total]
example : Cost.total (Event.indexSucc 2).time = 1 := by simp [Cost.total]
example : Cost.total (Event.indexAdd 2 3).time = 1 := by simp [Cost.total]

example :
    (do
      let value ← Event.usedRead 4
      Event.usedWrite (value + 1)).time =
      { (0 : Cost) with usedRead := 1, usedWrite := 1 } := by
  simp
  ext <;> simp

example : Cost.total (Event.stackPush 2 ()).time = 3 := by simp [Cost.total]
example : Cost.total (Event.stackPop 2 ()).time = 3 := by simp [Cost.total]
example : Cost.total (Event.outputStoreStart ()).time = 1 := by simp [Cost.total]
example : Cost.total (Event.outputEmitStep ()).time = 3 := by simp [Cost.total]
example : Cost.total (Event.outputCopyStep ()).time = 5 := by simp [Cost.total]
example : (Event.stackCheck ()).time = { (0 : Cost) with stackControl := 1 } := by simp
example : (Event.stackPush 2 ()).time =
    { (0 : Cost) with stackControl := 1, stackWrite := 2 } := by simp
example : (Event.stackPeek 2 ()).time =
    { (0 : Cost) with stackControl := 1, stackRead := 2 } := by simp
example : (Event.stackPop 2 ()).time =
    { (0 : Cost) with stackControl := 1, stackRead := 2 } := by simp
example : (Event.outputStoreStart ()).time = { (0 : Cost) with outputWrite := 1 } := by simp
example : (Event.outputEmitStep ()).time =
    { (0 : Cost) with outputControl := 1, outputWrite := 2 } := by simp
example : (Event.outputCopyStep ()).time =
    { (0 : Cost) with outputControl := 1, outputRead := 2, outputWrite := 2 } := by simp

-- Decoder: start first, then destinations; edge and step order are unchanged.
private def sampleIndexed : IndexedTour 3 2 :=
  { start := 0
    steps := [(0, 1), (1, 2)] }

example :
    (sampleIndexed.decode (Equiv.refl (Fin 3)) (Equiv.refl (Fin 2))).vertices = [0, 1, 2] := rfl

example :
    (sampleIndexed.decode (Equiv.refl (Fin 3)) (Equiv.refl (Fin 2))).edges = [0, 1] := rfl

example :
    (sampleIndexed.decode (Equiv.refl (Fin 3)) (Equiv.refl (Fin 2))).vertices.length = 3 := by
  simp [sampleIndexed]

example :
    (sampleIndexed.decode (Equiv.refl (Fin 3)) (Equiv.refl (Fin 2))).edges.length = 2 := by
  simp [sampleIndexed]

-- `ValidEulerTour`: abstract relations only, including edgeless/loop, duplicate, and coverage cases.
example :
    ValidEulerTour (fun (_ : Fin 0) (_ _ : Fin 1) => True) 0
      ({ vertices := [0], edges := [] } : TourData (Fin 1) (Fin 0)) := by
  constructor
  · decide
  · decide
  · decide
  · simp
  · simp
  · intro edge
    exact Fin.elim0 edge

example :
    ValidEulerTour (fun (_ : Unit) (_ _ : Unit) => True) ()
      ({ vertices := [(), ()], edges := [()] } : TourData Unit Unit) := by
  constructor <;> simp

-- The link clause is sensitive to edge position and to the ordered consecutive endpoints.
example :
    ValidEulerTour
      (fun (edge source destination : Fin 2) =>
        (edge = 0 ∧ source = 0 ∧ destination = 1) ∨
          (edge = 1 ∧ source = 1 ∧ destination = 0))
      0 ({ vertices := [0, 1, 0], edges := [0, 1] } : TourData (Fin 2) (Fin 2)) := by
  constructor <;> simp

example :
    ¬ ValidEulerTour
      (fun (edge source destination : Fin 2) =>
        (edge = 0 ∧ source = 0 ∧ destination = 1) ∨
          (edge = 1 ∧ source = 1 ∧ destination = 0))
      0 ({ vertices := [0, 1, 0], edges := [1, 0] } : TourData (Fin 2) (Fin 2)) := by
  intro valid
  have links := valid.links
  simp at links

example :
    ¬ ValidEulerTour (fun (_ : Unit) (_ _ : Unit) => True) ()
      ({ vertices := [(), (), ()], edges := [(), ()] } : TourData Unit Unit) := by
  intro valid
  simpa using valid.edges_nodup

example :
    ¬ ValidEulerTour (fun (_ : Bool) (_ _ : Unit) => True) ()
      ({ vertices := [(), ()], edges := [false] } : TourData Unit Bool) := by
  intro valid
  have missing := valid.edges_complete true
  simp at missing

end Benchmarks.Hierholzer.Common.Tests
