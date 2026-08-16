import Benchmarks.Hierholzer.GraphLib.Representation

/-!
# Timed iterative Hierholzer core

The core uses the standard stack/backtracking algorithm.  Per-edge used flags and per-vertex
cursors are linearly threaded persistent arrays.  Consing a step when its frame is popped already
builds the frozen traversal order, so no post-clock reversal is needed.
-/

set_option autoImplicit false

namespace Benchmarks.Hierholzer.GraphLib

open Cslib.Algorithms.Lean
open Benchmarks.Hierholzer.Common
open scoped _root_.GraphLib

universe u v w

variable {α : Type u} {β : Type v}

/-- A fixed three-word stack frame: vertex ID, option tag, and optional incoming edge ID. -/
structure Frame (n m : Nat) where
  vertex : Fin n
  incoming : Option (Fin m)
deriving DecidableEq, Repr

/-- Linearly threaded algorithm state.  Proof fields are erased. -/
structure CoreState (n m : Nat) where
  used : Vector Bool m
  cursors : Vector Nat n
  stack : List (Frame n m)
  outputSteps : List (Fin m × Fin n)

namespace CoreState

def usedAt {n m : Nat} (state : CoreState n m) (edgeId : Fin m) : Bool :=
  vectorGet state.used edgeId

def setUsed {n m : Nat} (state : CoreState n m) (edgeId : Fin m) (value : Bool) :
    CoreState n m :=
  { state with
    used := state.used.set edgeId.1 value edgeId.2 }

def cursorAt {n m : Nat} (state : CoreState n m) (vertexId : Fin n) : Nat :=
  vectorGet state.cursors vertexId

def setCursor {n m : Nat} (state : CoreState n m) (vertexId : Fin n) (value : Nat) :
    CoreState n m :=
  { state with
    cursors := state.cursors.set vertexId.1 value vertexId.2 }

@[simp] theorem usedAt_setUsed_self {n m : Nat} (state : CoreState n m)
    (edgeId : Fin m) (value : Bool) : (state.setUsed edgeId value).usedAt edgeId = value := by
  change (state.used.set edgeId.1 value edgeId.2)[edgeId.1] = value
  simp

@[simp] theorem cursorAt_setCursor_self {n m : Nat} (state : CoreState n m)
    (vertexId : Fin n) (value : Nat) :
    (state.setCursor vertexId value).cursorAt vertexId = value := by
  change (state.cursors.set vertexId.1 value vertexId.2)[vertexId.1] = value
  simp

end CoreState

/-- A one-call cache of an incidence-array pointer and its length.  The proof is erased. -/
structure BucketView (m : Nat) where
  entries : Array (Dart m)
  size : Nat
  size_eq : size = entries.size

/-- Preallocated, per-word-charged vector initialization.  The initial vector has logical length
zero but reserves the final array capacity, so every subsequent linearly threaded `push` fits.
-/
def initVectorLoop {γ : Type w} (value : γ) :
    (remaining : Nat) → {built : Nat} → Vector γ built → TimeM Cost (Vector γ (built + remaining))
  | 0, _, result => pure (result.cast (by omega))
  | remaining + 1, _, result => do
      let value ← Event.initWrite value
      let result ← initVectorLoop value remaining (result.push value)
      pure (result.cast (by omega))

/-- Reserve capacity first, then initialize exactly `size` logical words. -/
def initVector {γ : Type w} (size : Nat) (value : γ) : TimeM Cost (Vector γ size) :=
  let empty : Vector γ 0 := ⟨Array.mkEmpty size, by simp⟩
  do
    let result ← initVectorLoop value size empty
    pure (result.cast (Nat.zero_add size))

@[simp] theorem time_initVectorLoop {γ : Type w} (value : γ) (remaining : Nat)
    {built : Nat} (result : Vector γ built) :
    (initVectorLoop value remaining result).time =
      { (0 : Cost) with initWrite := remaining } := by
  induction remaining generalizing built with
  | zero =>
      simp [initVectorLoop]
      ext <;> simp
  | succ remaining ih =>
      simp [initVectorLoop, ih]
      ext <;> simp [Nat.add_comm]

@[simp] theorem time_initVector {γ : Type w} (size : Nat) (value : γ) :
    (initVector size value).time = { (0 : Cost) with initWrite := size } := by
  simp [initVector, time_initVectorLoop]

/-- Initialize flags, cursors, and the root stack frame. -/
def initializeState {n m : Nat} (start : Fin n) : TimeM Cost (CoreState n m) := do
  let used ← initVector m false
  let cursors ← initVector n 0
  let root ← Event.stackPush 3 ({ vertex := start, incoming := none } : Frame n m)
  pure
    { used := used
      cursors := cursors
      stack := [root]
      outputSteps := [] }

/-- Scan one bucket from its persistent cursor.  `dartFuel` is a global structural termination
budget; it decreases exactly when a dart is inspected and is returned to the caller.
-/
def scanBucket {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]
    (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (bucket : BucketView R.m) (fuel position : Nat) (state : CoreState R.n R.m) :
    TimeM Cost (Option (Dart R.m) × CoreState R.n R.m × Nat) :=
  match fuel with
  | 0 => pure (none, state, 0)
  | dartFuel + 1 =>
      let boundsTest := Event.indexLt position bucket.size
      match hBounds : boundsTest.ret with
      | false => do
          let _ ← boundsTest
          -- Return the original word instead of reconstructing it with an unticked increment.
          pure (none, state, fuel)
      | true => do
          let _ ← boundsTest
          have hposition : position < bucket.entries.size := by
            have hlt : position < bucket.size := by
              simpa [Event.indexLt] using of_decide_eq_true hBounds
            simpa [bucket.size_eq] using hlt
          let dart ← Event.incidenceRead bucket.entries[position]
          let dart ← Event.incidenceRead dart
          let nextPosition ← Event.indexSucc position
          let state ← Event.cursorWrite (state.setCursor vertexId nextPosition)
          let wasUsed ← Event.usedRead (state.usedAt dart.1)
          match wasUsed with
          | false => pure (some dart, state, dartFuel)
          | true => scanBucket R vertexId bucket dartFuel nextPosition state

/-- Read one bucket pointer, cache its length, read the persistent cursor, and scan to the next
unused actual edge. -/
def nextIncident {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]
    (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (dartFuel : Nat) (state : CoreState R.n R.m) :
    TimeM Cost (Option (Dart R.m) × CoreState R.n R.m × Nat) := do
  let bucketEvent := Event.incidenceRead (R.bucket vertexId)
  let _ ← bucketEvent
  let bucket := bucketEvent.ret
  let bucketSizeEvent := Event.incidenceRead bucket.size
  let _ ← bucketSizeEvent
  let bucketSize := bucketSizeEvent.ret
  let bucket : BucketView R.m := ⟨bucket, bucketSize, by simp [bucketSize, bucketSizeEvent]⟩
  let position ← Event.cursorRead (state.cursorAt vertexId)
  scanBucket R vertexId bucket dartFuel position state

/-- Standard stack growth/backtracking.  `stepFuel` is a structural termination guard initialized
to `2m+1`; the global dart budget is threaded through all bucket scans.
-/
def runLoop {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]
    (R : CertifiedIncidenceRepresentation G) :
    Nat → Nat → CoreState R.n R.m → TimeM Cost (CoreState R.n R.m × Nat)
  | 0, dartFuel, state => pure (state, dartFuel)
  | stepFuel + 1, dartFuel, state => do
      let _ ← Event.stackCheck state.stack.isEmpty
      match state.stack with
      | [] => pure (state, dartFuel)
      | frame :: rest =>
          let frame ← Event.stackPeek 3 frame
          let scan ← nextIncident R frame.vertex dartFuel state
          match scan.1 with
          | some dart =>
              let state ← Event.usedWrite (scan.2.1.setUsed dart.1 true)
              let ends ← Event.endpointRead (R.ends dart.1)
              let ends ← Event.endpointRead ends
              let other := if dart.2 then ends.1 else ends.2
              let nextFrame : Frame R.n R.m := { vertex := other, incoming := some dart.1 }
              let nextFrame ← Event.stackPush 3 nextFrame
              runLoop R stepFuel scan.2.2 { state with stack := nextFrame :: state.stack }
          | none =>
              let frame ← Event.stackPop 3 frame
              let state := { scan.2.1 with stack := rest }
              match frame.incoming with
              | none => runLoop R stepFuel scan.2.2 state
              | some edgeId =>
                  let step ← Event.outputEmitStep (edgeId, frame.vertex)
                  runLoop R stepFuel scan.2.2
                    { state with outputSteps := step :: state.outputSteps }

/-- Public timed Hierholzer core.  The return shape is exactly the frozen canonical `IndexedTour`.
-/
def hierholzer {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]
    (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    TimeM Cost (IndexedTour R.n R.m) := do
  let state ← initializeState (m := R.m) start
  let dartFuel ← Event.indexAdd R.m R.m
  let stepFuel ← Event.indexAdd dartFuel 1
  let result ← runLoop R stepFuel dartFuel state
  let start ← Event.outputStoreStart start
  pure { start := start, steps := result.1.outputSteps }

end Benchmarks.Hierholzer.GraphLib
