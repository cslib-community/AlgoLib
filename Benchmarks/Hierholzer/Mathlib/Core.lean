module

public import Benchmarks.Hierholzer.Mathlib.Representation

/-!
# Costed array-backed Hierholzer core

This is the standard stack/backtracking form of Hierholzer's algorithm.  Each forward step scans
one previously unscanned dart, marks its actual edge once, and pushes the other endpoint.  An
exhausted top vertex is popped; its incoming `(edge,destination)` step is consed onto the output.
Consing in pop order directly produces traversal order, so no post-clock reversal is hidden.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Cslib.Algorithms.Lean
open Benchmarks.Hierholzer.Common

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

/-- A fixed two-word stack frame. `none` is the bottom/start sentinel. -/
structure Frame (n m : Nat) where
  incoming : Option (Fin m)
  vertex : Fin n
deriving DecidableEq, Repr

/-- Algorithm-owned mutable state, modeled purely with linearly threaded persistent vectors. -/
structure CoreState (n m : Nat) where
  used : Vector Bool m
  cursor : Vector Nat n
  stack : List (Frame n m)
  output : List (Fin m × Fin n)
deriving DecidableEq, Repr

namespace Core

/-- Fixed-size array update through a dense ID; its bound proof is the ID payload itself. -/
def setFin {A : Type*} {n : Nat} (values : Vector A n) (i : Fin n) (value : A) : Vector A n :=
  values.set i.1 value i.2

/-- Charge exactly one initialization event per word of a bulk-created fixed vector. -/
def chargeInitWords {A : Type*} : Nat → A → TimeM Cost A
  | 0, value => pure value
  | k + 1, value => do
      let value ← Event.initWrite value
      chargeInitWords k value

@[simp] theorem chargeInitWords_ret {A : Type*} (k : Nat) (value : A) :
    (chargeInitWords k value).ret = value := by
  induction k with
  | zero => rfl
  | succ k ih => simp [chargeInitWords, ih]

@[simp] theorem chargeInitWords_time {A : Type*} (k : Nat) (value : A) :
    (chargeInitWords k value).time =
      { (0 : Cost) with initWrite := k } := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [chargeInitWords, ih]
      ext <;> simp [Nat.add_comm]

/-- Initialize `m` used flags, `n` cursor words, and the two-word bottom stack frame. -/
def initState (n m : Nat) (start : Fin n) : TimeM Cost (CoreState n m) := do
  let used ← chargeInitWords m (Vector.replicate m false)
  let cursor ← chargeInitWords n (Vector.replicate n 0)
  let stack ← Event.stackPush 2 [({ incoming := none, vertex := start } : Frame n m)]
  pure { used := used, cursor := cursor, stack := stack, output := [] }

@[simp] theorem initState_ret (n m : Nat) (start : Fin n) :
    (initState n m start).ret =
      { used := Vector.replicate m false
        cursor := Vector.replicate n 0
        stack := [({ incoming := none, vertex := start } : Frame n m)]
        output := [] } := by
  simp [initState]

/-- The other endpoint selected by a dart role; projections have already been charged. -/
def otherEndpoint {n : Nat} (role : Bool) (left right : Fin n) : Fin n :=
  if role then left else right

/-- Pure state transition after scanning a dart whose edge was already used. -/
def skipState {n m : Nat} (state : CoreState n m) (cursors : Vector Nat n) : CoreState n m :=
  { state with cursor := cursors }

/-- Pure state transition after first using a scanned edge and pushing its other endpoint. -/
def pushState {n m : Nat} (state : CoreState n m) (used : Vector Bool m)
    (cursors : Vector Nat n) (stack : List (Frame n m)) : CoreState n m :=
  { used := used
    cursor := cursors
    stack := stack
    output := state.output }

/-- Pure state transition for a pop, optionally emitting its incoming canonical step. -/
def popState {n m : Nat} (state : CoreState n m) (rest : List (Frame n m))
    (step : Option (Fin m × Fin n)) : CoreState n m :=
  match step with
  | none => { state with stack := rest }
  | some step => { state with stack := rest, output := step :: state.output }

/--
The transitive timed hot loop. `scanFuel` bounds previously unscanned darts; `popFuel` bounds stack
pops. Both counters stay within the frozen word-width envelope. Exhaustion branches are total but
are proved unreachable from a certified initial state in the correctness development.
-/
def run (R : CertifiedIncidenceRepresentation G) :
    (scanFuel popFuel : Nat) → CoreState R.n R.m → TimeM Cost (CoreState R.n R.m)
  | scanFuel, popFuel, state => do
      let stack ← Event.stackCheck state.stack
      match stack with
      | [] => pure state
      | top :: rest =>
          let top ← Event.stackPeek 2 top
          let bucket ← Event.incidenceRead (R.buckets.get top.vertex)
          let bucketSize ← Event.incidenceRead bucket.size
          let cursor ← Event.cursorRead (state.cursor.get top.vertex)
          let _ ← Event.indexLt cursor bucketSize
          match bucket[cursor]? with
          | some dart =>
              match scanFuel with
              | 0 => pure state
              | scanFuel + 1 =>
                  let edge ← Event.incidenceRead dart.edge
                  let role ← Event.incidenceRead dart.role
                  let nextCursor ← Event.indexSucc cursor
                  let cursors ← Event.cursorWrite (setFin state.cursor top.vertex nextCursor)
                  let wasUsed ← Event.usedRead (state.used.get edge)
                  if wasUsed then
                    run R scanFuel popFuel (skipState state cursors)
                  else
                    let used ← Event.usedWrite (setFin state.used edge true)
                    let storedEnds := R.ends.get edge
                    let left ← Event.endpointRead storedEnds.1
                    let right ← Event.endpointRead storedEnds.2
                    let next := otherEndpoint role left right
                    let newFrame : Frame R.n R.m := { incoming := some edge, vertex := next }
                    let newStack ← Event.stackPush 2 (newFrame :: stack)
                    run R scanFuel popFuel (pushState state used cursors newStack)
          | none =>
              match popFuel with
              | 0 => pure state
              | popFuel + 1 =>
                  let popped ← Event.stackPop 2 (top, rest)
                  match popped.1.incoming with
                  | none =>
                      run R scanFuel popFuel (popState state popped.2 none)
                  | some edge =>
                      let step ← Event.outputEmitStep (edge, popped.1.vertex)
                      run R scanFuel popFuel (popState state popped.2 (some step))
termination_by scanFuel popFuel _state => scanFuel + popFuel

/-- The public canonical result. The two budgets are `2m` dart scans and `m+1` pops. -/
def hierholzer (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    TimeM Cost (IndexedTour R.n R.m) := do
  let state ← initState R.n R.m start
  let scanFuel ← Event.indexAdd R.m R.m
  let popFuel ← Event.indexSucc R.m
  let state ← run R scanFuel popFuel state
  let storedStart ← Event.outputStoreStart start
  pure { start := storedStart, steps := state.output }

end Core

export Core (hierholzer)

end Benchmarks.Hierholzer.Mathlib
