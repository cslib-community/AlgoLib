module

public import Cslib.Algorithms.Lean.TimeM

/-!
# Frozen Hierholzer benchmark cost ledger

This module is the graph-independent, manually audited event ledger fixed by
`HIERHOLZER_BENCHMARK_PROTOCOL.md`.  Public primitive wrappers preserve their value and charge
exactly one literal unit-basis event; no arbitrary-cost wrapper is exposed.

Importing `TimeM` necessarily leaves `TimeM.tick` technically accessible to clients.  Avoiding raw
ticks outside this module is therefore a benchmark convention enforced by source audit rather than
by Lean's module system.

## Frozen storage-to-counter codebook

| Logical operation or storage class | Unit event |
| --- | --- |
| initialize one algorithm-owned word | `initWrite` |
| read one incidence or offset word | `incidenceRead` |
| read one stored endpoint-ID word | `endpointRead` |
| read/write one used-edge flag word | `usedRead` / `usedWrite` |
| read/write one cursor word | `cursorRead` / `cursorWrite` |
| compare, increment, or add bounded-word indices | `indexOp` |
| request a stack empty/top check, push, peek, or pop | `stackControl` |
| read/write one stack payload word | `stackRead` / `stackWrite` |
| emit or visit one logical output step | `outputControl` |
| read/write one output payload word | `outputRead` / `outputWrite` |

A separately stored incidence edge ID and role cost two `incidenceRead` events.  A stored endpoint
pair costs two `endpointRead` events.  Each distinct stack action has its own `stackControl` event;
payloads are charged per logical word.  A canonical output step has two payload words, so emitting
it costs one control plus two writes, while visiting and copying it costs one control, two reads,
and two writes.  Storing the result start ID costs one output write.  Function calls, constructor
projections, proof fields, pattern dispatch, and proof-only decoding cost zero.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Common

open Cslib.Algorithms.Lean

/-- The frozen fourteen-component abstract-RAM event ledger.  Field order is protocol-significant. -/
@[ext]
structure Cost where
  initWrite : Nat
  incidenceRead : Nat
  endpointRead : Nat
  usedRead : Nat
  usedWrite : Nat
  cursorRead : Nat
  cursorWrite : Nat
  indexOp : Nat
  stackControl : Nat
  stackRead : Nat
  stackWrite : Nat
  outputControl : Nat
  outputRead : Nat
  outputWrite : Nat
deriving DecidableEq, Repr

instance costZero : Zero Cost where
  zero :=
    { initWrite := 0
      incidenceRead := 0
      endpointRead := 0
      usedRead := 0
      usedWrite := 0
      cursorRead := 0
      cursorWrite := 0
      indexOp := 0
      stackControl := 0
      stackRead := 0
      stackWrite := 0
      outputControl := 0
      outputRead := 0
      outputWrite := 0 }

instance costAdd : Add Cost where
  add a b :=
    { initWrite := a.initWrite + b.initWrite
      incidenceRead := a.incidenceRead + b.incidenceRead
      endpointRead := a.endpointRead + b.endpointRead
      usedRead := a.usedRead + b.usedRead
      usedWrite := a.usedWrite + b.usedWrite
      cursorRead := a.cursorRead + b.cursorRead
      cursorWrite := a.cursorWrite + b.cursorWrite
      indexOp := a.indexOp + b.indexOp
      stackControl := a.stackControl + b.stackControl
      stackRead := a.stackRead + b.stackRead
      stackWrite := a.stackWrite + b.stackWrite
      outputControl := a.outputControl + b.outputControl
      outputRead := a.outputRead + b.outputRead
      outputWrite := a.outputWrite + b.outputWrite }

@[simp] theorem zero_initWrite : (0 : Cost).initWrite = 0 := rfl
@[simp] theorem zero_incidenceRead : (0 : Cost).incidenceRead = 0 := rfl
@[simp] theorem zero_endpointRead : (0 : Cost).endpointRead = 0 := rfl
@[simp] theorem zero_usedRead : (0 : Cost).usedRead = 0 := rfl
@[simp] theorem zero_usedWrite : (0 : Cost).usedWrite = 0 := rfl
@[simp] theorem zero_cursorRead : (0 : Cost).cursorRead = 0 := rfl
@[simp] theorem zero_cursorWrite : (0 : Cost).cursorWrite = 0 := rfl
@[simp] theorem zero_indexOp : (0 : Cost).indexOp = 0 := rfl
@[simp] theorem zero_stackControl : (0 : Cost).stackControl = 0 := rfl
@[simp] theorem zero_stackRead : (0 : Cost).stackRead = 0 := rfl
@[simp] theorem zero_stackWrite : (0 : Cost).stackWrite = 0 := rfl
@[simp] theorem zero_outputControl : (0 : Cost).outputControl = 0 := rfl
@[simp] theorem zero_outputRead : (0 : Cost).outputRead = 0 := rfl
@[simp] theorem zero_outputWrite : (0 : Cost).outputWrite = 0 := rfl

@[simp] theorem add_initWrite (a b : Cost) : (a + b).initWrite = a.initWrite + b.initWrite := rfl
@[simp] theorem add_incidenceRead (a b : Cost) :
    (a + b).incidenceRead = a.incidenceRead + b.incidenceRead := rfl
@[simp] theorem add_endpointRead (a b : Cost) :
    (a + b).endpointRead = a.endpointRead + b.endpointRead := rfl
@[simp] theorem add_usedRead (a b : Cost) : (a + b).usedRead = a.usedRead + b.usedRead := rfl
@[simp] theorem add_usedWrite (a b : Cost) : (a + b).usedWrite = a.usedWrite + b.usedWrite := rfl
@[simp] theorem add_cursorRead (a b : Cost) :
    (a + b).cursorRead = a.cursorRead + b.cursorRead := rfl
@[simp] theorem add_cursorWrite (a b : Cost) :
    (a + b).cursorWrite = a.cursorWrite + b.cursorWrite := rfl
@[simp] theorem add_indexOp (a b : Cost) : (a + b).indexOp = a.indexOp + b.indexOp := rfl
@[simp] theorem add_stackControl (a b : Cost) :
    (a + b).stackControl = a.stackControl + b.stackControl := rfl
@[simp] theorem add_stackRead (a b : Cost) : (a + b).stackRead = a.stackRead + b.stackRead := rfl
@[simp] theorem add_stackWrite (a b : Cost) :
    (a + b).stackWrite = a.stackWrite + b.stackWrite := rfl
@[simp] theorem add_outputControl (a b : Cost) :
    (a + b).outputControl = a.outputControl + b.outputControl := rfl
@[simp] theorem add_outputRead (a b : Cost) :
    (a + b).outputRead = a.outputRead + b.outputRead := rfl
@[simp] theorem add_outputWrite (a b : Cost) :
    (a + b).outputWrite = a.outputWrite + b.outputWrite := rfl

instance : AddCommMonoid Cost where
  add_assoc a b c := by ext <;> simp [Nat.add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by ext <;> simp [Nat.add_comm]

namespace Cost

/-- The frozen scalar projection: every primitive event has unit weight. -/
def total (cost : Cost) : Nat :=
  cost.initWrite + cost.incidenceRead + cost.endpointRead + cost.usedRead + cost.usedWrite +
    cost.cursorRead + cost.cursorWrite + cost.indexOp + cost.stackControl + cost.stackRead +
    cost.stackWrite + cost.outputControl + cost.outputRead + cost.outputWrite

@[simp] theorem total_zero : total 0 = 0 := rfl

@[simp] theorem total_add (a b : Cost) : total (a + b) = total a + total b := by
  simp only [total, add_initWrite, add_incidenceRead, add_endpointRead, add_usedRead,
    add_usedWrite, add_cursorRead, add_cursorWrite, add_indexOp, add_stackControl, add_stackRead,
    add_stackWrite, add_outputControl, add_outputRead, add_outputWrite]
  omega

end Cost

/- Frozen value-preserving primitive events and their graph-neutral composites. -/
namespace Event

universe u

def initWrite {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with initWrite := 1 }
    pure value

@[simp] theorem ret_initWrite {α : Type u} (value : α) : (initWrite value).ret = value := by
  simp [initWrite]

@[simp] theorem time_initWrite {α : Type u} (value : α) :
    (initWrite value).time = { (0 : Cost) with initWrite := 1 } := by
  simp [initWrite]

def incidenceRead {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with incidenceRead := 1 }
    pure value

@[simp] theorem ret_incidenceRead {α : Type u} (value : α) :
    (incidenceRead value).ret = value := by
  simp [incidenceRead]

@[simp] theorem time_incidenceRead {α : Type u} (value : α) :
    (incidenceRead value).time = { (0 : Cost) with incidenceRead := 1 } := by
  simp [incidenceRead]

def endpointRead {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with endpointRead := 1 }
    pure value

@[simp] theorem ret_endpointRead {α : Type u} (value : α) :
    (endpointRead value).ret = value := by
  simp [endpointRead]

@[simp] theorem time_endpointRead {α : Type u} (value : α) :
    (endpointRead value).time = { (0 : Cost) with endpointRead := 1 } := by
  simp [endpointRead]

def usedRead {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with usedRead := 1 }
    pure value

@[simp] theorem ret_usedRead {α : Type u} (value : α) : (usedRead value).ret = value := by
  simp [usedRead]

@[simp] theorem time_usedRead {α : Type u} (value : α) :
    (usedRead value).time = { (0 : Cost) with usedRead := 1 } := by
  simp [usedRead]

def usedWrite {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with usedWrite := 1 }
    pure value

@[simp] theorem ret_usedWrite {α : Type u} (value : α) : (usedWrite value).ret = value := by
  simp [usedWrite]

@[simp] theorem time_usedWrite {α : Type u} (value : α) :
    (usedWrite value).time = { (0 : Cost) with usedWrite := 1 } := by
  simp [usedWrite]

def cursorRead {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with cursorRead := 1 }
    pure value

@[simp] theorem ret_cursorRead {α : Type u} (value : α) : (cursorRead value).ret = value := by
  simp [cursorRead]

@[simp] theorem time_cursorRead {α : Type u} (value : α) :
    (cursorRead value).time = { (0 : Cost) with cursorRead := 1 } := by
  simp [cursorRead]

def cursorWrite {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with cursorWrite := 1 }
    pure value

@[simp] theorem ret_cursorWrite {α : Type u} (value : α) : (cursorWrite value).ret = value := by
  simp [cursorWrite]

@[simp] theorem time_cursorWrite {α : Type u} (value : α) :
    (cursorWrite value).time = { (0 : Cost) with cursorWrite := 1 } := by
  simp [cursorWrite]

/-- Compare two bounded-word indices for equality, charging one `indexOp`. -/
def indexEq (i j : Nat) : TimeM Cost Bool := do
  TimeM.tick { (0 : Cost) with indexOp := 1 }
  pure (decide (i = j))

@[simp] theorem ret_indexEq (i j : Nat) : (indexEq i j).ret = decide (i = j) := by
  simp [indexEq]

@[simp] theorem time_indexEq (i j : Nat) :
    (indexEq i j).time = { (0 : Cost) with indexOp := 1 } := by
  simp [indexEq]

/-- Compare two bounded-word indices, charging one `indexOp`. -/
def indexLt (i j : Nat) : TimeM Cost Bool := do
  TimeM.tick { (0 : Cost) with indexOp := 1 }
  pure (decide (i < j))

@[simp] theorem ret_indexLt (i j : Nat) : (indexLt i j).ret = decide (i < j) := by
  simp [indexLt]

@[simp] theorem time_indexLt (i j : Nat) :
    (indexLt i j).time = { (0 : Cost) with indexOp := 1 } := by
  simp [indexLt]

/-- Increment a bounded-word index, charging one `indexOp`. -/
def indexSucc (i : Nat) : TimeM Cost Nat := do
  TimeM.tick { (0 : Cost) with indexOp := 1 }
  pure (i + 1)

@[simp] theorem ret_indexSucc (i : Nat) : (indexSucc i).ret = i + 1 := by
  simp [indexSucc]

@[simp] theorem time_indexSucc (i : Nat) :
    (indexSucc i).time = { (0 : Cost) with indexOp := 1 } := by
  simp [indexSucc]

/-- Add two bounded-word indices, charging one `indexOp`. -/
def indexAdd (i j : Nat) : TimeM Cost Nat := do
  TimeM.tick { (0 : Cost) with indexOp := 1 }
  pure (i + j)

@[simp] theorem ret_indexAdd (i j : Nat) : (indexAdd i j).ret = i + j := by
  simp [indexAdd]

@[simp] theorem time_indexAdd (i j : Nat) :
    (indexAdd i j).time = { (0 : Cost) with indexOp := 1 } := by
  simp [indexAdd]

def stackControl {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with stackControl := 1 }
    pure value

@[simp] theorem ret_stackControl {α : Type u} (value : α) :
    (stackControl value).ret = value := by
  simp [stackControl]

@[simp] theorem time_stackControl {α : Type u} (value : α) :
    (stackControl value).time = { (0 : Cost) with stackControl := 1 } := by
  simp [stackControl]

def stackRead {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with stackRead := 1 }
    pure value

@[simp] theorem ret_stackRead {α : Type u} (value : α) : (stackRead value).ret = value := by
  simp [stackRead]

@[simp] theorem time_stackRead {α : Type u} (value : α) :
    (stackRead value).time = { (0 : Cost) with stackRead := 1 } := by
  simp [stackRead]

def stackWrite {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with stackWrite := 1 }
    pure value

@[simp] theorem ret_stackWrite {α : Type u} (value : α) : (stackWrite value).ret = value := by
  simp [stackWrite]

@[simp] theorem time_stackWrite {α : Type u} (value : α) :
    (stackWrite value).time = { (0 : Cost) with stackWrite := 1 } := by
  simp [stackWrite]

def outputControl {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with outputControl := 1 }
    pure value

@[simp] theorem ret_outputControl {α : Type u} (value : α) :
    (outputControl value).ret = value := by
  simp [outputControl]

@[simp] theorem time_outputControl {α : Type u} (value : α) :
    (outputControl value).time = { (0 : Cost) with outputControl := 1 } := by
  simp [outputControl]

def outputRead {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with outputRead := 1 }
    pure value

@[simp] theorem ret_outputRead {α : Type u} (value : α) : (outputRead value).ret = value := by
  simp [outputRead]

@[simp] theorem time_outputRead {α : Type u} (value : α) :
    (outputRead value).time = { (0 : Cost) with outputRead := 1 } := by
  simp [outputRead]

def outputWrite {α : Type u} (value : α) : TimeM Cost α :=
  do
    TimeM.tick { (0 : Cost) with outputWrite := 1 }
    pure value

@[simp] theorem ret_outputWrite {α : Type u} (value : α) : (outputWrite value).ret = value := by
  simp [outputWrite]

@[simp] theorem time_outputWrite {α : Type u} (value : α) :
    (outputWrite value).time = { (0 : Cost) with outputWrite := 1 } := by
  simp [outputWrite]

/-- Charge a stack availability/emptiness check. -/
def stackCheck {α : Type u} (value : α) : TimeM Cost α :=
  stackControl value

@[simp] theorem ret_stackCheck {α : Type u} (value : α) : (stackCheck value).ret = value := by
  simp [stackCheck]

@[simp] theorem time_stackCheck {α : Type u} (value : α) :
    (stackCheck value).time = { (0 : Cost) with stackControl := 1 } := by
  simp [stackCheck]

/-- Charge one stack push plus one payload write per logical word. -/
def stackPush {α : Type u} : Nat → α → TimeM Cost α
  | 0, value => stackControl value
  | words + 1, value => do
      let value ← stackPush words value
      stackWrite value

@[simp] theorem ret_stackPush {α : Type u} (words : Nat) (value : α) :
    (stackPush words value).ret = value := by
  induction words <;> simp_all [stackPush]

@[simp] theorem time_stackPush {α : Type u} (words : Nat) (value : α) :
    (stackPush words value).time =
      { (0 : Cost) with stackControl := 1, stackWrite := words } := by
  induction words with
  | zero => simp [stackPush]
  | succ words ih =>
      simp [stackPush, ih]
      ext <;> simp [Nat.add_comm]

/-- Charge one stack peek request plus one payload read per returned logical word. -/
def stackPeek {α : Type u} : Nat → α → TimeM Cost α
  | 0, value => stackControl value
  | words + 1, value => do
      let value ← stackPeek words value
      stackRead value

@[simp] theorem ret_stackPeek {α : Type u} (words : Nat) (value : α) :
    (stackPeek words value).ret = value := by
  induction words <;> simp_all [stackPeek]

@[simp] theorem time_stackPeek {α : Type u} (words : Nat) (value : α) :
    (stackPeek words value).time =
      { (0 : Cost) with stackControl := 1, stackRead := words } := by
  induction words with
  | zero => simp [stackPeek]
  | succ words ih =>
      simp [stackPeek, ih]
      ext <;> simp [Nat.add_comm]

/-- Charge one stack pop plus one payload read per returned logical word. -/
def stackPop {α : Type u} : Nat → α → TimeM Cost α
  | 0, value => stackControl value
  | words + 1, value => do
      let value ← stackPop words value
      stackRead value

@[simp] theorem ret_stackPop {α : Type u} (words : Nat) (value : α) :
    (stackPop words value).ret = value := by
  induction words <;> simp_all [stackPop]

@[simp] theorem time_stackPop {α : Type u} (words : Nat) (value : α) :
    (stackPop words value).time =
      { (0 : Cost) with stackControl := 1, stackRead := words } := by
  induction words with
  | zero => simp [stackPop]
  | succ words ih =>
      simp [stackPop, ih]
      ext <;> simp [Nat.add_comm]

/-- Charge storing the one-word `IndexedTour.start` result payload. -/
def outputStoreStart {α : Type u} (value : α) : TimeM Cost α :=
  outputWrite value

@[simp] theorem ret_outputStoreStart {α : Type u} (value : α) :
    (outputStoreStart value).ret = value := by
  simp [outputStoreStart]

@[simp] theorem time_outputStoreStart {α : Type u} (value : α) :
    (outputStoreStart value).time = { (0 : Cost) with outputWrite := 1 } := by
  simp [outputStoreStart]

/-- Charge emitting one canonical two-word `(edge ID, next vertex ID)` step. -/
def outputEmitStep {α : Type u} (value : α) : TimeM Cost α := do
  let value ← outputControl value
  let value ← outputWrite value
  outputWrite value

@[simp] theorem ret_outputEmitStep {α : Type u} (value : α) :
    (outputEmitStep value).ret = value := by
  simp [outputEmitStep]

@[simp] theorem time_outputEmitStep {α : Type u} (value : α) :
    (outputEmitStep value).time =
      { (0 : Cost) with outputControl := 1, outputWrite := 2 } := by
  simp [outputEmitStep]
  ext <;> simp

/-- Charge visiting and copying one canonical two-word output step. -/
def outputCopyStep {α : Type u} (value : α) : TimeM Cost α := do
  let value ← outputControl value
  let value ← outputRead value
  let value ← outputRead value
  let value ← outputWrite value
  outputWrite value

@[simp] theorem ret_outputCopyStep {α : Type u} (value : α) :
    (outputCopyStep value).ret = value := by
  simp [outputCopyStep]

@[simp] theorem time_outputCopyStep {α : Type u} (value : α) :
    (outputCopyStep value).time =
      { (0 : Cost) with outputControl := 1, outputRead := 2, outputWrite := 2 } := by
  simp [outputCopyStep]
  ext <;> simp

@[simp] theorem total_time_initWrite {α : Type u} (value : α) :
    Cost.total (initWrite value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_incidenceRead {α : Type u} (value : α) :
    Cost.total (incidenceRead value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_endpointRead {α : Type u} (value : α) :
    Cost.total (endpointRead value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_usedRead {α : Type u} (value : α) :
    Cost.total (usedRead value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_usedWrite {α : Type u} (value : α) :
    Cost.total (usedWrite value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_cursorRead {α : Type u} (value : α) :
    Cost.total (cursorRead value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_cursorWrite {α : Type u} (value : α) :
    Cost.total (cursorWrite value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_indexEq (i j : Nat) : Cost.total (indexEq i j).time = 1 := by
  simp [Cost.total]

@[simp] theorem total_time_indexLt (i j : Nat) : Cost.total (indexLt i j).time = 1 := by
  simp [Cost.total]

@[simp] theorem total_time_indexSucc (i : Nat) : Cost.total (indexSucc i).time = 1 := by
  simp [Cost.total]

@[simp] theorem total_time_indexAdd (i j : Nat) : Cost.total (indexAdd i j).time = 1 := by
  simp [Cost.total]

@[simp] theorem total_time_stackControl {α : Type u} (value : α) :
    Cost.total (stackControl value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_stackRead {α : Type u} (value : α) :
    Cost.total (stackRead value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_stackWrite {α : Type u} (value : α) :
    Cost.total (stackWrite value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_outputControl {α : Type u} (value : α) :
    Cost.total (outputControl value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_outputRead {α : Type u} (value : α) :
    Cost.total (outputRead value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_outputWrite {α : Type u} (value : α) :
    Cost.total (outputWrite value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_stackCheck {α : Type u} (value : α) :
    Cost.total (stackCheck value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_stackPush {α : Type u} (words : Nat) (value : α) :
    Cost.total (stackPush words value).time = words + 1 := by
  simp [Cost.total, Nat.add_comm]

@[simp] theorem total_time_stackPeek {α : Type u} (words : Nat) (value : α) :
    Cost.total (stackPeek words value).time = words + 1 := by
  simp [Cost.total, Nat.add_comm]

@[simp] theorem total_time_stackPop {α : Type u} (words : Nat) (value : α) :
    Cost.total (stackPop words value).time = words + 1 := by
  simp [Cost.total, Nat.add_comm]

@[simp] theorem total_time_outputStoreStart {α : Type u} (value : α) :
    Cost.total (outputStoreStart value).time = 1 := by simp [Cost.total]

@[simp] theorem total_time_outputEmitStep {α : Type u} (value : α) :
    Cost.total (outputEmitStep value).time = 3 := by simp [Cost.total]

@[simp] theorem total_time_outputCopyStep {α : Type u} (value : α) :
    Cost.total (outputCopyStep value).time = 5 := by simp [Cost.total]

end Event

end Benchmarks.Hierholzer.Common
