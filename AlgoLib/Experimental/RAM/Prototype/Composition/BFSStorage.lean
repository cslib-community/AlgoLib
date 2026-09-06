/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursorImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueRing
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueStacksImplementation

/-!
# Resident storage for the unchanged BFS client

Graph cells are read-only and separately owned from the visited bitmap, queue,
source, and generated locals. FIFO choice changes only this backend configuration.
The graph is already resident; initialization of visited and queue is executable
source code. Decoding the returned bitmap is a host-side observation.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BFSStorage
open Experimental.RAM.BFS Checked.Language

inductive FIFO where
  | circular
  | twoStacks
  deriving DecidableEq, Repr

abbrev queue (kind : FIFO) (base capacity : Nat) : Representation (List Nat) :=
  match kind with
  | .circular => QueueRing.representation ⟨"bfs.queue", base, capacity⟩
  | .twoStacks => QueueStacksImplementation.queue "bfs.queue" base capacity

def queueEncoder (kind : FIFO) (base capacity : Nat) : Encoder (queue kind base capacity) :=
  match kind with
  | .circular => QueueRing.encoder ⟨"bfs.queue", base, capacity⟩
  | .twoStacks => QueueStacksImplementation.encoder "bfs.queue" base capacity

instance (kind : FIFO) (base capacity : Nat) : Decoder (queue kind base capacity) := by
  cases kind <;> exact inferInstance

instance (kind : FIFO) (base capacity : Nat) :
    Primitive 24 (queue kind base capacity) Queue.reset (queue kind base capacity) := by
  cases kind <;> exact inferInstance

instance (kind : FIFO) (base capacity : Nat) (Q : Representation Nat) [ScalarStorage Q] :
    Primitive 24 ((queue kind base capacity).sep Q) (Queue.push capacity)
      ((queue kind base capacity).sep Q) := by
  cases kind <;> exact inferInstance

instance (kind : FIFO) (base capacity : Nat) (Q : Representation Nat) [ScalarStorage Q] :
    Primitive 24 ((queue kind base capacity).sep Q) Queue.pop
      ((queue kind base capacity).sep Q) := by
  cases kind <;> exact inferInstance

instance (kind : FIFO) (base capacity : Nat) :
    TestImplementation 24 (queue kind base capacity) Queue.nonempty := by
  cases kind <;> exact inferInstance

/-- The frontend's list query is interpreted by ownership, not by the list's spelling. -/
instance (a : Adjacency) (cursor : Var .word) :
    TestImplementation 24 (GraphCursorImplementation.representation a cursor) Queue.nonempty :=
  inferInstanceAs (TestImplementation 24 _ GraphCursor.nonempty)

abbrev source := scalarEncoder ⟨"bfs.source"⟩

def fifo (kind : FIFO) (base capacity : Nat) :=
  (queueEncoder kind base capacity).sep source (by
    cases kind <;>
      simp [queueEncoder, source, QueueRing.encoder, QueueRing.Layout.footprint,
        QueueRing.Layout.head, QueueRing.Layout.length,
        QueueStacksImplementation.encoder, QueueStacksImplementation.concreteEncoder,
        Encoder.sep, BufferImplementation.encoder, BufferImplementation.Layout.footprint,
        BufferImplementation.Layout.lengthVar, BufferImplementation.Layout.argumentVar,
        scalarEncoder, Finset.disjoint_left]
    rintro location (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp)

abbrev bitmap (base capacity : Nat) := arrayEncoder ⟨⟨"bfs.visited.size"⟩, base, capacity⟩

def state (kind : FIFO) (base capacity : Nat) :=
  (bitmap base capacity).sep (fifo kind (base + capacity) capacity) (by
    cases kind <;>
      simp [bitmap, fifo, queueEncoder, source, QueueRing.encoder, QueueRing.Layout.footprint,
        QueueRing.Layout.head, QueueRing.Layout.length,
        QueueStacksImplementation.encoder, QueueStacksImplementation.concreteEncoder,
        Encoder.sep, BufferImplementation.encoder, BufferImplementation.Layout.footprint,
        BufferImplementation.Layout.lengthVar, BufferImplementation.Layout.argumentVar,
        scalarEncoder, arrayEncoder, Storage.ArrayLayout.footprint, Finset.disjoint_left]
    all_goals grind)

/-- Graph allocation is determined by the resident adjacency layout, before running BFS. -/
def resident (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base) :=
  (GraphCursorImplementation.encoder a ⟨"bfs.row"⟩).sep
    (state kind base capacity) (by
      cases kind <;>
        simp [GraphCursorImplementation.encoder, GraphCursorImplementation.footprint,
          state, bitmap, fifo, queueEncoder, source, QueueRing.encoder,
          QueueRing.Layout.footprint, QueueRing.Layout.head, QueueRing.Layout.length,
          QueueStacksImplementation.encoder, QueueStacksImplementation.concreteEncoder,
          Encoder.sep, BufferImplementation.encoder, BufferImplementation.Layout.footprint,
          BufferImplementation.Layout.lengthVar, BufferImplementation.Layout.argumentVar,
          scalarEncoder, arrayEncoder, Storage.ArrayLayout.footprint, Finset.disjoint_left]
      all_goals intro location owned
      all_goals cases location with
      | register ty name => simp_all [GraphCursorImplementation.no_register]
      | heap address =>
        have bound := GraphCursorImplementation.below_extent a address owned
        grind)

end AlgoLib.Experimental.RAM.Prototype.Composition.BFSStorage
