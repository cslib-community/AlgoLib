/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.EncoderLayout
import AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursorImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.BFSQueue

/-!
# Resident storage for the unchanged BFS client

Graph cells are read-only and separately owned from the visited bitmap, queue,
source, and generated locals. FIFO choice changes only this backend configuration.
The graph is already resident; initialization of visited and queue is executable
source code. Decoding the returned bitmap is a host-side observation.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BFSStorage
open Experimental.RAM.BFS Checked.Language

/-- The frontend's list query is interpreted by ownership, not by the list's spelling. -/
instance (a : Adjacency) (cursor : Var .word) :
    TestImplementation 24 (GraphCursorImplementation.representation a cursor) Queue.nonempty :=
  inferInstanceAs (TestImplementation 24 _ GraphCursor.nonempty)

abbrev source := scalarEncoder ⟨"bfs.source"⟩
abbrev bitmap (base capacity : Nat) := arrayEncoder ⟨⟨"bfs.visited.size"⟩, base, capacity⟩

abbrev sourceRegion : MemoryRegion := .scalar ⟨"bfs.source"⟩
abbrev bitmapRegion (base capacity : Nat) : MemoryRegion :=
  .array ⟨⟨"bfs.visited.size"⟩, base, capacity⟩

theorem source_within : source.Within sourceRegion := scalarEncoder_within _
theorem bitmap_within (base capacity : Nat) :
    (bitmap base capacity).Within (bitmapRegion base capacity) := arrayEncoder_within _

abbrev fifo (kind : FIFO) (base capacity : Nat) :=
  (queueEncoder kind base capacity).sep source
    ((queue_within kind base capacity).disjoint source_within (by
      intro l hq hs; cases l <;>
        simp_all [MemoryRegion.contains, queueRegion, sourceRegion, MemoryRegion.scalar]))

theorem fifo_within (kind : FIFO) (base capacity : Nat) :
    (fifo kind base capacity).Within ((queueRegion base).union sourceRegion) :=
  (queue_within kind base capacity).sep source_within _

abbrev state (kind : FIFO) (base capacity : Nat) :=
  (bitmap base capacity).sep (fifo kind (base + capacity) capacity)
    ((bitmap_within base capacity).disjoint (fifo_within kind (base + capacity) capacity) (by
      intro l hb hq; cases l <;>
        simp_all [MemoryRegion.contains, MemoryRegion.union, bitmapRegion, queueRegion,
          sourceRegion, MemoryRegion.scalar, MemoryRegion.array]
      omega))

def stateRegion (base capacity : Nat) :=
  (bitmapRegion base capacity).union ((queueRegion (base + capacity)).union sourceRegion)

theorem state_within (kind : FIFO) (base capacity : Nat) :
    (state kind base capacity).Within (stateRegion base capacity) :=
  (bitmap_within base capacity).sep (fifo_within kind (base + capacity) capacity) _

abbrev graphRegion (a : Adjacency) : MemoryRegion :=
  GraphCursorImplementation.region a ⟨"bfs.row"⟩

theorem graph_within (a : Adjacency) :
    (GraphCursorImplementation.encoder a ⟨"bfs.row"⟩).Within (graphRegion a) :=
  GraphCursorImplementation.encoder_within a _

/-- Graph allocation is determined by the resident adjacency layout, before running BFS. -/
abbrev resident (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base) :=
  (GraphCursorImplementation.encoder a ⟨"bfs.row"⟩).sep (state kind base capacity)
    ((graph_within a).disjoint (state_within kind base capacity) (by
      intro l hg hs; cases l <;>
        simp_all [MemoryRegion.contains, MemoryRegion.union, stateRegion, graphRegion,
          bitmapRegion, queueRegion, sourceRegion, GraphCursorImplementation.region,
          MemoryRegion.scalar, MemoryRegion.array]
      omega))

/-- Public scratch compatibility: all resident registers avoid the compiler's namespace. -/
def residentRegion (a : Adjacency) (base capacity : Nat) :=
  (graphRegion a).union (stateRegion base capacity)

theorem resident_within (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base) :
    (resident kind a base capacity fits).Within (residentRegion a base capacity) :=
  (graph_within a).sep (state_within kind base capacity) _

/-- Stable input contract. Queue initialization details and private potential stay hidden. -/
theorem resident_input (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base) :
    (resident kind a base capacity fits).InputContract
      (fun x => x.1 = [] ∧ x.2.1.size ≤ capacity ∧ x.2.2.1 = []) (fun _ => 0) := by
  have contract : (resident kind a base capacity fits).InputContract _ _ :=
    (GraphCursorImplementation.encoder_input a _).sep
      ((arrayEncoder_input _).sep
        ((queue_input kind _ _).sep (scalarEncoder_input _) _) _) _
  simpa only [and_true, Nat.add_zero, Nat.zero_add] using contract

end AlgoLib.Experimental.RAM.Prototype.Composition.BFSStorage
