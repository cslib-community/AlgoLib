/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.EncoderLayout
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueRing
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueStacksImplementation

/-!
# FIFO implementation adapter with stable assembly contracts

All knowledge of a FIFO's private layout and initial potential is confined here.
The public namespace and lower heap bound allow padding and register renaming.
BFSStorage and BFSExecution use these contracts without opening queue definitions.
The relocated variant is a regression configuration of the verified circular queue.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BFSStorage
open Checked.Language

inductive FIFO where
  | circular
  | twoStacks
  /-- Regression backend: renamed private registers and a padded heap allocation. -/
  | relocated
  deriving DecidableEq, Repr

abbrev queue (kind : FIFO) (base capacity : Nat) : Representation (List Nat) :=
  match kind with
  | .circular => QueueRing.representation ⟨"bfs.queue", base, capacity⟩
  | .twoStacks => QueueStacksImplementation.queue "bfs.queue" base capacity
  | .relocated => QueueRing.representation ⟨"bfs.queue.relocated", base + 17, capacity⟩

def queueEncoder (kind : FIFO) (base capacity : Nat) : Encoder (queue kind base capacity) :=
  match kind with
  | .circular => QueueRing.encoder ⟨"bfs.queue", base, capacity⟩
  | .twoStacks => QueueStacksImplementation.encoder "bfs.queue" base capacity
  | .relocated => QueueRing.encoder ⟨"bfs.queue.relocated", base + 17, capacity⟩

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

/-- The queue owns a private namespace and cells above its arena start.
Neither its register names nor the offset of its first cell are public. -/
def queueRegion (base : Nat) : MemoryRegion where
  registers _ name := name.startsWith "bfs.queue." = true
  heap address := base ≤ address

/-- Only this adapter proof inspects the chosen queue implementation. -/
theorem queue_within (kind : FIFO) (base capacity : Nat) :
    (queueEncoder kind base capacity).Within (queueRegion base) := by
  intro location owned
  cases kind <;> cases location <;>
    simp_all [MemoryRegion.contains, queueRegion, queueEncoder,
      QueueRing.encoder, QueueRing.Layout.footprint, QueueRing.Layout.head,
      QueueRing.Layout.length, QueueStacksImplementation.encoder,
      QueueStacksImplementation.concreteEncoder, Encoder.sep,
      BufferImplementation.encoder, BufferImplementation.Layout.footprint,
      BufferImplementation.Layout.lengthVar, BufferImplementation.Layout.argumentVar]
  all_goals repeat' first | cases_type Or | cases_type And
  all_goals subst_vars
  all_goals first | decide | grind

/-- BFS creates an empty queue, so it owes no initial private potential. -/
theorem queue_input (kind : FIFO) (base capacity : Nat) :
    (queueEncoder kind base capacity).InputContract (fun xs => xs = []) (fun _ => 0) := by
  constructor <;> intro xs h <;> subst xs <;> cases kind <;>
    simp [queueEncoder, QueueRing.encoder, QueueStacksImplementation.encoder]

end AlgoLib.Experimental.RAM.Prototype.Composition.BFSStorage
