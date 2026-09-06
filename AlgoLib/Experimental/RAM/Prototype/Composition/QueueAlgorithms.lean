/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend
import AlgoLib.Experimental.RAM.Prototype.Composition.Queue

/-!
# Small FIFO clients used before linking graph traversal

The same declarations are linked with circular and two-stack queues. Paired calls
transfer a scalar result through the ordinary owned frontend. Proofs use only the
public FIFO contracts. Rotation exercises both full circular-buffer wraparound and
the amortized transfer path of the two-stack implementation.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.QueueAlgorithms

ram method rotate (capacity : Nat) (mut queue : List Nat) (mut value : Nat)
  return (result : List Nat × Nat)
  require queue ≠ []
  require queue.length ≤ capacity
  ensures queue = queueOld.tail ++ [queueOld.headD 0]
  ensures value = queueOld.headD 0
  do
    (queue, value) := Queue.API.dequeue
    (queue, value) := Queue.API.enqueue capacity

prove_algorithm rotate by
  contract_solve [Queue.pop, Queue.push, List.length_pos_iff]

end AlgoLib.Experimental.RAM.Prototype.Composition.QueueAlgorithms
