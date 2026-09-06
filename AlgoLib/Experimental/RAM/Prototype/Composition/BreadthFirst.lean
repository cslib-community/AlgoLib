/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend
import AlgoLib.Experimental.RAM.Prototype.Composition.Loom
import AlgoLib.Experimental.RAM.Prototype.Composition.Queue
import AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursor
import AlgoLib.Experimental.RAM.Prototype.Composition.BFSFacts

/-!
# One paper-style BFS over owned queue, graph cursor, and visited array

Read the body first: initialize, seed the FIFO, then scan the neighbors of each
dequeued vertex. The graph is specified using the repository Graph definition.
Queue representations and amortization are absent. The outer work measure counts
vertices and adjacency entries; the frontend supplies the logical cost multiplier.
The same source proof is intended for both registered FIFO implementations.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
open Experimental.RAM.BFS BFSFacts
open Queue (nonempty)

ram method bfs (β : Type) (a : Adjacency) (G : AlgoLib.Graph Nat β)
    (rep : Represents a G) (capacity : Nat)
    (mut row : List Nat) (mut visited : Array Nat) (mut queue : List Nat) (mut source : Nat)
  return (result : List Nat × Array Nat × List Nat × Nat)
  require row = []
  require visited.size = a.n
  require source < a.n
  require a.n ≤ capacity
  ensures ∀ v, v ∈ marked visited ↔ Reachable G sourceOld v
  ensures queue = []
  do
    let mut i := 0
    while i < visited.size
      invariant visited.size = a.n
      invariant i ≤ visited.size
      invariant ∀ v < i, visited[v]! = 0
      iterations_at_most visited.size - i
      do
        visited[i] := 0
        i := i + 1
    queue := Queue.API.initializeQueue
    visited[source] := 1
    (queue, source) := Queue.API.enqueue capacity
    let mut u := 0
    let mut v := 0
    while queue.nonempty
      invariant row = []
      invariant visited.size = a.n
      invariant "BFS frontier" Frontier a G source (marked visited) queue
      amortized_work work a (marked visited) queue initially_at_most a.n + a.entries
      do
        (queue, u) := Queue.API.dequeue
        (row, u) := GraphCursor.API.neighbors a
        while row.nonempty
          invariant visited.size = a.n
          invariant "FIFO contains discovered vertices" QueueOK visited queue
          invariant ∀ w ∈ row, w < a.n
          invariant "neighbor scan" scan row (marked visited) queue =
            at_loop_entry(scan row (marked visited) queue)
          iterations_at_most row.length
          do
            (row, v) := GraphCursor.API.nextNeighbor
            if visited[v]! == 0 then
              visited[v] := 1
              (queue, v) := Queue.API.enqueue capacity

set_option maxHeartbeats 2000000 in
-- Normalize the nested, parameterized VCs once; no compiler reasoning is required.
prove_algorithm bfs by
  intro β a G rep capacity
  paper_vc
  all_goals try simp_all [Queue.nonempty]
  all_goals try omega
  all_goals try solve
    | apply zero_prefix <;> first | assumption | omega
  all_goals try solve
    | apply seed rep <;> first | assumption | omega | (intro v hv; apply_assumption; omega)
  all_goals try have step := process_head rep (h := by assumption) (by assumption)
  all_goals try omega
  all_goals try solve
    | exact a.valid _ step.1 _ (by assumption)
  all_goals try solve_by_elim [List.mem_of_mem_tail]
  all_goals try solve
    | apply Nat.lt_of_lt_of_le (room_for_fresh _ _ _ (by assumption) ?_ (by assumption))
        (by omega)
      grind only [head_mem]
  all_goals try have done := finish_bitmap rep _ _ (by assumption)
  all_goals grind (gen := 4) (instances := 200) only [Array.size_setIfInBounds,
    frontier_queue, queue_tail, queue_enqueue, room_for_fresh, scan_mark, scan_skip,
    work_le_total, scan_work, frontier_head, head_mem, Adjacency.valid, List.mem_of_mem_tail,
    scan.eq_1, List.length_pos_iff, mem_marked]

/-- The same algorithm certificate also establishes actual Loom weakest preconditions. -/
theorem loom_correct (β : Type) (a : Adjacency) (G : Graph Nat β)
    (rep : Represents a G) (capacity : Nat) (input : List Nat × Array Nat × List Nat × Nat)
    (valid : (bfs β a G rep capacity).requires input) :
    _root_.wp (denote (bfs β a G rep capacity).body input)
      (fun output _ _ => (bfs β a G rep capacity).ensures input output)
      () ((bfs β a G rep capacity).credits input) :=
  (bfs β a G rep capacity).loom_correct (bfsVerification β a G rep capacity) input valid

end AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
