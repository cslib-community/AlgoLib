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
    while i < visited.size named clear
      invariant "size" visited.size = a.n
      invariant "index" i ≤ visited.size
      invariant "zero" ∀ v < i, visited[v]! = 0
      iterations_at_most visited.size - i
      do
        visited[i] := 0
        i := i + 1
    queue := Queue.API.initializeQueue
    visited[source] := 1
    (queue, source) := Queue.API.enqueue capacity
    let mut u := 0
    let mut v := 0
    while queue.nonempty named search
      invariant "empty" row = []
      invariant "size" visited.size = a.n
      invariant "frontier" Frontier a G source (marked visited) queue
      amortized_work work a (marked visited) queue initially_at_most a.n + a.entries
      do
        (queue, u) := Queue.API.dequeue
        (row, u) := GraphCursor.API.neighbors a
        while row.nonempty named scan
          invariant "size" visited.size = a.n
          invariant "discovered" QueueOK visited queue
          invariant "vertices" ∀ w ∈ row, w < a.n
          invariant "scan" scan row (marked visited) queue =
            at_loop_entry(scan row (marked visited) queue)
          iterations_at_most row.length
          do
            (row, v) := GraphCursor.API.nextNeighbor
            if visited[v]! == 0 then
              visited[v] := 1
              (queue, v) := Queue.API.enqueue capacity

-- During authoring: #named_goals bfs only search.scan.preserve
prove_algorithm bfs where
  case clear.preserve.zero => by
    apply zero_prefix <;> first | assumption | omega
  case search.initialize.frontier => by
    apply seed rep <;> first | assumption | omega | (intro v hv; apply_assumption; omega)
  case search.account.initial => by
    grind only [work_le_total]
  case search.requires => by
    simp_all [Queue.nonempty] <;>
      exact frontier_head (by assumption) (by assumption)
  case search.account.call => by
    simp_all [Queue.nonempty]
    have step := process_head rep (h := by assumption) (by assumption)
    omega
  case search.scan.account.initial => by
    simp_all [Queue.nonempty]
    have step := process_head rep (h := by assumption) (by assumption)
    omega
  case search.scan.initialize.discovered => by
    exact queue_tail _ _ (frontier_queue _ _ _ _ _ (by assumption))
  case search.scan.initialize.vertices => by
    simp_all [Queue.nonempty]
    exact a.valid _ (frontier_head (by assumption) (by assumption)) _ (by assumption)
  case search.scan.terminate => by
    simp_all [Queue.nonempty, List.length_pos_iff]
  case search.scan.requires => by
    simp_all [Queue.nonempty] <;> (
      apply Nat.lt_of_lt_of_le
        (room_for_fresh _ _ _ (by assumption) ?_ (by assumption)) (by omega)
      grind only [head_mem])
  case search.scan.safety => by
    simp_all [Queue.nonempty] <;> grind only [head_mem]
  case search.scan.preserve.discovered => by
    simp_all [Queue.nonempty]
    apply queue_enqueue <;> first | assumption | grind only [head_mem]
  case search.scan.preserve.vertices => by
    solve_by_elim [List.mem_of_mem_tail]
  case search.scan.preserve.scan => by
    simp_all [Queue.nonempty]
    grind only [scan_mark, scan_skip, head_mem]
  case search.preserve.empty => by simp_all [Queue.nonempty]
  case search.preserve.frontier => by
    simp_all [Queue.nonempty, scan.eq_1]
    have step := process_head rep (h := by assumption) (by assumption)
    grind only []
  case search.terminate.decrease => by
    simp_all [Queue.nonempty, scan.eq_1]
    have step := process_head rep (h := by assumption) (by assumption)
    grind only [scan_work]
  case search.account.iteration => by
    simp_all [Queue.nonempty, scan.eq_1]
    have step := process_head rep (h := by assumption) (by assumption)
    grind only [scan_work]
  case search.exit => by
    simp_all [Queue.nonempty] <;> (
      have done := finish_bitmap rep _ _ (by assumption)
      grind only [])

/-- The same algorithm certificate also establishes actual Loom weakest preconditions. -/
theorem loom_correct (β : Type) (a : Adjacency) (G : Graph Nat β)
    (rep : Represents a G) (capacity : Nat) (input : List Nat × Array Nat × List Nat × Nat)
    (valid : (bfs β a G rep capacity).requires input) :
    _root_.wp (denote (bfs β a G rep capacity).body input)
      (fun output _ _ => (bfs β a G rep capacity).ensures input output)
      () ((bfs β a G rep capacity).credits input) :=
  (bfs β a G rep capacity).loom_correct (bfsVerification β a G rep capacity) input valid

end AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
