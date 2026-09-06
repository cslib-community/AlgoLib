/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirstSpec

/-!
# BFS proof declarations against the generated source API

Initialization, preservation, termination, and accounting are checked independently.
The same assembled procedure certificate supplies Loom reasoning and all queue backends.
No instruction or private memory representation is available in this proof module.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
open Experimental.RAM.BFS BFSFacts
open Queue (nonempty)

-- During authoring: #named_goals bfs only search.scan.preserve
prove_obligation bfs.ObligationAPI.clear.preserve.zero by
  apply zero_prefix <;> first | assumption | omega

prove_obligation bfs.ObligationAPI.search.initialize.frontier by
  apply seed rep <;> first | assumption | omega | (intro v hv; apply_assumption; omega)

prove_obligation bfs.ObligationAPI.search.account.initial by
  grind only [work_le_total]

prove_obligation bfs.ObligationAPI.search.requires by
  simp_all [Queue.nonempty] <;>
    exact frontier_head (by assumption) (by assumption)

prove_obligation bfs.ObligationAPI.search.account.call by
  simp_all [Queue.nonempty]
  have step := process_head rep (h := by assumption) (by assumption)
  omega

prove_obligation bfs.ObligationAPI.search.scan.account.initial by
  simp_all [Queue.nonempty]
  have step := process_head rep (h := by assumption) (by assumption)
  omega

prove_obligation bfs.ObligationAPI.search.scan.initialize.discovered by
  exact queue_tail _ _ (frontier_queue _ _ _ _ _ (by assumption))

prove_obligation bfs.ObligationAPI.search.scan.initialize.vertices by
  simp_all [Queue.nonempty]
  exact a.valid _ (frontier_head (by assumption) (by assumption)) _ (by assumption)

prove_obligation bfs.ObligationAPI.search.scan.terminate.positive by
  simp_all [Queue.nonempty, List.length_pos_iff]

prove_obligation bfs.ObligationAPI.search.scan.terminate.decrease by
  simp_all [Queue.nonempty, List.length_pos_iff]

prove_obligation bfs.ObligationAPI.search.scan.requires by
  simp_all [Queue.nonempty] <;> (
    apply Nat.lt_of_lt_of_le
      (room_for_fresh _ _ _ (by assumption) ?_ (by assumption)) (by omega)
    grind only [head_mem])

prove_obligation bfs.ObligationAPI.search.scan.safety by
  simp_all [Queue.nonempty] <;> grind only [head_mem]

prove_obligation bfs.ObligationAPI.search.scan.preserve.discovered by
  simp_all [Queue.nonempty]
  apply queue_enqueue <;> first | assumption | grind only [head_mem]

prove_obligation bfs.ObligationAPI.search.scan.preserve.vertices by
  solve_by_elim [List.mem_of_mem_tail]

prove_obligation bfs.ObligationAPI.search.scan.preserve.scan by
  simp_all [Queue.nonempty]
  grind only [scan_mark, scan_skip, head_mem]

prove_obligation bfs.ObligationAPI.search.preserve.empty by
  simp_all [Queue.nonempty]

prove_obligation bfs.ObligationAPI.search.preserve.frontier by
  simp_all [Queue.nonempty, scan.eq_1]
  have step := process_head rep (h := by assumption) (by assumption)
  grind only []

prove_obligation bfs.ObligationAPI.search.terminate.decrease by
  simp_all [Queue.nonempty, scan.eq_1]
  have step := process_head rep (h := by assumption) (by assumption)
  grind only [scan_work]

prove_obligation bfs.ObligationAPI.search.account.iteration by
  simp_all [Queue.nonempty, scan.eq_1]
  have step := process_head rep (h := by assumption) (by assumption)
  grind only [scan_work]

prove_obligation bfs.ObligationAPI.search.exit by
  simp_all [Queue.nonempty] <;> (
    have done := finish_bitmap rep _ _ (by assumption)
    grind only [])

complete_algorithm bfs

/-- The same algorithm certificate also establishes actual Loom weakest preconditions. -/
theorem loom_correct (β : Type) (a : Adjacency) (G : Graph Nat β)
    (rep : Represents a G) (capacity : Nat) (input : List Nat × Array Nat × List Nat × Nat)
    (valid : (bfs β a G rep capacity).requires input) :
    _root_.wp (denote (bfs β a G rep capacity).body input)
      (fun output _ _ => (bfs β a G rep capacity).ensures input output)
      () ((bfs β a G rep capacity).credits input) :=
  (bfs β a G rep capacity).loom_correct (bfsVerification β a G rep capacity) input valid

end AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
