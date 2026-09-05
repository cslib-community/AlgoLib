/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Paper
import AlgoLib.Experimental.RAM.BFS.GraphInput

/-!
# Explicit BFS arguments and returned values

`Arguments` supplies the adjacency input and source. Its representation and
bounds proofs are erased. `Result.visited` is the returned bitmap, and `steps`
is the machine operation count. Clients do not inspect registers or addresses.
-/
namespace AlgoLib.Experimental.RAM.BFS
open Checked

/-- Inputs `(V, adjacency, s)`: `V` is `0, …, adjacency.n-1`, and `source` is in V. -/
structure Arguments {β : Type*} (G : Graph Nat β) where
  adjacency : Adjacency
  representation : Represents adjacency G
  source : Fin adjacency.n

def Arguments.vertices {β : Type*} {G : Graph Nat β} (args : Arguments G) : Finset Nat :=
  Finset.range args.adjacency.n

def Arguments.toInput {β : Type*} {G : Graph Nat β} (args : Arguments G) : Input args.adjacency G :=
  args.representation.input args.source.val args.source.isLt

/-- The typed program signature: adjacency/source arguments in, visited bitmap out. -/
def procedure {β : Type*} (G : Graph Nat β) : Procedure (Arguments G) Bitmap where
  encode args := args.toInput.initial
  body := Paper.bfs.compile
  output := Paper.bfs.output
  terminates args := by
    obtain ⟨k, t, hx, _⟩ := bfs_correct args.representation args.source.val args.source.isLt
      args.toInput.initial (by simp [Input.initial])
      (by simp [Input.initial, Arguments.toInput, Represents.input, vertex, size]) args.toInput.heap
    exact ⟨k, t, by simpa [Paper.bfs_compiles] using hx⟩

/-- Named results rather than a raw `(steps, RAM state)` tuple. -/
structure Result where
  visited : Bitmap
  steps : Nat

/-- Run the paper program. No fuel or register/memory arguments are exposed. -/
def run {β : Type*} {G : Graph Nat β} (args : Arguments G) : Result :=
  let result := (procedure G).run args
  ⟨result.output, result.steps⟩

private theorem run_view {β : Type*} {G : Graph Nat β} (args : Arguments G) :
    run args = ⟨⟨args.toInput.run.2.regs size, args.toInput.run.2.memory, 5, 1⟩,
      args.toInput.run.1⟩ := rfl

/-- The return descriptor's length is preserved by every instruction of BFS. -/
theorem result_length {β : Type*} {G : Graph Nat β} (args : Arguments G) :
    (run args).visited.length = args.adjacency.n := by
  rw [run_view]
  have h := args.toInput.correct.1.frame_register size (by decide)
  simpa [Input.initial] using h

/-- Exact graph specification through the public output interface. -/
theorem result_correct {β : Type*} {G : Graph Nat β} (args : Arguments G) (v : Nat) :
    (run args).visited.contains v = true ↔ Reachable G args.source.val v := by
  simp only [Bitmap.contains, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, result_length]
  rw [run_view]
  exact args.toInput.correct.2.1 v

theorem result_list_correct {β : Type*} {G : Graph Nat β} (args : Arguments G) (v : Nat) :
    v ∈ (run args).visited.toList ↔ Reachable G args.source.val v := by
  simp only [Bitmap.toList, List.mem_filter, List.mem_range, result_length]
  constructor
  · intro h; exact (result_correct args v).mp h.2
  · intro h
    exact ⟨(args.representation.vertices v).mp h.right_mem, (result_correct args v).mpr h⟩

theorem result_connected {β : Type*} {G : Graph Nat β} (args : Arguments G) :
    (∀ v ∈ args.vertices, (run args).visited.contains v = true) ↔ Connected G := by
  have h := visits_all_iff_connected
    ((args.representation.vertices _).mpr args.source.isLt) (result_correct args)
  simpa [Arguments.vertices, args.representation.vertices] using h

theorem result_linear {β : Type*} {G : Graph Nat β} (args : Arguments G) :
    (run args).steps ≤ 32 * (args.adjacency.n + args.representation.edges.card) := by
  rw [run_view]
  exact args.toInput.linear

/-- Convenience constructor: callers name their graph input and source explicitly. -/
def EdgeInput.arguments (input : EdgeInput) (source : Nat) (hs : source < input.n) :
    Arguments input.graph where
  adjacency := input.adjacency
  representation := input.represents
  source := ⟨source, hs⟩

end AlgoLib.Experimental.RAM.BFS
