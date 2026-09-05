/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Syntax
import AlgoLib.Experimental.RAM.Backend.Language.Refinement
import AlgoLib.Experimental.RAM.Backend.Memory.GraphInput
import AlgoLib.Experimental.RAM.Backend.Certificates.BFS

/-!
# Legacy demonstration: BFS

Retains an earlier lower-level example for historical comparison and compiler regression coverage.
This is an explicit opt-in module and is not imported by the public RAM entry point.

Use Programs/Sorting and Programs/Connectivity for the current input/output method and
algorithm-level VC workflow.

## Further details

# BFS connectivity through the complete source-to-RAM stack

The executable is the compiled typed DSL. The internal invariant certificate
relates a FIFO and linked adjacency lists to the repository's Graph definition.
All initialization, source expressions, guards, and library operations are paid.
-/
namespace AlgoLib.Experimental.RAM.Legacy.BFS
open Checked Checked.Language

private abbrev head := Refinement.slot .base
private abbrev tail := Refinement.slot .count
private abbrev size := Refinement.slot .limit
private abbrev arc := Refinement.slot .cursor
private abbrev vertex := Refinement.slot .key
private abbrev address := Refinement.slot .next
private abbrev neighbor := Refinement.slot .temp
private abbrev marked := Refinement.slot .live
private abbrev heap := Refinement.memory

/-- Clear one visited flag and advance the vertex iterator. -/
def clearVertex : Cmd := program {
  address := 5 * head;
  address := address + 1;
  heap[address] := 0;
  head := head + 1;
}

/-- Mark the source before enqueuing it. -/
def seedSource : Cmd := program {
  address := 5 * vertex;
  address := address + 1;
  heap[address] := 1;
  heap[2] := vertex;
  head := 0;
  tail := 1;
}

/-- Read the FIFO front and open that vertex's adjacency list. -/
def dequeueAndOpen : Cmd := program {
  address := 5 * head;
  address := address + 2;
  vertex := heap[address];
  head := head + 1;
  address := 5 * vertex;
  arc := heap[address];
}

/-- One adjacency entry. Each newly discovered vertex is enqueued once. -/
def discoverAndAdvance : Cmd := program {
  address := 5 * arc;
  address := address + 3;
  neighbor := heap[address];
  address := 5 * neighbor;
  address := address + 1;
  marked := heap[address];
  if marked == 0 {
    heap[address] := 1;
    address := 5 * tail;
    address := address + 2;
    heap[address] := neighbor;
    tail := tail + 1;
  } else {}
  address := 5 * arc;
  address := address + 4;
  arc := heap[address];
}

/-- The complete source program, including clearing arbitrary initial flag memory. -/
def sourceProgram : Cmd := program {
  head := 0;
  while head < size { call clearVertex; }
  call seedSource;
  while head < tail {
    call dequeueAndOpen;
    while 0 < arc { call discoverAndAdvance; }
  }
}

theorem refinement :
    (Refinement.lift Experimental.RAM.BFS.bfsCode).normalize = sourceProgram.normalize := rfl

def Requires (a : Experimental.RAM.BFS.Adjacency) (source : Nat) (s : Store) : Prop :=
  Refinement.Ready s ∧ s.vars .word size.name = a.n ∧
    s.vars .word vertex.name = source ∧ Experimental.RAM.BFS.Heap a s.heap

def Post {β : Type*} (a : Experimental.RAM.BFS.Adjacency) (G : Graph Nat β)
    (source : Nat) (_s t : Store) : Prop :=
  Experimental.RAM.BFS.ReturnsReachable G source (fun v => v < a.n ∧ t.heap (5 * v + 1) = 1)

def budget (n m : Nat) : Nat := 65 * n + 160 * m + 45

theorem correct {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (rep : Experimental.RAM.BFS.Represents a G) (source : Nat) (hs : source < a.n) :
    Contract sourceProgram (Requires a source) (Post a G source)
      (fun _ => budget a.n rep.edges.card) := by
  intro s ⟨hready, hn, hsource, hheap⟩
  obtain ⟨k, t, hx, hQ, hk⟩ := Experimental.RAM.BFS.bfs_correct rep source hs
    (Refinement.view s) hn hsource hheap
  obtain ⟨j, u, hu, _, hview, hj⟩ := Refinement.lift_correct hx (by decide) s hready rfl
  refine ⟨j, u, hu.transfer refinement, ?_, ?_⟩
  · have hm : u.heap = t.memory := congrArg State.memory hview
    simpa [Post, hm] using hQ
  · dsimp [budget]; omega

/-- Correctness and time VCs for the actual frontend program. -/
theorem verification {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (rep : Experimental.RAM.BFS.Represents a G) (source : Nat) (hs : source < a.n)
    (s : Store) (h : Requires a source s) :
    VC sourceProgram (fun t _ => Post a G source s t) s (budget a.n rep.edges.card) :=
  (correct rep source hs).vc s h

def executable {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (rep : Experimental.RAM.BFS.Represents a G) (source : Nat) (hs : source < a.n) : Method where
  body := sourceProgram
  requires := Requires a source
  ensures := Post a G source
  budget _ := budget a.n rep.edges.card
  verification := VC.contract _ _ _ _ (verification rep source hs)

def input {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) : Store where
  vars ty name := if ty = .word ∧ name = size.name then a.n else
    if ty = .word ∧ name = vertex.name then args.source else 0
  heap := args.memory

theorem input_valid {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) : Requires a args.source (input args) := by
  refine ⟨?_, ?_, ?_, args.heap⟩ <;>
    simp [input, Refinement.Ready, Refinement.slot, Refinement.name]

structure Result where
  visited : Bitmap
  steps : Nat

def run {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) : Result :=
  let r := (executable args.representation args.source args.source_valid).run
    (input args) (input_valid args)
  ⟨⟨a.n, r.2.heap, 5, 1⟩, r.1⟩

theorem run_correct {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) (v : Nat) :
    (run args).visited.contains v = true ↔ Experimental.RAM.BFS.Reachable G args.source v := by
  have h := (executable args.representation args.source args.source_valid).correct
    (input args) (input_valid args)
  simpa [run, Bitmap.contains, executable, Post] using h.2.1 v

theorem result_length {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) : (run args).visited.length = a.n := rfl

theorem result_list_correct {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) (v : Nat) :
    v ∈ (run args).visited.toList ↔ Experimental.RAM.BFS.Reachable G args.source v := by
  simp only [Bitmap.toList, List.mem_filter, List.mem_range, result_length]
  constructor
  · intro h; exact (run_correct args v).mp h.2
  · intro h
    exact ⟨(args.representation.vertices v).mp h.right_mem, (run_correct args v).mpr h⟩

theorem linear {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) :
    (run args).steps ≤ 160 * (a.n + args.representation.edges.card) := by
  have h := (executable args.representation args.source args.source_valid).correct
    (input args) (input_valid args)
  have hpos := args.source_valid
  have hk := h.2.2
  dsimp [run, executable, budget] at *
  omega

theorem connected_iff {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (args : Experimental.RAM.BFS.Input a G) :
    (∀ v ∈ G.vertexSet, (run args).visited.contains v = true) ↔ Experimental.RAM.BFS.Connected G :=
  Experimental.RAM.BFS.visits_all_iff_connected
    ((args.representation.vertices args.source).mpr args.source_valid) (run_correct args)

/-- End-to-end refinement of the compiled instructions to the graph specification. -/
theorem ram_correct {β : Type*} {a : Experimental.RAM.BFS.Adjacency} {G : Graph Nat β}
    (rep : Experimental.RAM.BFS.Represents a G) (source : Nat) (hs : source < a.n)
    (s : State) (h : Requires a source (observe s)) :
    ∃ k t, Exec sourceProgram.compile s k t ∧ Post a G source (observe s) (observe t) ∧
      k ≤ budget a.n rep.edges.card := (correct rep source hs).ram s h

end AlgoLib.Experimental.RAM.Legacy.BFS
