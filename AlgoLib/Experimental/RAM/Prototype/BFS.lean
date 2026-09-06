/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Graph

/-!
# BFS by procedure composition: graph input → reachable set → connectivity

`code` is the outer FIFO loop, with the paper invariant alongside the program.
`Graph.processVertex` calls a separately verified neighbor scan with its own loop.
Calls inline actual bodies into the same program observed by Loom and compiled to
RAM. The proof below uses graph mathematics and procedure contracts only.

`search graph source` accepts ordinary certified edge-list data and a `Fin` source;
no fuel, memory-layout facts, compiler facts, or runtime proof arguments are needed.
`main` establishes exact reachability, connectivity iff every graph vertex is in
the output, and linear compiled RAM time including visited/FIFO initialization.
-/
namespace AlgoLib.Experimental.RAM.Prototype.BFS
open Authoring Authoring.Search Experimental.RAM.BFS

abbrev VertexSet := Checked.Bitmap

def vertices (s : VertexSet) : Set Nat := {v | s.contains v = true}

def Returns {β : Type} (G : AlgoLib.Graph Nat β) (source : Nat) (out : VertexSet) : Prop :=
  ∀ v, out.contains v = true ↔ Reachable G source v

/-- The discovered set is processed ∪ queued; processed vertices are closed under edges. -/
def frontierInvariant {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) (source : Nat)
    (s : Search.State) : Prop :=
  s.seen = discovered s.processed s.queue ∧ s.row = [] ∧
    Invariant a G source s.processed s.queue

/-- Each vertex pays once for dequeue/loop tests and each adjacency entry twice. -/
def potential (a : Adjacency) (s : Search.State) : Nat :=
  Credits.remaining (Finset.range a.n) s.processed (fun v => 3 + 2 * (a.neighbors v).length)

/-- The complete outer program. Its callee exposes the nested adjacency loop in Graph.lean. -/
def code {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) (source : Nat) :
    Annotated (Search.model a) :=
  ram_do (_entry, s, remaining) do
    while (Graph.queueNotEmpty a)
      invariant frontierInvariant a G source s
      invariant potential a s + 1 ≤ remaining
      do
        call Graph.processVertex a

/-- One application of the graph invariant pays for and summarizes a whole procedure call. -/
theorem process_preserves {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    (rep : Represents a G) {source : Nat} {s : Search.State}
    (hs : frontierInvariant a G source s) (running : s.queue ≠ []) :
    (s.queue ≠ [] ∧ s.queue.headD 0 < a.n) ∧
    frontierInvariant a G source (Graph.processEffect a s) ∧
    potential a (Graph.processEffect a s) + Graph.processWork a s + 1 = potential a s := by
  obtain ⟨seen, row, frontier⟩ := hs
  cases hq : s.queue with
  | nil => exact (running hq).elim
  | cons u queue =>
    have hi : Invariant a G source s.processed (u :: queue) := hq ▸ frontier
    have valid := hi.valid_queue u (by simp)
    have fresh := hi.disjoint u (by simp)
    have maintenance := hi.process rep
    have charge := Credits.remove (Finset.range a.n) s.processed
      (fun v => 3 + 2 * (a.neighbors v).length) (by simpa using valid) fresh
    dsimp only at charge
    refine ⟨⟨by simp, by simpa [hq] using valid⟩, ?_, ?_⟩
    · simpa [Graph.processEffect, openEffect, scanEffect, finishEffect, frontierInvariant,
        hq, seen] using maintenance
    · simp only [Graph.processEffect, Graph.processWork, openEffect, scanEffect,
        finishEffect, potential, hq, List.headD_cons]
      omega

/-- Generated correctness and time-credit conditions for the composed outer loop. -/
theorem verification {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    (rep : Represents a G) (source : Nat) (entry : Search.State)
    (initial : frontierInvariant a G source entry) :
    (code a G source).plan.vc (fun t _ => ∀ v, v ∈ t.seen ↔ Reachable G source v)
      entry (potential a entry + 1) := by
  simp only [code, Plan.vc]
  refine ⟨⟨initial, Nat.le_refl _, trivial⟩, ?_⟩
  intro s remaining hs
  obtain ⟨hi, budget, _⟩ := hs
  refine ⟨by omega, ?_⟩
  cases queue : s.queue with
  | nil =>
    simp only [Graph.queueNotEmpty, queueNonempty, queue, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    have result := (queue ▸ hi.2.2).exit rep
    simpa [hi.1, queue, discovered] using result
  | cons u rest =>
    have step := process_preserves rep hi (by simp [queue])
    simp only [Graph.queueNotEmpty, queueNonempty, queue, List.isEmpty_cons, Bool.not_false,
      ↓reduceIte, Graph.processVertex, Annotated.verify]
    refine ⟨by simpa [queue] using step.1, by omega, ?_⟩
    intro t k ht hk
    subst t
    exact ⟨step.2.1, by omega, trivial⟩

/-- BFS is itself reusable as a procedure with a reachability and cost contract. -/
def procedure {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    (rep : Represents a G) (source : Nat) : Routine (Search.model a) :=
  (code a G source).verify
    (frontierInvariant a G source)
    (fun _ t => ∀ v, v ∈ t.seen ↔ Reachable G source v)
    (fun s => potential a s + 1)
    (verification rep source)

/-- Standard initialization argument: only the valid source is discovered. -/
theorem initially {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} (i : Input a G) :
    frontierInvariant a G i.source (Search.initial i.source) := by
  refine ⟨by simp [Search.initial, discovered], rfl, ?_⟩
  refine ⟨by simp [Search.initial], by simp [Search.initial], by simp [Search.initial],
    ?_, by simp [Search.initial], ?_, by simp [Search.initial]⟩
  · intro v hv
    have : v = i.source := by simpa [Search.initial] using hv
    exact this ▸ i.source_valid
  · intro v hv
    have : v = i.source := by simpa [Search.initial] using hv
    subst v
    exact .refl ((i.representation.vertices i.source).mpr i.source_valid)

/-- Summing the per-vertex budgets counts every adjacency entry exactly once. -/
theorem initial_credits (a : Adjacency) (source : Nat) :
    potential a (Search.initial source) = 3 * a.n + 2 * a.entries := by
  simp [potential, Search.initial, Credits.remaining, Adjacency.entries,
    Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

/-- Explicit input/output contract. The executable body is independent of source and proof. -/
def breadthFirstSearch {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) :
    Method (Search.interface a G) where
  body := (code a G 0).body
  requires _ := True
  «ensures» i out := Returns G i.source out
  «credits» _ := 3 * a.n + 2 * a.entries + 1
  «time» i := 370 * (a.n + i.representation.edges.card)

/-- The source affects input data and annotations, never program generation. -/
theorem body_independent {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) (s t : Nat) :
    (code a G s).body = (code a G t).body := rfl

/-- Even the graph data do not specialize machine code: adjacency is read from RAM. -/
theorem compiled_code_independent {β γ : Type} (a b : Adjacency)
    (G : AlgoLib.Graph Nat β) (H : AlgoLib.Graph Nat γ) (s t : Nat) :
    compile (code a G s).body = compile (code b H t).body := rfl

/-- Generated interface conditions: logical reachability and automatic RAM cost transport. -/
theorem methodVerification {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) :
    Obligations (breadthFirstSearch a G)
      (fun i => Plan.call (procedure i.representation i.source)) := by
  intro i _
  constructor
  · change (procedure i.representation i.source).requires _ ∧ _
    refine ⟨initially i, ?_, ?_⟩
    · simp [procedure, Annotated.verify, breadthFirstSearch, Search.interface, initial_credits]
    · intro t k post cost out view v
      change ∀ v, out.contains v = true ↔ v < a.n ∧ v ∈ t.seen at view
      rw [view v, post v]
      exact ⟨And.right, fun h => ⟨(i.representation.vertices v).mp h.right_mem, h⟩⟩
  · have := i.representation.incidenceBound
    have := i.source_valid
    dsimp only [breadthFirstSearch]
    method_time

/-- A certificate for the same inlined procedure composition as `code`. -/
def certified {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) :
    VerifiedMethod (Search.interface a G) :=
  certify (breadthFirstSearch a G) (methodVerification a G)

/-- Execute the composed, compiled BFS with no user-supplied fuel. -/
def run {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} (i : Input a G) :
    Result VertexSet := (certified a G).run i (by trivial)

/-- The returned bitmap is precisely the source's reachable set. -/
theorem run_correct {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    (i : Input a G) : Returns G i.source (run i).value :=
  ((certified a G).correct i (by trivial)).1

/-- Linear RAM time, including initialization, for the very same executable. -/
theorem linear {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} (i : Input a G) :
    (run i).steps ≤ 370 * (a.n + i.representation.edges.card) :=
  ((certified a G).correct i (by trivial)).2

/-- BFS solves connectivity by checking whether its returned set is the whole vertex set. -/
theorem connected_iff {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    (i : Input a G) : Connected G ↔ vertices (run i).value = G.vertexSet := by
  have all := visits_all_iff_connected
    ((i.representation.vertices i.source).mpr i.source_valid) (run_correct i)
  constructor
  · intro connected
    ext v
    exact ⟨fun hv => ((run_correct i v).mp hv).right_mem, (all.mpr connected) v⟩
  · intro eq
    apply all.mp
    intro v hv
    change v ∈ vertices (run i).value
    rwa [eq]

/-- One theorem combines exact reachability, connectivity, and linear RAM complexity. -/
theorem main {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} (i : Input a G) :
    Returns G i.source (run i).value ∧
    (Connected G ↔ vertices (run i).value = G.vertexSet) ∧
    (run i).steps ≤ 370 * (a.n + i.representation.edges.card) :=
  ⟨run_correct i, connected_iff i, linear i⟩

/-- Ordinary edge-list graph plus a valid source; returns a Lean bitmap/vertex-set view. -/
def search (graph : EdgeInput) (source : Fin graph.n) : Result VertexSet :=
  run (graph.fromSource source.val source.isLt)

/-- The public theorem for the two-argument graph/source interface. -/
theorem search_correct (graph : EdgeInput) (source : Fin graph.n) :
    Returns graph.graph source.val (search graph source).value ∧
    (Connected graph.graph ↔ vertices (search graph source).value = graph.graph.vertexSet) ∧
    (search graph source).steps ≤ 370 * (graph.n + graph.represents.edges.card) :=
  main (graph.fromSource source.val source.isLt)

/-- The same program, including composed procedure bodies, satisfies upstream Loom WP. -/
theorem loom_correct {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} (i : Input a G) :
    _root_.wp (denote (breadthFirstSearch a G).body)
      (fun _ t _ => ∀ v, v ∈ t.seen ↔ Reachable G i.source v)
      (Search.initial i.source) (3 * a.n + 2 * a.entries + 1) := by
  have h := (procedure i.representation i.source).loom_correct _ (initially i)
  simpa only [procedure, Annotated.verify, initial_credits] using h

end AlgoLib.Experimental.RAM.Prototype.BFS
