/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Library.Search
import AlgoLib.Experimental.RAM.Authoring.Methods

/-!
# Connectivity: specification → BFS method → obligations → theorem

This is the canonical BFS program and its complete algorithm-level proof. The
input is an adjacency-list representation of the repository's `Graph` together
with a valid source. The output `VertexSet` is a membership-query view of the
visited vertices. `Claim` states exact reachability, connectivity iff the output
is the whole vertex set, and a bound linear in vertices plus labelled edges.

Read `breadthFirstSearch`, `loopProof`, `verification`, then `main`. The row scan
is a separately certified library procedure, exactly as one would reuse a
proved subroutine in a paper. No memory or compiler lemmas occur in this proof.
-/
namespace AlgoLib.Experimental.RAM.Programs.Connectivity
open Authoring Experimental.RAM.BFS Authoring.Search

/-- An executable vertex-set view; displaying it as a list is a host operation. -/
abbrev VertexSet := Checked.Bitmap

/-- The mathematical set represented by the returned membership interface. -/
def vertices (S : VertexSet) : Set Nat := {v | S.contains v = true}

/-- The desired output contains exactly the vertices reachable from the source. -/
def Returns {β : Type} (G : Graph Nat β) (s : Nat) (S : VertexSet) : Prop :=
  ∀ v, v ∈ vertices S ↔ Reachable G s v

/-- The target theorem, stated before the program or its proof. A valid source
excludes an empty graph; disconnected inputs are still valid BFS inputs. -/
def Claim {β : Type} {a : Adjacency} {G : Graph Nat β}
    (bfs : Input a G → Result VertexSet) : Prop :=
  ∀ i, Returns G i.source (bfs i).value ∧
    (Connected G ↔ vertices (bfs i).value = G.vertexSet) ∧
    (bfs i).steps ≤ 370 * (a.n + i.representation.edges.card)

/-- Explicit graph/source input, vertex-set output, and linear-time contract.
Preparation initializes visited flags and the frontier; `scanNeighbors` implements
"for v in adjacency[u]: if not visited[v]: mark and enqueue v". -/
def breadthFirstSearch {β : Type} (a : Adjacency) (G : Graph Nat β) :
    Method (Search.interface a G) :=
  ram_method (input : Input a G) returns (S : VertexSet)
    using (Search.interface a G);
    requires True;
    ensures Returns G input.source S;
    credits (3 * a.n + 2 * a.entries + 1);
    time (370 * (a.n + input.representation.edges.card));
  do {
    while (queueNonempty a) {
      call dequeue a;
      call (scanNeighbors a).call;
      call finish a;
    }
  }

/-- The declared body depends on the adjacency API, not on the source value. -/
def program {β : Type} (a : Adjacency) (G : Graph Nat β) : Program (model a) :=
  (breadthFirstSearch a G).body

/-- Dequeue a vertex, scan its adjacency list, then record it as processed. -/
def processVertex (a : Adjacency) : Program (model a) := paper {
  call dequeue a;
  call (scanNeighbors a).call;
  call finish a;
}

/-- The usual frontier invariant: seen = processed ∪ queued, discovered vertices
are reachable, and processed vertices have no undiscovered neighbors. -/
def invariant {β : Type} (a : Adjacency) (G : Graph Nat β) (source : Nat)
    (s : Search.State) : Prop :=
  s.seen = discovered s.processed s.queue ∧ s.row = [] ∧
    Invariant a G source s.processed s.queue

/-- Reserve three credits per unprocessed vertex and two per adjacency entry. -/
def potential (a : Adjacency) (s : Search.State) : Nat :=
  Credits.remaining (Finset.range a.n) s.processed (fun v => 3 + 2 * (a.neighbors v).length)

/-- The user's proof has only preservation, payment, and exit cases. -/
theorem loopProof {β : Type} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) :
    LoopProof (queueNonempty a) (processVertex a) (invariant a G source) (potential a)
      (fun s => ∀ v, v ∈ s.seen ↔ Reachable G source v) where
  preservation := by
    intro s hs running
    obtain ⟨seen, _, frontier⟩ := hs
    cases hq : s.queue with
    | nil => simp [hq] at running
    | cons u queue =>
      have hi : Invariant a G source s.processed (u :: queue) := hq ▸ frontier
      have valid := hi.valid_queue u (by simp)
      have fresh := hi.disjoint u (by simp)
      have maintenance := hi.process rep
      have charge := Credits.remove (Finset.range a.n) s.processed
        (fun v => 3 + 2 * (a.neighbors v).length) (by simpa using valid) fresh
      dsimp only at charge
      paper_steps [processVertex, scanNeighbors]
      simp only [openEffect, scanEffect, finishEffect, invariant, potential,
        hq, seen, List.headD_cons, List.tail_cons, true_and, Nat.sub_zero]
      refine ⟨⟨by simp, valid⟩, by omega, a.valid u valid, by omega, Nat.zero_le _,
        maintenance, ?_⟩
      omega
  payment := by
    intro s hs running
    cases hq : s.queue with
    | nil => simp [hq] at running
    | cons u queue =>
      have hi : Invariant a G source s.processed (u :: queue) := hq ▸ hs.2.2
      have charge := Credits.remove (Finset.range a.n) s.processed
        (fun v => 3 + 2 * (a.neighbors v).length)
        (by simpa using hi.valid_queue u (by simp)) (hi.disjoint u (by simp))
      dsimp only at charge
      dsimp [potential]
      omega
  exit := by
    intro s hs stopped
    have empty : s.queue = [] := by simpa using stopped
    have result := (empty ▸ hs.2.2).exit rep
    simpa [hs.1, empty, discovered] using result

theorem correct {β : Type} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) :
    Correct (program a G) (invariant a G source)
      (fun _ s => ∀ v, v ∈ s.seen ↔ Reachable G source v) (fun s => potential a s + 1) :=
  (loopProof rep source).correct

private theorem initially {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    invariant a G i.source (Search.initial i.source) := by
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

/-- The initial potential sums one vertex charge and all adjacency-entry charges. -/
private theorem initial_credits (a : Adjacency) (source : Nat) :
    potential a (Search.initial source) = 3 * a.n + 2 * a.entries := by
  simp [potential, Search.initial, Credits.remaining, Adjacency.entries,
    Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

/-- The generated VCs use the frontier proof and the graph incidence bound.
The final payment includes initialization and all compiled operations. -/
theorem verification {β : Type} (a : Adjacency) (G : Graph Nat β) :
    (breadthFirstSearch a G).VCs := by
  method_vc [breadthFirstSearch]
  intro i _
  constructor
  · apply (correct i.representation i.source).output_vc
    · exact initially i
    · simp only [method_simps, initial_credits, Nat.le_refl]
    · intro t ht out view v
      rw [show v ∈ vertices out ↔ v < a.n ∧ v ∈ t.seen from view v, ht v]
      exact ⟨And.right, fun h => ⟨(i.representation.vertices v).mp h.right_mem, h⟩⟩
  · have := i.representation.incidenceBound
    have := i.source_valid
    method_time

/-- One certificate packages this program, its output contract, and its time bound. -/
def certified {β : Type} (a : Adjacency) (G : Graph Nat β) :
    VerifiedMethod (Search.interface a G) := ⟨breadthFirstSearch a G, verification a G⟩

/-- Run on a certified graph/source input without supplying fuel. -/
def run {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) : Result VertexSet :=
  (certified a G).run i (by trivial)

/-- Exact reachability, including vertices outside the source's component. -/
theorem run_correct {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) (v : Nat) :
    (run i).value.contains v = true ↔ Reachable G i.source v :=
  (certified a G).correct i (by trivial) |>.1 v

/-- The time contract counts actual compiled RAM steps, including visited initialization. -/
theorem linear {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    (run i).steps ≤ 370 * (a.n + i.representation.edges.card) :=
  ((certified a G).correct i (by trivial)).2

/-- All graph vertices are visited exactly when the graph is connected. -/
theorem connected_iff {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    (∀ v ∈ G.vertexSet, (run i).value.contains v = true) ↔ Connected G :=
  visits_all_iff_connected ((i.representation.vertices i.source).mpr i.source_valid) (run_correct i)

/-- Set equality version: the result has no extraneous vertices either. -/
theorem connected_iff_set {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    Connected G ↔ vertices (run i).value = G.vertexSet := by
  constructor
  · intro connected
    ext v
    constructor
    · intro hv
      exact ((run_correct i v).mp hv).right_mem
    · intro hv
      exact (connected_iff i).mpr connected v hv
  · intro all
    apply (connected_iff i).mp
    intro v hv
    change v ∈ vertices (run i).value
    rw [all]
    exact hv

/-- Main theorem: one compiled BFS returns precisely the reachable set, solves
connectivity by set equality, and runs in O(|V| + |E|) RAM steps. -/
theorem main {β : Type} {a : Adjacency} {G : Graph Nat β} : Claim (@run β a G) :=
  fun i => ⟨run_correct i, connected_iff_set i, linear i⟩

/-- Convenience API with two explicit arguments: finite graph data and source.
The source's type supplies the bounds proof; the graph constructor supplies the
representation certificate. The returned value is the reachable vertex set. -/
def search (graph : EdgeInput) (source : Fin graph.n) : Result VertexSet :=
  run (graph.fromSource source.val source.isLt)

/-- The same main theorem for the explicit graph/source convenience API. -/
theorem search_correct (graph : EdgeInput) (source : Fin graph.n) :
    Returns graph.graph source.val (search graph source).value ∧
    (Connected graph.graph ↔ vertices (search graph source).value = graph.graph.vertexSet) ∧
    (search graph source).steps ≤ 370 * (graph.n + graph.represents.edges.card) :=
  main (graph.fromSource source.val source.isLt)

end AlgoLib.Experimental.RAM.Programs.Connectivity
