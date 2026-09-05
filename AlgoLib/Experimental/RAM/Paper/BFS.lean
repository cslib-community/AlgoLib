/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Paper.Search

/-!
# BFS: the algorithm author's proof

The state contains only sets, lists, and the current vertex. All calls have
functional/cost contracts. The proof below never mentions a store or compiler.
-/
namespace AlgoLib.Experimental.RAM.Paper.BFS
open Experimental.RAM.BFS Search

/-- Dequeue a vertex, scan its adjacency list, then record it as processed. -/
def processVertex (a : Adjacency) : Program (model a) := paper {
  call dequeue a;
  call (scanNeighbors a).call;
  call finish a;
}

def program (a : Adjacency) : Program (model a) := paper {
  while (queueNonempty a) {
    call dequeue a;
    call (scanNeighbors a).call;
    call finish a;
  }
}

/-- The usual frontier invariant: seen = processed ∪ queued, discovered vertices
are reachable, and processed vertices have no undiscovered neighbors. -/
def invariant {β : Type*} (a : Adjacency) (G : Graph Nat β) (source : Nat)
    (s : Search.State) : Prop :=
  s.seen = discovered s.processed s.queue ∧ s.row = [] ∧
    Invariant a G source s.processed s.queue

/-- Reserve three credits per unprocessed vertex and two per adjacency entry. -/
def potential (a : Adjacency) (s : Search.State) : Nat :=
  Credits.remaining (Finset.range a.n) s.processed (fun v => 3 + 2 * (a.neighbors v).length)

/-- The user's proof has only preservation, payment, and exit cases. -/
theorem loopProof {β : Type*} {a : Adjacency} {G : Graph Nat β}
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

theorem correct {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) :
    Correct (program a) (invariant a G source)
      (fun _ s => ∀ v, v ∈ s.seen ↔ Reachable G source v) (fun s => potential a s + 1) :=
  (loopProof rep source).correct

end AlgoLib.Experimental.RAM.Paper.BFS
