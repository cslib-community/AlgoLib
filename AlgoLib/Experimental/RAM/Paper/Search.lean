/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Internal.Search
import AlgoLib.Experimental.RAM.Paper.Syntax

/-! Public functional/cost contracts for graph traversal. The row traversal
is a procedure with a reusable summary; callers never unfold its loop proof. -/
namespace AlgoLib.Experimental.RAM.Paper.Search
open Experimental.RAM.BFS

/-- A generic while loop over a certified adjacency cursor. -/
def scanRow (a : Adjacency) : Program (model a) := paper {
  while (rowNonempty a) { call visit a; }
}

def scanEffect (g : State) : State :=
  let result := scan g.row g.seen g.queue
  { g with seen := result.1, queue := result.2, row := [] }

private theorem scanRow_run (a : Adjacency) (g : State)
    (valid : ∀ v ∈ g.row, v < a.n) :
    Run (scanRow a) g (2 * g.row.length + 1) (scanEffect g) := by
  obtain ⟨seen, queue, row, current, processed⟩ := g
  induction row generalizing seen queue with
  | nil => exact .whileFalse rfl
  | cons v vs ih =>
    have hv : v < a.n := valid v (by simp)
    have hvs : ∀ w ∈ vs, w < a.n := fun w hw => valid w (by simp [hw])
    have hx := Run.whileTrue (q := rowNonempty a) (b := .action (visit a))
      (s := ⟨seen, queue, v :: vs, current, processed⟩) rfl
      (Run.action (visit a) _ ⟨by simp, hv⟩)
      (ih (discover seen queue v).1 (discover seen queue v).2 hvs)
    convert hx using 1
    simp [visit, List.length_cons]
    omega

/-- Functional summary and linear cost of scanning any well-formed row. -/
def scanNeighbors (a : Adjacency) : Procedure (model a) where
  body := scanRow a
  requires g := ∀ v ∈ g.row, v < a.n
  effect := scanEffect
  work g := 2 * g.row.length + 1
  verification g hg := ⟨_, _, scanRow_run a g hg, rfl, Nat.le_refl _⟩

/-- Stable API equations for symbolic execution. Implementations stay opaque. -/
@[simp] theorem dequeue_requires (a : Adjacency) (g : State) :
    (dequeue a).requires g ↔ g.queue ≠ [] ∧ g.queue.headD 0 < a.n := Iff.rfl
@[simp] theorem dequeue_effect (a : Adjacency) (g : State) :
    (dequeue a).effect g = openEffect a g := rfl
@[simp] theorem dequeue_work (a : Adjacency) (g : State) : (dequeue a).work g = 1 := rfl
@[simp] theorem visit_requires (a : Adjacency) (g : State) :
    (visit a).requires g ↔ g.row ≠ [] ∧ g.row.headD 0 < a.n := Iff.rfl
@[simp] theorem visit_effect (a : Adjacency) (g : State) : (visit a).effect g = visitEffect g := rfl
@[simp] theorem visit_work (a : Adjacency) (g : State) : (visit a).work g = 1 := rfl
@[simp] theorem finish_requires (a : Adjacency) (g : State) :
    (finish a).requires g ↔ g.row = [] := Iff.rfl
@[simp] theorem finish_effect (a : Adjacency) (g : State) :
    (finish a).effect g = finishEffect g := rfl
@[simp] theorem finish_work (a : Adjacency) (g : State) : (finish a).work g = 0 := rfl
@[simp] theorem queue_test (a : Adjacency) (g : State) :
    (queueNonempty a).test g = !g.queue.isEmpty := rfl

attribute [paper_simps] dequeue_requires dequeue_effect dequeue_work
  visit_requires visit_effect visit_work finish_requires finish_effect finish_work queue_test

end AlgoLib.Experimental.RAM.Paper.Search
