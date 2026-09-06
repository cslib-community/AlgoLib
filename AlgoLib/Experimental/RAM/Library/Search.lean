/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Adapters.Search
import AlgoLib.Experimental.RAM.Backend.Adapters.SearchInput
import AlgoLib.Experimental.RAM.Authoring.Methods

/-!
# Public graph traversal contracts

Use dequeue, visit, scanNeighbors, and finish to manipulate a logical frontier and adjacency
cursor. The input/output adapter is re-exported here so programs never import backend files.

scanNeighbors is a separately specified and verified library procedure. Its row loop is reused by
the one canonical connectivity algorithm in Programs/Connectivity.lean.

## Further details

Public functional/cost contracts for graph traversal. The row traversal
is a procedure with a reusable summary; callers never unfold its loop proof.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Search
open Experimental.RAM.BFS

/-- A generic while loop over a certified adjacency cursor. -/
def scanRow (a : Adjacency) : Program State := paper {
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
def scanNeighbors (a : Adjacency) : Procedure State where
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

/-- Public logical initial-state equation; preparation code remains internal. -/
@[method_simps] theorem input_state {β : Type} (a : Adjacency) (G : Graph Nat β)
    (i : Input a G) : (interface a G).initial i = initial i.source := rfl

/-- Public meaning of a returned visited-set view. -/
@[method_simps] theorem output_view {β : Type} (a : Adjacency) (G : Graph Nat β)
    (s : State) (out : Checked.Bitmap) :
    (interface a G).Observes s out ↔
      ∀ v, out.contains v = true ↔ v < a.n ∧ v ∈ s.seen := Iff.rfl

/-- Certified graph preparation cost, consumed by method_time. -/
@[method_simps] theorem preparation_work {β : Type} (a : Adjacency) (G : Graph Nat β)
    (i : Input a G) : (interface a G).preparationCost i = 25 * a.n + 45 := rfl

/-- Certified implementation overhead, consumed by method_time. -/
@[method_simps] theorem implementation_work (a : Adjacency) : (model a).overhead = 75 := rfl

/-- Normalize inferred RAM cost using the adjacency representation's incidence bound. -/
theorem linear_of_credits {β : Type} {a : Adjacency} {G : Graph Nat β}
    (i : Input a G) {steps : Nat}
    (h : steps ≤ (interface a G).preparationCost i +
      (model a).overhead * (3 * a.n + 2 * a.entries + 1)) :
    steps ≤ 370 * (a.n + i.representation.edges.card) := by
  have := i.representation.incidenceBound
  have := i.source_valid
  simp only [preparation_work, implementation_work] at h
  omega

end AlgoLib.Experimental.RAM.Authoring.Search
