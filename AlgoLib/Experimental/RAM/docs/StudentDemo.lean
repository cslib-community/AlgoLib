import AlgoLib.Experimental.RAM.Paper.Examples

/-!
# Student tutorial companion

Run from the repository root with `lake env lean StudentDemo.lean` after copying
this file there. Read the matching PDF for the trace, invariant, and cost proof.
The component walkthrough constructs `twoInsertions`, calls it through `client`,
and binds that client to `sortTwo` with functional and compiled-cost theorems.
-/
namespace AlgoLib.Experimental.RAM.Paper.StudentDemo
open Experimental.RAM.BFS

/-- A diamond on vertices 0..3 and one isolated vertex, 4.
Each triple is (edge label, first endpoint, second endpoint). -/
def graph : EdgeInput where
  n := 5
  edges := [(0, 0, 1), (1, 0, 2), (2, 1, 3), (3, 2, 3)]
  distinct := by decide
  valid := by decide

set_option linter.hashCommand false in
/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval (BFS.run (graph.fromSource 0 (by decide))).value.toList

set_option linter.hashCommand false in
/-- info: [4] -/
#guard_msgs in
#eval (BFS.run (graph.fromSource 4 (by decide))).value.toList

set_option linter.hashCommand false in
/-- info: [1, 2, 3] -/
#guard_msgs in
#eval (Insertion.run [3, 1, 2]).value

/-- A use of the generic correctness theorem; no compiler proof is needed. -/
example (xs : List Nat) : (Insertion.run xs).value.Perm xs :=
  (Insertion.run_correct xs).2

/-- The bound concerns actual compiled RAM steps. -/
example : (BFS.run (graph.fromSource 0 (by decide))).steps <= 370 * (5 + 4) := by
  have h := BFS.linear (graph.fromSource 0 (by decide))
  exact h

/-- Prove a local specification using symbolic execution and a supplied budget. -/
example (s : Insertion.State) (safe : s.todo ≠ []) :
    VC (.action Insertion.insertNext)
      (fun t _ => t = Insertion.effect s) s (s.sorted.length + 1) := by
  paper_steps []
  exact ⟨safe, Nat.le_refl _, by trivial⟩

/-- An algorithmic exit argument: no remaining values means the suffix is the result. -/
example (xs : List Nat) (s : Insertion.State)
    (h : Insertion.invariant xs s) (empty : s.todo = []) :
    s.sorted.Pairwise (· ≤ ·) ∧ s.sorted.Perm xs := by
  simpa [Insertion.invariant, empty] using h

/-- Both reachability directions hold, even when the graph is disconnected. -/
example {β : Type} {a : Adjacency} {G : Graph Nat β}
    (input : Input a G) (v : Nat) :
    (BFS.run input).value.contains v = true ↔ Reachable G input.source v :=
  BFS.run_correct input v

/-- Compose two existing certified array operations. -/
def twoBody : Program Insertion.model := paper {
  call Insertion.insertNext;
  call Insertion.insertNext;
}

/-- Two available values are sufficient; a suffix of length r costs at most 2r+3. -/
theorem twoBody_correct : Correct twoBody
    (fun s => 2 ≤ s.todo.length)
    (fun s t => t = Insertion.effect (Insertion.effect s))
    (fun s => 2 * s.sorted.length + 3) := by
  apply VC.correct
  intro s hs
  cases ht : s.todo with
  | nil => simp [ht] at hs
  | cons x xs =>
    cases xs with
    | nil => simp [ht] at hs
    | cons y ys =>
      paper_steps [twoBody, Insertion.effect, ht]
      exact ⟨by simp, by omega, by simp, by omega, by trivial⟩

/-- Package the checked body so another program can call just its contract. -/
def twoInsertions : Procedure Insertion.model where
  body := twoBody
  requires s := 2 ≤ s.todo.length
  effect s := Insertion.effect (Insertion.effect s)
  work s := 2 * s.sorted.length + 3
  verification := twoBody_correct

/-- A client uses the procedure without unfolding its body. -/
def client : Program Insertion.model := paper {
  call twoInsertions.call;
}

/-- Procedure abstraction keeps its implementation in the executable source. -/
example : client.source = twoBody.source := rfl

theorem client_correct : Correct client
    (fun s => 2 ≤ s.todo.length)
    (fun s t => t = Insertion.effect (Insertion.effect s))
    (fun s => 2 * s.sorted.length + 3) := by
  apply VC.correct
  intro s hs
  paper_steps [client, twoInsertions]
  exact ⟨hs, Nat.le_refl _, by trivial⟩

/-- Bind the client to an existing array input/output interface, without fuel. -/
def sortTwo (x y : Nat) : Result (List Nat) :=
  Insertion.interface.run client_correct [x, y] (by
    simp [Insertion.interface, Insertion.initial])

/-- The interface connects the logical effect to the observed output. -/
theorem sortTwo_value (x y : Nat) :
    (sortTwo x y).value = List.orderedInsert (· ≤ ·) x [y] := by
  obtain ⟨⟨g, hg, ho⟩, _⟩ := Insertion.interface.correct client_correct [x, y]
    (by simp [Insertion.interface, Insertion.initial])
  subst g
  simpa [sortTwo, Insertion.interface, Insertion.initial, Insertion.effect,
    List.orderedInsert] using ho

/-- The reusable result says sorted AND a permutation, for arbitrary values. -/
theorem sortTwo_correct (x y : Nat) :
    (sortTwo x y).value.Pairwise (· ≤ ·) ∧ (sortTwo x y).value.Perm [x, y] := by
  rw [sortTwo_value]
  exact ⟨(show [y].Pairwise (· ≤ ·) by simp).orderedInsert x [y],
    List.perm_orderedInsert (· ≤ ·) x [y]⟩

/-- The compiled-step bound is obtained from the same correctness certificate. -/
theorem sortTwo_cost (x y : Nat) : (sortTwo x y).steps ≤ 155 := by
  have h := (Insertion.interface.correct client_correct [x, y]
    (by simp [Insertion.interface, Insertion.initial])).2
  simpa [sortTwo, Insertion.interface, Insertion.initial, Insertion.model] using h

set_option linter.hashCommand false in
/-- info: [4, 9] -/
#guard_msgs in
#eval (sortTwo 9 4).value

set_option linter.hashCommand false in
/-- info: [4, 9] -/
#guard_msgs in
#eval (sortTwo 4 9).value

set_option linter.hashCommand false in
/-- info: [7, 7] -/
#guard_msgs in
#eval (sortTwo 7 7).value

/-- Student-facing uses of the final theorems. -/
example (x y : Nat) :
    (sortTwo x y).value.Pairwise (· ≤ ·) ∧
    (sortTwo x y).value.Perm [x, y] :=
  sortTwo_correct x y

example (x y : Nat) : (sortTwo x y).steps ≤ 155 :=
  sortTwo_cost x y

/-- A BFS call preserves untouched logical fields by symbolic execution. -/
example (a : Adjacency) (s : Search.State) (safe : (Search.visit a).requires s) :
    VC (.action (Search.visit a))
      (fun t _ => t.current = s.current ∧ t.processed = s.processed) s 1 := by
  paper_steps [Search.visitEffect]
  exact ⟨safe, by omega, by trivial⟩

end AlgoLib.Experimental.RAM.Paper.StudentDemo
