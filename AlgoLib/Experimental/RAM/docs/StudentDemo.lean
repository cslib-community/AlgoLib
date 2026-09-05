import AlgoLib.Experimental.RAM.Paper.Examples

/-!
# Student tutorial companion

Run from the repository root with `lake env lean StudentDemo.lean` after copying
this file there. Read the matching PDF for the trace, invariant, and cost proof.
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

end AlgoLib.Experimental.RAM.Paper.StudentDemo
