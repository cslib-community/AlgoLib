/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Programs.Examples
import AlgoLib.Experimental.RAM.Tests.Algorithms

/-!
# Regression checks: Paper

Checks the relevant executable, proof, or compiler guarantees against regressions. Expected-output
assertions and theorem checks are part of the test, not extra algorithm implementations.

See Tests/README.md for coverage and build commands. Canonical programs live exclusively under
Programs.

## Further details

# Regression tests for paper-level RAM verification

Check compositional syntax, symbolic framing, rejected budgets, and compiled
sorting and graph traversal against independent reference implementations.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Tests
open Experimental.RAM.BFS

/-- The syntax is compositional: nested control flow is not a BFS macro. -/
def nested : Program Insertion.model := paper {
  while (Insertion.more) {
    if (Insertion.more) { call Insertion.insertNext; } else {}
  }
}

example : nested.source = Checked.Language.Cmd.loop Insertion.more.implementation
    (.branch Insertion.more.implementation Insertion.insertNext.implementation .skip) := rfl

/-- Symbolic execution preserves untouched logical fields automatically. -/
example (a : Adjacency) (s : Search.State) (safe : (Search.visit a).requires s) :
    VC (.action (Search.visit a))
      (fun t _ => t.current = s.current ∧ t.processed = s.processed) s 1 := by
  paper_steps [Search.visitEffect]
  exact ⟨safe, by omega, by trivial⟩

/-- A false invariant with a true guard cannot claim free termination. -/
theorem zero_budget_rejected {State : Type} {M : Model State} {q : Guard M}
    {body : Program M} {I Q : State → Prop} {s : State} (hs : I s) (go : q.test s = true) :
    ¬ LoopProof q body I (fun _ => 0) Q := by
  intro h
  have := h.payment s hs go
  omega

/-- A library cannot mint an action's required credits. -/
example (s : Insertion.State) :
    ¬ VC (.action Insertion.insertNext) (fun _ _ => True) s 0 := by
  paper_steps []
  omega

/-- Overlapping writes cannot frame a protected cell. -/
example : ¬ Checked.Language.Framing.WritesOnly (∅ : Set Nat)
    (fun _ => 0) (Function.update (fun _ => 0) 0 1) := by
  intro h
  have := h 0 (by simp)
  simp at this

/- Empty input, duplicate values, all small graphs, disconnected graphs,
self-loops and parallel edges exercise the new compiled authoring path. -/
set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  for n in List.range 6 do
    for mask in List.range (3 ^ n) do
      let xs := (List.range n).map (fun i => mask / 3 ^ i % 3)
      let r := Programs.Sorting.run xs
      unless r.value == xs.mergeSort (· ≤ ·) do
        throw <| IO.userError s!"paper sort: {xs}"
      unless r.steps ≤ 50*n*n + 100*n + 55 do
        throw <| IO.userError s!"paper sort budget: {xs}"
  for mask in List.range 64 do
    for source in List.finRange 4 do
      let graph := Experimental.RAM.Tests.smallGraph mask
      let r := Programs.Connectivity.run (graph.fromSource source.val source.isLt)
      unless r.value.toList == Experimental.RAM.Tests.reference graph source.val do
        throw <| IO.userError s!"paper BFS: mask={mask}, source={source.val}"
      unless r.steps ≤ 370 * (4 + graph.edges.length) do
        throw <| IO.userError s!"paper BFS budget: mask={mask}, source={source.val}"
  let singleton := Experimental.RAM.Legacy.Examples.singleton
  unless (Programs.Connectivity.run (singleton.fromSource 0 (by decide))).value.toList == [0] do
    throw <| IO.userError "paper singleton"
  let multi := Experimental.RAM.Legacy.Examples.multigraph
  unless (Programs.Connectivity.run (multi.fromSource 0 (by decide))).value.toList == [0, 1, 2] do
    throw <| IO.userError "paper loops/parallel edges"

end AlgoLib.Experimental.RAM.Authoring.Tests
