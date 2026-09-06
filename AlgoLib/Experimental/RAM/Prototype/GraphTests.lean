/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.BFS
import AlgoLib.Experimental.RAM.Tests.Algorithms

/-!
# Executable and negative tests for graph procedure composition

All 64 simple graphs on four vertices and all four sources are compared with an
independent bounded graph-closure oracle. Extra tests cover isolated vertices,
loops and parallel labelled edges. Every run executes the new composed RAM body.
Negative checks ensure a procedure call cannot omit its precondition or time
payment, and an invalid adjacency access cannot be accepted as a safe primitive.
-/
namespace AlgoLib.Experimental.RAM.Prototype.GraphTests
open Authoring Experimental.RAM.BFS

/-- Expected model types also support procedures with no primitive to infer from. -/
def emptyCode (State : Type) : Annotated State :=
  ram_do (_entry, _s, _remaining) do
    pure ()

example (State : Type) (s : State) (c : Nat) :
    (emptyCode State).plan.vc (fun t r => t = s ∧ r = c) s c := ⟨rfl, rfl⟩

/-- A small ordinary input: edges are (label, source, target). -/
def path : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2), (2, 2, 3)]
  distinct := by decide
  valid := by decide

/-- The source component is {0,1}; vertex 2 is isolated. -/
def disconnected : EdgeInput where
  n := 3
  edges := [(0, 0, 1)]
  distinct := by decide
  valid := by decide

set_option linter.hashCommand false in
/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval (BFS.search path ⟨0, by decide⟩).value.toList

set_option linter.hashCommand false in
/-- info: [0, 1] -/
#guard_msgs in
#eval (BFS.search disconnected ⟨0, by decide⟩).value.toList

set_option linter.hashCommand false in
/-- info: [2] -/
#guard_msgs in
#eval (BFS.search disconnected ⟨2, by decide⟩).value.toList

/-- Modular calls retain the callee's program, rather than replacing it by an action. -/
example (a : Adjacency) : (Graph.processCode a).body =
    .seq (.action (Graph.dequeue a))
      (.seq (Graph.scanCode a).body (.seq (.action (Graph.finishVertex a)) .skip)) := rfl

/-- A call's proof plan cannot supply an unpaid computation. -/
theorem unpaid_call {State : Type} (p : Routine State) (s : State)
    (positive : 0 < p.work s) : ¬ (Plan.call p).vc (fun _ _ => True) s 0 := by
  simp only [Plan.vc]
  omega

/-- Callers must establish the precondition, even if they ignore the output. -/
theorem invalid_call {State : Type} (p : Routine State) (s : State)
    (invalid : ¬ p.requires s) (credits : Nat) :
    ¬ (Plan.call p).vc (fun _ _ => True) s credits := by
  simp only [Plan.vc]
  tauto

/-- The row primitive rejects an empty cursor. -/
example (a : Adjacency) (s : Authoring.Search.State) (empty : s.row = []) (credits : Nat) :
    ¬ (Plan.action (Graph.discoverNext a)).vc (fun _ _ => True) s credits := by
  simp [Plan.vc, Graph.discoverNext, Authoring.Search.visit, empty]

/-- A malformed vertex identifier is not an executable graph operation. -/
example (a : Adjacency) (s : Authoring.Search.State)
    (invalid : a.n ≤ s.row.headD 0) (credits : Nat) :
    ¬ (Plan.action (Graph.discoverNext a)).vc (fun _ _ => True) s credits := by
  simp only [Plan.vc, Graph.discoverNext, Authoring.Search.visit]
  omega

/-- A source is mandatory; the empty graph has no valid call to this API. -/
example (graph : EdgeInput) (empty : graph.n = 0) : IsEmpty (Fin graph.n) := by
  rw [empty]
  infer_instance

set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  for mask in List.range 64 do
    for source in List.finRange 4 do
      let graph := Experimental.RAM.Tests.smallGraph mask
      let result := BFS.search graph source
      unless result.value.toList == Experimental.RAM.Tests.reference graph source.val do
        throw <| IO.userError s!"composed BFS: mask={mask}, source={source.val}"
      unless result.steps ≤ 370 * (4 + graph.edges.length) do
        throw <| IO.userError s!"composed BFS budget: mask={mask}, source={source.val}"
  let singleton := Legacy.Examples.singleton
  unless (BFS.search singleton ⟨0, by decide⟩).value.toList == [0] do
    throw <| IO.userError "composed singleton"
  let multi := Legacy.Examples.multigraph
  let result := BFS.search multi ⟨0, by decide⟩
  unless result.value.toList == [0, 1, 2] do
    throw <| IO.userError "composed loops and parallel edges"
  unless result.steps ≤ 370 * (multi.n + multi.edges.length) do
    throw <| IO.userError "composed multigraph budget"

end AlgoLib.Experimental.RAM.Prototype.GraphTests
