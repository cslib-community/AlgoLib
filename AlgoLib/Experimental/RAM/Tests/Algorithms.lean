/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Algorithms.Examples

/-! Regression checks for complete compiled algorithms and their cost bounds. -/
namespace AlgoLib.Experimental.RAM.Tests
open Checked Experimental.RAM.BFS Algorithms.Examples

/-- Six possible undirected edges on four vertices, in a fixed input order. -/
def pairs : List EdgeData :=
  [(0, 0, 1), (1, 0, 2), (2, 0, 3), (3, 1, 2), (4, 1, 3), (5, 2, 3)]

def smallGraph (mask : Nat) : EdgeInput where
  n := 4
  edges := pairs.filter (fun e => mask.testBit e.1)
  distinct := (show pairs.Nodup by decide).filter _
  valid := by
    intro e he
    exact (show ∀ e ∈ pairs, e.2.1 < 4 ∧ e.2.2 < 4 by decide) e (List.mem_of_mem_filter he)

/-- Independent finite-layer reference, used only as a runtime test oracle. -/
def reference (input : EdgeInput) (source : Nat) : List Nat :=
  let step (seen : List Nat) := (List.range input.n).filter fun v =>
    seen.contains v || input.edges.any (fun e =>
      (seen.contains e.2.1 && v == e.2.2) || (seen.contains e.2.2 && v == e.2.1))
  step^[input.n] [source]

/-- An empty graph cannot supply the required source vertex. -/
theorem empty_source_rejected (input : EdgeInput) (hn : input.n = 0) (s : Nat) :
    ¬ s < input.n := by omega

/-- Time credits cannot be assigned zero at a true loop guard. -/
theorem zero_potential_rejected {Ghost : Type*} {q : Test} {body : Code}
    {rep : Ghost → State → Prop} {Q : State → Prop} {g s}
    (h : rep g s) (hq : q.eval s = true) :
    ¬ LoopVC q body rep (fun _ => 0) Q := by
  intro vc
  obtain ⟨_, k, _, _, _, hk⟩ := vc.step g s h hq
  omega

/- An arbitrary base address and sentinel cells exercise the raw contract's frame. -/
def offsetInput : Language.Store where
  vars ty name := if ty = .word ∧ name = "base" then 2 else
    if ty = .word ∧ name = "count" then 4 else 0
  heap := ofList [99, 88, 3, 1, 3, 2, 77]

/- All simple graphs on four vertices, all sources, and an independent closure oracle. -/
set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  let offset := Algorithms.InsertionSort.method.run offsetInput (by
    change Language.Refinement.Ready offsetInput
    simp [Language.Refinement.Ready, offsetInput, Language.Refinement.memory])
  unless contents offset.2.heap 0 7 == [99, 88, 1, 2, 3, 3, 77] do
    throw <| IO.userError "nonzero base and frame"
  for mask in List.range 64 do
    for source in List.finRange 4 do
      let graph := smallGraph mask
      let result := Algorithms.BFS.run (graph.fromSource source.val source.isLt)
      unless result.visited.toList == reference graph source.val && result.visited.length == 4 do
        throw <| IO.userError s!"reachability mismatch: mask={mask}, source={source.val}"
      unless result.steps ≤ 160 * (4 + graph.edges.length) do
        throw <| IO.userError s!"BFS cost bound: mask={mask}, source={source.val}"
  unless (report singleton 0 (by decide)).1 == [0] do
    throw <| IO.userError "singleton"
  unless (report splitGraph 3 (by decide)).1 == [3] do
    throw <| IO.userError "isolated source"
  unless (report diamond 0 (by decide)).1 == [0, 1, 2, 3] do
    throw <| IO.userError "diamond"
  unless (report multigraph 0 (by decide)).1 == [0, 1, 2] do
    throw <| IO.userError "loops and parallel edges"
  for n in List.range 6 do
    for mask in List.range (3 ^ n) do
      let xs := (List.range n).map (fun i => mask / 3 ^ i % 3)
      let r := Algorithms.InsertionSort.run xs
      unless r.values == xs.mergeSort (· ≤ ·) do
        throw <| IO.userError s!"sorting mismatch: {xs}"
      unless r.steps ≤ Algorithms.InsertionSort.budget n do
        throw <| IO.userError s!"sorting cost: {xs}"

end AlgoLib.Experimental.RAM.Tests
