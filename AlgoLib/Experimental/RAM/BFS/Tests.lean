/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Demo

/-!
# BFS runtime and logical regression checks

Exercise every graph/source pair on four vertices, input boundaries, and time-credit soundness.
-/

namespace AlgoLib.Experimental.RAM.BFS.Tests
open Checked Demo

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

/- Runtime checks cover all 64 simple graphs on four vertices and all four
sources, plus loops, parallel edges, an isolated source, and the singleton.
The reference computes finite closure; the tested program executes RAM code. -/
set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  for mask in List.range 64 do
    for source in List.finRange 4 do
      let graph := smallGraph mask
      let input := graph.fromSource source.val source.isLt
      let result := input.run
      let reached := (List.range 4).filter (fun v => result.2.memory (5 * v + 1) == 1)
      let expected := reference graph source.val
      unless reached == expected do
        throw <| IO.userError s!"reachability mismatch: mask={mask}, source={source.val}"
      unless result.1 ≤ 32 * (4 + graph.edges.length) do
        throw <| IO.userError s!"cost bound failed: mask={mask}, source={source.val}"
      unless result.2.regs head == result.2.regs tail && result.2.regs tail == reached.length do
        throw <| IO.userError s!"queue uniqueness failed: mask={mask}, source={source.val}"
  unless report singleton 0 (by decide) == ([0], 22) do
    throw <| IO.userError "singleton"
  unless report splitGraph 3 (by decide) == ([3], 37) do
    throw <| IO.userError "isolated source"
  unless report diamond 0 (by decide) == ([0, 1, 2, 3], 164) do
    throw <| IO.userError "diamond"
  unless report multigraph 0 (by decide) == ([0, 1, 2], 168) do
    throw <| IO.userError "parallel edges and loops"
  let reverseRun := (path.fromSource 3 (by decide)).run
  let fifo := (List.range 4).map (fun i => reverseRun.2.memory (5 * i + 2))
  unless fifo == [3, 2, 1, 0] do
    throw <| IO.userError "FIFO discovery order"

end AlgoLib.Experimental.RAM.BFS.Tests
