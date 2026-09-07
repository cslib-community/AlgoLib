/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Historical.Legacy.InsertionSort
import AlgoLib.Experimental.RAM.Historical.Legacy.BFS
import AlgoLib.Experimental.RAM.Examples.BFS.Inputs

/-!
# Legacy demonstration: Examples

Retains an earlier lower-level example for historical comparison and compiler regression coverage.
This is an explicit opt-in module and is not imported by the public RAM entry point.

Use Programs/Sorting and Programs/Connectivity for the current input/output method and
algorithm-level VC workflow.

## Further details

Executable demonstrations. Only input encoding and result formatting run on the host.
-/
namespace AlgoLib.Experimental.RAM.Legacy.Examples
open Experimental.RAM.BFS

/-- Compatibility name for the shared BFS example input. -/
abbrev path := Experimental.RAM.Examples.BFS.Inputs.path

/-- Compatibility name for the shared BFS example input. -/
abbrev splitGraph := Experimental.RAM.Examples.BFS.Inputs.splitGraph

/-- Compatibility name for the shared BFS example input. -/
abbrev singleton := Experimental.RAM.Examples.BFS.Inputs.singleton

/-- Compatibility name for the shared BFS example input. -/
abbrev diamond := Experimental.RAM.Examples.BFS.Inputs.diamond

/-- Compatibility name for the shared BFS example input. -/
abbrev multigraph := Experimental.RAM.Examples.BFS.Inputs.multigraph

def report (graph : EdgeInput) (source : Nat) (hs : source < graph.n) : List Nat × Nat :=
  let r := Legacy.BFS.run (graph.fromSource source hs)
  (r.visited.toList, r.steps)

example (xs : List Nat) : (InsertionSort.run xs).values.Perm xs :=
  (InsertionSort.run_correct xs).2.1

example (graph : EdgeInput) (s : Nat) (hs : s < graph.n) (v : Nat) :
    (Legacy.BFS.run (graph.fromSource s hs)).visited.contains v = true ↔
      Reachable graph.graph s v := Legacy.BFS.run_correct _ v

example (graph : EdgeInput) (s : Nat) (hs : s < graph.n) :
    (∀ v ∈ graph.graph.vertexSet,
      (Legacy.BFS.run (graph.fromSource s hs)).visited.contains v = true) ↔
        Connected graph.graph := Legacy.BFS.connected_iff _

set_option linter.hashCommand false in
#eval (InsertionSort.run [3, 1, 4, 2, 1]).values
set_option linter.hashCommand false in
#eval report path 0 (by decide)
set_option linter.hashCommand false in
#eval report splitGraph 3 (by decide)
set_option linter.hashCommand false in
#eval report multigraph 0 (by decide)

end AlgoLib.Experimental.RAM.Legacy.Examples
