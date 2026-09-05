/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Legacy.InsertionSort
import AlgoLib.Experimental.RAM.Legacy.BFS

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

/-- Edges are `(label, u, v)`. -/
def path : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2), (2, 2, 3)]
  distinct := by decide
  valid := by decide

/-- Vertex 3 is isolated. -/
def splitGraph : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2)]
  distinct := by decide
  valid := by decide

def singleton : EdgeInput where
  n := 1
  edges := []
  distinct := by decide
  valid := by decide

/-- Reaching vertex 3 through two parents must enqueue it only once. -/
def diamond : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 0, 2), (2, 1, 3), (3, 2, 3)]
  distinct := by decide
  valid := by decide

/-- Two parallel 0–1 edges and two loops exercise incidence multiplicities. -/
def multigraph : EdgeInput where
  n := 3
  edges := [(0, 0, 0), (1, 0, 1), (2, 0, 1), (3, 1, 2), (4, 2, 2)]
  distinct := by decide
  valid := by decide

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
