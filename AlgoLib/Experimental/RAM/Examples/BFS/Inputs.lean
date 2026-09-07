/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Natural.Memory.GraphInput

/-!
# Small adjacency-list inputs for BFS examples

Shared executable inputs, independent of the historical sorting and BFS runners.
Use these with `Examples.BFS.Execution`; see the adjacent README.
-/
namespace AlgoLib.Experimental.RAM.Examples.BFS.Inputs
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

end AlgoLib.Experimental.RAM.Examples.BFS.Inputs
