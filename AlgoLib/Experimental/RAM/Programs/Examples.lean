/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Programs.Sorting
import AlgoLib.Experimental.RAM.Programs.Connectivity

/-!
# Run the canonical methods

Runs sorting and BFS on ordinary inputs and demonstrates their correctness and compiled-time
theorem projections.

No algorithm is defined here. Open Programs/Sorting or Programs/Connectivity to see the
declaration and its complete proof.

## Further details

Start here: ordinary inputs, named outputs, and complete theorems.
-/
namespace AlgoLib.Experimental.RAM.Programs.Examples
open Experimental.RAM.BFS

def path : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2), (2, 2, 3)]
  distinct := by decide
  valid := by decide

set_option linter.hashCommand false in
/-- info: [1, 1, 2, 3, 4] -/
#guard_msgs in
#eval (Programs.Sorting.run [3, 1, 4, 2, 1]).value

set_option linter.hashCommand false in
/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval (Programs.Connectivity.run (path.fromSource 0 (by decide))).value.toList

example (xs : List Nat) : (Programs.Sorting.run xs).value.Perm xs :=
  (Programs.Sorting.run_correct xs).2

example (xs : List Nat) (h : xs ≠ []) :
    (Programs.Sorting.run xs).steps ≤ 205 * xs.length ^ 2 := Programs.Sorting.quadratic xs h

example {β : Type} {a : Adjacency} {G : Graph Nat β} (input : Input a G) (v : Nat) :
    (Programs.Connectivity.run input).value.contains v = true ↔ Reachable G input.source v :=
  Programs.Connectivity.run_correct input v

example {β : Type} {a : Adjacency} {G : Graph Nat β} (input : Input a G) :
    (Programs.Connectivity.run input).steps ≤ 370 * (a.n + input.representation.edges.card) :=
  Programs.Connectivity.linear input

/- Explicit graph/source arguments; the result is a vertex-set view. -/
set_option linter.hashCommand false in
/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval (Connectivity.search path ⟨0, by decide⟩).value.toList

/-- Read the full connectivity/time statement from the same execution. -/
example : Connectivity.Claim (@Connectivity.run EdgeData path.adjacency path.graph) :=
  Connectivity.main

end AlgoLib.Experimental.RAM.Programs.Examples
