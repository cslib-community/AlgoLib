/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Paper.InsertionExecutable
import AlgoLib.Experimental.RAM.Paper.BFSExecutable

/-! Start here: ordinary inputs, named outputs, and complete theorems. -/
namespace AlgoLib.Experimental.RAM.Paper.Examples
open Experimental.RAM.BFS

def path : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2), (2, 2, 3)]
  distinct := by decide
  valid := by decide

set_option linter.hashCommand false in
/-- info: [1, 1, 2, 3, 4] -/
#guard_msgs in
#eval (Insertion.run [3, 1, 4, 2, 1]).value

set_option linter.hashCommand false in
/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval (BFS.run (path.fromSource 0 (by decide))).value.toList

example (xs : List Nat) : (Insertion.run xs).value.Perm xs := (Insertion.run_correct xs).2

example (xs : List Nat) (h : xs ≠ []) :
    (Insertion.run xs).steps ≤ 205 * xs.length ^ 2 := Insertion.quadratic xs h

example {β : Type} {a : Adjacency} {G : Graph Nat β} (input : Input a G) (v : Nat) :
    (BFS.run input).value.contains v = true ↔ Reachable G input.source v := BFS.run_correct input v

example {β : Type} {a : Adjacency} {G : Graph Nat β} (input : Input a G) :
    (BFS.run input).steps ≤ 370 * (a.n + input.representation.edges.card) := BFS.linear input

end AlgoLib.Experimental.RAM.Paper.Examples
