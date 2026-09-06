/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts
import AlgoLib.Experimental.RAM.Specification.Graph

/-!
# Read-only adjacency cursors

A cursor is observed as its remaining list of neighbors. Opening a row and taking
its next neighbor are constant-charge operations, not host list computations.
The graph parameter specifies the immutable adjacency relation; the implementation
must read it from resident RAM. The same ownership interface frames queues, visited
arrays, and unrelated cursors. No graph representation appears in the client proof.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursor
open Experimental.RAM.BFS

def openRow (a : Adjacency) : Operation (List Nat × Nat) (List Nat × Nat) where
  requires input := input.2 < a.n
  effect input := (a.neighbors input.2, input.2)
  charge _ := 1

def next : Operation (List Nat × Nat) (List Nat × Nat) where
  requires input := input.1 ≠ []
  effect input := (input.1.tail, input.1.headD 0)
  charge _ := 1

def nonempty (row : List Nat) : Bool := !row.isEmpty

namespace API
@[reducible] def neighbors (a : Adjacency) : Procedure (List Nat × Nat) (List Nat × Nat) :=
  Procedure.verify (.invoke (openRow a)) (fun input => input.2 < a.n)
    (fun input result => result = (a.neighbors input.2, input.2)) (fun _ => 1)
    (by simp [VC, openRow])
@[reducible] def nextNeighbor : Procedure (List Nat × Nat) (List Nat × Nat) :=
  Procedure.verify (.invoke next) (fun input => input.1 ≠ [])
    (fun input result => result = (input.1.tail, input.1.headD 0)) (fun _ => 1)
    (by simp [VC, next])
instance (a : Adjacency) : UniformCredits (neighbors a) := ⟨1, fun _ => Nat.le_refl _⟩
instance : UniformCredits nextNeighbor := ⟨1, fun _ => Nat.le_refl _⟩
end API
end AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursor
