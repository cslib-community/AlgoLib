/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Library.Sequences
import AlgoLib.Experimental.RAM.BFS.Specification
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Reusable adjacency-list interface

Compressed adjacency lists use an offsets array and a targets array. `Rep`
connects these arrays to the existing graph abstraction, including parallel
edges. Clients use row bounds and cursor reads; neither BFS nor reachability
is baked into the executable operations. Input construction is outside cost.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

structure GraphRef where
  offsets : ArrayRef
  targets : ArrayRef

/-- Offset table plus contiguous rows. The final offset of each row is stored,
so acquiring row bounds needs two constant-time reads. -/
structure GraphRef.Rep (g : GraphRef) (a : BFS.Adjacency) (s : Store) : Prop where
  rows : ∀ u < a.n,
    let start := s.heap (s.vars .ptr g.offsets.base.name + u)
    s.heap (s.vars .ptr g.offsets.base.name + (u + 1)) = start + (a.neighbors u).length ∧
      Segment s (s.vars .ptr g.targets.base.name + start) (a.neighbors u)

def GraphRef.beginRow (g : GraphRef) (vertex : Expr .word) (out : Var .word) : Cmd :=
  g.offsets.get vertex out

def GraphRef.endRow (g : GraphRef) (vertex : Expr .word) (out : Var .word) : Cmd :=
  g.offsets.get (.bin .add vertex (.lit 1)) out

def GraphRef.readNeighbor (g : GraphRef) (cursor : Expr .word) (out : Var .word) : Cmd :=
  g.targets.get cursor out

theorem GraphRef.begin_spec (g : GraphRef) (vertex : Expr .word) (out : Var .word) :
    Contract (g.beginRow vertex out) (fun _ => True)
      (fun s t => t = s.set out (s.heap (s.vars .ptr g.offsets.base.name + vertex.eval s)))
      (fun _ => vertex.cost + 4) := by
  intro s _
  exact ⟨_, _, .assign _ _ _, rfl, by simp [ArrayRef.cell, ArrayRef.address, Expr.cost]; omega⟩

theorem GraphRef.end_spec (g : GraphRef) (a : BFS.Adjacency) (vertex : Expr .word)
    (out : Var .word) : Contract (g.endRow vertex out)
      (fun s => g.Rep a s ∧ vertex.eval s < a.n)
      (fun s t => t = s.set out
        (s.heap (s.vars .ptr g.offsets.base.name + vertex.eval s) + 
          (a.neighbors (vertex.eval s)).length))
      (fun _ => vertex.cost + 6) := by
  intro s ⟨hr, hv⟩
  refine ⟨_, _, .assign _ _ _, ?_, by simp [ArrayRef.cell, ArrayRef.address, Expr.cost]; omega⟩
  congr 1
  exact (hr.rows _ hv).1

/-- A cursor read yields exactly the corresponding abstract neighbor, in five
RAM operations for a variable cursor, and preserves all heap data. -/
theorem GraphRef.neighbor_spec (g : GraphRef) (a : BFS.Adjacency) (u i : Nat)
    (hi : i < (a.neighbors u).length) (cursor : Expr .word) (out : Var .word) :
    Contract (g.readNeighbor cursor out)
      (fun s => g.Rep a s ∧ u < a.n ∧
        cursor.eval s = s.heap (s.vars .ptr g.offsets.base.name + u) + i)
      (fun s t => t = s.set out (a.neighbors u)[i])
      (fun _ => cursor.cost + 4) := by
  intro s ⟨hr, hu, hc⟩
  refine ⟨_, _, .assign _ _ _, ?_, by simp [ArrayRef.cell, ArrayRef.address, Expr.cost]; omega⟩
  congr 1
  simpa [ArrayRef.cell, ArrayRef.address, Expr.eval, Op.eval, Op.machine, BinOp.eval,
    hc, Nat.add_assoc] using (hr.rows u hu).2 i hi

/-- The adjacency interface refines this repository's labelled undirected Graph. -/
theorem GraphRef.neighbor_is_edge {β : Type*} (a : BFS.Adjacency) (G : Graph Nat β)
    (h : BFS.Represents a G) (u i : Nat) (hu : u < a.n) (hi : i < (a.neighbors u).length) :
    BFS.Link G u (a.neighbors u)[i] :=
  (h.adjacency u hu _).mp (List.getElem_mem hi)

/-- Repeated traversal of each row once is linear, counting parallel incidences.
`entryCost` is supplied by a verified client-body contract, never by runtime code. -/
theorem GraphRef.traversal_budget {β : Type*} (a : BFS.Adjacency) (G : Graph Nat β)
    (h : BFS.Represents a G) (rowCost entryCost : Nat) :
    (∑ u ∈ Finset.range a.n, (rowCost + entryCost * (a.neighbors u).length)) ≤
      rowCost * a.n + entryCost * (2 * h.edges.card) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have he := Nat.mul_le_mul_left entryCost h.incidenceBound
  dsimp [BFS.Adjacency.entries] at he
  simpa [Nat.mul_comm] using Nat.add_le_add_left he (rowCost * a.n)

end AlgoLib.Experimental.RAM.Checked.Language
