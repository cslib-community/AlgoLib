/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Theory.Graph.Adjacency
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Graph-level algorithm specification

Uses the repository Graph to define reachability, connectivity, finite adjacency representations,
and the BFS frontier invariant.

Contains the mathematical contract that Programs/Connectivity proves. Physical heap layouts are
confined to Backend/Memory.

## Further details

# The graph specification of breadth-first search

The specification uses AlgoLib's `Graph`, including isolated vertices, loops,
and parallel labelled edges. Reachability is a proposition about finite walks;
it does not mention the executable representation or its running time.
-/
namespace AlgoLib.Experimental.RAM.BFS

/-- One undirected edge, retaining the repository's labelled edge set. -/
def Link {β : Type*} (G : Graph Nat β) (u v : Nat) : Prop :=
  ∃ e ∈ G.edgeSet, e.endpoints = s(u, v)

namespace Link
variable {β : Type*} {G : Graph Nat β} {u v : Nat}
theorem symm (h : Link G u v) : Link G v u := by
  simpa [Link, Sym2.eq_swap] using h

theorem left_mem (h : Link G u v) : u ∈ G.vertexSet := by
  obtain ⟨e, he, hp⟩ := h
  exact G.incidence' e he u (by simp [hp])

theorem right_mem (h : Link G u v) : v ∈ G.vertexSet := h.symm.left_mem
end Link

/-- Finite edge walks; the reflexive case requires an actual vertex. -/
inductive Reachable {β : Type*} (G : Graph Nat β) (source : Nat) : Nat → Prop
  | refl : source ∈ G.vertexSet → Reachable G source source
  | step {u v} : Reachable G source u → Link G u v → Reachable G source v

namespace Reachable
variable {β : Type*} {G : Graph Nat β} {u v w : Nat}
theorem left_mem (h : Reachable G u v) : u ∈ G.vertexSet := by
  induction h with
  | refl h => exact h
  | step _ _ ih => exact ih

theorem right_mem (h : Reachable G u v) : v ∈ G.vertexSet := by
  cases h with
  | refl h => exact h
  | step _ h => exact h.right_mem

theorem trans (h : Reachable G u v) (h' : Reachable G v w) : Reachable G u w := by
  induction h' with
  | refl => exact h
  | step _ he ih => exact .step ih he

theorem symm (h : Reachable G u v) : Reachable G v u := by
  induction h with
  | refl hv => exact .refl hv
  | step h he ih => exact (Reachable.step (.refl he.right_mem) he.symm).trans ih
end Reachable

/-- The same nonempty, pairwise-reachable convention used by `SimpleGraph.IsConnected`. -/
def Connected {β : Type*} (G : Graph Nat β) : Prop :=
  G.vertexSet.Nonempty ∧ ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, Reachable G u v

/-- The correctness contract says *exactly* which vertices the output marks. -/
def ReturnsReachable {β : Type*} (G : Graph Nat β) (source : Nat) (marked : Nat → Prop) : Prop :=
  ∀ v, marked v ↔ Reachable G source v

theorem visits_all_iff_connected {β : Type*} {G : Graph Nat β} {source : Nat}
    (hs : source ∈ G.vertexSet) {marked : Nat → Prop}
    (h : ReturnsReachable G source marked) :
    (∀ v ∈ G.vertexSet, marked v) ↔ Connected G := by
  constructor
  · intro hall
    refine ⟨⟨source, hs⟩, ?_⟩
    intro u hu v hv
    exact ((h u).mp (hall u hu)).symm.trans ((h v).mp (hall v hv))
  · intro hc v hv
    exact (h v).mpr (hc.2 source hs v hv)

/-- A finite adjacency-list representation. Lists may contain duplicates (parallel
edges or the two incidences of a loop). Vertex identifiers are `0, …, n-1`. -/
structure Adjacency where
  n : Nat
  neighbors : Nat → List Nat
  valid : ∀ u < n, ∀ v ∈ neighbors u, v < n

/-- Number of stored adjacency entries, without suppressing multiplicities. -/
def Adjacency.entries (a : Adjacency) : Nat :=
  ∑ v ∈ Finset.range a.n, (a.neighbors v).length

/-- Representation correctness is separate from BFS. The adjacency-entry bound
is a proof obligation about the encoding, not an assumption about execution time.
`EdgeInput.represents` proves it by counting two incidences per labelled edge.
Use the labelled `G.edgeSet`: the repository's `E(G)` forgets parallel labels. -/
structure Represents {β : Type*} (a : Adjacency) (G : Graph Nat β) where
  vertices : ∀ v, v ∈ G.vertexSet ↔ v < a.n
  adjacency : ∀ u < a.n, ∀ v, v ∈ a.neighbors u ↔ Link G u v
  edges : Finset (Edge Nat β)
  edgeSet : ∀ e, e ∈ edges ↔ e ∈ G.edgeSet
  incidenceBound : a.entries ≤ 2 * edges.card

/-- The algorithm-level invariant: discovered vertices are reachable; each
processed vertex has all of its neighbors discovered. The FIFO contains precisely
the discovered vertices that have not yet been processed. -/
structure Invariant {β : Type*} (a : Adjacency) (G : Graph Nat β) (source : Nat)
    (done : Finset Nat) (queue : List Nat) where
  distinct : queue.Nodup
  disjoint : ∀ v ∈ queue, v ∉ done
  valid_done : ∀ v ∈ done, v < a.n
  valid_queue : ∀ v ∈ queue, v < a.n
  source_seen : source ∈ done ∨ source ∈ queue
  sound : ∀ v, v ∈ done ∨ v ∈ queue → Reachable G source v
  closed : ∀ u ∈ done, ∀ v ∈ a.neighbors u, v ∈ done ∨ v ∈ queue

/-- At exit the invariant is the usual paper proof: the discovered set contains
s, is closed under edges, and contains only vertices reachable from s. -/
theorem Invariant.exit {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) {source : Nat} {done : Finset Nat}
    (h : Invariant a G source done []) : ReturnsReachable G source (· ∈ done) := by
  intro v
  constructor
  · intro hv; exact h.sound v (Or.inl hv)
  · intro hv
    induction hv with
    | refl => simpa using h.source_seen
    | @step u v _ he ih =>
      have hn := (rep.adjacency u (h.valid_done u ih) v).mpr he
      simpa using h.closed u ih v hn

end AlgoLib.Experimental.RAM.BFS
