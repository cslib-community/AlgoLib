/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Procedures
import AlgoLib.Experimental.RAM.Library.Search

/-!
# Graph primitives and reusable adjacency-scan procedures

The logical interface has a visited set (`seen`), FIFO (`queue`), adjacency cursor
(`row`), current vertex, and ghost processed set. The physical graph, bitmap, FIFO,
and cursor have disjoint certified memory contracts in Library.Search.

`discoverNext` tests the current neighbor, marks/enqueues it only if unseen, and
advances the cursor. It is a bounded-cost primitive implemented by RAM instructions,
not an entire hidden neighbor loop. `scanNeighbors` exposes that loop below and is
verified through generated conditions. `processVertex` composes dequeue, that
procedure, and ghost completion; its clients use only a functional/cost summary.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Graph
open Authoring Authoring.Search Experimental.RAM.BFS

abbrev Frontier := Search.State
abbrev queueNotEmpty := Search.queueNonempty
abbrev neighborsRemain := Search.rowNonempty
abbrev dequeue := Search.dequeue
abbrev discoverNext := Search.visit
abbrev finishVertex := Search.finish

/-- Scan the open adjacency row. Invariants refer only to the functional scan. -/
def scanCode (a : Adjacency) : Annotated Search.State :=
  ram_do (entry, s, remaining) do
    while (neighborsRemain a)
      invariant ∀ v ∈ s.row, v < a.n
      invariant scanEffect s = scanEffect entry
      invariant 2 * s.row.length + 1 ≤ remaining
      decreasing s.row.length
      do
        perform discoverNext a

/-- Removing one entry preserves the meaning of the remaining functional scan. -/
theorem scanEffect_visit (s : Frontier) (h : s.row ≠ []) :
    scanEffect (visitEffect s) = scanEffect s := by
  cases s with
  | mk seen queue row current processed =>
    cases row with
    | nil => simp at h
    | cons v vs => rfl

/-- At an exhausted cursor, scanning is the identity. -/
theorem scanEffect_empty (s : Frontier) (h : s.row = []) : scanEffect s = s := by
  cases s
  simp_all [scanEffect, scan]

/-- Generated safety, termination, functional, and credit obligations for the row loop. -/
theorem scanVerification (a : Adjacency) (entry : Frontier)
    (valid : ∀ v ∈ entry.row, v < a.n) :
    (scanCode a).plan.vc (fun t _ => t = scanEffect entry) entry
      (2 * entry.row.length + 1) := by
  simp only [scanCode, Plan.vc]
  refine ⟨⟨valid, trivial, Nat.le_refl _, trivial⟩, ?_⟩
  intro s remaining hs
  obtain ⟨valid, effect, budget, _⟩ := hs
  refine ⟨by omega, ?_⟩
  cases row : s.row with
  | nil =>
    simp only [neighborsRemain, rowNonempty, row, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    exact (scanEffect_empty s row).symm.trans effect
  | cons v vs =>
    have hv := valid v (by simp [row])
    have hvs : ∀ w ∈ vs, w < a.n := fun w hw => valid w (by simp [row, hw])
    have he := (scanEffect_visit s (by simp [row])).trans effect
    simp only [neighborsRemain, rowNonempty, row, List.isEmpty_cons, Bool.not_false,
      ↓reduceIte, discoverNext, visit, visitEffect, List.headD_cons, List.tail_cons,
      List.length_cons] at *
    refine ⟨⟨by simp, hv⟩, by omega, by omega, hvs, he, by omega, trivial⟩

/-- Modular neighbor scan; the compiler still sees `scanCode`'s actual loop. -/
def scanNeighbors (a : Adjacency) : Routine Search.State :=
  (scanCode a).verify
    (fun s => ∀ v ∈ s.row, v < a.n)
    (fun s t => t = scanEffect s)
    (fun s => 2 * s.row.length + 1)
    (scanVerification a)

/-- Dequeue, scan the row through its contract, then record the completed vertex. -/
def processCode (a : Adjacency) : Annotated Search.State :=
  ram_do (_entry, s, remaining) do
    perform dequeue a
    call scanNeighbors a
    perform finishVertex a

/-- Logical effect of processing one frontier vertex. -/
def processEffect (a : Adjacency) (s : Frontier) : Frontier :=
  finishEffect (scanEffect (openEffect a s))

/-- Work allowance includes dequeue and the final unsuccessful row test. -/
def processWork (a : Adjacency) (s : Frontier) : Nat :=
  2 * (a.neighbors (s.queue.headD 0)).length + 2

/-- Procedure composition is checked using only callee contracts and adjacency validity. -/
theorem processVerification (a : Adjacency) (s : Frontier)
    (valid : s.queue ≠ [] ∧ s.queue.headD 0 < a.n) :
    (processCode a).plan.vc (fun t _ => t = processEffect a s) s (processWork a s) := by
  simp only [processCode, Plan.vc, dequeue, Search.dequeue_requires,
    Search.dequeue_work, Search.dequeue_effect, scanNeighbors, Annotated.verify]
  refine ⟨valid, by simp [processWork]; omega, a.valid _ valid.2, ?_, ?_⟩
  · simp [processWork, openEffect]
    omega
  · intro t k ht hk
    subst t
    simp [finishVertex, Search.finish, scanEffect, processEffect]

/-- A reusable vertex-processing contract, independently composed from the row scan. -/
def processVertex (a : Adjacency) : Routine Search.State :=
  (processCode a).verify
    (fun s => s.queue ≠ [] ∧ s.queue.headD 0 < a.n)
    (fun s t => t = processEffect a s)
    (processWork a)
    (processVerification a)

end AlgoLib.Experimental.RAM.Prototype.Graph
