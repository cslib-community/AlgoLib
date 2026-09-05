/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Semantics
import AlgoLib.Experimental.RAM.Backend.Language.Refinement
import AlgoLib.Experimental.RAM.Backend.Certificates.BFS

/-!
# Graph traversal representation adapter

Relates seen, queue, row, current, and processed to physical flags, FIFO storage, and adjacency
pointers.

Certifies the effects and work of each graph action using backend memory and instruction proofs.
The user-facing API is Library/Search.

## Further details

Library implementation of a visited set, FIFO, and adjacency cursor.
All physical framing and legacy instruction adaptation are confined here.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Search
open Checked Checked.Language
open Experimental.RAM.BFS

structure State where
  seen : Finset Nat
  queue : List Nat
  row : List Nat
  current : Nat
  processed : Finset Nat
  deriving DecidableEq

def model (a : Adjacency) : Model State where
  Represents g s := Refinement.Ready s ∧ Heap a s.heap ∧
    View a.n s.heap g.seen g.queue ((Refinement.view s).regs head) ∧
    (Refinement.view s).regs tail = (Refinement.view s).regs head + g.queue.length ∧
    Chain s.heap ((Refinement.view s).regs ptr) g.row
  overhead := 75

def openEffect (a : Adjacency) (g : State) : State :=
  { g with queue := g.queue.tail, row := a.neighbors (g.queue.headD 0), current := g.queue.headD 0 }

def visitEffect (g : State) : State :=
  let d := discover g.seen g.queue (g.row.headD 0)
  { g with seen := d.1, queue := d.2, row := g.row.tail }

def finishEffect (g : State) : State := { g with processed := insert g.current g.processed }

/-- FIFO removal and opening its adjacency iterator; graph and visited set frame automatically. -/
def dequeue (a : Adjacency) : Action (model a) where
  requires g := g.queue ≠ [] ∧ g.queue.headD 0 < a.n
  effect := openEffect a
  work _ := 1
  implementation := Refinement.lift popBody
  correct g s hs hg := by
    obtain ⟨ready, heap, view, ht, _⟩ := hs
    rcases hqueue : g.queue with _ | ⟨v, vs⟩
    · exact (hg.1 hqueue).elim
    have hv : v < a.n := by simpa [hqueue] using hg.2
    have hvw : View a.n s.heap g.seen (v :: vs) ((Refinement.view s).regs head) := hqueue ▸ view
    have hslot : s.heap (5 * (Refinement.view s).regs head + 2) = v := by
      simpa using hvw.slots 0 v rfl
    obtain ⟨hx, hm, hh, htail, hp⟩ := pop_correct (Refinement.view s)
    obtain ⟨j, t, he, hr, heq, hj⟩ := Refinement.lift_correct hx (by decide) s ready rfl
    have hmem : t.heap = s.heap := (congrArg Checked.State.memory heq).trans hm
    refine ⟨j, t, he, ⟨hr, hmem ▸ heap, ?_, ?_, ?_⟩, by norm_num [model] at *; omega⟩
    · simp only [openEffect, hqueue, List.tail_cons]
      rw [heq, hh, hmem]
      exact hvw.pop
    · simp only [openEffect, hqueue, List.tail_cons]
      rw [heq, htail, hh]
      simp only [hqueue, List.length_cons] at ht
      omega
    · simp only [openEffect, hqueue, List.headD_cons]
      rw [heq, hp, hmem]
      change Chain s.heap (s.heap (5 * s.heap (5 * (Refinement.view s).regs head + 2))) _
      rw [hslot]
      exact heap v hv

/-- Mark-before-enqueue at the current iterator entry. The whole graph frame is automatic. -/
def visit (a : Adjacency) : Action (model a) where
  requires g := g.row ≠ [] ∧ g.row.headD 0 < a.n
  effect := visitEffect
  work _ := 1
  implementation := Refinement.lift scanBody
  correct g s hs hg := by
    obtain ⟨ready, heap, view, ht, chain⟩ := hs
    rcases hrow : g.row with _ | ⟨v, vs⟩
    · exact (hg.1 hrow).elim
    have hv : v < a.n := by simpa [hrow] using hg.2
    have hc : Chain s.heap ((Refinement.view s).regs ptr) (v :: vs) := hrow ▸ chain
    obtain ⟨k, u, hx, hk, hh, htail, hp, hf, hview⟩ := scanBody_correct hv view ht hc.2.1
    obtain ⟨j, t, he, hr, heq, hj⟩ := Refinement.lift_correct hx (by decide) s ready rfl
    have hm : t.heap = u.memory := congrArg Checked.State.memory heq
    refine ⟨j, t, he, ⟨hr, ?_, ?_, ?_, ?_⟩, by norm_num [model] at *; omega⟩
    · rw [hm]; exact heap.frame hf
    · simpa [visitEffect, hrow, hm, heq] using hview
    · simpa [visitEffect, hrow, heq] using htail
    · simp only [visitEffect, hrow, List.tail_cons]
      rw [hm, heq, hp]
      exact hc.2.2.frame hf

/-- Recording a processed vertex is ghost bookkeeping and emits no instructions. -/
def finish (a : Adjacency) : Action (model a) where
  requires g := g.row = []
  effect := finishEffect
  work _ := 0
  implementation := .skip
  correct _ s hs _ := ⟨0, s, .skip s, hs, by simp⟩

def queueNonempty (a : Adjacency) : Guard (model a) where
  test g := !g.queue.isEmpty
  implementation := Refinement.condition bfsTest
  correct g s hs := by
    rw [Refinement.condition_eval]
    simp only [bfsTest, Test.eval, Operand.eval, hs.2.2.2.1, Nat.lt_add_right_iff_pos]
    cases g.queue <;> simp
  cost := by simp [model]

def rowNonempty (a : Adjacency) : Guard (model a) where
  test g := !g.row.isEmpty
  implementation := Refinement.condition scanTest
  correct g s hs := by
    rw [Refinement.condition_eval]
    have hc := hs.2.2.2.2
    cases hrow : g.row with
    | nil =>
      have hp : (Refinement.view s).regs ptr = 0 := by simpa [hrow, Chain] using hc
      simp [scanTest, Test.eval, Operand.eval, hp]
    | cons v vs =>
      have hp : (Refinement.view s).regs ptr ≠ 0 := (show Chain _ _ (v :: vs) from hrow ▸ hc).1
      simp [scanTest, Test.eval, Operand.eval, Nat.pos_of_ne_zero hp]
  cost := by simp [model]

end AlgoLib.Experimental.RAM.Authoring.Search
