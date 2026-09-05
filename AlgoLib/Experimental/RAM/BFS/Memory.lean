/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Specification
import AlgoLib.Experimental.RAM.Syntax
import AlgoLib.Experimental.RAM.LoopVC

/-!
# Adjacency lists and FIFO queues in addressed RAM memory

Five disjoint address classes: vertex head `5v`, visited flag `5v+1`, queue
slot `5i+2`, arc destination `5p+3`, arc next pointer `5p+4`. Pointer zero is
null. Lists can share immutable tails. Mutable flags and queue entries cannot
alias the graph, even when a vertex identifier equals an arc pointer.

The mathematical lists and finite sets below are *ghost views* of memory.
Their membership, append, and cardinality computations are never RAM primitives.
-/
namespace AlgoLib.Experimental.RAM.BFS
open Checked Checked.Source

abbrev Memory := Nat → Nat

/-- A finite linked adjacency list, including its null terminator. -/
def Chain (m : Memory) : Nat → List Nat → Prop
  | p, [] => p = 0
  | p, v :: vs => p ≠ 0 ∧ m (5 * p + 3) = v ∧ Chain m (m (5 * p + 4)) vs

/-- All graph lists are immutable, well formed, and decode to the specification. -/
def Heap (a : Adjacency) (m : Memory) : Prop :=
  ∀ v < a.n, Chain m (m (5 * v)) (a.neighbors v)

/-- Changes in the mutable address classes preserve all adjacency information. -/
def GraphFrame (m m' : Memory) : Prop :=
  (∀ v, m' (5 * v) = m (5 * v)) ∧
  (∀ p, m' (5 * p + 3) = m (5 * p + 3)) ∧
  (∀ p, m' (5 * p + 4) = m (5 * p + 4))

theorem Chain.frame {m m' : Memory} (h : GraphFrame m m') {p xs}
    (hc : Chain m p xs) : Chain m' p xs := by
  induction xs generalizing p with
  | nil => exact hc
  | cons v vs ih =>
    exact ⟨hc.1, (h.2.1 p).trans hc.2.1, by rw [h.2.2]; exact ih hc.2.2⟩

theorem Heap.frame {a : Adjacency} {m m'} (h : GraphFrame m m') (ha : Heap a m) :
    Heap a m' := by
  intro v hv
  rw [h.1]
  exact (ha v hv).frame h

theorem GraphFrame.refl (m : Memory) : GraphFrame m m :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
theorem GraphFrame.trans {a b c : Memory} (h : GraphFrame a b) (h' : GraphFrame b c) :
    GraphFrame a c := ⟨fun v => (h'.1 v).trans (h.1 v),
      fun v => (h'.2.1 v).trans (h.2.1 v), fun v => (h'.2.2 v).trans (h.2.2 v)⟩

theorem graphFrame_write (m : Memory) (i value tag : Nat) (ht : tag = 1 ∨ tag = 2) :
    GraphFrame m (Function.update m (5 * i + tag) value) := by
  rcases ht with rfl | rfl <;>
    exact ⟨fun v => Function.update_of_ne (by omega) _ _,
      fun v => Function.update_of_ne (by omega) _ _,
      fun v => Function.update_of_ne (by omega) _ _⟩

/-- The live queue occupies consecutive slots starting at `head`. -/
structure View (n : Nat) (m : Memory) (seen : Finset Nat)
    (queue : List Nat) (head : Nat) : Prop where
  marks : ∀ v < n, m (5 * v + 1) = if v ∈ seen then 1 else 0
  slots : ∀ i v, queue[i]? = some v → m (5 * (head + i) + 2) = v

/-- Dequeue is a change of view, plus one head-register increment. -/
theorem View.pop {n m seen v queue head} (h : View n m seen (v :: queue) head) :
    View n m seen queue (head + 1) := by
  refine ⟨h.marks, ?_⟩
  intro i w hi
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.slots (i + 1) w hi

/-- Mark-before-enqueue preserves the memory abstraction. Appending to the ghost
list corresponds to writing *one* queue cell, not traversing a runtime list. -/
def enqueueMemory (m : Memory) (v tail : Nat) : Memory :=
  Function.update (Function.update m (5 * v + 1) 1) (5 * tail + 2) v

theorem View.enqueue {n m seen queue head v} (h : View n m seen queue head) :
    View n (enqueueMemory m v (head + queue.length)) (insert v seen) (queue ++ [v]) head := by
  constructor
  · intro w hw
    simp only [enqueueMemory, Function.update_of_ne (show 5 * w + 1 ≠
      5 * (head + queue.length) + 2 by omega), Finset.mem_insert]
    by_cases he : w = v
    · subst w; simp
    · rw [Function.update_of_ne (by omega), h.marks w hw]
      simp [he]
  · intro i w hi
    by_cases hil : i < queue.length
    · have hqi : queue[i]? = some w := by simpa [List.getElem?_append, hil] using hi
      simpa [enqueueMemory, Function.update_of_ne (show 5 * (head + i) + 2 ≠
        5 * (head + queue.length) + 2 by omega),
        Function.update_of_ne (show 5 * (head + i) + 2 ≠ 5 * v + 1 by omega)] using h.slots i w hqi
    · have hie : i = queue.length := by
        obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp hi
        simp only [List.length_append, List.length_singleton] at hb
        omega
      subst i
      have hwv : w = v := by simpa using hi.symm
      subst w
      simp [enqueueMemory]

theorem enqueue_frame (m : Memory) (v tail : Nat) : GraphFrame m (enqueueMemory m v tail) :=
  (graphFrame_write m v 1 1 (Or.inl rfl)).trans
    (graphFrame_write _ tail v 2 (Or.inr rfl))

/-- Register aliases: all are members of the existing fixed eight-register bank. -/
abbrev head : Reg := .base
abbrev tail : Reg := .count
abbrev ptr : Reg := .cursor
abbrev vertex : Reg := .key
abbrev addr : Reg := .next
abbrev neighbor : Reg := .temp
abbrev marked : Reg := .live

/-- One adjacency entry, lowered to ordinary RAM loads, stores, and arithmetic. -/
def scanBody : Stmt := imperative {
  addr := 5 * ptr;
  addr := addr + 3;
  neighbor := A[addr];
  addr := 5 * neighbor;
  addr := addr + 1;
  marked := A[addr];
  if marked == 0 {
    A[addr] := 1;
    addr := 5 * tail;
    addr := addr + 2;
    A[addr] := neighbor;
    tail := tail + 1;
  } else { }
  addr := 5 * ptr;
  addr := addr + 4;
  ptr := A[addr];
}

def scanTest : Test := .lt (.lit 0) (.reg ptr)
def scanCode : Code := .while scanTest scanBody.compile

/-- Preparing one FIFO vertex costs six instructions. -/
def popBody : Stmt := imperative {
  addr := 5 * head;
  addr := addr + 2;
  vertex := A[addr];
  head := head + 1;
  addr := 5 * vertex;
  ptr := A[addr];
}

def bfsTest : Test := .lt (.reg head) (.reg tail)
def bfsBody : Code := .seq popBody.compile scanCode
def bfsLoop : Code := .while bfsTest bfsBody

end AlgoLib.Experimental.RAM.BFS
