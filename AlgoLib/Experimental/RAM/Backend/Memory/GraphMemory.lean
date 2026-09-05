/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Specification.Graph
import AlgoLib.Experimental.RAM.Machine.Machine
import AlgoLib.Experimental.RAM.Backend.Memory.Framing

/-!
# Adjacency layout and graph inputs

Defines the physical linked-adjacency representation and certifies its relationship to logical
adjacency data.

The Input certificate connects memory, finite adjacency, the repository Graph, and a valid source.
GraphInput constructs it from ordinary edge data.
-/
namespace AlgoLib.Experimental.RAM.BFS
open Checked

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
  have untouched (offset : Nat) (ho : offset = 0 ∨ offset = 3 ∨ offset = 4) :
      ∀ v, (Function.update m (5*i+tag) value) (5*v+offset) = m (5*v+offset) := by
    have reads := Checked.Language.Framing.cells {x | ∃ v, x = 5*v+offset} m
    have outside : 5*i+tag ∉ {x | ∃ v, x = 5*v+offset} := by
      rintro ⟨v, hv⟩
      rcases ht with ht | ht <;> rcases ho with ho | ho | ho <;> omega
    have framed := Checked.Language.Framing.frame_write reads (v := value) outside (by intros; rfl)
    exact fun v => framed _ ⟨v, rfl⟩
  exact ⟨by simpa using untouched 0 (Or.inl rfl),
    untouched 3 (Or.inr (Or.inl rfl)), untouched 4 (Or.inr (Or.inr rfl))⟩

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

/-- A valid input to the machine. Proof fields are erased by Lean's evaluator. -/
structure Input {β : Type*} (a : Adjacency) (G : Graph Nat β) where
  representation : Represents a G
  source : Nat
  source_valid : source < a.n
  memory : Memory
  heap : Heap a memory


end AlgoLib.Experimental.RAM.BFS
