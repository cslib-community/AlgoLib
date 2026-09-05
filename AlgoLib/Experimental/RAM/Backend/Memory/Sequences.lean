/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Memory.Array

/-!
# Physical stack and FIFO contracts

Builds sequential data-structure operations over the array layer, with logical contents and
operation cost bounds.

These are reusable backend contracts. A new student-facing operation should expose an
Authoring.Action through Library.

## Further details

# Verified stacks and FIFO queues

Both use contiguous storage and explicit cursors. Queue storage is append-only:
capacity bounds total enqueues since initialization, as in textbook BFS. No
amortized host-list operations or uncharged resizing are hidden in these APIs.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

def increment (v : Var .word) : Cmd := .assign v (.bin .add (.var v) (.lit 1))
def decrement (v : Var .word) : Cmd := .assign v (.bin .sub (.var v) (.lit 1))

/-- Shared append primitive: write a slot, then advance its cursor. -/
def appendSlot (a : ArrayRef) (cursor : Var .word) (value : Expr .word) : Cmd :=
  .seq (a.put (.var cursor) value) (increment cursor)

def appendState (a : ArrayRef) (cursor : Var .word) (value : Expr .word) (s : Store) : Store :=
  (s.write (s.vars .ptr a.base.name + s.vars .word cursor.name) (value.eval s)).set cursor
    (s.vars .word cursor.name + 1)

theorem appendSlot_eval (a : ArrayRef) (cursor : Var .word) (value : Expr .word) (s : Store) :
    Eval (appendSlot a cursor value) s (value.cost + 8) (appendState a cursor value s) := by
  have h := Eval.seq (Eval.write (a.address (.var cursor)) value s)
    (Eval.assign cursor (.bin .add (.var cursor) (.lit 1))
      (s.write ((a.address (.var cursor)).eval s) (value.eval s)))
  convert h using 1
  simp [ArrayRef.address, Expr.cost]
  omega


structure StackRef where
  data : ArrayRef
  size : Var .word

def StackRef.Rep (a : StackRef) (capacity : Nat) (s : Store) (xs : List Nat) : Prop :=
  s.vars .word a.size.name = xs.length ∧ xs.length ≤ capacity ∧ a.data.Rep s xs

def StackRef.push (a : StackRef) (value : Expr .word) : Cmd := appendSlot a.data a.size value

def StackRef.pop (a : StackRef) (out : Var .word) : Cmd :=
  .seq (decrement a.size) (a.data.get (.var a.size) out)

/-- Stack push implements list append, pays every operation, and exposes its exact frame. -/
theorem StackRef.push_spec (a : StackRef) (capacity : Nat) (xs : List Nat) (value : Expr .word) :
    Contract (a.push value) (fun s => a.Rep capacity s xs ∧ xs.length < capacity)
      (fun s t => a.Rep capacity t (xs ++ [value.eval s]) ∧
        t = appendState a.data a.size value s) (fun _ => value.cost + 8) := by
  intro s ⟨⟨hs, hc, hr⟩, hcap⟩
  refine ⟨_, _, appendSlot_eval _ _ _ _, ⟨?_, rfl⟩, Nat.le_refl _⟩
  refine ⟨?_, by simp; omega, ?_⟩
  · simp [appendState, hs]
  · have h := hr.append (value.eval s)
    simpa [ArrayRef.Rep, appendState, hs] using h

def popState (a : StackRef) (out : Var .word) (s : Store) : Store :=
  (s.set a.size (s.vars .word a.size.name - 1)).set out
    (s.heap (s.vars .ptr a.data.base.name + (s.vars .word a.size.name - 1)))

theorem StackRef.pop_eval (a : StackRef) (out : Var .word) (s : Store) :
    Eval (a.pop out) s 9 (popState a out s) := by
  simpa [StackRef.pop, decrement, ArrayRef.get, ArrayRef.cell, ArrayRef.address,
    popState, Expr.cost, Expr.eval, Op.eval, Op.machine, BinOp.eval] using
    Eval.seq (Eval.assign a.size (.bin .sub (.var a.size) (.lit 1)) s)
      (Eval.assign out (a.data.cell (.var a.size)) (s.set a.size (s.vars .word a.size.name - 1)))

/-- Pop is safe only for a nonempty stack; output must not alias its size cursor. -/
theorem StackRef.pop_spec (a : StackRef) (out : Var .word) (hne : out.name ≠ a.size.name)
    (capacity : Nat) (xs : List Nat) (v : Nat) :
    Contract (a.pop out) (fun s => a.Rep capacity s (xs ++ [v]))
      (fun s t => a.Rep capacity t xs ∧ t.vars .word out.name = v ∧ t.heap = s.heap)
      (fun _ => 9) := by
  intro s ⟨hs, hc, hr⟩
  have hs' : s.vars .word a.size.name - 1 = xs.length := by simp_all
  have hv := hr.last
  refine ⟨9, _, a.pop_eval out s, ?_, Nat.le_refl _⟩
  refine ⟨⟨?_, by simp_all; omega, ?_⟩, ?_, rfl⟩
  · simp [popState, hs', Ne.symm hne]
  · simpa [StackRef.Rep, ArrayRef.Rep, popState] using hr.prefix
  · simp [popState, hs', hv]

structure QueueRef where
  data : ArrayRef
  front : Var .word
  back : Var .word
  distinct : front.name ≠ back.name

def QueueRef.Rep (q : QueueRef) (capacity : Nat) (s : Store) (xs : List Nat) : Prop :=
  s.vars .word q.back.name = s.vars .word q.front.name + xs.length ∧
  s.vars .word q.back.name ≤ capacity ∧
  Segment s (s.vars .ptr q.data.base.name + s.vars .word q.front.name) xs

def QueueRef.enqueue (q : QueueRef) (value : Expr .word) : Cmd := appendSlot q.data q.back value

def QueueRef.dequeue (q : QueueRef) (out : Var .word) : Cmd :=
  .seq (q.data.get (.var q.front) out) (increment q.front)

theorem QueueRef.enqueue_spec (q : QueueRef) (capacity : Nat) (xs : List Nat)
    (value : Expr .word) : Contract (q.enqueue value)
      (fun s => q.Rep capacity s xs ∧ s.vars .word q.back.name < capacity)
      (fun s t => q.Rep capacity t (xs ++ [value.eval s]) ∧
        t = appendState q.data q.back value s) (fun _ => value.cost + 8) := by
  intro s ⟨⟨ht, hc, hr⟩, hcap⟩
  refine ⟨_, _, appendSlot_eval _ _ _ _, ⟨?_, rfl⟩, Nat.le_refl _⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [appendState, q.distinct, ht, Nat.add_assoc]
  · simp [appendState]; omega
  · have h := hr.append (value.eval s)
    simpa [appendState, q.distinct, ht, Nat.add_assoc] using h

def dequeueState (q : QueueRef) (out : Var .word) (s : Store) : Store :=
  (s.set out (s.heap (s.vars .ptr q.data.base.name + s.vars .word q.front.name))).set q.front
    (s.vars .word q.front.name + 1)

theorem QueueRef.dequeue_eval (q : QueueRef) (out : Var .word)
    (hne : out.name ≠ q.front.name) (s : Store) :
    Eval (q.dequeue out) s 9 (dequeueState q out s) := by
  simpa [QueueRef.dequeue, ArrayRef.get, ArrayRef.cell, ArrayRef.address, increment,
    dequeueState, Expr.cost, Expr.eval, Op.eval, Op.machine, BinOp.eval, Ne.symm hne] using
    Eval.seq (Eval.assign out (q.data.cell (.var q.front)) s)
      (Eval.assign q.front (.bin .add (.var q.front) (.lit 1))
        (s.set out ((q.data.cell (.var q.front)).eval s)))

/-- Dequeue returns the head, retains the tail, preserves the heap, and costs nine. -/
theorem QueueRef.dequeue_spec (q : QueueRef) (out : Var .word)
    (hf : out.name ≠ q.front.name) (hb : out.name ≠ q.back.name)
    (capacity : Nat) (xs : List Nat) (v : Nat) :
    Contract (q.dequeue out) (fun s => q.Rep capacity s (v :: xs))
      (fun s t => q.Rep capacity t xs ∧ t.vars .word out.name = v ∧ t.heap = s.heap)
      (fun _ => 9) := by
  intro s ⟨ht, hc, hr⟩
  refine ⟨9, _, q.dequeue_eval out hf s, ?_, Nat.le_refl _⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, rfl⟩
  · simp [dequeueState, Ne.symm hb, Ne.symm q.distinct, ht, Nat.add_assoc, Nat.add_comm]
  · simpa [dequeueState, Ne.symm hb, Ne.symm q.distinct] using hc
  · simpa [dequeueState, Nat.add_assoc] using hr.tail
  · simp [dequeueState, hf, hr.head]

def StackRef.clear (a : StackRef) : Cmd := .assign a.size (.lit 0)
def QueueRef.clear (q : QueueRef) : Cmd :=
  .seq (.assign q.front (.lit 0)) (.assign q.back (.lit 0))

theorem StackRef.clear_spec (a : StackRef) (capacity : Nat) :
    Contract a.clear (fun _ => True)
      (fun s t => a.Rep capacity t [] ∧ t.heap = s.heap) (fun _ => 2) := by
  intro s _
  exact ⟨2, _, .assign _ _ _,
    ⟨⟨by simp [Expr.eval], by simp, Segment.nil _ _⟩, rfl⟩, Nat.le_refl _⟩

theorem QueueRef.clear_spec (q : QueueRef) (capacity : Nat) :
    Contract q.clear (fun _ => True)
      (fun s t => q.Rep capacity t [] ∧ t.heap = s.heap) (fun _ => 4) := by
  intro s _
  refine ⟨4, _, .seq (.assign _ _ _) (.assign _ _ _), ?_, Nat.le_refl _⟩
  exact ⟨⟨by simp [q.distinct, Expr.eval], by simp [Expr.eval], Segment.nil _ _⟩, rfl⟩

def StackRef.isEmpty (a : StackRef) : Condition := ⟨.word, .eq, .var a.size, .lit 0⟩
def QueueRef.isEmpty (q : QueueRef) : Condition := ⟨.word, .eq, .var q.front, .var q.back⟩

theorem StackRef.empty_iff (a : StackRef) (capacity : Nat) (s : Store) (xs : List Nat)
    (h : a.Rep capacity s xs) : a.isEmpty.eval s = true ↔ xs = [] := by
  simp [StackRef.isEmpty, Condition.eval, Comparison.eval, Expr.eval, h.1]

theorem QueueRef.empty_iff (q : QueueRef) (capacity : Nat) (s : Store) (xs : List Nat)
    (h : q.Rep capacity s xs) : q.isEmpty.eval s = true ↔ xs = [] := by
  simp [QueueRef.isEmpty, Condition.eval, Comparison.eval, Expr.eval, h.1]

end AlgoLib.Experimental.RAM.Checked.Language
