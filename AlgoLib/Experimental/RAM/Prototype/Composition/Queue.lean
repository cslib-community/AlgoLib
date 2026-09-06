/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts

/-!
# FIFO contracts shared by owned graph algorithms

A queue is observed as a list in removal order. Calls transfer exclusive ownership
of the queue and, when needed, a scalar argument/result. Capacity is fixed library
configuration. Neither representation nor amortization potential occurs here.
Every operation has a fixed logical charge; a backend must justify its implementation
and any private savings against that charge. Initialization discards old contents.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Queue

/-- Initialization is an executed operation, not free input preprocessing. -/
def reset : Operation (List Nat) (List Nat) where
  requires _ := True
  effect _ := []
  charge _ := 10

/-- Enqueue preserves the borrowed scalar, so its owner may continue to use it. -/
def push (capacity : Nat) : Operation (List Nat × Nat) (List Nat × Nat) where
  requires q := q.1.length < capacity
  effect q := (q.1 ++ [q.2], q.2)
  charge _ := 10

/-- Dequeue replaces the scalar result and removes precisely the oldest element. -/
def pop : Operation (List Nat × Nat) (List Nat × Nat) where
  requires q := q.1 ≠ []
  effect q := (q.1.tail, q.1.headD 0)
  charge _ := 10

def nonempty (q : List Nat) : Bool := !q.isEmpty

namespace API

@[reducible] def initializeQueue : Procedure (List Nat) (List Nat) :=
  Procedure.verify (.invoke reset) (fun _ => True) (fun _ q => q = [])
    (fun _ => 10) (by simp [VC, reset])

@[reducible] def enqueue (capacity : Nat) : Procedure (List Nat × Nat) (List Nat × Nat) :=
  Procedure.verify (.invoke (push capacity)) (fun q => q.1.length < capacity)
    (fun q result => result = (q.1 ++ [q.2], q.2)) (fun _ => 10)
    (by simp [VC, push])

@[reducible] def dequeue : Procedure (List Nat × Nat) (List Nat × Nat) :=
  Procedure.verify (.invoke pop) (fun q => q.1 ≠ [])
    (fun q result => result = (q.1.tail, q.1.headD 0)) (fun _ => 10)
    (by simp [VC, pop])

instance : UniformCredits initializeQueue := ⟨10, fun _ => Nat.le_refl _⟩
instance (capacity : Nat) : UniformCredits (enqueue capacity) := ⟨10, fun _ => Nat.le_refl _⟩
instance : UniformCredits dequeue := ⟨10, fun _ => Nat.le_refl _⟩

end API
end AlgoLib.Experimental.RAM.Prototype.Composition.Queue
