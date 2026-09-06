/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Queue
import AlgoLib.Experimental.RAM.Prototype.Composition.Stack
import AlgoLib.Experimental.RAM.Prototype.Composition.Expressions

/-!
# Private two-stack FIFO implementation

The front stack is read in reverse and the back stack in insertion order. When
the front becomes empty, an explicit loop moves every back element to the front.
The loop is part of the compiled program. Five private logical credits per back
element pay for its guard and two stack operations; clients see only FIFO charges.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

private theorem swap_run (a : A × B) : Run Program.swap a 0 (a.2, a.1) := ⟨rfl, rfl⟩

/-- Focus a borrowed-argument call on the second of two owned components. -/
def Program.borrowRight (p : Program (B × X) (B × X)) : Program ((A × B) × X) ((A × B) × X) :=
  .seq (.invoke (associate A B X))
    (.seq (Program.both .identity p) (.invoke (unassociate A B X)))

/-- Focus a borrowed-argument call on the first component, framing the second. -/
def Program.borrowLeft (p : Program (A × X) (A × X)) : Program ((A × B) × X) ((A × B) × X) :=
  .seq (.frame .swap X) (.seq (Program.borrowRight p) (.frame .swap X))

theorem Run.borrowRight (h : Run p (b, x) k (b', x')) (a : A) :
    Run (Program.borrowRight p) ((a, b), x) k ((a, b'), x') := by
  have both := Run.seq (Run.frame (Run.identity a) (b, x))
    (Run.seq (swap_run (a, (b, x)))
      (Run.seq (Run.frame h a) (swap_run ((b', x'), a))))
  have result := Run.seq (Run.invoke (associate A _ _) ((a, b), x) trivial)
    (Run.seq both (Run.invoke (unassociate A _ _) (a, b', x') trivial))
  simpa [Program.borrowRight, associate, unassociate] using result

theorem Run.borrowLeft (h : Run p (a, x) k (a', x')) (b : B) :
    Run (Program.borrowLeft p) ((a, b), x) k ((a', b), x') := by
  have result := Run.seq (Run.frame (swap_run (a, b)) x)
    (Run.seq (Run.borrowRight h b) (Run.frame (swap_run (b, a')) x'))
  simpa [Program.borrowLeft] using result

namespace QueueStacks
abbrev State := List Nat × List Nat

def model (s : State) : List Nat := s.1.reverse ++ s.2
def valid (capacity : Nat) (s : State) : Prop := s.1.length + s.2.length ≤ capacity
def potential (s : State) : Nat := 5 * s.2.length

def push (capacity : Nat) : Program (State × Nat) (State × Nat) :=
  Program.borrowRight (.invoke (Buffer.appendBorrowed capacity))

def move (capacity : Nat) : Program (State × Nat) (State × Nat) :=
  .seq (Program.borrowRight (.invoke Stack.pop))
    (Program.borrowLeft (.invoke (Buffer.appendBorrowed capacity)))

def backNonempty (s : State × Nat) : Bool := !s.1.2.isEmpty
def frontNonempty (s : State × Nat) : Bool := !s.1.1.isEmpty

def transfer (capacity : Nat) : Program (State × Nat) (State × Nat) :=
  .loop backNonempty (move capacity)

def pop (capacity : Nat) : Program (State × Nat) (State × Nat) :=
  .seq (.branch frontNonempty .identity (transfer capacity))
    (Program.borrowLeft (.invoke Stack.pop))

def reset : Program State State := Program.both (.invoke Buffer.clear) (.invoke Buffer.clear)

theorem push_run (capacity : Nat) (f b : List Nat) (x : Nat)
    (space : f.length + b.length < capacity) :
    Run (push capacity) ((f, b), x) 2 ((f, b ++ [x]), x) :=
  Run.borrowRight (Run.invoke (Buffer.appendBorrowed capacity) (b, x) (by
    change b.length < capacity; omega)) f

theorem move_run (capacity : Nat) (f b : List Nat) (x y : Nat)
    (space : f.length + (b ++ [y]).length ≤ capacity) :
    Run (move capacity) ((f, b ++ [y]), x) 4 ((f ++ [y], b), y) := by
  have hp := Run.borrowRight (Run.invoke Stack.pop (b ++ [y], x) (by simp [Stack.pop])) f
  simp only [Stack.pop, List.dropLast_concat, List.getLastD_concat] at hp
  have hq := Run.borrowLeft (Run.invoke (Buffer.appendBorrowed capacity) (f, y)
    (by change f.length < capacity; simp at space; omega)) b
  simpa [move, Stack.pop, Buffer.appendBorrowed] using Run.seq hp hq

/-- The transfer loop reverses every back entry with a proved linear logical count. -/
theorem transfer_run (capacity : Nat) (b : List Nat) (f : List Nat) (x : Nat)
    (space : f.length + b.length ≤ capacity) :
    ∃ y, Run (transfer capacity) ((f, b), x) (5 * b.length + 1) ((f ++ b.reverse, []), y) := by
  induction b using List.reverseRecOn generalizing f x with
  | nil => exact ⟨x, by simpa [transfer, backNonempty] using
      (Run.done (body := move capacity) (a := ((f, []), x)) rfl)⟩
  | append_singleton b y ih =>
    obtain ⟨z, rest⟩ := ih (f ++ [y]) y (by simpa [List.length_append, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using space)
    have step := Run.step (test := backNonempty) (by simp [backNonempty])
      (move_run capacity f b x y space) rest
    refine ⟨z, ?_⟩
    convert step using 1
    · simp; omega
    · simp [List.reverse_append, List.append_assoc]

theorem reset_run (s : State) : Run reset s 2 ([], []) := by
  have step := Run.seq (Run.frame (Run.invoke Buffer.clear s.1 trivial) s.2)
    (Run.seq (swap_run ([], s.2))
      (Run.seq (Run.frame (Run.invoke Buffer.clear s.2 trivial) []) (swap_run ([], []))))
  exact step

/-- The top of the front stack is exactly the FIFO head. -/
theorem front_pop (f b : List Nat) (nonempty : f ≠ []) :
    model (f.dropLast, b) = (model (f, b)).tail ∧
      f.getLastD 0 = (model (f, b)).headD 0 := by
  induction f using List.reverseRecOn with
  | nil => contradiction
  | append_singleton f x _ => simp [model, List.reverse_append]

/-- A constant public enqueue allowance pays for saving the new element's transfer work. -/
theorem push_refines (capacity : Nat) (s : State × Nat) (inv : valid capacity s.1)
    (pre : (Queue.push capacity).requires (model s.1, s.2)) :
    ∃ k t, Run (push capacity) s k t ∧ valid capacity t.1 ∧
      (model t.1, t.2) = (Queue.push capacity).effect (model s.1, s.2) ∧
      k + potential t.1 ≤ (Queue.push capacity).charge (model s.1, s.2) + potential s.1 := by
  obtain ⟨⟨f, b⟩, x⟩ := s
  have space : f.length + b.length < capacity := by simpa [Queue.push, model] using pre
  refine ⟨2, ((f, b ++ [x]), x), push_run capacity f b x space, ?_, ?_, ?_⟩
  · simp [valid]; omega
  · simp [model, Queue.push, List.append_assoc]
  · simp [potential, Queue.push]; omega

/-- The transfer is paid privately; the client always receives the same FIFO summary. -/
theorem pop_refines (capacity : Nat) (s : State × Nat) (inv : valid capacity s.1)
    (pre : Queue.pop.requires (model s.1, s.2)) :
    ∃ k t, Run (pop capacity) s k t ∧ valid capacity t.1 ∧
      (model t.1, t.2) = Queue.pop.effect (model s.1, s.2) ∧
      k + potential t.1 ≤ Queue.pop.charge (model s.1, s.2) + potential s.1 := by
  obtain ⟨⟨f, b⟩, x⟩ := s
  by_cases empty : f = []
  · subst f
    have hb : b ≠ [] := by simpa [Queue.pop, model] using pre
    obtain ⟨y, transferProof⟩ := transfer_run capacity b [] x inv
    have hp := Run.borrowLeft (Run.invoke Stack.pop (b.reverse, y)
      (by simpa [Stack.pop] using hb)) ([] : List Nat)
    have branch := Run.no (p := Program.identity) (test := frontNonempty)
      (by simp [frontNonempty]) transferProof
    have run := Run.seq branch hp
    have facts := front_pop b.reverse [] (by simpa using hb)
    refine ⟨1 + (5 * b.length + 1) + 2, ((b.reverse.dropLast, []), b.reverse.getLastD 0),
      ?_, ?_, ?_, ?_⟩
    · simpa [pop, Stack.pop] using run
    · simp [valid] at *; omega
    · simp [Queue.pop, model] at facts ⊢
    · simp [Queue.pop, potential]; omega
  · have hp := Run.borrowLeft (Run.invoke Stack.pop (f, x) empty) b
    have branch := Run.yes (q := transfer capacity) (test := frontNonempty)
      (a := ((f, b), x)) (by simpa [frontNonempty, List.isEmpty_eq_false_iff] using empty)
      (Run.identity _)
    have facts := front_pop f b empty
    refine ⟨3, ((f.dropLast, b), f.getLastD 0), ?_, ?_, ?_, ?_⟩
    · simpa [pop, Stack.pop] using Run.seq branch hp
    · simp [valid] at *; omega
    · exact Prod.ext facts.1 facts.2
    · simp [Queue.pop, potential]

end QueueStacks
end AlgoLib.Experimental.RAM.Prototype.Composition
