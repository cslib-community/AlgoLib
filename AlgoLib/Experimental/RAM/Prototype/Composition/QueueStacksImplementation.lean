/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueStacks
import AlgoLib.Experimental.RAM.Prototype.Composition.StackImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.DataRefinement

/-!
# Link the two-stack FIFO to actual RAM

The concrete loop and its amortized proof live in QueueStacks. This file selects
two separately owned array-backed stacks and reconstructs their RAM certificates.
FIFO clients never see these stacks or their saved potential. Each stack reserves
capacity cells; moving elements does not allocate or copy an entire array.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.QueueStacksImplementation
open Checked.Language BufferImplementation

abbrev storage (name : String) (base capacity : Nat) : Representation QueueStacks.State :=
  (representation ⟨name ++ ".front", base, capacity⟩ false).sep
    (representation ⟨name ++ ".back", base + capacity, capacity⟩ false)

def view (capacity : Nat) : DataView QueueStacks.State (List Nat) :=
  ⟨QueueStacks.model, QueueStacks.valid capacity, QueueStacks.potential⟩

abbrev queue (name : String) (base capacity : Nat) : Representation (List Nat) :=
  (view capacity).representation 24 (storage name base capacity)

instance backTest (name : String) (base capacity : Nat) (Q : Representation Nat) :
    TestImplementation 24 ((storage name base capacity).sep Q) QueueStacks.backNonempty :=
  inferInstanceAs (TestImplementation 24 _ (testLeft (testRight Buffer.nonempty)))

instance frontTest (name : String) (base capacity : Nat) (Q : Representation Nat) :
    TestImplementation 24 ((storage name base capacity).sep Q) QueueStacks.frontNonempty :=
  inferInstanceAs (TestImplementation 24 _ (testLeft (testLeft Buffer.nonempty)))

instance pushLinked (name : String) (base capacity : Nat) [ScalarStorage Q] :
    Linked 24 ((storage name base capacity).sep Q) (QueueStacks.push capacity)
      ((storage name base capacity).sep Q) := by
  unfold QueueStacks.push Program.borrowRight Program.both storage
  ram_link

instance popLinked (name : String) (base capacity : Nat) [ScalarStorage Q] :
    Linked 24 ((storage name base capacity).sep Q) (QueueStacks.pop capacity)
      ((storage name base capacity).sep Q) := by
  unfold QueueStacks.pop QueueStacks.transfer QueueStacks.move
    Program.borrowLeft Program.borrowRight Program.both
  ram_link

instance pushImplementation (name : String) (base capacity : Nat) [ScalarStorage Q] :
    Primitive 24 ((queue name base capacity).sep Q) (Queue.push capacity)
      ((queue name base capacity).sep Q) :=
  (view capacity).realizeBorrowed (P := storage name base capacity)
    (Queue.push capacity) (QueueStacks.push capacity) (QueueStacks.push_refines capacity)

instance popImplementation (name : String) (base capacity : Nat) [ScalarStorage Q] :
    Primitive 24 ((queue name base capacity).sep Q) Queue.pop
      ((queue name base capacity).sep Q) :=
  (view capacity).realizeBorrowed (P := storage name base capacity)
    Queue.pop (QueueStacks.pop capacity) (QueueStacks.pop_refines capacity)

instance resetLinked (name : String) (base capacity : Nat) :
    Linked 24 (storage name base capacity) QueueStacks.reset (storage name base capacity) := by
  unfold QueueStacks.reset Program.both storage
  ram_link

instance resetImplementation (name : String) (base capacity : Nat) :
    Primitive 24 (queue name base capacity) Queue.reset (queue name base capacity) :=
  (view capacity).realize (P := storage name base capacity) Queue.reset QueueStacks.reset (by
    intro c valid pre
    exact ⟨2, ([],[]), QueueStacks.reset_run c, by simp [view, QueueStacks.valid],
      rfl, by simp [view, QueueStacks.potential, Queue.reset]; omega⟩)

instance nonemptyImplementation (name : String) (base capacity : Nat) :
    TestImplementation 24 (queue name base capacity) Queue.nonempty where
  condition := ⟨.word, .lt, .lit 0,
    .bin .add (.var (Layout.lengthVar ⟨name ++ ".front", base, capacity⟩))
      (.var (Layout.lengthVar ⟨name ++ ".back", base + capacity, capacity⟩))⟩
  correct a r s saved h := by
    obtain ⟨⟨f,b⟩, left, hp, valid, rfl, paid⟩ := h
    obtain ⟨rf, rb, cf, cb, hd, hr, hc, hf, hb⟩ := hp
    simp only [Condition.eval, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval,
      Comparison.eval, hf.2.1.2.1, hb.2.1.2.1]
    cases f <;> cases b <;> simp [view, QueueStacks.model, Queue.nonempty]
  cost := by simp [Condition.cost, Expr.cost]

/-- The two stack allocations are adjacent but disjoint, including their registers. -/
theorem allocations_disjoint (name : String) (base capacity : Nat) :
    Disjoint (Layout.footprint ⟨name ++ ".front", base, capacity⟩)
      (Layout.footprint ⟨name ++ ".back", base + capacity, capacity⟩) := by
  apply Finset.disjoint_left.mpr
  intro location front back
  cases location with
  | register ty label =>
    simp [Layout.footprint, Layout.lengthVar, Layout.argumentVar] at front back
    rcases front with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [String.append_assoc] at back
  | heap address =>
    simp [Layout.footprint] at front back
    obtain ⟨i, hi, rfl⟩ := front
    obtain ⟨j, hj, equal⟩ := back
    omega

def concreteEncoder (name : String) (base capacity : Nat) : Encoder (storage name base capacity) :=
  (BufferImplementation.encoder ⟨name ++ ".front", base, capacity⟩ false).sep
    (BufferImplementation.encoder ⟨name ++ ".back", base + capacity, capacity⟩ false)
    (allocations_disjoint name base capacity)

/-- Resident input is represented explicitly; initial back entries carry charged potential. -/
def encoder (name : String) (base capacity : Nat) : Encoder (queue name base capacity) where
  footprint := (concreteEncoder name base capacity).footprint
  requires xs := xs.length ≤ capacity
  saved xs := 120 * xs.length
  store xs := (concreteEncoder name base capacity).store ([], xs)
  correct xs bound := by
    have h := (concreteEncoder name base capacity).correct ([], xs)
      (by simpa [concreteEncoder, Encoder.sep, BufferImplementation.encoder] using bound)
    refine ⟨([], xs), 0, ?_, by simpa [view, QueueStacks.valid] using bound, by simp [view,
      QueueStacks.model], ?_⟩
    · simpa [concreteEncoder, Encoder.sep, BufferImplementation.encoder, potential] using h
    · simp [view, QueueStacks.potential]; omega

end AlgoLib.Experimental.RAM.Prototype.Composition.QueueStacksImplementation
