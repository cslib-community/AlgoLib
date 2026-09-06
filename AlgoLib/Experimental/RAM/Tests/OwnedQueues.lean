/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueAlgorithms
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueRing
import AlgoLib.Experimental.RAM.Prototype.Composition.QueueStacksImplementation

/-!
# Actual RAM substitution tests for two FIFO implementations

Both runners consume QueueAlgorithms.rotateProcedure, including the very same
source proof. Full queues exercise circular wraparound and stack transfer. The
initial potential of a resident nonempty two-stack queue is included in its bound.
-/
namespace AlgoLib.Experimental.RAM.Tests.OwnedQueues
open Prototype.Composition

def ringEncoder (capacity : Nat) :=
  (QueueRing.encoder ⟨"fifo", 0, capacity⟩).sep (scalarEncoder ⟨"result"⟩) (by
    simp [QueueRing.encoder, scalarEncoder, QueueRing.Layout.footprint,
      QueueRing.Layout.head, QueueRing.Layout.length, Finset.disjoint_left])

def stacksEncoder (capacity : Nat) :=
  (QueueStacksImplementation.encoder "fifo" 0 capacity).sep (scalarEncoder ⟨"result"⟩) (by
    simp [QueueStacksImplementation.encoder, QueueStacksImplementation.concreteEncoder,
      Encoder.sep, BufferImplementation.encoder, BufferImplementation.Layout.footprint,
      BufferImplementation.Layout.lengthVar, BufferImplementation.Layout.argumentVar,
      scalarEncoder, Finset.disjoint_left]
    rintro location (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp)

instance (capacity : Nat) : Linked 24 (ringEncoder capacity).representation
    (QueueAlgorithms.rotateProcedure capacity).body (ringEncoder capacity).representation := by
  unfold ringEncoder
  ram_link

instance (capacity : Nat) : Linked 24 (stacksEncoder capacity).representation
    (QueueAlgorithms.rotateProcedure capacity).body (stacksEncoder capacity).representation := by
  unfold stacksEncoder
  ram_link

def ring (xs : List Nat) (nonempty : xs ≠ []) : Result (List Nat × Nat) :=
  runEncoded (rate := 24) (QueueAlgorithms.rotateProcedure xs.length) (ringEncoder xs.length)
    (xs, 0) ⟨nonempty, Nat.le_refl _, trivial⟩ (by
      simp [ringEncoder, Encoder.sep, QueueRing.encoder, scalarEncoder])

def twoStacks (xs : List Nat) (nonempty : xs ≠ []) : Result (List Nat × Nat) :=
  runEncoded (rate := 24) (QueueAlgorithms.rotateProcedure xs.length) (stacksEncoder xs.length)
    (xs, 0) ⟨nonempty, Nat.le_refl _, trivial⟩ (by
      simp [stacksEncoder, Encoder.sep, QueueStacksImplementation.encoder, scalarEncoder])

theorem ring_correct (xs : List Nat) (nonempty : xs ≠ []) :
    (ring xs nonempty).value = (xs.tail ++ [xs.headD 0], xs.headD 0) ∧
      (ring xs nonempty).steps ≤ 480 := by
  have h := runEncoded_correct (rate := 24) (QueueAlgorithms.rotateProcedure xs.length)
    (ringEncoder xs.length) (xs, 0) ⟨nonempty, Nat.le_refl _, trivial⟩
    (by simp [ringEncoder, Encoder.sep, QueueRing.encoder, scalarEncoder])
  exact ⟨Prod.ext h.1.1 h.1.2.1, h.2⟩

theorem stacks_correct (xs : List Nat) (nonempty : xs ≠ []) :
    (twoStacks xs nonempty).value = (xs.tail ++ [xs.headD 0], xs.headD 0) ∧
      (twoStacks xs nonempty).steps ≤ 480 + 120 * xs.length := by
  have h := runEncoded_correct (rate := 24) (QueueAlgorithms.rotateProcedure xs.length)
    (stacksEncoder xs.length) (xs, 0) ⟨nonempty, Nat.le_refl _, trivial⟩
    (by simp [stacksEncoder, Encoder.sep, QueueStacksImplementation.encoder, scalarEncoder])
  exact ⟨Prod.ext h.1.1 h.1.2.1, h.2⟩

theorem same_result (xs : List Nat) (nonempty : xs ≠ []) :
    (ring xs nonempty).value = (twoStacks xs nonempty).value :=
  (ring_correct xs nonempty).1.trans (stacks_correct xs nonempty).1.symm

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 6 do
    for mask in List.range (3 ^ n) do
      let xs := 7 :: (List.range n).map (fun i => mask / 3 ^ i % 3)
      let a := ring xs (by simp [xs])
      let b := twoStacks xs (by simp [xs])
      unless a.value == b.value && a.value.1 == xs.tail ++ [7] && a.value.2 == 7 do
        throw <| IO.userError s!"FIFO substitution: {xs}"
      unless a.steps ≤ 480 && b.steps ≤ 480 + 120 * xs.length do
        throw <| IO.userError s!"FIFO amortized bound: {xs}"

end AlgoLib.Experimental.RAM.Tests.OwnedQueues
