/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Adapters.Insertion
import AlgoLib.Experimental.RAM.Authoring.Interface

/-!
# Array input/output adapter

Encodes a list, performs paid preparation, and relates the final array observation to todo.reverse
++ sorted.

The generic Interface consumes these proofs once. Library/Insertion publishes stable equations for
initial state, observation, and cost accounting.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Insertion
open Checked Checked.Language

def initial (xs : List Nat) : State := ⟨xs.reverse, []⟩

private def encode (xs : List Nat) : Store where
  vars ty name := if ty = .word ∧ name = Refinement.name .count then xs.length else 0
  heap := ofList xs

private def prepareCode : Code := .block [.bin .add .limit (.reg .base) (.reg .count)]

private theorem prepare_correct (xs : List Nat) :
    ∃ k t, Eval (Refinement.lift prepareCode) (encode xs) k t ∧
      model.Represents (initial xs) t ∧ k ≤ 5 := by
  have ready : Refinement.Ready (encode xs) := by simp [encode, Refinement.Ready]
  obtain ⟨k, t, ht, hr, heq, hk⟩ := Refinement.lift_correct
    (Exec.block [.bin .add .limit (.reg .base) (.reg .count)] (Refinement.view (encode xs)))
    (by decide) (encode xs) ready rfl
  have hm : t.heap = ofList xs := congrArg Checked.State.memory heq
  refine ⟨k, t, ht, ⟨hr, ?_, ?_, ?_, ?_, ?_⟩, hk⟩
  · rw [heq]
    simp [blockEval, Instr.eval, Operand.eval, BinOp.eval, Checked.State.set,
      Refinement.view, encode, Refinement.name]
  · rw [heq]
    simp [blockEval, Instr.eval, Operand.eval, BinOp.eval, Checked.State.set,
      Refinement.view, encode, Refinement.name, initial]
  · rw [heq]
    simp [blockEval, Instr.eval, Operand.eval, BinOp.eval, Checked.State.set,
      Refinement.view, encode, Refinement.name, initial]
  · simp only [initial, List.reverse_reverse]
    intro i hi
    simp [hm, ofList, List.getElem?_eq_getElem hi]
  · exact Segment.nil _ _

private theorem contents_append (m : Memory) (b n k : Nat) :
    contents m b (n+k) = contents m b n ++ contents m (b+n) k := by
  induction n generalizing b with
  | zero => simp [contents]
  | succ n ih =>
    simpa [contents, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (List.cons (m b)) (ih (b+1))

def interface : Interface model (List Nat) (List Nat) where
  initial := initial
  encode := encode
  prepare := Refinement.lift prepareCode
  preparationCost _ := 5
  preparation := prepare_correct
  decode _ s := contents s.heap 0 ((Refinement.view s).regs .limit)
  Observes g out := out = g.todo.reverse ++ g.sorted
  output _ g s hs := by
    rw [hs.2.2.2.1, contents_append]
    have hprefix := segment_contents hs.2.2.2.2.1
    have hsuffix := segment_contents hs.2.2.2.2.2
    simpa using congrArg₂ (List.append) hprefix hsuffix

end AlgoLib.Experimental.RAM.Authoring.Insertion
