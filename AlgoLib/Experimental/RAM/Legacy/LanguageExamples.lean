/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Syntax
import AlgoLib.Experimental.RAM.Backend.Language.Interface
import AlgoLib.Experimental.RAM.Backend.Memory.Graph

/-!
# Legacy demonstration: LanguageExamples

Retains an earlier lower-level example for historical comparison and compiler regression coverage.
This is an explicit opt-in module and is not imported by the public RAM entry point.

Use Programs/Sorting and Programs/Connectivity for the current input/output method and
algorithm-level VC workflow.

## Further details

# Extending algorithms through the public language and library

No compiler or parser modifications are needed for these examples. The proofs
use source substitutions, a textbook loop invariant, and library contracts.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language.Demo

def counter : Var .word := ⟨"counter"⟩
def answer : Var .word := ⟨"answer"⟩

/-- A typed procedure with an expression input and an explicit output variable. -/
def twicePlusOne : Procedure .word .word := procedure (input) returns output {
  output := 2 * input + 1;
}

theorem twicePlusOne_spec (input : Expr .word) (output : Var .word)
    (hne : output.name ≠ twicePlusOne.parameter.name) :
    Contract (twicePlusOne.call input output) (fun _ => True)
      (fun s t => t = s.set output (2 * input.eval s + 1))
      (fun _ => input.cost + 9) := by
  apply VC.contract
  intro s _
  simp only [Procedure.call, twicePlusOne, VC, expression, ToExpr.toExpr, Expr.cost,
    Expr.eval, Op.eval, Op.machine, BinOp.eval, Store.set_vars, and_self, if_true]
  refine ⟨by omega, by omega, ?_⟩
  change ((s.set twicePlusOne.parameter (input.eval s)).set output
    (2 * input.eval s + 1)).set twicePlusOne.parameter
      (s.vars .word twicePlusOne.parameter.name) = _
  rw [Store.set_comm _ output twicePlusOne.parameter _ _ hne, Store.set_restore]

/-- A loop whose invariant and time bound fit the usual paper proof. -/
def count : Cmd := program {
  answer := 0;
  while 0 < counter {
    counter := counter - 1;
    answer := answer + 1;
  }
}

/-- Invariant: counter + answer = original counter.
Credits: 11 * counter + 3, paying eight body instructions and a three-step guard. -/
theorem count_verified : Contract count (fun _ => True)
    (fun s t => t.vars .word answer.name = s.vars .word counter.name ∧ t.heap = s.heap)
    (fun s => 11 * s.vars .word counter.name + 5) := by
  apply VC.contract
  intro s _
  simp only [count, VC, Expr.cost, Expr.eval, expression, ToExpr.toExpr]
  refine ⟨by omega, ?_⟩
  refine ⟨fun t credits => t.vars .word counter.name + t.vars .word answer.name =
      s.vars .word counter.name ∧ t.heap = s.heap ∧
      credits = 11 * t.vars .word counter.name + 3, ?_, ?_⟩
  · simp [Store.set, counter, answer]
  · intro t credits ⟨hinv, hheap, hcredits⟩
    simp only [Condition.cost, Expr.cost, Condition.eval, Comparison.eval, Expr.eval,
      Op.eval, Op.machine, BinOp.eval]
    refine ⟨by omega, ?_⟩
    split
    · rename_i hpos
      simp only [decide_eq_true_eq] at hpos
      have hne : counter.name ≠ answer.name := by decide
      simp only [Nat.reduceAdd, Store.set_vars, true_and, and_self,
        if_true, if_neg hne, if_neg (Ne.symm hne), Store.set_heap]
      exact ⟨by omega, by omega, by omega, hheap, by omega⟩
    · rename_i hzero
      simp only [decide_eq_true_eq] at hzero
      exact ⟨by omega, hheap⟩

/-- The executable interface takes a natural number and returns a natural number. -/
def countFunction : Function Nat where
  body := count
  input n := ⟨fun _ name => if name = counter.name then n else 0, fun _ => 0⟩
  output := answer
  ensures n result := result = n
  budget n := 11 * n + 5
  verification n := by
    obtain ⟨k, t, hx, hQ, hk⟩ := count_verified
      ⟨fun _ name => if name = counter.name then n else 0, fun _ => 0⟩ trivial
    exact ⟨k, t, hx, by simpa using hQ.1, by simpa using hk⟩

/-- BFS's ordinary distance/parent update, previously impossible in Authoring.Plan. -/
def recordDiscovery (distance parent : ArrayRef) (u v : Var .word) : Cmd := program {
  distance[v] := distance[u] + 1;
  parent[v] := u;
}

/-- The complete heap update and its cost, with arbitrary runtime array bases.
This exact state equation supplies the frame for disjoint queues and other arrays. -/
theorem recordDiscovery_spec (distance parent : ArrayRef) (u v : Var .word) :
    Contract (recordDiscovery distance parent u v) (fun _ => True)
      (fun s t => t =
        (s.write (s.vars .ptr distance.base.name + s.vars .word v.name)
          (s.heap (s.vars .ptr distance.base.name + s.vars .word u.name) + 1)).write
          (s.vars .ptr parent.base.name + s.vars .word v.name) (s.vars .word u.name))
      (fun _ => 15) := by
  apply VC.contract
  intro s _
  simp [recordDiscovery, VC, ArrayRef.put, ArrayRef.address, ArrayRef.cell,
    expression, ToExpr.toExpr, Expr.cost, Expr.eval, Op.eval, Op.machine, BinOp.eval]

/-- Calls, library operations, and arbitrary conditionals compose as ordinary syntax. -/
def discoverAndEnqueue (distance parent visited : ArrayRef) (q : QueueRef)
    (u v : Var .word) : Cmd := program {
  if visited[v] == 0 {
    visited[v] := 1;
    call (recordDiscovery distance parent u v);
    call (q.enqueue (.var v));
  } else {}
}

end AlgoLib.Experimental.RAM.Checked.Language.Demo
