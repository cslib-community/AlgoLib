/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Legacy.LanguageExamples

/-!
# Regression checks: Language

Checks the relevant executable, proof, or compiler guarantees against regressions. Expected-output
assertions and theorem checks are part of the test, not extra algorithm implementations.

See Tests/README.md for coverage and build commands. Canonical programs live exclusively under
Programs.

## Further details

# Compiler, executable-interface, and data-structure regressions
-/
namespace AlgoLib.Experimental.RAM.Checked.Language.Tests
open Demo

/-- Expression evaluation executes compiled RAM without fuel. -/
def evaluate {ty : Ty} (e : Expr ty) (s : Store) : Nat × Nat :=
  let r := Checked.run (e.compile 0) (encode s) (by
    obtain ⟨t, hx, _, _⟩ := e.correct 0 (encode s)
    exact ⟨e.cost, t, hx⟩)
  (r.2.regs (.scratch 0), r.1)

def expressions : List (Expr .word) := [
  .lit 7, .var counter,
  source_expr% (counter + 3) * (counter - 2),
  .load (.bin .offset (.lit 10) (source_expr% counter * 2 + 1)),
  source_expr% (counter + counter) * ((counter + 1) * (counter + 2))]

def q : QueueRef := ⟨⟨⟨"queue.data"⟩⟩, ⟨"queue.front"⟩, ⟨"queue.back"⟩, by decide⟩
def stack : StackRef := ⟨⟨⟨"stack.data"⟩⟩, ⟨"stack.size"⟩⟩
def result : Var .word := ⟨"result"⟩
def initial : Store := ⟨fun ty name => if ty = .ptr then 100 else
  if name = q.back.name then 2 else 0, fun address => if address = 100 then 7 else 9⟩

/-- Use the actual public queue representation, not only a raw memory assertion. -/
theorem initial_queue : q.Rep 10 initial [7, 9] := by
  refine ⟨by decide, by decide, ?_⟩
  intro i hi
  have : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases this with rfl | rfl <;> rfl

def dequeueMethod : Method where
  body := q.dequeue result
  requires s := q.Rep 10 s [7, 9]
  ensures s t := q.Rep 10 t [9] ∧ t.vars .word result.name = 7 ∧ t.heap = s.heap
  budget _ := 9
  verification := q.dequeue_spec result (by decide) (by decide) 10 [9] 7

def popInitial : Store := ⟨fun ty _ => if ty = .ptr then 100 else 2,
  fun address => if address = 100 then 7 else 9⟩

theorem initial_stack : stack.Rep 10 popInitial [7, 9] := by
  refine ⟨by decide, by decide, ?_⟩
  intro i hi
  have : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases this with rfl | rfl <;> rfl

def popMethod : Method where
  body := stack.pop result
  requires s := stack.Rep 10 s ([7] ++ [9])
  ensures s t := stack.Rep 10 t [7] ∧ t.vars .word result.name = 9 ∧ t.heap = s.heap
  budget _ := 9
  verification := stack.pop_spec result (by decide) 10 [7] 9

/-- Nested scopes deliberately reuse one source variable: both saved values must survive. -/
def nested : Cmd := program {
  local counter := counter + 1 {
    local counter := counter + 1 {
      answer := counter;
    }
  }
}

theorem nested_spec : Contract nested (fun _ => True)
    (fun s t => t.vars .word counter.name = s.vars .word counter.name ∧
      t.vars .word answer.name = s.vars .word counter.name + 2 ∧ t.heap = s.heap)
    (fun _ => 14) := by
  apply VC.contract
  intro s _
  simp [nested, VC, expression, ToExpr.toExpr, Expr.eval, Expr.cost, Op.eval, Op.machine,
    BinOp.eval, Store.set, counter, answer, Nat.add_assoc]

def nestedMethod : Method := ⟨nested, _, _, _, nested_spec⟩

def twiceMethod : Method where
  body := twicePlusOne.call (.var counter) answer
  requires _ := True
  ensures s t := t = s.set answer (2 * s.vars .word counter.name + 1)
  budget _ := 10
  verification := twicePlusOne_spec (.var counter) answer (by decide)

example : Cmd := program { answer := twicePlusOne(counter + 2); }

/-- Literal-only nested guards have a default word type. -/
example : (source_condition% (1 + 2) < 4).eval initial = true := by decide

/-- Static typing rejects a pointer where arithmetic expects a word. -/
example : True := by
  fail_if_success
    let bad : Expr .word := Expr.bin .add (Expr.lit (ty := .ptr) 0) (.lit 1)
  trivial

/-- Zero credits cannot verify even a constant assignment. -/
example (s : Store) : ¬ VC (.assign result (.lit 42)) (fun _ _ => True) s 0 := by
  simp [VC, Expr.cost]

/-- Reusing the queue's front cursor as its result fails the public aliasing obligation. -/
example : ¬ q.front.name ≠ q.front.name := by simp

set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  for n in List.range 51 do
    let r := countFunction.run n
    unless r.output == n && r.steps == 11 * n + 5 do
      throw (IO.userError s!"count regression at {n}")
    let s : Store := ⟨fun _ _ => n, fun i => i + 3⟩
    let scopeResult := nestedMethod.run s trivial
    unless scopeResult.1 == 14 && scopeResult.2.vars .word counter.name == n &&
        scopeResult.2.vars .word answer.name == n + 2 do
      throw (IO.userError s!"nested scope regression at {n}")
    let called := twiceMethod.run s trivial
    unless called.1 == 10 && called.2.vars .word counter.name == n &&
        called.2.vars .word answer.name == 2 * n + 1 do
      throw (IO.userError s!"procedure regression at {n}")
    for e in expressions do
      unless evaluate e s == (e.eval s, e.cost) do
        throw (IO.userError s!"expression regression at {n}")
  let dequeue := dequeueMethod.run initial initial_queue
  unless dequeue.1 == 9 && dequeue.2.vars .word result.name == 7 do
    throw (IO.userError "FIFO regression")
  let pop := popMethod.run popInitial initial_stack
  unless pop.1 == 9 && pop.2.vars .word result.name == 9 do
    throw (IO.userError "LIFO regression")

end AlgoLib.Experimental.RAM.Checked.Language.Tests
