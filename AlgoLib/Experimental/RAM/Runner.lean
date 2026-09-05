/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Machine

/-!
# Execution without fuel

`TotalProgram.run` needs only the initial state. A program's termination theorem
is checked once when packaging it. Execution is well-founded recursion on the
machine transition relation; its accessibility proof is erased by Lean. There
is no guessed bound, fuel search, timeout, or noncomputable choice of output.
-/

namespace AlgoLib.Experimental.RAM.Checked

/-- A control stack and machine state. The stack is interpreter bookkeeping. -/
structure Config where
  todo : List Code
  state : State

/-- One transition. Only actual RAM work contributes to the returned cost. -/
def step (c : Config) : Option (Nat × Config) :=
  match c.todo with
  | [] => none
  | .block is :: rest => some (is.length, ⟨rest, blockEval is c.state⟩)
  | .seq a b :: rest => some (0, ⟨a :: b :: rest, c.state⟩)
  | .ite q a b :: rest =>
    some (1, ⟨(if q.eval c.state then a else b) :: rest, c.state⟩)
  | .while q b :: rest =>
    some (1, ⟨if q.eval c.state then b :: .while q b :: rest else rest, c.state⟩)

/-- Successor configurations are smaller in this relation. -/
def Next (d c : Config) : Prop := ∃ k, step c = some (k, d)

/-- A terminating transition trace. -/
inductive Trace : Config → Nat → State → Prop where
  | done (s : State) : Trace ⟨[], s⟩ 0 s
  | next {c d : Config} {i j : Nat} {t : State} :
      step c = some (i, d) → Trace d j t → Trace c (i + j) t

/-- Big-step executions implement the transition machine, including continuations. -/
theorem Exec.trace {a : Code} {s t : State} {i : Nat} (h : Exec a s i t)
    {rest : List Code} {u : State} {j : Nat} (ht : Trace ⟨rest, t⟩ j u) :
    Trace ⟨a :: rest, s⟩ (i + j) u := by
  induction h generalizing rest u j with
  | block is s => exact .next rfl ht
  | seq ha hb iha ihb =>
    simpa [Nat.add_assoc] using Trace.next (c := ⟨.seq _ _ :: rest, _⟩) rfl (iha (ihb ht))
  | ifTrue hq ha ih =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.ite _ _ _ :: rest, _⟩) (by simp [step, hq]) (ih ht)
  | ifFalse hq ha ih =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.ite _ _ _ :: rest, _⟩) (by simp [step, hq]) (ih ht)
  | whileFalse hq =>
    exact .next (by simp [step, hq]) ht
  | whileTrue hq ha hb iha ihb =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.while _ _ :: rest, _⟩) (by simp [step, hq]) (iha (ihb ht))

/-- A terminating trace supplies accessibility of the deterministic transition relation. -/
theorem Trace.accessible {c : Config} {k : Nat} {s : State} (h : Trace c k s) :
    Acc Next c := by
  induction h with
  | done s =>
    constructor
    rintro d ⟨k, hk⟩
    simp [step] at hk
  | next hs ht ih =>
    constructor
    rintro d ⟨k, hk⟩
    rw [hs] at hk
    obtain ⟨rfl, rfl⟩ := Option.some.inj hk
    exact ih

/-- The actual evaluator: recursion follows the termination proof, with no fuel. -/
def execute (c : Config) (h : Acc Next c) : Nat × State :=
  match hs : step c with
  | none => (0, c.state)
  | some (k, d) =>
    let r := execute d (h.inv ⟨k, hs⟩)
    (k + r.1, r.2)
termination_by (⟨c, h⟩ : { c : Config // Acc Next c })
decreasing_by exact ⟨k, hs⟩

/-- Execution returns exactly the result and cost specified by a trace. -/
theorem execute_eq {c : Config} {k : Nat} {t : State} (ht : Trace c k t)
    (h : Acc Next c) : execute c h = (k, t) := by
  induction ht with
  | done s => rw [execute]; rfl
  | next hs ht ih =>
    rw [execute]
    split
    · rename_i hnone
      rw [hs] at hnone
      contradiction
    · rename_i i d hsome
      obtain ⟨rfl, rfl⟩ := Option.some.inj (hsome.symm.trans hs)
      rw [ih]

/-- Termination is a proposition, not a runtime budget or an output oracle. -/
def Terminates (c : Code) (s : State) : Prop := ∃ k t, Exec c s k t

def run (c : Code) (s : State) (h : Terminates c s) : Nat × State :=
  execute ⟨[c], s⟩ (by
    obtain ⟨k, t, hx⟩ := h
    exact (hx.trace (.done t)).accessible)

/-- The total evaluator agrees with every valid execution derivation. -/
theorem run_eq {c : Code} {s t : State} {k : Nat} (hx : Exec c s k t)
    (h : Terminates c s) : run c s h = (k, t) := by
  simpa [run] using execute_eq (hx.trace (.done t)) _

theorem run_correct (c : Code) (s : State) (h : Terminates c s) :
    Exec c s (run c s h).1 (run c s h).2 := by
  obtain ⟨k, t, hx⟩ := h
  rw [run_eq hx]
  exact hx

/-- Check termination once, then call `.run initialState` without any proof or fuel. -/
structure TotalProgram where
  code : Code
  terminates : ∀ s, Terminates code s

def TotalProgram.run (p : TotalProgram) (s : State) : Nat × State :=
  Checked.run p.code s (p.terminates s)

theorem TotalProgram.run_correct (p : TotalProgram) (s : State) :
    Exec p.code s (p.run s).1 (p.run s).2 := Checked.run_correct _ _ _

end AlgoLib.Experimental.RAM.Checked
