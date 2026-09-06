/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Nondeterministic

/-!
# Fuel-free execution with procedure calls and an explicit choice schedule

The interpreter keeps a control stack, including return markers. Calls do not save
registers or copy arrays; activation data must be saved by explicit RAM instructions.
Each call and return costs one step. An external schedule resolves nondeterministic
choices for one run; it is not part of the algorithm and cannot establish a bound
for all choices. Invalid procedure identifiers are stuck, not successful outcomes.

`run` requires a terminating trace for its chosen schedule, erased at runtime.
For choice-free code, any big-step execution supplies this proof automatically,
including recursive calls. No input fuel, guessed timeout, or output oracle is used.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Nondeterministic
open Checked

inductive Frame where
  | code (body : Nondeterministic.Code)
  | returning

structure Config where
  todo : List Frame
  state : Checked.State
  choiceIndex : Nat := 0

/-- The schedule supplies the next natural word only at a choice instruction. -/
def step (procedures : List Nondeterministic.Code) (schedule : Nat → Nat)
    (c : Config) : Option (Nat × Config) :=
  match c.todo with
  | [] => none
  | .returning :: rest => some (1, { c with todo := rest })
  | .code (.deterministic (.block is)) :: rest =>
    some (is.length, { c with todo := rest, state := blockEval is c.state })
  | .code (.deterministic (.seq a b)) :: rest =>
    some (0, { c with todo := .code (.deterministic a) :: .code (.deterministic b) :: rest })
  | .code (.deterministic (.ite q a b)) :: rest =>
    some (1, { c with todo := .code (.deterministic (if q.eval c.state then a else b)) :: rest })
  | .code (.deterministic (.while q b)) :: rest =>
    let pending := Frame.code (.deterministic b) :: .code (.deterministic (.while q b)) :: rest
    some (1, { c with todo := if q.eval c.state then pending else rest })
  | .code (.choose r) :: rest =>
    some (1, ⟨rest, c.state.set r (schedule c.choiceIndex), c.choiceIndex + 1⟩)
  | .code (.seq a b) :: rest => some (0, { c with todo := .code a :: .code b :: rest })
  | .code (.branch q a b) :: rest =>
    some (1, { c with todo := .code (if q.eval c.state then a else b) :: rest })
  | .code (.loop q b) :: rest =>
    let pending := Frame.code b :: .code (.loop q b) :: rest
    some (1, { c with todo := if q.eval c.state then pending else rest })
  | .code (.call index) :: rest => match procedures[index]? with
    | none => none
    | some body => some (1, { c with todo := .code body :: .returning :: rest })

def Next (procedures : List Nondeterministic.Code) (schedule : Nat → Nat)
    (d c : Config) : Prop := ∃ k, step procedures schedule c = some (k, d)

/-- A successful finite trace must reach the empty control stack. -/
inductive Trace (procedures : List Nondeterministic.Code) (schedule : Nat → Nat) :
    Config → Nat → Checked.State → Prop where
  | done (s : Checked.State) (index : Nat) : Trace procedures schedule ⟨[], s, index⟩ 0 s
  | next {c d : Config} {i j : Nat} {t : Checked.State} :
      step procedures schedule c = some (i, d) → Trace procedures schedule d j t →
      Trace procedures schedule c (i + j) t

theorem Trace.accessible {procedures : List Nondeterministic.Code} {schedule : Nat → Nat}
    {c : Config} {k : Nat} {s : Checked.State} (h : Trace procedures schedule c k s) :
    Acc (Next procedures schedule) c := by
  induction h with
  | done s index =>
    constructor
    rintro d ⟨k, hk⟩
    simp [step] at hk
  | next hs ht ih =>
    constructor
    rintro d ⟨k, hk⟩
    rw [hs] at hk
    obtain ⟨rfl, rfl⟩ := Option.some.inj hk
    exact ih

/-- Termination proofs are erased; evaluation follows actual machine transitions. -/
def execute (procedures : List Nondeterministic.Code) (schedule : Nat → Nat)
    (c : Config) (h : Acc (Next procedures schedule) c) : Nat × Checked.State :=
  match hs : step procedures schedule c with
  | none => (0, c.state)
  | some (k, d) =>
    let r := execute procedures schedule d (h.inv ⟨k, hs⟩)
    (k + r.1, r.2)
termination_by (⟨c, h⟩ : { c : Config // Acc (Next procedures schedule) c })
decreasing_by exact ⟨k, hs⟩

theorem execute_eq {procedures : List Nondeterministic.Code} {schedule : Nat → Nat}
    {c : Config} {k : Nat} {t : Checked.State} (trace : Trace procedures schedule c k t)
    (h : Acc (Next procedures schedule) c) : execute procedures schedule c h = (k, t) := by
  induction trace with
  | done s index => rw [execute]; rfl
  | next hs trace ih =>
    rw [execute]
    split
    · rename_i no
      rw [hs] at no
      contradiction
    · rename_i i d yes
      obtain ⟨rfl, rfl⟩ := Option.some.inj (yes.symm.trans hs)
      rw [ih]

def Terminates (procedures : List Nondeterministic.Code) (schedule : Nat → Nat)
    (code : Nondeterministic.Code) (s : Checked.State) : Prop :=
  ∃ k t, Trace procedures schedule ⟨[.code code], s, 0⟩ k t

def run (procedures : List Nondeterministic.Code) (schedule : Nat → Nat)
    (code : Nondeterministic.Code) (s : Checked.State)
    (h : Terminates procedures schedule code s) : Nat × Checked.State :=
  execute procedures schedule ⟨[.code code], s, 0⟩ (by
    obtain ⟨_, _, trace⟩ := h
    exact trace.accessible)

theorem run_eq {procedures : List Nondeterministic.Code} {schedule : Nat → Nat}
    {code : Nondeterministic.Code} {s t : Checked.State} {k : Nat}
    (trace : Trace procedures schedule ⟨[.code code], s, 0⟩ k t)
    (h : Terminates procedures schedule code s) : run procedures schedule code s h = (k, t) :=
  execute_eq trace _

/-- Execution of a pending control stack; return markers are charged explicitly. -/
private inductive StackExec (procedures : List Nondeterministic.Code) :
    List Frame → Checked.State → Nat → Checked.State → Prop where
  | nil (s) : StackExec procedures [] s 0 s
  | code {a rest s u t i j} : ExecIn procedures a s i u → StackExec procedures rest u j t →
      StackExec procedures (.code a :: rest) s (i + j) t
  | returning {rest s t k} : StackExec procedures rest s k t →
      StackExec procedures (.returning :: rest) s (1 + k) t

private theorem step_back {procedures : List Nondeterministic.Code} {schedule : Nat → Nat}
    {c d : Config} {i j : Nat} {t : Checked.State}
    (hs : step procedures schedule c = some (i, d))
    (rest : StackExec procedures d.todo d.state j t) :
    StackExec procedures c.todo c.state (i+j) t := by
  rcases c with ⟨todo, s, index⟩
  cases todo with
  | nil => simp [step] at hs
  | cons frame tail =>
    cases frame with
    | returning =>
      cases Option.some.inj hs
      exact .returning rest
    | code a =>
      cases a with
      | deterministic a =>
        cases a with
        | block is =>
          cases Option.some.inj hs
          exact .code (.deterministic (.block is s)) rest
        | seq a b =>
          cases Option.some.inj hs
          cases rest with
          | code ha rest =>
            cases rest with
            | code hb rest =>
              cases ha with | deterministic ha =>
                cases hb with | deterministic hb =>
                  simpa [Nat.add_assoc] using StackExec.code (.deterministic (.seq ha hb)) rest
        | ite q a b =>
          cases hq : q.eval s
          <;> simp only [step, hq, Bool.false_eq_true, ↓reduceIte] at hs
          <;> cases Option.some.inj hs
          <;> cases rest with
          | code h rest =>
            cases h with | deterministic h =>
              first
              | simpa [Nat.add_assoc] using StackExec.code (.deterministic (.ifFalse hq h)) rest
              | simpa [Nat.add_assoc] using StackExec.code (.deterministic (.ifTrue hq h)) rest
        | «while» q b =>
          cases hq : q.eval s
          · simp only [step, hq, Bool.false_eq_true, ↓reduceIte] at hs
            cases Option.some.inj hs
            exact .code (.deterministic (.whileFalse hq)) rest
          · simp only [step, hq, ↓reduceIte] at hs
            cases Option.some.inj hs
            cases rest with
            | code hb rest =>
              cases rest with
              | code hl rest =>
                cases hb with | deterministic hb =>
                  cases hl with | deterministic hl =>
                    simpa [Nat.add_assoc] using
                      StackExec.code (.deterministic (.whileTrue hq hb hl)) rest
      | choose r =>
        cases Option.some.inj hs
        exact .code (.choose s r (schedule index)) rest
      | seq a b =>
        cases Option.some.inj hs
        cases rest with
        | code ha rest =>
          cases rest with
          | code hb rest => simpa [Nat.add_assoc] using StackExec.code (.seq ha hb) rest
      | branch q a b =>
        cases hq : q.eval s
        <;> simp only [step, hq, Bool.false_eq_true, ↓reduceIte] at hs
        <;> cases Option.some.inj hs
        <;> cases rest with
        | code h rest =>
          first
          | simpa [Nat.add_assoc] using StackExec.code (.ifFalse hq h) rest
          | simpa [Nat.add_assoc] using StackExec.code (.ifTrue hq h) rest
      | loop q b =>
        cases hq : q.eval s
        · simp only [step, hq, Bool.false_eq_true, ↓reduceIte] at hs
          cases Option.some.inj hs
          exact .code (.whileFalse hq) rest
        · simp only [step, hq, ↓reduceIte] at hs
          cases Option.some.inj hs
          cases rest with
          | code hb rest =>
            cases rest with
            | code hl rest => simpa [Nat.add_assoc] using StackExec.code (.whileTrue hq hb hl) rest
      | call id =>
        cases lookup : procedures[id]? with
        | none => simp [step, lookup] at hs
        | some body =>
          simp only [step, lookup] at hs
          cases Option.some.inj hs
          cases rest with
          | code hb rest =>
            cases rest with
            | returning rest =>
              simpa [Nat.add_assoc] using StackExec.code (.call lookup hb) rest

/-- Every successful interpreter trace reconstructs a declarative RAM execution. -/
theorem Trace.exec {procedures : List Nondeterministic.Code} {schedule : Nat → Nat}
    {code : Nondeterministic.Code} {s t : Checked.State} {k index : Nat}
    (trace : Trace procedures schedule ⟨[.code code], s, index⟩ k t) :
    ExecIn procedures code s k t := by
  have aux : ∀ {c : Config} {k : Nat} {t : Checked.State}, Trace procedures schedule c k t →
      StackExec procedures c.todo c.state k t := by
    intro c k t h
    induction h with
    | done s index => exact .nil s
    | next hs trace ih => exact step_back hs ih
  have h := aux trace
  cases h with
  | code h rest =>
    cases rest
    simpa using h

/-- All public executions satisfy the same RAM relation used in translation and cost theorems. -/
theorem run_correct (procedures : List Nondeterministic.Code) (schedule : Nat → Nat)
    (code : Nondeterministic.Code) (s : Checked.State)
    (h : Terminates procedures schedule code s) :
    ExecIn procedures code s (run procedures schedule code s h).1
      (run procedures schedule code s h).2 := by
  obtain ⟨k, t, trace⟩ := h
  rw [run_eq trace]
  exact trace.exec

/-- Syntactic absence of choice, independent of whether calls terminate. -/
def Code.ChoiceFree : Nondeterministic.Code → Prop
  | .choose _ => False
  | .deterministic _ | .call _ => True
  | .seq a b | .branch _ a b => a.ChoiceFree ∧ b.ChoiceFree
  | .loop _ b => b.ChoiceFree

private theorem deterministic_trace {procedures : List Nondeterministic.Code}
    {schedule : Nat → Nat} {a : Checked.Code} {s t : Checked.State} {i : Nat}
    (h : Checked.Exec a s i t) {rest : List Frame} {u : Checked.State} {j index : Nat}
    (ht : Trace procedures schedule ⟨rest, t, index⟩ j u) :
    Trace procedures schedule ⟨.code (.deterministic a) :: rest, s, index⟩ (i + j) u := by
  induction h generalizing rest u j with
  | block is s => exact .next rfl ht
  | seq ha hb iha ihb =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.code (.deterministic (.seq _ _)) :: rest, _, index⟩) rfl (iha (ihb ht))
  | ifTrue hq ha ih =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.code (.deterministic (.ite _ _ _)) :: rest, _, index⟩)
      (by simp [step, hq]) (ih ht)
  | ifFalse hq ha ih =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.code (.deterministic (.ite _ _ _)) :: rest, _, index⟩)
      (by simp [step, hq]) (ih ht)
  | whileFalse hq => exact .next (by simp [step, hq]) ht
  | whileTrue hq ha hb iha ihb =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.code (.deterministic (.while _ _)) :: rest, _, index⟩)
      (by simp [step, hq]) (iha (ihb ht))

/-- Recursive choice-free execution supplies a trace for every external schedule. -/
theorem ExecIn.trace {procedures : List Nondeterministic.Code} {schedule : Nat → Nat}
    (closed : ∀ code ∈ procedures, code.ChoiceFree)
    {a : Nondeterministic.Code} {s t : Checked.State} {i : Nat} (h : ExecIn procedures a s i t)
    (noChoice : a.ChoiceFree) {rest : List Frame} {u : Checked.State} {j index : Nat}
    (ht : Trace procedures schedule ⟨rest, t, index⟩ j u) :
    Trace procedures schedule ⟨.code a :: rest, s, index⟩ (i + j) u := by
  induction h generalizing rest u j with
  | deterministic h => exact deterministic_trace h ht
  | choose => exact noChoice.elim
  | seq ha hb iha ihb =>
    simpa [Nat.add_assoc] using Trace.next
      (c := ⟨.code (.seq _ _) :: rest, _, index⟩) rfl (iha noChoice.1 (ihb noChoice.2 ht))
  | ifTrue hq ha ih =>
    simpa [Nat.add_assoc] using Trace.next (c := ⟨.code (.branch _ _ _) :: rest, _, index⟩)
      (by simp [step, hq]) (ih noChoice.1 ht)
  | ifFalse hq ha ih =>
    simpa [Nat.add_assoc] using Trace.next (c := ⟨.code (.branch _ _ _) :: rest, _, index⟩)
      (by simp [step, hq]) (ih noChoice.2 ht)
  | whileFalse hq => exact .next (by simp [step, hq]) ht
  | whileTrue hq ha hb iha ihb =>
    simpa [Nat.add_assoc] using Trace.next (c := ⟨.code (.loop _ _) :: rest, _, index⟩)
      (by simp [step, hq]) (iha noChoice (ihb noChoice ht))
  | call lookup h ih =>
    have bodyFree := closed _ (List.mem_of_getElem? lookup)
    simpa [Nat.add_assoc] using Trace.next (c := ⟨.code (.call _) :: rest, _, index⟩)
      (by simp [step, lookup])
      (ih bodyFree (.next (c := ⟨.returning :: rest, _, index⟩) rfl ht))

end AlgoLib.Experimental.RAM.Prototype.Nondeterministic
