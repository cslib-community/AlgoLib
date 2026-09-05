/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Runner

/-!
# An annotated imperative language and verified compiler

This deliberately small source language has assignments, memory indexing,
flat arithmetic expressions, conditionals, and while loops. Loop invariants
may refer to a ghost snapshot of the loop's entry state; natural-valued
`decreases` functions establish termination. Annotations may contain ordinary
Lean mathematics but are erased. Runtime expressions remain restricted syntax.

`VC` generates total-correctness obligations. `VC.sound` proves their soundness
against an independent source execution relation. `Eval.compile` then proves
that compilation preserves the entire state and exact RAM operation count.
-/

namespace AlgoLib.Experimental.RAM.Checked.Source

inductive Expr where
  | atom (a : Operand)
  | load (a : Operand)
  | bin (op : BinOp) (x y : Operand)

def Expr.eval (s : State) : Expr → Nat
  | .atom a => a.eval s
  | .load a => s.memory (a.eval s)
  | .bin op x y => op.eval (x.eval s) (y.eval s)

inductive Simple where
  | assign (r : Reg) (e : Expr)
  | store (a v : Operand)

def Simple.eval (i : Simple) (s : State) : State :=
  match i with
  | .assign r e => s.set r (e.eval s)
  | .store a v => { s with memory := Function.update s.memory (a.eval s) (v.eval s) }

def Simple.compile : Simple → Instr
  | .assign r (.atom a) => .mov r a
  | .assign r (.load a) => .load r a
  | .assign r (.bin op x y) => .bin op r x y
  | .store a v => .store a v

@[simp] theorem Simple.compile_eval (i : Simple) (s : State) :
    i.compile.eval s = i.eval s := by
  cases i with
  | assign r e => cases e <;> rfl
  | store => rfl

def block (is : List Simple) (s : State) : State := is.foldl (fun t i => i.eval t) s

theorem block_compile (is : List Simple) (s : State) :
    blockEval (is.map Simple.compile) s = block is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => simpa [blockEval, block] using ih (i.eval s)

/-- The first invariant argument is the ghost state at this loop's entry. -/
inductive Stmt where
  | block (is : List Simple)
  | seq (a b : Stmt)
  | ite (q : Test) (yes no : Stmt)
  | loop (q : Test) (invariant : State → State → Prop) (rank : State → Nat) (body : Stmt)

def Stmt.compile : Stmt → Code
  | .block is => .block (is.map Simple.compile)
  | .seq a b => .seq a.compile b.compile
  | .ite q a b => .ite q a.compile b.compile
  | .loop q _ _ b => .while q b.compile

/-- Independent source semantics. Annotations never influence execution. -/
inductive Eval : Stmt → State → Nat → State → Prop where
  | block (is : List Simple) (s : State) : Eval (.block is) s is.length (Source.block is s)
  | seq {a b : Stmt} {s u t : State} {i j : Nat} :
      Eval a s i u → Eval b u j t → Eval (.seq a b) s (i + j) t
  | ifTrue {q : Test} {a b : Stmt} {s t : State} {i : Nat} :
      q.eval s = true → Eval a s i t → Eval (.ite q a b) s (1 + i) t
  | ifFalse {q : Test} {a b : Stmt} {s t : State} {i : Nat} :
      q.eval s = false → Eval b s i t → Eval (.ite q a b) s (1 + i) t
  | whileFalse {q : Test} {I : State → State → Prop} {V : State → Nat}
      {b : Stmt} {s : State} :
      q.eval s = false → Eval (.loop q I V b) s 1 s
  | whileTrue {q : Test} {I : State → State → Prop} {V : State → Nat}
      {b : Stmt} {s u t : State} {i j : Nat} :
      q.eval s = true → Eval b s i u → Eval (.loop q I V b) u j t →
      Eval (.loop q I V b) s (1 + i + j) t

/-- Compilation preserves observable state and the exact number of operations. -/
theorem Eval.compile {p : Stmt} {s t : State} {k : Nat} (h : Eval p s k t) :
    Exec p.compile s k t := by
  induction h with
  | block is s => simpa [Stmt.compile, block_compile] using Exec.block (is.map Simple.compile) s
  | seq ha hb iha ihb => exact .seq iha ihb
  | ifTrue hq ha ih => exact .ifTrue hq ih
  | ifFalse hq ha ih => exact .ifFalse hq ih
  | whileFalse hq => exact .whileFalse hq
  | whileTrue hq ha hb iha ihb => exact .whileTrue hq iha ihb

/-- Generated verification conditions for a postcondition. The three loop
obligations are initialization, preservation with strict decrease, and exit.
The loop-entry snapshot permits frame invariants without runtime ghost code. -/
def VC : Stmt → (State → Prop) → State → Prop
  | .block is, Q, s => Q (block is s)
  | .seq a b, Q, s => VC a (VC b Q) s
  | .ite q a b, Q, s => if q.eval s then VC a Q s else VC b Q s
  | .loop q I V b, Q, s =>
    I s s ∧
      (∀ t, I s t → q.eval t = true → VC b (fun u => I s u ∧ V u < V t) t) ∧
      (∀ t, I s t → q.eval t = false → Q t)

/-- Verification conditions imply termination and the requested postcondition. -/
theorem VC.sound {p : Stmt} {Q : State → Prop} {s : State} (h : VC p Q s) :
    ∃ k t, Eval p s k t ∧ Q t := by
  induction p generalizing Q s with
  | block is => exact ⟨is.length, block is s, .block is s, h⟩
  | seq a b iha ihb =>
    obtain ⟨i, u, ha, hu⟩ := iha h
    obtain ⟨j, t, hb, ht⟩ := ihb hu
    exact ⟨i + j, t, .seq ha hb, ht⟩
  | ite q a b iha ihb =>
    cases hq : q.eval s with
    | false =>
      obtain ⟨k, t, hx, ht⟩ := ihb (by simpa [VC, hq] using h)
      exact ⟨1 + k, t, .ifFalse hq hx, ht⟩
    | true =>
      obtain ⟨k, t, hx, ht⟩ := iha (by simpa [VC, hq] using h)
      exact ⟨1 + k, t, .ifTrue hq hx, ht⟩
  | loop q I V b ihb =>
    obtain ⟨hinit, hbody, hexit⟩ := h
    have loop : ∀ n t, V t = n → I s t → ∃ k u, Eval (.loop q I V b) t k u ∧ Q u := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro t hn ht
        cases hq : q.eval t with
        | false => exact ⟨1, t, .whileFalse hq, hexit t ht hq⟩
        | true =>
          obtain ⟨i, u, hu, hI, hV⟩ := ihb (hbody t ht hq)
          obtain ⟨j, v, hv, hQ⟩ := ih (V u) (by omega) u rfl hI
          exact ⟨1 + i + j, v, .whileTrue hq hu hv, hQ⟩
    exact loop (V s) s rfl hinit

/-- Generated termination conditions suffice to construct a fuel-free executable. -/
def verified (p : Stmt) (h : ∀ s, VC p (fun _ => True) s) : TotalProgram where
  code := p.compile
  terminates s := by
    obtain ⟨k, t, hx, _⟩ := VC.sound (h s)
    exact ⟨k, t, hx.compile⟩

/-- Certified execution also transports arbitrary source postconditions. -/
theorem verified_post (p : Stmt) (h : ∀ s, VC p (fun _ => True) s)
    (s : State) (Q : State → Prop) (hq : VC p Q s) : Q ((verified p h).run s).2 := by
  obtain ⟨k, t, hx, ht⟩ := VC.sound hq
  change Q (Checked.run p.compile s _).2
  rw [run_eq hx.compile]
  exact ht


/-- A procedure contract. Verification conditions establish total correctness
under `requires`; `ensures` may refer to the original input as a ghost snapshot. -/
structure Method where
  body : Stmt
  requires : State → Prop
  ensures : State → State → Prop
  verification : ∀ s, requires s → VC body (ensures s) s

/-- A precondition proof is synthesized when possible; it is not a runtime argument. -/
def Method.run (m : Method) (s : State) (h : m.requires s := by trivial) : Nat × State :=
  Checked.run m.body.compile s (by
    obtain ⟨k, t, hx, _⟩ := VC.sound (m.verification s h)
    exact ⟨k, t, hx.compile⟩)

theorem Method.correct (m : Method) (s : State) (h : m.requires s) :
    Exec m.body.compile s (m.run s h).1 (m.run s h).2 ∧ m.ensures s (m.run s h).2 := by
  obtain ⟨k, t, hx, ht⟩ := VC.sound (m.verification s h)
  constructor
  · exact Checked.run_correct _ _ _
  · change m.ensures s (Checked.run m.body.compile s _).2
    rw [run_eq hx.compile]
    exact ht

end AlgoLib.Experimental.RAM.Checked.Source
