/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Core.Runner

/-!
# A compositional, typed source language

Source stores, expression evaluation, and command execution are independent of
RAM code. Words and addresses are distinct types. Expressions are syntax trees,
never user-supplied evaluators. Named variables have no fixed register limit.
Arrays use explicit addresses; bounds and ownership belong to library contracts.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

inductive Ty where
  | word | ptr
  deriving DecidableEq, Repr

def Ty.tag : Ty → Nat | .word => 0 | .ptr => 1

structure Var (ty : Ty) where
  name : String
  deriving DecidableEq, Repr

def Var.reg {ty : Ty} (v : Var ty) : Reg := .user ty.tag v.name

/-- Source state has no compiler temporaries and no clock. -/
structure Store where
  vars : (ty : Ty) → String → Nat
  heap : Nat → Nat

def Store.set {ty : Ty} (s : Store) (v : Var ty) (n : Nat) : Store where
  vars t x := if t = ty ∧ x = v.name then n else s.vars t x
  heap := s.heap

def Store.write (s : Store) (a v : Nat) : Store :=
  { s with heap := Function.update s.heap a v }

inductive Op : Ty → Ty → Ty → Type where
  | add : Op .word .word .word
  | sub : Op .word .word .word
  | mul : Op .word .word .word
  | offset : Op .ptr .word .ptr

def Op.machine {a b c : Ty} : Op a b c → BinOp
  | .add | .offset => .add
  | .sub => .sub
  | .mul => .mul

def Op.eval {a b c : Ty} (op : Op a b c) : Nat → Nat → Nat := op.machine.eval

inductive Expr : Ty → Type where
  | lit {ty : Ty} (n : Nat) : Expr ty
  | var {ty : Ty} (v : Var ty) : Expr ty
  | bin {a b c : Ty} (op : Op a b c) (x : Expr a) (y : Expr b) : Expr c
  | load (a : Expr .ptr) : Expr .word

def Expr.eval {ty : Ty} (s : Store) : Expr ty → Nat
  | .lit n => n
  | @Expr.var ty v => s.vars ty v.name
  | .bin op x y => op.eval (x.eval s) (y.eval s)
  | .load a => s.heap (a.eval s)

/-- Exact cost of evaluating an expression to a temporary register. -/
def Expr.cost {ty : Ty} : Expr ty → Nat
  | .lit _ | .var _ => 1
  | .bin _ x y => x.cost + y.cost + 1
  | .load a => a.cost + 1

inductive Comparison where
  | lt | le | eq
  deriving DecidableEq, Repr

def Comparison.eval : Comparison → Nat → Nat → Bool
  | .lt => fun x y => decide (x < y)
  | .le => fun x y => decide (x ≤ y)
  | .eq => fun x y => decide (x = y)

structure Condition where
  ty : Ty
  comparison : Comparison
  left : Expr ty
  right : Expr ty

def Condition.eval (q : Condition) (s : Store) : Bool :=
  q.comparison.eval (q.left.eval s) (q.right.eval s)

def Condition.cost (q : Condition) : Nat := q.left.cost + q.right.cost + 1

inductive Cmd where
  | skip
  | assign {ty : Ty} (v : Var ty) (e : Expr ty)
  | write (a : Expr .ptr) (v : Expr .word)
  | seq (a b : Cmd)
  | branch (q : Condition) (yes no : Cmd)
  | loop (q : Condition) (body : Cmd)
  | localVar {ty : Ty} (v : Var ty) (value : Expr ty) (body : Cmd)

/-- Independent big-step semantics. Costs charge expression work and every guard. -/
inductive Eval : Cmd → Store → Nat → Store → Prop where
  | skip (s : Store) : Eval .skip s 0 s
  | assign {ty : Ty} (v : Var ty) (e : Expr ty) (s : Store) :
      Eval (.assign v e) s (e.cost + 1) (s.set v (e.eval s))
  | write (a : Expr .ptr) (v : Expr .word) (s : Store) :
      Eval (.write a v) s (a.cost + v.cost + 1) (s.write (a.eval s) (v.eval s))
  | seq {a b : Cmd} {s u t : Store} {i j : Nat} :
      Eval a s i u → Eval b u j t → Eval (.seq a b) s (i + j) t
  | ifTrue {q : Condition} {a b : Cmd} {s t : Store} {k : Nat} :
      q.eval s = true → Eval a s k t → Eval (.branch q a b) s (q.cost + k) t
  | ifFalse {q : Condition} {a b : Cmd} {s t : Store} {k : Nat} :
      q.eval s = false → Eval b s k t → Eval (.branch q a b) s (q.cost + k) t
  | whileFalse {q : Condition} {b : Cmd} {s : Store} :
      q.eval s = false → Eval (.loop q b) s q.cost s
  | whileTrue {q : Condition} {b : Cmd} {s u t : Store} {i j : Nat} :
      q.eval s = true → Eval b s i u → Eval (.loop q b) u j t →
      Eval (.loop q b) s (q.cost + i + j) t
  | localVar {ty : Ty} {v : Var ty} {e : Expr ty} {body : Cmd}
      {s t : Store} {k : Nat} : Eval body (s.set v (e.eval s)) k t →
      Eval (.localVar v e body) s (e.cost + 3 + k) (t.set v (s.vars ty v.name))

/-- A nonrecursive procedure has a scoped, call-by-value input. Workspace and
output locations are explicit; heap effects are described by its contract. -/
structure Procedure (input output : Ty) where
  parameter : Var input
  body : Var output → Cmd

def Procedure.call {input output : Ty} (p : Procedure input output)
    (argument : Expr input) (result : Var output) : Cmd :=
  .localVar p.parameter argument (p.body result)

end AlgoLib.Experimental.RAM.Checked.Language
