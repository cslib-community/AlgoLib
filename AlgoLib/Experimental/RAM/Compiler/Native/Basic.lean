/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Machine.Integer.Runner
import Mathlib.Tactic

/-!
# Native integer implementation language

This implementation language stores signed integers directly, including in heap cells.
Its independent expression semantics distinguish natural words, addresses, and integers.
Natural reads and subtraction normalize at zero; signed reads and subtraction do not.
Typing guarantees nonnegative address expressions. Allocation and bounds belong to the
ownership contracts, rather than to this compiler layer.

Costs below count the instructions emitted by the native compiler, not logical credits.
The public Nat/Int expression language and its logical allowances remain separate.
-/
namespace AlgoLib.Experimental.RAM.Native
open Integer (State Code Exec)
open Checked (Reg)

inductive Ty where
  | word | ptr | integer
  deriving DecidableEq, Repr

def Ty.tag : Ty → Nat | .word => 0 | .ptr => 1 | .integer => 2

def Ty.normalize : Ty → Int → Int
  | .integer, x => x
  | _, x => max x 0

def Ty.readCost : Ty → Nat | .integer => 1 | _ => 2

structure Var (ty : Ty) where
  name : String
  deriving DecidableEq, Repr

def Var.reg {ty : Ty} (v : Var ty) : Reg := .user ty.tag v.name

/-- A single raw integer per user variable or heap cell; no paired signed encoding. -/
structure Store where
  vars : Ty → String → Int
  heap : Nat → Int

def Store.set {ty : Ty} (s : Store) (v : Var ty) (n : Int) : Store where
  vars t x := if t = ty ∧ x = v.name then n else s.vars t x
  heap := s.heap

def Store.write (s : Store) (a : Nat) (v : Int) : Store :=
  { s with heap := Function.update s.heap a v }

inductive Op : Ty → Ty → Ty → Type where
  | add : Op .word .word .word
  | sub : Op .word .word .word
  | mul : Op .word .word .word
  | offset : Op .ptr .word .ptr
  | intAdd : Op .integer .integer .integer
  | intSub : Op .integer .integer .integer
  | intMul : Op .integer .integer .integer

def Op.machine {a b c : Ty} : Op a b c → Integer.BinOp
  | .add | .offset | .intAdd => .add
  | .sub | .intSub => .sub
  | .mul | .intMul => .mul

def Op.eval {a b c : Ty} : Op a b c → Int → Int → Int
  | .sub, x, y => max (x - y) 0
  | op, x, y => op.machine.eval x y

def Op.cost {a b c : Ty} : Op a b c → Nat | .sub => 2 | _ => 1

inductive Expr : Ty → Type where
  | lit {ty : Ty} (n : Int) : Expr ty
  | var {ty : Ty} (v : Var ty) : Expr ty
  | bin {a b c : Ty} (op : Op a b c) (x : Expr a) (y : Expr b) : Expr c
  | load {ty : Ty} (a : Expr .ptr) : Expr ty
  | ofNat (a : Expr .word) : Expr .integer
  | toNat (a : Expr .integer) : Expr .word
  | pointer (a : Expr .word) : Expr .ptr

def Expr.eval {ty : Ty} (s : Store) : Expr ty → Int
  | .lit n => ty.normalize n
  | .var v => ty.normalize (s.vars ty v.name)
  | .bin op x y => op.eval (x.eval s) (y.eval s)
  | .load a => ty.normalize (s.heap (a.eval s).toNat)
  | .ofNat a | .pointer a => a.eval s
  | .toNat a => max (a.eval s) 0

/-- Expression syntax guarantees that a natural word or pointer is nonnegative. -/
theorem Expr.nonnegative {ty : Ty} (e : Expr ty) (s : Store) (h : ty ≠ .integer) :
    0 ≤ e.eval s := by
  induction e with
  | lit n => cases ty <;> simp_all [Expr.eval, Ty.normalize]
  | var v => cases ty <;> simp_all [Expr.eval, Ty.normalize]
  | bin op a b iha ihb =>
    cases op with
    | add | offset => exact add_nonneg (iha (by decide)) (ihb (by decide))
    | sub => exact le_max_right _ _
    | mul => exact mul_nonneg (iha (by decide)) (ihb (by decide))
    | intAdd | intSub | intMul => exact False.elim (h rfl)
  | load a _ => cases ty <;> simp_all [Expr.eval, Ty.normalize]
  | ofNat a _ => exact False.elim (h rfl)
  | toNat a _ => simp [Expr.eval]
  | pointer a ih => exact ih (by decide)

def Expr.cost {ty : Ty} : Expr ty → Nat
  | .lit _ => 1
  | .var _ => ty.readCost
  | .bin op x y => x.cost + y.cost + op.cost
  | .load a => a.cost + ty.readCost
  | .ofNat a | .pointer a => a.cost
  | .toNat a => a.cost + 1

inductive Comparison where
  | lt | le | eq
  deriving DecidableEq, Repr

def Comparison.eval : Comparison → Int → Int → Bool
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
  | write {ty : Ty} (a : Expr .ptr) (v : Expr ty)
  | seq (a b : Cmd)
  | branch (q : Condition) (yes no : Cmd)
  | loop (q : Condition) (body : Cmd)
  | localVar {ty : Ty} (v : Var ty) (value : Expr ty) (body : Cmd)

/-- Independent terminating source semantics, counting emitted machine instructions. -/
inductive Eval : Cmd → Store → Nat → Store → Prop where
  | skip (s : Store) : Eval .skip s 0 s
  | assign {ty : Ty} (v : Var ty) (e : Expr ty) (s : Store) :
      Eval (.assign v e) s (e.cost + 1) (s.set v (e.eval s))
  | write {ty : Ty} (a : Expr .ptr) (v : Expr ty) (s : Store) :
      Eval (.write a v) s (a.cost + v.cost + 1) (s.write (a.eval s).toNat (v.eval s))
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

end AlgoLib.Experimental.RAM.Native
