/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts

/-!
# Expressions over separately owned values

A path selects a typed component of the method state. Expressions are syntax, not
Lean callbacks: every arithmetic operation and indexed read has a public charge.
Assignments and indexed writes are ordinary operations of the same language as
procedure calls. Bounds become verification conditions. The backend implements
paths using ownership; client proofs see only ordinary numbers and arrays.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

inductive Path : Type → Type → Type 1 where
  | here : Path A A
  | left : Path A C → Path (A × B) C
  | right : Path B C → Path (A × B) C

def Path.get : Path A B → A → B
  | .here, a => a
  | .left p, a => p.get a.1
  | .right p, a => p.get a.2

def Path.set : Path A B → A → B → A
  | .here, _, b => b
  | .left p, a, b => (p.set a.1 b, a.2)
  | .right p, a, b => (a.1, p.set a.2 b)

inductive Arithmetic where
  | add | sub | mul
  deriving DecidableEq

def Arithmetic.eval : Arithmetic → Nat → Nat → Nat
  | .add => Nat.add | .sub => Nat.sub | .mul => Nat.mul

inductive Value (S : Type) where
  | literal : Nat → Value S
  | scalar : Path S Nat → Value S
  | size : Path S (Array Nat) → Value S
  | index : Path S (Array Nat) → Value S → Value S
  | binary : Arithmetic → Value S → Value S → Value S

def Value.eval : Value S → S → Nat
  | .literal n, _ => n
  | .scalar p, s => p.get s
  | .size p, s => (p.get s).size
  | .index p i, s => (p.get s)[i.eval s]!
  | .binary op a b, s => op.eval (a.eval s) (b.eval s)

def Value.Safe : Value S → S → Prop
  | .literal _, _ | .scalar _, _ | .size _, _ => True
  | .index p i, s => i.Safe s ∧ i.eval s < (p.get s).size
  | .binary _ a b, s => a.Safe s ∧ b.Safe s

def Value.credits : Value S → Nat
  | .literal _ | .scalar _ | .size _ => 1
  | .index _ i => i.credits + 3
  | .binary _ a b => a.credits + b.credits + 1

/-- Updating one scalar leaves every other component mathematically unchanged. -/
def assign (p : Path S Nat) (e : Value S) : Operation S S where
  requires := e.Safe
  effect s := p.set s (e.eval s)
  charge _ := e.credits + 1

/-- Indexed updates require an in-bounds index; unchecked Lean reads cannot bypass this VC. -/
def write (p : Path S (Array Nat)) (i e : Value S) : Operation S S where
  requires s := i.Safe s ∧ e.Safe s ∧ i.eval s < (p.get s).size
  effect s := p.set s ((p.get s).set! (i.eval s) (e.eval s))
  charge _ := i.credits + e.credits + 3

inductive Relation where
  | lt | le | eq

def Relation.eval : Relation → Nat → Nat → Bool
  | .lt => fun a b => decide (a < b)
  | .le => fun a b => decide (a ≤ b)
  | .eq => fun a b => decide (a = b)

/-- Guards compare already materialized scalars, so each guard has constant cost. -/
def compare (op : Relation) (a b : Path S Nat) (s : S) : Bool :=
  op.eval (a.get s) (b.get s)

/-- Compiler-reserved locals have a finite structural initialization allowance. -/
class Locals (L : Type) where
  initial : L
  credits : Nat

instance : Locals Nat := ⟨0, 2⟩
instance [a : Locals A] [b : Locals B] : Locals (A × B) :=
  ⟨(a.initial, b.initial), a.credits + b.credits⟩

/-- Enter/leave hide scratch from the mathematical input and output interface. -/
def enterLocals (S L : Type) [locals : Locals L] : Operation S (S × L) where
  requires _ := True
  effect s := (s, locals.initial)
  charge _ := locals.credits

def leaveLocals (S L : Type) : Operation (S × L) S where
  requires _ := True
  effect s := s.1
  charge _ := 0

/-- Structural ownership regrouping has no runtime copying or logical charge. -/
def associate (A B C : Type) : Operation ((A × B) × C) (A × B × C) where
  requires _ := True
  effect s := (s.1.1, s.1.2, s.2)
  charge _ := 0

def unassociate (A B C : Type) : Operation (A × B × C) ((A × B) × C) where
  requires _ := True
  effect s := ((s.1, s.2.1), s.2.2)
  charge _ := 0

end AlgoLib.Experimental.RAM.Prototype.Composition
