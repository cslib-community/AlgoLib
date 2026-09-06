/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Syntax

/-!
# Pure mutable-array language and logical credits

These are the scalar expressions, array actions, guards, and mathematical state
used by the frontend. No RAM type, compiler, representation, or instruction cost
is imported. Contiguous and indirect array implementations realize these same
contracts without changing programs or their invariant/credit proofs.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Mutable

/-- Logical comparisons, independent of the backend condition language. -/
inductive Comparison where
  | lt | le | eq
  deriving Repr

def Comparison.eval : Comparison → Nat → Nat → Bool
  | .lt => fun x y => decide (x < y)
  | .le => fun x y => decide (x ≤ y)
  | .eq => fun x y => decide (x = y)

structure State where
  array : Array Nat
  locals : String → Nat

def State.set (s : State) (name : String) (value : Nat) : State :=
  { s with locals := Function.update s.locals name value }

/-- Scalar expressions; array reads are materialized automatically by the frontend. -/
inductive Value where
  | literal (n : Nat)
  | local (name : String)
  | size
  | add (a b : Value)
  | sub (a b : Value)
  | mul (a b : Value)
  deriving Repr

def Value.eval (s : State) : Value → Nat
  | .literal n => n
  | .local x => s.locals x
  | .size => s.array.size
  | .add a b => a.eval s + b.eval s
  | .sub a b => a.eval s - b.eval s
  | .mul a b => a.eval s * b.eval s

/-- Logical expression charge, independent of any target instruction language. -/
def Value.credits : Value → Nat
  | .literal _ | .local _ | .size => 1
  | .add x y | .sub x y | .mul x y => x.credits + y.credits + 1

/-- Scalar assignment with a purely logical credit charge. -/
def assign (x : String) (e : Value) : Action State where
  requires _ := True
  effect s := s.set x (e.eval s)
  work _ := e.credits + 1

/-- Array access generates a bounds obligation, not a memory-address proof. -/
def read (x : String) (i : Value) : Action State where
  requires s := i.eval s < s.array.size
  effect s := s.set x s.array[i.eval s]!
  work _ := i.credits + 4

/-- Array update frames every scalar and the array length automatically. -/
def write (i v : Value) : Action State where
  requires s := i.eval s < s.array.size
  effect s := { s with array := s.array.set! (i.eval s) (v.eval s) }
  work _ := i.credits + v.credits + 3

/-- Guards compare materialized scalar operands, so their cost is uniformly bounded. -/
def compare (op : Comparison) (x y : String) : Guard State where
  test s := op.eval (s.locals x) (s.locals y)

def initial (input : Array Nat) : State := ⟨input, fun _ => 0⟩

attribute [paper_simps] assign read write Value.eval State.set

end AlgoLib.Experimental.RAM.Authoring.Mutable
