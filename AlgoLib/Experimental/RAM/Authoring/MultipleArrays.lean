/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Mutable

/-!
# Pure language for multiple mutable arrays

Finite array handles, mathematical updates, and local credit charges are independent
of layouts or RAM costs. `write_other` is the logical frame rule used by the frontend.
The physical lane implementation lives in Prototype/MultipleArrays.lean.
-/
namespace AlgoLib.Experimental.RAM.Authoring.MultipleArrays
variable {count : Nat}

structure State (count : Nat) where
  arrays : Fin count → Array Nat
  locals : String → Nat

def State.set (s : State count) (x : String) (v : Nat) : State count :=
  { s with locals := Function.update s.locals x v }

def State.write (s : State count) (a : Fin count) (i v : Nat) : State count :=
  { s with arrays := Function.update s.arrays a ((s.arrays a).set! i v) }

/-- The logical frame equation is available independently of memory representation. -/
@[simp] theorem write_other (s : State count) (a b : Fin count) (i v : Nat) (h : b ≠ a) :
    (s.write a i v).arrays b = s.arrays b := by simp [State.write, h]

inductive Value (count : Nat) where
  | literal (n : Nat)
  | local (name : String)
  | size (array : Fin count)
  | add (x y : Value count)
  | sub (x y : Value count)
  | mul (x y : Value count)

def Value.eval (s : State count) : Value count → Nat
  | .literal n => n
  | .local x => s.locals x
  | .size a => (s.arrays a).size
  | .add x y => x.eval s + y.eval s
  | .sub x y => x.eval s - y.eval s
  | .mul x y => x.eval s * y.eval s

/-- Logical expression charge, independent of any target instruction language. -/
def Value.credits : Value count → Nat
  | .literal _ | .local _ | .size _ => 1
  | .add x y | .sub x y | .mul x y => x.credits + y.credits + 1

def assign (x : String) (e : Value count) : Action (State count) where
  requires _ := True
  effect s := s.set x (e.eval s)
  work _ := e.credits + 1

def read (x : String) (b : Fin count) (i : Value count) : Action (State count) where
  requires s := i.eval s < (s.arrays b).size
  effect s := s.set x (s.arrays b)[i.eval s]!
  work _ := i.credits + 6

def write (b : Fin count) (i v : Value count) : Action (State count) where
  requires s := i.eval s < (s.arrays b).size
  effect s := s.write b (i.eval s) (v.eval s)
  work _ := i.credits + v.credits + 5

def compare (op : Mutable.Comparison) (x y : String) : Guard (State count) where
  test s := op.eval (s.locals x) (s.locals y)

/-- Ordinary finite tuples of arrays are resident input values. -/
def initial (input : Fin count → Array Nat) : State count := ⟨input, fun _ => 0⟩


end AlgoLib.Experimental.RAM.Authoring.MultipleArrays
