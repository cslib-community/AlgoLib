/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Methods
import AlgoLib.Experimental.RAM.Authoring.Mutable

/-!
# Implementation of mutable variables and array operations

This is framework code. The frontend generates these certified primitives from
ordinary assignments and indexing; students never construct an `Action`, a model,
or a representation proof. The logical state contains an ordinary Lean array and
named natural-number locals. Representation, framing, and instruction costs are
proved here once, independently of insertion sort.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Mutable
open Authoring Checked.Language

def localVar (name : String) : Var .word := ⟨"v:" ++ name⟩
def sizeVar : Var .word := ⟨"size"⟩

@[simp] theorem size_ne_local (name : String) : sizeVar.name ≠ (localVar name).name := by
  intro h
  have := congrArg String.toList h
  simp [sizeVar, localVar] at this

@[simp] theorem local_injective (x y : String) :
    (localVar x).name = (localVar y).name ↔ x = y := by simp [localVar]

def Represents (a : State) (s : Store) : Prop :=
  (∀ x, s.vars .word (localVar x).name = a.locals x) ∧
  s.vars .word sizeVar.name = a.array.size ∧
  ∀ i, i < a.array.size → s.heap i = a.array[i]!

def model : Model State := ⟨Represents, 3⟩

theorem represents_set {a : State} {s : Store} (h : Represents a s) (x : String) (v : Nat) :
    Represents (a.set x v) (s.set (localVar x) v) := by
  refine ⟨?_, ?_, h.2.2⟩
  · intro y
    simp [State.set, Store.set, local_injective, h.1, Function.update_apply]
  · simpa [Store.set] using h.2.1

theorem represents_write {a : State} {s : Store} (h : Represents a s) (i v : Nat)
    (_hi : i < a.array.size) :
    Represents { a with array := a.array.set! i v } (s.write i v) := by
  refine ⟨h.1, by simpa using h.2.1, ?_⟩
  intro j hj
  have hj' : j < a.array.size := by simpa using hj
  simp [Store.write, Function.update_apply, Array.set!, getElem!_pos,
    Array.getElem_setIfInBounds, hj', h.2.2 j hj', eq_comm]

def Value.compile : Value → Expr .word
  | .literal n => .lit n
  | .local x => .var (localVar x)
  | .size => .var sizeVar
  | .add a b => .bin .add a.compile b.compile
  | .sub a b => .bin .sub a.compile b.compile
  | .mul a b => .bin .mul a.compile b.compile

/-- This backend implements the independently defined expression charge. -/
@[simp] theorem Value.compile_credits (e : Value) : e.compile.cost = e.credits := by
  induction e <;> simp_all [Value.compile, Value.credits, Expr.cost]

theorem Value.correct (e : Value) {a : State} {s : Store} (h : Represents a s) :
    e.compile.eval s = e.eval a := by
  induction e <;> simp_all only [compile, eval, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval]
  · exact h.1 _
  · exact h.2.1

def address (e : Value) : Expr .ptr := .bin .offset (.lit 0) e.compile

theorem address_correct (e : Value) {a : State} {s : Store} (h : Represents a s) :
    (address e).eval s = e.eval a := by
  simp [address, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, e.correct h]

instance assignImplementation (x : String) (e : Value) :
    ActionImplementation model (assign x e) where
  implementation := .assign (localVar x) e.compile
  correct a s hs _ := by
    dsimp only [assign] at *
    refine ⟨_, _, .assign _ _ _, ?_, by simp [model]⟩
    simpa [e.correct hs] using represents_set hs x (e.eval a)

instance readImplementation (x : String) (i : Value) : ActionImplementation model (read x i) where
  implementation := .assign (localVar x) (.load (address i))
  correct a s hs hi := by
    dsimp only [read] at *
    refine ⟨_, _, .assign _ _ _, ?_, by simp [Expr.cost, model, address]; omega⟩
    simpa [Expr.eval, address_correct i hs, hs.2.2 _ hi] using
      represents_set hs x a.array[i.eval a]!

instance writeImplementation (i v : Value) : ActionImplementation model (write i v) where
  implementation := .write (address i) v.compile
  correct a s hs hi := by
    dsimp only [write] at *
    refine ⟨_, _, .write _ _ _, ?_, by simp [model, Expr.cost, address]; omega⟩
    simpa [address_correct i hs, v.correct hs] using
      represents_write hs (i.eval a) (v.eval a) hi

/-- Compile the pure comparison tag; the logical language imports no RAM enums. -/
def Comparison.compile : Comparison → Checked.Language.Comparison
  | .lt => .lt | .le => .le | .eq => .eq

@[simp] theorem Comparison.compile_eval (op : Comparison) (x y : Nat) :
    op.compile.eval x y = op.eval x y := by cases op <;> rfl

instance compareImplementation (op : Comparison) (x y : String) :
    GuardImplementation model (compare op x y) where
  implementation := ⟨.word, op.compile, .var (localVar x), .var (localVar y)⟩
  correct _ _ h := by
    dsimp only [compare] at *
    simp [Condition.eval, Expr.eval, h.1]
  cost := by simp [Condition.cost, Expr.cost, model]

def encode (input : Array Nat) : Store where
  vars ty name := if ty = .word ∧ name = sizeVar.name then input.size else 0
  heap i := input[i]!

theorem represents_initial (input : Array Nat) : Represents (initial input) (encode input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [encode, initial, Ne.symm (size_ne_local x)]
  · simp [encode, initial]
  · intro i _; rfl

/-- Input arrays are supplied in RAM memory; decoding is a host-side observation. -/
def interface : Interface model (Array Nat) (Array Nat) where
  initial := initial
  encode := encode
  prepare := .skip
  preparationCost _ := 0
  preparation input := ⟨0, _, .skip _, represents_initial input, by omega⟩
  decode _ s := Array.ofFn (fun i : Fin (s.vars .word sizeVar.name) => s.heap i)
  Observes s output := output = s.array
  output _ a s hs := by
    apply Array.ext
    · simpa using hs.2.1
    · intro i hi hj
      simpa [getElem!_pos, hj] using hs.2.2 i hj


end AlgoLib.Experimental.RAM.Authoring.Mutable
