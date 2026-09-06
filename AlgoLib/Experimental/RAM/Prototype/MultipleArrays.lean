/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Mutable

/-!
# Independently mutable arrays with automatic cross-array framing

There are finitely many array handles, each with its own length. Physical cells
are interleaved: array `a`, element `i` occupies `count * i + a`. Distinct handles
therefore cannot alias, regardless of their lengths. The arithmetic separation
proof is reusable; algorithm authors never prove that an update preserves another
array. Input arrays have value semantics and are encoded into independent lanes.

This module is a certified data-structure adapter. It does not by itself add a
parser for arbitrary Velvet array expressions or allocate new array handles.
-/
namespace AlgoLib.Experimental.RAM.Prototype.MultipleArrays
open Authoring Checked.Language

variable {count : Nat}

structure State (count : Nat) where
  arrays : Fin count → Array Nat
  locals : String → Nat

def State.set (s : State count) (x : String) (v : Nat) : State count :=
  { s with locals := Function.update s.locals x v }

def State.write (s : State count) (a : Fin count) (i v : Nat) : State count :=
  { s with arrays := Function.update s.arrays a ((s.arrays a).set! i v) }

def arrayName (a : Fin count) : String := String.ofList (List.replicate a.val 'a')
def sizeVar (a : Fin count) : Var .word := ⟨"s:" ++ arrayName a⟩
def localVar (x : String) : Var .word := ⟨"v:" ++ x⟩

@[simp] theorem size_injective (a b : Fin count) :
    (sizeVar a).name = (sizeVar b).name ↔ a = b := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg String.length h
    simpa [sizeVar, arrayName] using this
  · rintro rfl; rfl

@[simp] theorem size_ne_local (a : Fin count) (x : String) :
    (sizeVar a).name ≠ (localVar x).name := by
  intro h
  have := congrArg String.toList h
  simp [sizeVar, localVar] at this

/-- Disjoint handles denote disjoint physical cells, at all indices. -/
theorem cell_injective (a b : Fin count) (i j : Nat) :
    count * i + a.val = count * j + b.val ↔ i = j ∧ a = b := by
  constructor
  · intro h
    have hm := congrArg (· % count) h
    have ha : a = b := by
      apply Fin.ext
      simpa [Nat.add_mod, Nat.mod_eq_of_lt] using hm
    subst b
    have hn : 0 < count := Nat.zero_lt_of_lt a.isLt
    exact ⟨by nlinarith, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

def Represents (a : State count) (s : Store) : Prop :=
  (∀ x, s.vars .word (localVar x).name = a.locals x) ∧
  (∀ b, s.vars .word (sizeVar b).name = (a.arrays b).size) ∧
  ∀ b i, i < (a.arrays b).size → s.heap (count * i + b.val) = (a.arrays b)[i]!

def model (count : Nat) : Model (State count) := ⟨Represents, 3⟩

theorem represents_set {a : State count} {s : Store} (h : Represents a s)
    (x : String) (v : Nat) : Represents (a.set x v) (s.set (localVar x) v) := by
  refine ⟨?_, ?_, h.2.2⟩
  · intro y
    have hy := h.1 y
    simp only [localVar] at hy
    simp [State.set, Store.set, localVar, hy, Function.update_apply]
  · intro b
    simpa [Store.set] using h.2.1 b

/-- One proof frames all arrays other than the updated handle. -/
theorem represents_write {a : State count} {s : Store} (h : Represents a s)
    (b : Fin count) (i v : Nat) :
    Represents (a.write b i v) (s.write (count * i + b.val) v) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro d
    by_cases hd : d = b <;> simp [Store.write, State.write, hd, h.2.1]
  · intro d j hj
    by_cases hd : d = b
    · subst d
      have hn : count ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt b.isLt)
      have hj' : j < (a.arrays b).size := by simpa [State.write] using hj
      simp [State.write, Store.write, Function.update_apply,
        Array.set!, getElem!_pos, Array.getElem_setIfInBounds, hj', h.2.2 b j hj', eq_comm, hn]
    · have hn : count * j + d.val ≠ count * i + b.val := by
        intro he; exact hd ((cell_injective d b j i).mp he).2
      have hj' : j < (a.arrays d).size := by simpa [State.write, hd] using hj
      simpa [State.write, Store.write, Function.update_apply, hd, hn] using h.2.2 d j hj'

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

def Value.compile : Value count → Expr .word
  | .literal n => .lit n
  | .local x => .var (localVar x)
  | .size a => .var (sizeVar a)
  | .add x y => .bin .add x.compile y.compile
  | .sub x y => .bin .sub x.compile y.compile
  | .mul x y => .bin .mul x.compile y.compile

/-- This backend implements the independently defined expression charge. -/
@[simp] theorem Value.compile_credits (e : Value count) : e.compile.cost = e.credits := by
  induction e <;> simp_all [Value.compile, Value.credits, Expr.cost]

theorem Value.correct (e : Value count) {a : State count} {s : Store} (h : Represents a s) :
    e.compile.eval s = e.eval a := by
  induction e <;> simp_all only [compile, eval, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval]
  · exact h.1 _
  · exact h.2.1 _

def address (a : Fin count) (i : Value count) : Expr .ptr :=
  .bin .offset (.lit a.val) (.bin .mul (.lit count) i.compile)

theorem address_correct (b : Fin count) (i : Value count) {a : State count} {s : Store}
    (h : Represents a s) : (address b i).eval s = count * i.eval a + b.val := by
  simp [address, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, i.correct h, Nat.add_comm]

def assign (x : String) (e : Value count) : Action (State count) where
  requires _ := True
  effect s := s.set x (e.eval s)
  work _ := e.credits + 1

instance assignImplementation (x : String) (e : Value count) :
    ActionImplementation (model count) (assign x e) where
  implementation := .assign (localVar x) e.compile
  correct a s hs _ := by
    dsimp only [assign] at *
    refine ⟨_, _, .assign _ _ _, ?_, by simp [model]⟩
    simpa [e.correct hs] using represents_set hs x (e.eval a)

def read (x : String) (b : Fin count) (i : Value count) : Action (State count) where
  requires s := i.eval s < (s.arrays b).size
  effect s := s.set x (s.arrays b)[i.eval s]!
  work _ := i.credits + 6

instance readImplementation (x : String) (b : Fin count) (i : Value count) :
    ActionImplementation (model count) (read x b i) where
  implementation := .assign (localVar x) (.load (address b i))
  correct a s hs hi := by
    dsimp only [read] at *
    refine ⟨_, _, .assign _ _ _, ?_, by simp [Expr.cost, model, address] <;> omega⟩
    simpa [Expr.eval, address_correct b i hs, hs.2.2 b _ hi] using
      represents_set hs x (a.arrays b)[i.eval a]!

def write (b : Fin count) (i v : Value count) : Action (State count) where
  requires s := i.eval s < (s.arrays b).size
  effect s := s.write b (i.eval s) (v.eval s)
  work _ := i.credits + v.credits + 5

instance writeImplementation (b : Fin count) (i v : Value count) :
    ActionImplementation (model count) (write b i v) where
  implementation := .write (address b i) v.compile
  correct a s hs _ := by
    dsimp only [write] at *
    refine ⟨_, _, .write _ _ _, ?_, by simp [model, Expr.cost, address]; omega⟩
    simpa [address_correct b i hs, v.correct hs] using
      represents_write hs b (i.eval a) (v.eval a)

def compare (op : Comparison) (x y : String) : Guard (State count) where
  test s := op.eval (s.locals x) (s.locals y)

instance compareImplementation (op : Comparison) (x y : String) :
    GuardImplementation (model count) (compare op x y) where
  implementation := ⟨.word, op, .var (localVar x), .var (localVar y)⟩
  correct _ _ h := by
    dsimp only [compare] at *
    simp [Condition.eval, Expr.eval, h.1]
  cost := by simp [Condition.cost, Expr.cost, model]

private def findArray (count : Nat) (name : String) : Option (Fin count) :=
  (List.finRange count).find? (fun a => name == (sizeVar a).name)

private theorem find_size (a : Fin count) : findArray count (sizeVar a).name = some a := by
  cases h : findArray count (sizeVar a).name with
  | none =>
    have no := List.find?_eq_none.mp h a (by simp)
    simp at no
  | some b =>
    have same := List.find?_some h
    have eq : a = b := by simpa using same
    subst b
    rfl

private theorem find_local (count : Nat) (x : String) :
    findArray count (localVar x).name = none := by
  simp [findArray, List.find?_eq_none, Ne.symm (size_ne_local _ _)]

/-- Ordinary finite tuples of arrays are resident input values. -/
def initial (input : Fin count → Array Nat) : State count := ⟨input, fun _ => 0⟩

def encode (input : Fin count → Array Nat) : Store where
  vars ty name := match findArray count name with
    | none => 0
    | some a => if ty = .word then (input a).size else 0
  heap address := if h : 0 < count then
    (input ⟨address % count, Nat.mod_lt _ h⟩)[address / count]! else 0

theorem represents_initial (input : Fin count → Array Nat) :
    Represents (initial input) (encode input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; simp [encode, initial, find_local]
  · intro a; simp [encode, initial, find_size]
  · intro a i _
    have hn : 0 < count := Nat.zero_lt_of_lt a.isLt
    have hi : (count * i + a.val) / count = i := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn]
      simp [Nat.div_eq_of_lt a.isLt]
    have ha : (⟨(count * i + a.val) % count, Nat.mod_lt _ hn⟩ : Fin count) = a := by
      apply Fin.ext
      simp [Nat.add_mod, Nat.mod_eq_of_lt a.isLt]
    simp only [encode, dif_pos hn, hi, ha, initial]

/-- Fuel-free execution observes each independently mutable array as a Lean array. -/
def interface (count : Nat) :
    Interface (model count) (Fin count → Array Nat) (Fin count → Array Nat) where
  initial := initial
  encode := encode
  prepare := .skip
  preparationCost _ := 0
  preparation input := ⟨0, _, .skip _, represents_initial input, by omega⟩
  decode _ s a := Array.ofFn
    (fun i : Fin (s.vars .word (sizeVar a).name) => s.heap (count * i.val + a.val))
  Observes s output := output = s.arrays
  output _ a s hs := by
    funext b
    apply Array.ext
    · simpa using hs.2.1 b
    · intro i hi hj
      simpa [getElem!_pos, hj] using hs.2.2 b i hj

end AlgoLib.Experimental.RAM.Prototype.MultipleArrays
