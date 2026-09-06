/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Mutable

/-!
# A second implementation of the pure mutable-array interface

Contiguous arrays access element `i` directly. This backend instead stores a table
at even addresses and payloads at distinct odd addresses. Every array access loads
its pointer from the table. The representation permits any injective placement of
payloads; the executable encoder uses reverse order to exercise real indirection.

The backend proves table preservation, non-aliasing, scalar framing, bounds, and
instruction costs once. It implements exactly Authoring.Mutable's logical actions:
algorithm code, annotations, credit budgets, and proofs are unchanged.
Input storage is preloaded, as in the contiguous backend; allocation and resizing
are outside this interface. No logical array computation executes as a RAM primitive.
-/
namespace AlgoLib.Experimental.RAM.Prototype.IndirectArrays
open Authoring Checked.Language
open Mutable (localVar sizeVar)

/-- Table cells and payload cells occupy disjoint address classes. -/
def Represents (a : Mutable.State) (s : Store) : Prop :=
  (∀ x, s.vars .word (localVar x).name = a.locals x) ∧
  s.vars .word sizeVar.name = a.array.size ∧
  (∀ i, i < a.array.size → s.heap (2 * i) % 2 = 1) ∧
  (∀ i j, i < a.array.size → j < a.array.size →
    s.heap (2 * i) = s.heap (2 * j) → i = j) ∧
  ∀ i, i < a.array.size → s.heap (s.heap (2 * i)) = a.array[i]!

def model : Model Mutable.State := ⟨Represents, 3⟩

theorem represents_set {a : Mutable.State} {s : Store} (h : Represents a s)
    (x : String) (v : Nat) : Represents (a.set x v) (s.set (localVar x) v) := by
  refine ⟨?_, ?_, h.2.2⟩
  · intro y
    simp [Mutable.State.set, Store.set, Mutable.local_injective, h.1, Function.update_apply]
  · simpa [Store.set] using h.2.1

/-- A payload write preserves the entire pointer table, including unused cells. -/
theorem table_frame {a : Mutable.State} {s : Store} (h : Represents a s)
    (i v : Nat) (hi : i < a.array.size) (j : Nat) :
    (s.write (s.heap (2 * i)) v).heap (2 * j) = s.heap (2 * j) := by
  have odd := h.2.2.1 i hi
  have distinct : 2 * j ≠ s.heap (2 * i) := by omega
  simp [Store.write, distinct]

/-- Non-aliasing proves that writing one element preserves every other element. -/
theorem represents_write {a : Mutable.State} {s : Store} (h : Represents a s)
    (i v : Nat) (hi : i < a.array.size) :
    Represents { a with array := a.array.set! i v } (s.write (s.heap (2 * i)) v) := by
  refine ⟨h.1, by simpa using h.2.1, ?_, ?_, ?_⟩
  · intro j hj
    rw [table_frame h i v hi j]
    exact h.2.2.1 j (by simpa using hj)
  · intro j k hj hk equal
    rw [table_frame h i v hi j, table_frame h i v hi k] at equal
    exact h.2.2.2.1 j k (by simpa using hj) (by simpa using hk) equal
  · intro j hj
    have hj' : j < a.array.size := by simpa using hj
    rw [table_frame h i v hi j]
    have equal : s.heap (2 * j) = s.heap (2 * i) ↔ j = i :=
      ⟨h.2.2.2.1 j i hj' hi, fun e => congrArg (fun k => s.heap (2*k)) e⟩
    simp [Store.write, Function.update_apply, equal, Array.set!, getElem!_pos,
      Array.getElem_setIfInBounds, hj', h.2.2.2.2 j hj', eq_comm]

/-- Scalar compilation is reused verbatim; it never reads the array heap. -/
theorem value_correct (e : Mutable.Value) {a : Mutable.State} {s : Store}
    (h : Represents a s) : e.compile.eval s = e.eval a := by
  induction e <;> simp_all only [Mutable.Value.compile, Mutable.Value.eval,
    Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval]
  · exact h.1 _
  · exact h.2.1

def tableAddress (i : Mutable.Value) : Expr .ptr :=
  .bin .offset (.lit 0) (.bin .mul (.lit 2) i.compile)

/-- The word loaded from the table is converted to an address by pointer offset. -/
def address (i : Mutable.Value) : Expr .ptr :=
  .bin .offset (.lit 0) (.load (tableAddress i))

theorem address_correct (i : Mutable.Value) {a : Mutable.State} {s : Store}
    (h : Represents a s) : (address i).eval s = s.heap (2 * i.eval a) := by
  simp [address, tableAddress, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval,
    value_correct i h]

instance assignImplementation (x : String) (e : Mutable.Value) :
    ActionImplementation model (Mutable.assign x e) where
  implementation := .assign (localVar x) e.compile
  correct a s hs _ := by
    dsimp only [Mutable.assign] at *
    refine ⟨_, _, .assign _ _ _, ?_, by simp [model]⟩
    simpa [value_correct e hs] using represents_set hs x (e.eval a)

instance readImplementation (x : String) (i : Mutable.Value) :
    ActionImplementation model (Mutable.read x i) where
  implementation := .assign (localVar x) (.load (address i))
  correct a s hs hi := by
    dsimp only [Mutable.read] at *
    refine ⟨_, _, .assign _ _ _, ?_, ?_⟩
    · simpa [Expr.eval, address_correct i hs, hs.2.2.2.2 _ hi] using
        represents_set hs x a.array[i.eval a]!
    · simp [model, Expr.cost, address, tableAddress]; omega

instance writeImplementation (i v : Mutable.Value) :
    ActionImplementation model (Mutable.write i v) where
  implementation := .write (address i) v.compile
  correct a s hs hi := by
    dsimp only [Mutable.write] at *
    refine ⟨_, _, .write _ _ _, ?_, ?_⟩
    · simpa [address_correct i hs, value_correct v hs] using
        represents_write hs (i.eval a) (v.eval a) hi
    · simp [model, Expr.cost, address, tableAddress]; omega

instance compareImplementation (op : Mutable.Comparison) (x y : String) :
    GuardImplementation model (Mutable.compare op x y) where
  implementation := ⟨.word, op.compile, .var (localVar x), .var (localVar y)⟩
  correct _ _ h := by simp [Mutable.compare, Condition.eval, Expr.eval, h.1]
  cost := by simp [Condition.cost, Expr.cost, model]

/-- Initial payloads are physically reversed and separated by pointer-table cells. -/
def encode (input : Array Nat) : Store where
  vars := (Mutable.encode input).vars
  heap p := if p % 2 = 0 then 2 * (input.size - 1 - p / 2) + 1
    else input[input.size - 1 - p / 2]!

theorem represents_initial (input : Array Nat) :
    Represents (Mutable.initial input) (encode input) := by
  have dense := Mutable.represents_initial input
  refine ⟨dense.1, dense.2.1, ?_, ?_, ?_⟩
  · intro i _
    simp [encode]
  · intro i j hi hj equal
    simp [encode] at equal
    simp only [Mutable.initial] at hi hj
    omega
  · intro i hi
    have hi' : i < input.size := hi
    have reverse : input.size - 1 - (input.size - 1 - i) = i := by omega
    have half : (2 * (input.size - 1 - i) + 1) / 2 = input.size - 1 - i := by omega
    simp [encode, half, reverse, Mutable.initial]

/-- Same logical input/output interface, with a different physical representation. -/
def interface : Interface model (Array Nat) (Array Nat) where
  initial := Mutable.initial
  encode := encode
  prepare := .skip
  preparationCost _ := 0
  preparation input := ⟨0, _, .skip _, represents_initial input, by omega⟩
  decode _ s := Array.ofFn (fun i : Fin (s.vars .word sizeVar.name) => s.heap (s.heap (2*i)))
  Observes s output := output = s.array
  output _ a s hs := by
    apply Array.ext
    · simpa using hs.2.1
    · intro i hi hj
      simpa [getElem!_pos, hj] using hs.2.2.2.2 i hj

end AlgoLib.Experimental.RAM.Prototype.IndirectArrays
