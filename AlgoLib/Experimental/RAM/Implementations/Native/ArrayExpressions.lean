/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Native.Expressions

/-!
# Native array operations with source-level contracts

The interface reserves one integer cell per element. Source Nat and Int arrays
specialize the same functional interface with their respective cell encodings.
Path focusing automatically frames other arrays, scalars, and private potential.
Array bounds remain the existing source safety obligations.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Native
open Prototype.Composition (Value SignedValue write signedWrite)

class ArrayStorage {A : Type} [Inhabited A] (encode : A → Int)
    (P : Representation (Array A)) where
  base : Nat
  size : Var .word
  length : ∀ a r s c, P.holds a r s c → s.vars .word size.name = (a.size : Int)
  read : ∀ a r s c, P.holds a r s c → ∀ i, i < a.size →
    s.heap (base + i) = encode a[i]!
  update : ∀ a r s c, P.holds a r s c → ∀ i b, i < a.size →
    P.holds (a.set! i b) r (s.write (base + i) (encode b)) c ∧
      Writes r s (s.write (base + i) (encode b))

abbrev NatArrayStorage (P : Representation (Array Nat)) := ArrayStorage Int.ofNat P
abbrev SignedArrayStorage (P : Representation (Array Int)) := ArrayStorage id P

instance [f : Focus P p Q] [q : NatArrayStorage Q] : Expression P (.size p) where
  code := .var q.size
  cost := by simp [Expr.cost, Ty.readCost, Value.credits]
  correct a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    simp [Expr.eval, Ty.normalize, q.length _ _ _ _ h', Value.eval]

instance [f : Focus P p Q] [q : SignedArrayStorage Q] : Expression P (.intSize p) where
  code := .var q.size
  cost := by simp [Expr.cost, Ty.readCost, Value.credits]
  correct a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    simp [Expr.eval, Ty.normalize, q.length _ _ _ _ h', Value.eval]

/-- A natural source index becomes a nonnegative native address. -/
def arrayAddress (base : Nat) (index : Expr .word) : Expr .ptr :=
  .bin .offset (.lit base) index

theorem arrayAddress_eval (base : Nat) (index : Expr .word) (s : Store) (n : Nat)
    (h : index.eval s = (n : Int)) :
    (arrayAddress base index).eval s = ((base + n : Nat) : Int) := by
  simp [arrayAddress, Expr.eval, Ty.normalize, Op.eval, Op.machine, Integer.BinOp.eval, h]

instance [f : Focus P p Q] [q : NatArrayStorage Q] [i : Expression P index] :
    Expression P (.index p index) where
  code := .load (arrayAddress q.base i.code)
  cost := by
    have := i.cost
    simp only [Expr.cost, arrayAddress, Op.cost, Ty.readCost, Value.credits]
    omega
  correct a r s c h safe := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    have ha := arrayAddress_eval q.base i.code s _ (i.correct a r s c h safe.1)
    simp only [Expr.eval, ha, Int.toNat_natCast]
    simp [Ty.normalize, q.read _ _ _ _ h' _ safe.2, Value.eval]

instance [f : Focus P p Q] [q : SignedArrayStorage Q] [i : Expression P index] :
    SignedExpression P (.index p index) where
  code := .load (arrayAddress q.base i.code)
  negative := .bin .intSub (.lit 0) (.load (arrayAddress q.base i.code))
  positivePart := .toNat (.load (arrayAddress q.base i.code))
  negativePart := .toNat (.bin .intSub (.lit 0) (.load (arrayAddress q.base i.code)))
  cost := by
    have := i.cost
    simp only [Expr.cost, arrayAddress, Op.cost, Ty.readCost, SignedValue.credits, SignedValue.costs]
    omega
  negativeCost := by
    have := i.cost
    simp only [Expr.cost, arrayAddress, Op.cost, Ty.readCost, SignedValue.credits, SignedValue.costs]
    omega
  positivePartCost := by
    have := i.cost
    simp only [Expr.cost, arrayAddress, Op.cost, Ty.readCost, SignedValue.costs]
    omega
  negativePartCost := by
    have := i.cost
    simp only [Expr.cost, arrayAddress, Op.cost, Ty.readCost, SignedValue.costs]
    omega
  correct a r s c h safe := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    have ha := arrayAddress_eval q.base i.code s _ (i.correct a r s c h safe.1)
    simp only [Expr.eval, ha, Int.toNat_natCast]
    simp [Ty.normalize, q.read _ _ _ _ h' _ safe.2, SignedValue.eval]
  negativeCorrect a r s c h safe := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    have ha := arrayAddress_eval q.base i.code s _ (i.correct a r s c h safe.1)
    simp only [Expr.eval, ha, Int.toNat_natCast]
    simp [Ty.normalize, Op.eval, Op.machine, Integer.BinOp.eval,
      q.read _ _ _ _ h' _ safe.2, SignedValue.eval]
  positivePartCorrect a r s c h safe := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    have ha := arrayAddress_eval q.base i.code s _ (i.correct a r s c h safe.1)
    simp only [Expr.eval, ha, Int.toNat_natCast]
    simp [Ty.normalize, q.read _ _ _ _ h' _ safe.2, SignedValue.eval]
  negativePartCorrect a r s c h safe := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    have ha := arrayAddress_eval q.base i.code s _ (i.correct a r s c h safe.1)
    simp only [Expr.eval, ha, Int.toNat_natCast]
    simp [Ty.normalize, Op.eval, Op.machine, Integer.BinOp.eval,
      q.read _ _ _ _ h' _ safe.2, SignedValue.eval]

instance [f : Focus P p Q] [q : NatArrayStorage Q]
    [i : Expression P index] [e : Expression P value] : Primitive 24 P (write p index value) P where
  code := .write (arrayAddress q.base i.code) e.code
  correct a safe r s saved rep := by
    obtain ⟨r', c', h', restore⟩ := f.open_ a r s saved rep
    obtain ⟨hq, hw⟩ := q.update _ _ _ _ h' (index.eval a) (value.eval a) safe.2.2
    obtain ⟨total, hp, writes, eq⟩ := restore _ _ c' hq hw
    have ev := Eval.write (arrayAddress q.base i.code) e.code s
    rw [arrayAddress_eval _ _ _ _ (i.correct a r s saved rep safe.1),
      e.correct a r s saved rep safe.2.1] at ev
    simp only [Int.toNat_natCast] at ev
    refine ⟨_, _, total, ev, hp, writes, ?_⟩
    have := i.cost
    have := e.cost
    simp only [write, Expr.cost, arrayAddress, Op.cost]
    omega

instance [f : Focus P p Q] [q : SignedArrayStorage Q]
    [i : Expression P index] [e : SignedExpression P value] :
    Primitive 24 P (signedWrite p index value) P where
  code := .write (arrayAddress q.base i.code) e.code
  correct a safe r s saved rep := by
    obtain ⟨r', c', h', restore⟩ := f.open_ a r s saved rep
    obtain ⟨hq, hw⟩ := q.update _ _ _ _ h' (index.eval a) (value.eval a) safe.2.2
    obtain ⟨total, hp, writes, eq⟩ := restore _ _ c' hq hw
    have ev := Eval.write (arrayAddress q.base i.code) e.code s
    rw [arrayAddress_eval _ _ _ _ (i.correct a r s saved rep safe.1),
      e.correct a r s saved rep safe.2.1] at ev
    simp only [Int.toNat_natCast] at ev
    refine ⟨_, _, total, ev, hp, writes, ?_⟩
    have := i.cost
    have := e.cost
    simp only [signedWrite, Expr.cost, arrayAddress, Op.cost]
    omega

end AlgoLib.Experimental.RAM.Native
