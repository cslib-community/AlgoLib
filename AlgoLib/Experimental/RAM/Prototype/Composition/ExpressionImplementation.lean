/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Expressions
import AlgoLib.Experimental.RAM.Prototype.Composition.Linking

/-!
# Ownership-directed compilation of scalar and array expressions

Register and array interfaces specify reads and local updates once. Product
instances frame every unrelated component, including its private potential.
Expression certificates reconstruct compositionally; assignments and indexed writes
link through the existing `Primitive`, `Supported.compile`, and RAM compiler.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

/-- A typed path borrows a represented component and can put an updated component back. -/
class Focus (P : Representation S) (p : Path S A) (Q : outParam (Representation A)) where
  open_ : ∀ a r s saved, P.holds a r s saved → ∃ f credit,
    Q.holds (p.get a) f s credit ∧
    ∀ b t left, Q.holds b f t left → Writes f s t →
      ∃ total, P.holds (p.set a b) r t total ∧ Writes r s t ∧
        total + credit = left + saved

instance : Focus P .here P where
  open_ a r s saved h := ⟨r, saved, h, fun _ _ left hb hw => ⟨left, hb, hw, by omega⟩⟩

instance [f : Focus P p T] : Focus (P.sep Q) (.left p) T where
  open_ a r s saved rep := by
    obtain ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨r, c, hr, restore⟩ := f.open_ a.1 r₁ s c₁ hp
    refine ⟨r, c, hr, ?_⟩
    intro b t left hb hw
    obtain ⟨total, ht, hw', hc⟩ := restore b t left hb hw
    exact ⟨total + c₂, ⟨r₁, r₂, total, c₂, hd, rfl, rfl, ht, Q.frame hq hd hw'⟩,
      hw'.mono Finset.subset_union_left, by omega⟩

instance (P : Representation A) [f : Focus Q p T] : Focus (P.sep Q) (.right p) T where
  open_ a r s saved rep := by
    obtain ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨r, c, hr, restore⟩ := f.open_ a.2 r₂ s c₂ hq
    refine ⟨r, c, hr, ?_⟩
    intro b t left hb hw
    obtain ⟨total, ht, hw', hc⟩ := restore b t left hb hw
    exact ⟨c₁ + total, ⟨r₁, r₂, c₁, total, hd, rfl, rfl, P.frame hp hd.symm hw', ht⟩,
      hw'.mono Finset.subset_union_right, by omega⟩

/-- A scalar occupies one word register; updates preserve its potential. -/
class ScalarStorage (P : Representation Nat) where
  register : Var .word
  read : ∀ a r s c, P.holds a r s c → s.vars .word register.name = a
  update : ∀ a r s c, P.holds a r s c → ∀ b,
    P.holds b r (s.set register b) c ∧ Writes r s (s.set register b)

/-- Fixed-capacity arrays expose no address facts to client verification. -/
class ArrayStorage (P : Representation (Array Nat)) where
  base : Nat
  size : Var .word
  length : ∀ a r s c, P.holds a r s c → s.vars .word size.name = a.size
  read : ∀ a r s c, P.holds a r s c → ∀ i, i < a.size → s.heap (base + i) = a[i]!
  update : ∀ a r s c, P.holds a r s c → ∀ i b, i < a.size →
    P.holds (a.set! i b) r (s.write (base + i) b) c ∧ Writes r s (s.write (base + i) b)

/-- Read-only expressions have exact structural costs and reconstructed semantic certificates. -/
class Expression (P : Representation S) (e : Value S) where
  code : Expr .word
  cost : code.cost = e.credits
  correct : ∀ a r s c, P.holds a r s c → e.Safe a → code.eval s = e.eval a

instance : Expression P (.literal n) where
  code := .lit n
  cost := rfl
  correct _ _ _ _ _ _ := rfl

instance [f : Focus P p Q] [q : ScalarStorage Q] : Expression P (.scalar p) where
  code := .var q.register
  cost := rfl
  correct a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    exact q.read _ _ _ _ h'

instance [f : Focus P p Q] [q : ArrayStorage Q] : Expression P (.size p) where
  code := .var q.size
  cost := rfl
  correct a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    exact q.length _ _ _ _ h'

instance [f : Focus P p Q] [q : ArrayStorage Q] [i : Expression P index] :
    Expression P (.index p index) where
  code := .load (.bin .offset (.lit q.base) i.code)
  cost := by simp [Expr.cost, i.cost, Value.credits]; omega
  correct a r s c h safe := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    simp only [Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval,
      i.correct a r s c h safe.1]
    exact q.read _ _ _ _ h' _ safe.2

def Arithmetic.compile : Arithmetic → Op .word .word .word
  | .add => .add | .sub => .sub | .mul => .mul

instance [a : Expression P x] [b : Expression P y] : Expression P (.binary op x y) where
  code := .bin op.compile a.code b.code
  cost := by simp [Expr.cost, a.cost, b.cost, Value.credits]
  correct s r t c h safe := by
    cases op <;> simp [Arithmetic.compile, Expr.eval, Op.eval, Op.machine,
      Checked.BinOp.eval, a.correct s r t c h safe.1, b.correct s r t c h safe.2,
      Value.eval, Arithmetic.eval]

instance [f : Focus P p Q] [q : ScalarStorage Q] [e : Expression P value] :
    Primitive 24 P (assign p value) P where
  code := .assign q.register e.code
  correct a safe r s saved rep := by
    obtain ⟨r', c', h', restore⟩ := f.open_ a r s saved rep
    obtain ⟨hq, hw⟩ := q.update _ _ _ _ h' (value.eval a)
    obtain ⟨total, hp, writes, eq⟩ := restore _ _ c' hq hw
    have ev := Eval.assign q.register e.code s
    rw [e.correct a r s saved rep safe] at ev
    refine ⟨_, _, total, ev, hp, writes, ?_⟩
    simp only [assign, e.cost]
    omega

instance [f : Focus P p Q] [q : ArrayStorage Q]
    [i : Expression P index] [e : Expression P value] : Primitive 24 P (write p index value) P where
  code := .write (.bin .offset (.lit q.base) i.code) e.code
  correct a safe r s saved rep := by
    obtain ⟨r', c', h', restore⟩ := f.open_ a r s saved rep
    obtain ⟨hq, hw⟩ := q.update _ _ _ _ h' (index.eval a) (value.eval a) safe.2.2
    obtain ⟨total, hp, writes, eq⟩ := restore _ _ c' hq hw
    have ev := Eval.write (.bin .offset (.lit q.base) i.code) e.code s
    simp only [Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval,
      i.correct a r s saved rep safe.1, e.correct a r s saved rep safe.2.1] at ev
    refine ⟨_, _, total, ev, hp, writes, ?_⟩
    simp only [write, Expr.cost, i.cost, e.cost]
    omega

instance [a : Expression P (.scalar x)] [b : Expression P (.scalar y)] :
    TestImplementation 24 P (compare op x y) where
  condition := ⟨.word, match op with | .lt => .lt | .le => .le | .eq => .eq, a.code, b.code⟩
  correct s r t c h := by
    cases op <;> simp [Condition.eval, Comparison.eval, compare, Relation.eval,
      a.correct s r t c h trivial, b.correct s r t c h trivial, Value.eval]
  cost := by simp [Condition.cost, a.cost, b.cost, Value.credits]

instance (P : Representation A) (Q : Representation B) (R : Representation C) :
    Primitive rate ((P.sep Q).sep R) (associate A B C) (P.sep (Q.sep R)) where
  code := .skip
  correct a _ r s c h := ⟨0, s, c, .skip s,
    (Representation.sep_assoc P Q R).mp h, Writes.refl _ _, by simp [associate]⟩

instance (P : Representation A) (Q : Representation B) (R : Representation C) :
    Primitive rate (P.sep (Q.sep R)) (unassociate A B C) ((P.sep Q).sep R) where
  code := .skip
  correct a _ r s c h := ⟨0, s, c, .skip s,
    (Representation.sep_assoc P Q R).mpr h, Writes.refl _ _, by simp [unassociate]⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
