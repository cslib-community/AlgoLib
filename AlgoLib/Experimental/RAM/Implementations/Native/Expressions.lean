/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Compiler.Assembly.Native.Linking
import AlgoLib.Experimental.RAM.Implementations.Contracts.Focus

/-!
# Native lowering of the unchanged Nat/Int source expressions

Native storage holds one integer per signed value. Expression certificates retain
four *code views*: the value, its negation, and each truncated natural part. These
are alternative expressions, not paired storage. Negation exchanges views, so a
chain of source negations introduces no uncharged work. The natural part of a
negative embedded Nat is constant zero. These choices preserve the existing logical
credit contracts, including the deliberately cheap truncation/negation cases.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Native
open Prototype.Composition (Path Value SignedValue Arithmetic Relation compare compareSigned assign signedAssign)

abbrev Focus (P : Representation S) (p : Path S A) (Q : Representation A) :=
  Ownership.Focus P p Q

class ScalarStorage (P : Representation Nat) where
  register : Var .word
  read : ∀ a r s c, P.holds a r s c → s.vars .word register.name = (a : Int)
  update : ∀ a r s c, P.holds a r s c → ∀ b : Nat,
    P.holds b r (s.set register b) c ∧ Writes r s (s.set register b)

class SignedStorage (P : Representation Int) where
  register : Var .integer
  read : ∀ a r s c, P.holds a r s c → s.vars .integer register.name = a
  update : ∀ a r s c, P.holds a r s c → ∀ b : Int,
    P.holds b r (s.set register b) c ∧ Writes r s (s.set register b)

class Expression (P : Representation S) (e : Value S) where
  code : Expr .word
  cost : code.cost ≤ 4 * e.credits
  correct : ∀ a r s c, P.holds a r s c → e.Safe a → code.eval s = (e.eval a : Int)

class SignedExpression (P : Representation S) (e : SignedValue S) where
  code : Expr .integer
  negative : Expr .integer
  positivePart : Expr .word
  negativePart : Expr .word
  cost : code.cost ≤ 4 * e.credits
  negativeCost : negative.cost ≤ 4 * e.credits
  positivePartCost : positivePart.cost ≤ 4 * e.costs.1
  negativePartCost : negativePart.cost ≤ 4 * e.costs.2
  correct : ∀ a r s c, P.holds a r s c → e.Safe a → code.eval s = e.eval a
  negativeCorrect : ∀ a r s c, P.holds a r s c → e.Safe a → negative.eval s = -e.eval a
  positivePartCorrect : ∀ a r s c, P.holds a r s c → e.Safe a →
    positivePart.eval s = (e.eval a).toNat
  negativePartCorrect : ∀ a r s c, P.holds a r s c → e.Safe a →
    negativePart.eval s = (-e.eval a).toNat

instance : Expression P (.literal n) where
  code := .lit n
  cost := by simp [Expr.cost, Value.credits]
  correct _ _ _ _ _ _ := by simp [Expr.eval, Ty.normalize, Value.eval]

instance : SignedExpression P (.literal n) where
  code := .lit n
  negative := .lit (-n)
  positivePart := .lit n.toNat
  negativePart := .lit (-n).toNat
  cost := by simp [Expr.cost, SignedValue.credits, SignedValue.costs]
  negativeCost := by simp [Expr.cost, SignedValue.credits, SignedValue.costs]
  positivePartCost := by simp [Expr.cost, SignedValue.costs]
  negativePartCost := by simp [Expr.cost, SignedValue.costs]
  correct _ _ _ _ _ _ := rfl
  negativeCorrect _ _ _ _ _ _ := rfl
  positivePartCorrect _ _ _ _ _ _ := by simp [Expr.eval, Ty.normalize, SignedValue.eval]
  negativePartCorrect _ _ _ _ _ _ := by simp [Expr.eval, Ty.normalize, SignedValue.eval]

instance [f : Focus P p Q] [q : ScalarStorage Q] : Expression P (.scalar p) where
  code := .var q.register
  cost := by simp [Expr.cost, Ty.readCost, Value.credits]
  correct a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    simp [Expr.eval, Ty.normalize, q.read _ _ _ _ h', Value.eval]

instance [f : Focus P p Q] [q : SignedStorage Q] : SignedExpression P (.scalar p) where
  code := .var q.register
  negative := .bin .intSub (.lit 0) (.var q.register)
  positivePart := .toNat (.var q.register)
  negativePart := .toNat (.bin .intSub (.lit 0) (.var q.register))
  cost := by simp [Expr.cost, Ty.readCost, SignedValue.credits, SignedValue.costs]
  negativeCost := by simp [Expr.cost, Ty.readCost, Op.cost, SignedValue.credits, SignedValue.costs]
  positivePartCost := by simp [Expr.cost, Ty.readCost, SignedValue.costs]
  negativePartCost := by simp [Expr.cost, Ty.readCost, Op.cost, SignedValue.costs]
  correct a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    exact q.read _ _ _ _ h'
  negativeCorrect a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    simp [Expr.eval, Ty.normalize, Op.eval, Op.machine, Integer.BinOp.eval,
      q.read _ _ _ _ h', SignedValue.eval]
  positivePartCorrect a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    simp [Expr.eval, Ty.normalize, q.read _ _ _ _ h', SignedValue.eval]
  negativePartCorrect a r s c h _ := by
    obtain ⟨r', c', h', _⟩ := f.open_ a r s c h
    simp [Expr.eval, Ty.normalize, Op.eval, Op.machine, Integer.BinOp.eval,
      q.read _ _ _ _ h', SignedValue.eval]

instance [e : SignedExpression P value] : SignedExpression P (.neg value) where
  code := e.negative
  negative := e.code
  positivePart := e.negativePart
  negativePart := e.positivePart
  cost := by simpa [SignedValue.credits, SignedValue.costs, Nat.add_comm] using e.negativeCost
  negativeCost := by simpa [SignedValue.credits, SignedValue.costs, Nat.add_comm] using e.cost
  positivePartCost := e.negativePartCost
  negativePartCost := e.positivePartCost
  correct := e.negativeCorrect
  negativeCorrect a r s c h safe := by simpa [SignedValue.eval] using e.correct a r s c h safe
  positivePartCorrect := e.negativePartCorrect
  negativePartCorrect a r s c h safe := by
    simpa [SignedValue.eval] using e.positivePartCorrect a r s c h safe

instance [e : SignedExpression P value] : Expression P (.toNat value) where
  code := e.positivePart
  cost := e.positivePartCost
  correct := e.positivePartCorrect

instance [e : SignedExpression P value] : Expression P (.checkedToNat value) where
  code := e.positivePart
  cost := e.positivePartCost
  correct a r s c h safe := e.positivePartCorrect a r s c h safe.1

instance [e : Expression P value] : SignedExpression P (.ofNat value) where
  code := .ofNat e.code
  negative := .bin .intSub (.lit 0) (.ofNat e.code)
  positivePart := e.code
  negativePart := .lit 0
  cost := by have := e.cost; simp [Expr.cost, SignedValue.credits, SignedValue.costs]; omega
  negativeCost := by
    have := e.cost
    simp [Expr.cost, Op.cost, SignedValue.credits, SignedValue.costs]
    omega
  positivePartCost := e.cost
  negativePartCost := by simp [Expr.cost, SignedValue.costs]
  correct := e.correct
  negativeCorrect a r s c h safe := by
    simp [Expr.eval, Ty.normalize, Op.eval, Op.machine, Integer.BinOp.eval,
      e.correct a r s c h safe, SignedValue.eval]
  positivePartCorrect a r s c h safe := by
    simpa [SignedValue.eval] using e.correct a r s c h safe
  negativePartCorrect a _ _ _ _ _ := by simp [Expr.eval, Ty.normalize, SignedValue.eval]

def naturalOp : Arithmetic → Op .word .word .word
  | .add => .add | .sub => .sub | .mul => .mul

def signedOp : Arithmetic → Op .integer .integer .integer
  | .add => .intAdd | .sub => .intSub | .mul => .intMul

instance [a : Expression P x] [b : Expression P y] : Expression P (.binary op x y) where
  code := .bin (naturalOp op) a.code b.code
  cost := by
    have := a.cost
    have := b.cost
    cases op <;> simp only [Expr.cost, naturalOp, Op.cost, Value.credits] <;> omega
  correct s r t c h safe := by
    cases op <;> simp [Expr.eval, naturalOp, Op.eval, Op.machine, Integer.BinOp.eval,
      a.correct s r t c h safe.1, b.correct s r t c h safe.2, Value.eval, Arithmetic.eval]
    omega

instance [a : SignedExpression P x] [b : SignedExpression P y] :
    SignedExpression P (.binary op x y) where
  code := .bin (signedOp op) a.code b.code
  negative := .bin .intSub (.lit 0) (.bin (signedOp op) a.code b.code)
  positivePart := .toNat (.bin (signedOp op) a.code b.code)
  negativePart := .toNat (.bin .intSub (.lit 0) (.bin (signedOp op) a.code b.code))
  cost := by
    have := a.cost
    have := b.cost
    cases op <;> simp_all [Expr.cost, signedOp, Op.cost, SignedValue.credits, SignedValue.costs]
    all_goals omega
  negativeCost := by
    have := a.cost
    have := b.cost
    cases op <;> simp_all [Expr.cost, signedOp, Op.cost, SignedValue.credits, SignedValue.costs]
    all_goals omega
  positivePartCost := by
    have := a.cost
    have := b.cost
    cases op <;> simp_all [Expr.cost, signedOp, Op.cost, SignedValue.credits, SignedValue.costs]
    all_goals omega
  negativePartCost := by
    have := a.cost
    have := b.cost
    cases op <;> simp_all [Expr.cost, signedOp, Op.cost, SignedValue.credits, SignedValue.costs]
    all_goals omega
  correct s r t c h safe := by
    cases op <;> simp [Expr.eval, signedOp, Op.eval, Op.machine, Integer.BinOp.eval,
      a.correct s r t c h safe.1, b.correct s r t c h safe.2,
      SignedValue.eval, Arithmetic.evalInt]
  negativeCorrect s r t c h safe := by
    cases op <;> simp [Expr.eval, Ty.normalize, signedOp, Op.eval, Op.machine, Integer.BinOp.eval,
      a.correct s r t c h safe.1, b.correct s r t c h safe.2,
      SignedValue.eval, Arithmetic.evalInt]
  positivePartCorrect s r t c h safe := by
    cases op <;> simp [Expr.eval, signedOp, Op.eval, Op.machine, Integer.BinOp.eval,
      a.correct s r t c h safe.1, b.correct s r t c h safe.2,
      SignedValue.eval, Arithmetic.evalInt] <;> omega
  negativePartCorrect s r t c h safe := by
    cases op <;> simp [Expr.eval, Ty.normalize, signedOp, Op.eval, Op.machine, Integer.BinOp.eval,
      a.correct s r t c h safe.1, b.correct s r t c h safe.2,
      SignedValue.eval, Arithmetic.evalInt] <;> omega

instance [f : Focus P p Q] [q : SignedStorage Q] [e : SignedExpression P value] :
    Primitive 24 P (signedAssign p value) P where
  code := .assign q.register e.code
  correct a safe r s saved rep := by
    obtain ⟨r', c', h', restore⟩ := f.open_ a r s saved rep
    obtain ⟨hq, hw⟩ := q.update _ _ _ _ h' (value.eval a)
    obtain ⟨total, hp, writes, eq⟩ := restore _ _ c' hq hw
    have ev := Eval.assign q.register e.code s
    rw [e.correct a r s saved rep safe] at ev
    refine ⟨_, _, total, ev, hp, writes, ?_⟩
    have := e.cost
    simp only [signedAssign]
    omega

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
    have := e.cost
    simp only [assign]
    omega

instance [a : Expression P (.scalar x)] [b : Expression P (.scalar y)] :
    TestImplementation 24 P (compare op x y) where
  condition := ⟨.word, match op with | .lt => .lt | .le => .le | .eq => .eq, a.code, b.code⟩
  correct s r t c h := by
    cases op <;> simp [Condition.eval, Comparison.eval, Prototype.Composition.compare, Relation.eval,
      a.correct s r t c h trivial, b.correct s r t c h trivial, Value.eval]
  cost := by
    have := a.cost
    have := b.cost
    simp only [Value.credits] at *
    simp only [Condition.cost]
    omega

instance [a : SignedExpression P (.scalar x)] [b : SignedExpression P (.scalar y)] :
    TestImplementation 24 P (compareSigned op x y) where
  condition := ⟨.integer, match op with | .lt => .lt | .le => .le | .eq => .eq, a.code, b.code⟩
  correct s r t c h := by
    cases op <;> simp [Condition.eval, Comparison.eval, compareSigned, Relation.evalInt,
      a.correct s r t c h trivial, b.correct s r t c h trivial, SignedValue.eval]
  cost := by
    have := a.cost
    have := b.cost
    simp only [SignedValue.credits, SignedValue.costs] at *
    simp only [Condition.cost]
    omega

end AlgoLib.Experimental.RAM.Native
