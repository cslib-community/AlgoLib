/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.ExpressionImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.SignedArithmetic

/-!
# Certified signed expression and storage interfaces

Signed source values have integer semantics. The temporary Nat compiler IR uses
canonical positive/negative lanes with private staging registers. Staging preserves
the abstract value, so expressions are evaluated before the destination changes.
The existing Int-RAM interpreter executes the resulting certified instruction code.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

class SignedStorage (P : Representation Int) where
  positive : Var .word
  negative : Var .word
  temporaryPositive : Var .word
  temporaryNegative : Var .word
  temporaryDistinct : temporaryPositive.name ≠ temporaryNegative.name
  readPositive : ∀ a r s c, P.holds a r s c → s.vars .word positive.name = a.toNat
  readNegative : ∀ a r s c, P.holds a r s c → s.vars .word negative.name = (-a).toNat
  stagePositive : ∀ a r s c, P.holds a r s c → ∀ b,
    P.holds a r (s.set temporaryPositive b) c ∧ Writes r s (s.set temporaryPositive b)
  stageNegative : ∀ a r s c, P.holds a r s c → ∀ b,
    P.holds a r (s.set temporaryNegative b) c ∧ Writes r s (s.set temporaryNegative b)
  finish : Cmd
  finishCorrect : ∀ a r s c, P.holds a r s c → ∀ (b : Int),
    s.vars .word temporaryPositive.name = b.toNat →
    s.vars .word temporaryNegative.name = (-b).toNat →
    ∃ k t, Eval finish s k t ∧ P.holds b r t c ∧ Writes r s t ∧ k ≤ 4

class SignedArrayStorage (P : Representation (Array Int)) where
  positiveBase : Nat
  negativeBase : Nat
  size : Var .word
  length : ∀ a r s c, P.holds a r s c → s.vars .word size.name = a.size
  readPositive : ∀ a r s c, P.holds a r s c → ∀ i, i < a.size →
    s.heap (positiveBase + 2 * i) = (a[i]!).toNat
  readNegative : ∀ a r s c, P.holds a r s c → ∀ i, i < a.size →
    s.heap (negativeBase + 2 * i) = (-(a[i]!)).toNat

/-- A mutable array stages all expression results before changing either value lane. -/
class MutableSignedArrayStorage (P : Representation (Array Int)) extends SignedArrayStorage P where
  temporaryIndex : Var .word
  temporaryPositive : Var .word
  temporaryNegative : Var .word
  indexPositiveDistinct : temporaryIndex.name ≠ temporaryPositive.name
  indexNegativeDistinct : temporaryIndex.name ≠ temporaryNegative.name
  valueDistinct : temporaryPositive.name ≠ temporaryNegative.name
  stageIndex : ∀ a r s c, P.holds a r s c → ∀ b,
    P.holds a r (s.set temporaryIndex b) c ∧ Writes r s (s.set temporaryIndex b)
  stagePositive : ∀ a r s c, P.holds a r s c → ∀ b,
    P.holds a r (s.set temporaryPositive b) c ∧ Writes r s (s.set temporaryPositive b)
  stageNegative : ∀ a r s c, P.holds a r s c → ∀ b,
    P.holds a r (s.set temporaryNegative b) c ∧ Writes r s (s.set temporaryNegative b)
  finish : Cmd
  finishCorrect : ∀ a r s c, P.holds a r s c → ∀ (i : Nat) (b : Int),
    i < a.size → s.vars .word temporaryIndex.name = i →
    s.vars .word temporaryPositive.name = b.toNat →
    s.vars .word temporaryNegative.name = (-b).toNat →
    ∃ k t, Eval finish s k t ∧ P.holds (a.set! i b) r t c ∧ Writes r s t ∧ k ≤ 14

class SignedExpression (P : Representation S) (e : SignedValue S) where
  positive : Expr .word
  negative : Expr .word
  positiveCost : positive.cost = e.costs.1
  negativeCost : negative.cost = e.costs.2
  correct : ∀ a r s c, P.holds a r s c → e.Safe a →
    positive.eval s = (e.eval a).toNat ∧ negative.eval s = (-(e.eval a)).toNat

instance : SignedExpression P (.literal n) where
  positive := .lit n.toNat
  negative := .lit (-n).toNat
  positiveCost := rfl
  negativeCost := rfl
  correct _ _ _ _ _ _ := ⟨rfl, rfl⟩

instance [f : Focus P p Q] [q : SignedStorage Q] : SignedExpression P (.scalar p) where
  positive := .var q.positive
  negative := .var q.negative
  positiveCost := rfl
  negativeCost := rfl
  correct a r s c h _ := by
    obtain ⟨r', c', rep, _⟩ := f.open_ a r s c h
    exact ⟨q.readPositive _ _ _ _ rep, q.readNegative _ _ _ _ rep⟩

instance [e : SignedExpression P value] : Expression P (.toNat value) where
  code := e.positive
  cost := e.positiveCost
  correct a r s c h safe := (e.correct a r s c h safe).1

instance [e : SignedExpression P value] : Expression P (.checkedToNat value) where
  code := e.positive
  cost := e.positiveCost
  correct a r s c h safe := (e.correct a r s c h safe.1).1

instance [e : Expression P value] : SignedExpression P (.ofNat value) where
  positive := e.code
  negative := .lit 0
  positiveCost := e.cost
  negativeCost := rfl
  correct a r s c h safe := by simp [SignedValue.eval, Expr.eval, e.correct a r s c h safe]

instance [e : SignedExpression P value] : SignedExpression P (.neg value) where
  positive := e.negative
  negative := e.positive
  positiveCost := e.negativeCost
  negativeCost := e.positiveCost
  correct a r s c h safe := by
    simpa [SignedValue.eval] using (e.correct a r s c h safe).symm

private def binaryCode (op : Arithmetic) (ap an bp bn : Expr .word) : Expr .word × Expr .word :=
  match op with
  | .add => (.bin .sub (.bin .add ap bp) (.bin .add an bn),
      .bin .sub (.bin .add an bn) (.bin .add ap bp))
  | .sub => (.bin .sub (.bin .add ap bn) (.bin .add an bp),
      .bin .sub (.bin .add an bp) (.bin .add ap bn))
  | .mul => (.bin .sub (.bin .add (.bin .mul ap bp) (.bin .mul an bn))
        (.bin .add (.bin .mul ap bn) (.bin .mul an bp)),
      .bin .sub (.bin .add (.bin .mul ap bn) (.bin .mul an bp))
        (.bin .add (.bin .mul ap bp) (.bin .mul an bn)))

instance [a : SignedExpression P x] [b : SignedExpression P y] :
    SignedExpression P (.binary op x y) where
  positive := (binaryCode op a.positive a.negative b.positive b.negative).1
  negative := (binaryCode op a.positive a.negative b.positive b.negative).2
  positiveCost := by
    cases op <;> simp [binaryCode, Expr.cost, a.positiveCost, a.negativeCost,
      b.positiveCost, b.negativeCost, SignedValue.costs]; omega
  negativeCost := by
    cases op <;> simp [binaryCode, Expr.cost, a.positiveCost, a.negativeCost,
      b.positiveCost, b.negativeCost, SignedValue.costs]; omega
  correct s r t c h safe := by
    obtain ⟨ap, an⟩ := a.correct s r t c h safe.1
    obtain ⟨bp, bn⟩ := b.correct s r t c h safe.2
    have fact := SignedArithmetic.correct op (x.eval s) (y.eval s)
    cases op <;>
      simpa [binaryCode, SignedValue.eval, Expr.eval, Op.eval, Op.machine,
        Checked.BinOp.eval, ap, an, bp, bn, SignedArithmetic.calculate, Prod.mk.injEq] using fact

instance [f : Focus P p Q] [q : SignedArrayStorage Q] : Expression P (.intSize p) where
  code := .var q.size
  cost := rfl
  correct a r s c h _ := by
    obtain ⟨r', c', rep, _⟩ := f.open_ a r s c h
    exact q.length _ _ _ _ rep

instance [f : Focus P p Q] [q : SignedArrayStorage Q] [i : Expression P index] :
    SignedExpression P (.index p index) where
  positive := .load (.bin .offset (.lit q.positiveBase) (.bin .mul (.lit 2) i.code))
  negative := .load (.bin .offset (.lit q.negativeBase) (.bin .mul (.lit 2) i.code))
  positiveCost := by simp [Expr.cost, i.cost, SignedValue.costs]; omega
  negativeCost := by simp [Expr.cost, i.cost, SignedValue.costs]; omega
  correct a r s c h safe := by
    obtain ⟨r', c', rep, _⟩ := f.open_ a r s c h
    simp only [Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval,
      i.correct a r s c h safe.1, SignedValue.eval]
    exact ⟨q.readPositive _ _ _ _ rep _ safe.2, q.readNegative _ _ _ _ rep _ safe.2⟩

instance [f : Focus P p Q] [q : SignedStorage Q] [e : SignedExpression P value] :
    Primitive 24 P (signedAssign p value) P where
  code := .seq (.assign q.temporaryPositive e.positive)
    (.seq (.assign q.temporaryNegative e.negative) q.finish)
  correct a safe r s saved rep := by
    let x := value.eval a
    obtain ⟨owned, credit, inner, restore⟩ := f.open_ a r s saved rep
    obtain ⟨hp, wp⟩ := q.stagePositive _ _ _ _ inner x.toNat
    obtain ⟨total, outer, _, same⟩ := restore _ _ credit hp wp
    have ht : total = saved := by omega
    subst total
    rw [Path.set_get] at outer
    obtain ⟨hn, wn⟩ := q.stageNegative _ _ _ _ hp (-x).toNat
    obtain ⟨k, t, finish, result, wf, cost⟩ := q.finishCorrect _ _ _ _ hn x
      (by simp [Store.set, q.temporaryDistinct]) (by simp [Store.set])
    obtain ⟨left, final, writes, paid⟩ := restore _ _ credit result (wp.trans (wn.trans wf))
    have positive := Eval.assign q.temporaryPositive e.positive s
    rw [(e.correct a r s saved rep safe).1] at positive
    have negative := Eval.assign q.temporaryNegative e.negative (s.set q.temporaryPositive x.toNat)
    rw [(e.correct a r _ saved outer safe).2] at negative
    refine ⟨_, t, left, .seq positive (.seq negative finish), final, writes, ?_⟩
    simp only [signedAssign, SignedValue.credits, e.positiveCost, e.negativeCost]
    omega

instance [f : Focus P p Q] [q : MutableSignedArrayStorage Q]
    [i : Expression P index] [e : SignedExpression P value] :
    Primitive 24 P (signedWrite p index value) P where
  code := .seq (.assign q.temporaryIndex i.code)
    (.seq (.assign q.temporaryPositive e.positive)
      (.seq (.assign q.temporaryNegative e.negative) q.finish))
  correct a safe r s saved rep := by
    let x := value.eval a
    let j := index.eval a
    obtain ⟨owned, credit, inner, restore⟩ := f.open_ a r s saved rep
    obtain ⟨hi, wi⟩ := q.stageIndex _ _ _ _ inner j
    obtain ⟨total, outerI, _, same⟩ := restore _ _ credit hi wi
    have ht : total = saved := by omega
    subst total
    rw [Path.set_get] at outerI
    obtain ⟨hp, wp⟩ := q.stagePositive _ _ _ _ hi x.toNat
    obtain ⟨total, outerP, _, same⟩ := restore _ _ credit hp (wi.trans wp)
    have ht : total = saved := by omega
    subst total
    rw [Path.set_get] at outerP
    obtain ⟨hn, wn⟩ := q.stageNegative _ _ _ _ hp (-x).toNat
    obtain ⟨k, t, finish, result, wf, cost⟩ := q.finishCorrect _ _ _ _ hn j x safe.2.2
      (by simp [Store.set, q.indexPositiveDistinct, q.indexNegativeDistinct])
      (by simp [Store.set, q.valueDistinct]) (by simp [Store.set])
    obtain ⟨left, final, writes, paid⟩ := restore _ _ credit result
      (wi.trans (wp.trans (wn.trans wf)))
    have ei := Eval.assign q.temporaryIndex i.code s
    rw [i.correct a r s saved rep safe.1] at ei
    have ep := Eval.assign q.temporaryPositive e.positive (s.set q.temporaryIndex j)
    rw [(e.correct a r _ saved outerI safe.2.1).1] at ep
    have en := Eval.assign q.temporaryNegative e.negative
      ((s.set q.temporaryIndex j).set q.temporaryPositive x.toNat)
    rw [(e.correct a r _ saved outerP safe.2.1).2] at en
    refine ⟨_, t, left, .seq ei (.seq ep (.seq en finish)), final, writes, ?_⟩
    simp only [signedWrite, SignedValue.credits, i.cost, e.positiveCost, e.negativeCost]
    omega

instance [a : SignedExpression P (.scalar x)] [b : SignedExpression P (.scalar y)] :
    TestImplementation 24 P (compareSigned op x y) where
  condition := ⟨.word, match op with | .lt => .lt | .le => .le | .eq => .eq,
    .bin .add a.positive b.negative, .bin .add b.positive a.negative⟩
  correct s r t c h := by
    obtain ⟨ap, an⟩ := a.correct s r t c h trivial
    obtain ⟨bp, bn⟩ := b.correct s r t c h trivial
    cases op <;> simp [Condition.eval, Comparison.eval, Expr.eval, Op.eval,
      Op.machine, Checked.BinOp.eval, compareSigned, Relation.evalInt, ap, an, bp, bn,
      SignedValue.eval] <;> omega
  cost := by
    simp [Condition.cost, Expr.cost, a.positiveCost, a.negativeCost,
      b.positiveCost, b.negativeCost, SignedValue.costs]

end AlgoLib.Experimental.RAM.Prototype.Composition
