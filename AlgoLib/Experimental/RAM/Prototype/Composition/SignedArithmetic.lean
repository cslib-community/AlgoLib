/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Expressions
import Mathlib.Tactic

/-!
# Exact signed arithmetic through the temporary natural-valued compiler IR

A canonical pair `(positive, negative)` represents their integer difference. These
lemmas justify finite arithmetic expansions; they do not add trusted host operations.
The representation is private to the implementation, not part of source contracts.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.SignedArithmetic

@[simp] theorem difference (x : Int) : (x.toNat : Int) - (-x).toNat = x := by omega

def calculate (op : Arithmetic) (ap an bp bn : Nat) : Nat × Nat :=
  match op with
  | .add => ((ap + bp) - (an + bn), (an + bn) - (ap + bp))
  | .sub => ((ap + bn) - (an + bp), (an + bp) - (ap + bn))
  | .mul => ((ap * bp + an * bn) - (ap * bn + an * bp),
      (ap * bn + an * bp) - (ap * bp + an * bn))

theorem correct (op : Arithmetic) (a b : Int) :
    calculate op a.toNat (-a).toNat b.toNat (-b).toNat =
      ((op.evalInt a b).toNat, (-(op.evalInt a b)).toNat) := by
  cases op with
  | add => simp only [calculate, Arithmetic.evalInt]; apply Prod.ext <;> dsimp <;> omega
  | sub => simp only [calculate, Arithmetic.evalInt]; apply Prod.ext <;> dsimp <;> omega
  | mul =>
    have eq : a * b =
        ((a.toNat * b.toNat + (-a).toNat * (-b).toNat : Nat) : Int) -
        ((a.toNat * (-b).toNat + (-a).toNat * b.toNat : Nat) : Int) := by
      calc
        a * b = ((a.toNat : Int) - (-a).toNat) * ((b.toNat : Int) - (-b).toNat) := by
          rw [difference, difference]
        _ = _ := by push_cast; ring
    simp only [calculate, Arithmetic.evalInt]
    rw [eq]
    apply Prod.ext <;> dsimp <;> omega

end AlgoLib.Experimental.RAM.Prototype.Composition.SignedArithmetic
