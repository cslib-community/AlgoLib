/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Stack
import AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation

/-!
# Array-backed stack removal

Buffers already implement constant-cost stack push. Removal decrements the length
and reads the last occupied cell into a borrowed scalar. Both the scalar and the
buffer are exclusively owned; all other resources and their potential are framed.
Inactive payloads need not be erased.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.StackImplementation
open Checked.Language BufferImplementation

theorem dropLast_valid (l : Layout) (xs : List Nat) (s : Store)
    (valid : Valid l false xs s) :
    Valid l false xs.dropLast (s.set l.lengthVar (xs.length - 1)) := by
  have cap := valid.1
  refine ⟨by simp; omega, by simp [Store.set], ?_, by simp⟩
  intro i hi
  have hi' : i < xs.length - 1 := by simpa using hi
  have hb : i < xs.length := by omega
  simpa [Store.set, List.getElem!_eq_getElem?_getD, List.getElem?_dropLast,
    hi', getElem?_pos xs i hb] using valid.2.2.1 i hb

@[reducible] def popImplementation (l : Layout) [q : ScalarStorage Q] :
    Primitive 24 ((representation l false).sep Q) Stack.pop
      ((representation l false).sep Q) where
  code := .seq (.assign l.lengthVar (decrease l))
    (.assign q.register (.load (address l)))
  correct input pre r s saved rep := by
    obtain ⟨rp, rq, cp, cq, disjoint, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨rfl, valid, rfl⟩ := hp
    have pos : 0 < input.1.length := by simpa [Stack.pop, List.length_pos_iff] using pre
    let t := s.set l.lengthVar (input.1.length - 1)
    have first : Eval (.assign l.lengthVar (decrease l)) s 4 t := by
      simpa [t, decrease, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval,
        valid.2.1] using Eval.assign l.lengthVar (decrease l) s
    have frame : Q.holds input.2 rq t cq :=
      Q.frame hq disjoint (Writes.set s _ (input.1.length - 1) (length_owned l))
    have cellValue : t.heap (l.base + (input.1.length - 1)) = input.1.getLastD 0 := by
      rw [show t.heap = s.heap from rfl, valid.2.2.1 _ (by omega)]
      simp only [List.getElem!_eq_getElem?_getD, List.getLastD_eq_getLast?,
        List.getLast?_eq_getElem?]
      rfl
    have read : (Expr.load (address l)).eval t = input.1.getLastD 0 := by
      simpa [address, Expr.eval, t, Store.set, Op.eval, Op.machine, Checked.BinOp.eval]
        using cellValue
    have second := Eval.assign q.register (.load (address l)) t
    rw [read] at second
    obtain ⟨hq', changed⟩ := q.update input.2 rq t cq frame (input.1.getLastD 0)
    have hp' : (representation l false).holds input.1.dropLast l.footprint t 0 :=
      ⟨rfl, dropLast_valid l input.1 s valid, rfl⟩
    refine ⟨9, _, 0 + cq, .seq first second,
      ⟨l.footprint, rq, 0, cq, disjoint, rfl, rfl,
        (representation l false).frame hp' disjoint.symm changed, hq'⟩,
      (Writes.mono Finset.subset_union_left (Writes.set s _ _ (length_owned l))).trans
        (changed.mono Finset.subset_union_right), ?_⟩
    simp [Stack.pop, potential]

instance (l : Layout) [ScalarStorage Q] :
    Primitive 24 ((representation l false).sep Q) Stack.pop
      ((representation l false).sep Q) := popImplementation l

end AlgoLib.Experimental.RAM.Prototype.Composition.StackImplementation
