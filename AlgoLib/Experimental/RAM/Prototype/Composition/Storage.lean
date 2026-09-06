/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.ExpressionImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.Execution

/-!
# Default separately owned scalar and array storage

These implementations reserve finite footprints. Register names and heap bases are
linker configuration, never obligations in an algorithm proof. Array length stays
fixed under indexing; capacity and arbitrary inactive cells remain private.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Storage
open Checked.Language

def scalar (v : Var .word) : Representation Nat where
  holds a r s c := r = {.register .word v.name} ∧ s.vars .word v.name = a ∧ c = 0
  locality := by
    rintro a r s t c h ⟨rfl, ha, hc⟩
    exact ⟨rfl, (h (.register .word v.name) (by simp)).trans ha, hc⟩

instance (v : Var .word) : ScalarStorage (scalar v) where
  register := v
  read _ _ _ _ h := h.2.1
  update a r s c h b := by
    obtain ⟨rfl, _, rfl⟩ := h
    exact ⟨⟨rfl, by simp [Store.set], rfl⟩, Writes.set _ _ _ (by simp)⟩

instance (v : Var .word) : Decoder (scalar v) where
  decode s := s.vars .word v.name
  correct _ _ _ _ h := h.2.1

structure ArrayLayout where
  size : Var .word
  base : Nat
  capacity : Nat

def ArrayLayout.footprint (l : ArrayLayout) : Footprint :=
  {.register .word l.size.name} ∪
    (Finset.range l.capacity).image (fun i => Location.heap (l.base + i))

theorem ArrayLayout.owned (l : ArrayLayout) (hi : i < l.capacity) :
    Location.heap (l.base + i) ∈ l.footprint := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

def array (l : ArrayLayout) : Representation (Array Nat) where
  holds a r s c := r = l.footprint ∧ a.size ≤ l.capacity ∧
    s.vars .word l.size.name = a.size ∧ (∀ i, i < a.size → s.heap (l.base + i) = a[i]!) ∧ c = 0
  locality := by
    rintro a r s t c h ⟨rfl, hb, hn, ha, hc⟩
    refine ⟨rfl, hb,
      (h (.register .word l.size.name) (by simp [ArrayLayout.footprint])).trans hn, ?_, hc⟩
    intro i hi
    exact (h _ (l.owned (hi.trans_le hb))).trans (ha i hi)

instance (l : ArrayLayout) : ArrayStorage (array l) where
  base := l.base
  size := l.size
  length _ _ _ _ h := h.2.2.1
  read _ _ _ _ h := h.2.2.2.1
  update a r s c h i b hi := by
    obtain ⟨rfl, hb, hn, ha, hc⟩ := h
    refine ⟨⟨rfl, by simpa, by simpa using hn, ?_, hc⟩, Writes.write _ _ _ (l.owned (by omega))⟩
    intro j hj
    have hj' : j < a.size := by simpa using hj
    simp [Store.write, Function.update_apply, Array.set!, getElem!_pos,
      Array.getElem_setIfInBounds, hj', ha j hj', eq_comm]

instance (l : ArrayLayout) : Decoder (array l) where
  decode s := Array.ofFn (fun i : Fin (s.vars .word l.size.name) => s.heap (l.base + i))
  correct a r s c h := by
    apply Array.ext
    · simpa using h.2.2.1
    · intro i hi hj
      simpa [getElem!_pos, hj] using h.2.2.2.1 i hj

end AlgoLib.Experimental.RAM.Prototype.Composition.Storage
