/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Native.ArrayExpressions

/-!
# Relocatable single-cell native arrays

The layout owns a size register and a finite consecutive heap region. Natural and
signed arrays share this representation construction; their only difference is
whether an element embeds Nat into Int or is already Int. Unused capacity is
private and unconstrained. Updates preserve size and every other owned component.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Native

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

/-- The functional representation is uniform in its mathematical element type. -/
def array {A : Type} [Inhabited A] (encode : A → Int) (l : ArrayLayout) :
    Representation (Array A) where
  holds a r s c := r = l.footprint ∧ a.size ≤ l.capacity ∧
    s.vars .word l.size.name = (a.size : Int) ∧
    (∀ i, i < a.size → s.heap (l.base + i) = encode a[i]!) ∧ c = 0
  locality := by
    rintro a r s t c h ⟨rfl, hb, hn, ha, hc⟩
    refine ⟨rfl, hb,
      (h (.register .word l.size.name) (by simp [ArrayLayout.footprint])).trans hn, ?_, hc⟩
    intro i hi
    exact (h _ (l.owned (hi.trans_le hb))).trans (ha i hi)

instance {A : Type} [Inhabited A] (encode : A → Int) (l : ArrayLayout) :
    ArrayStorage encode (array encode l) where
  base := l.base
  size := l.size
  length _ _ _ _ h := h.2.2.1
  read _ _ _ _ h := h.2.2.2.1
  update a r s c h i b hi := by
    obtain ⟨rfl, hb, hn, ha, hc⟩ := h
    refine ⟨⟨rfl, by simpa, by simpa using hn, ?_, hc⟩,
      writes_write _ _ _ (l.owned (by omega))⟩
    intro j hj
    have hj' : j < a.size := by simpa using hj
    by_cases hij : i = j
    · subst j
      simp [Store.write, Array.set!, getElem!_pos, Array.getElem_setIfInBounds, hi]
    · simp [Store.write, Function.update_apply, Array.set!, getElem!_pos,
        Array.getElem_setIfInBounds, hj', ha j hj', hij, Ne.symm hij]

abbrev naturalArray (l : ArrayLayout) : Representation (Array Nat) := array Int.ofNat l
abbrev signedArray (l : ArrayLayout) : Representation (Array Int) := array id l

end AlgoLib.Experimental.RAM.Native
