/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.SignedStorage

/-!
# Owned interleaved signed arrays

Each element uses two canonical natural lanes in the compiler IR. Adjacent cells
avoid any input-size specialization of generated code. Three private registers
stage an index and both result lanes before a write, including self-indexing writes.
All representation and framing proofs stay below the source obligation API.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.SignedArrays
open Checked.Language

structure Layout where
  registers : SignedStorageImpl.Layout
  base : Nat
  capacity : Nat

def Layout.footprint (l : Layout) : Footprint :=
  l.registers.footprint ∪
    (Finset.range (2 * l.capacity)).image (fun i => Location.heap (l.base + i))

theorem Layout.regOwned (l : Layout) (i : Fin 4) :
    Location.register .word (l.registers.register i).name ∈ l.footprint :=
  Finset.mem_union_left _ (l.registers.owned i)

theorem Layout.heapOwned (l : Layout) (hi : i < 2 * l.capacity) :
    Location.heap (l.base + i) ∈ l.footprint :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)

def representation (l : Layout) : Representation (Array Int) where
  holds a r s c := r = l.footprint ∧ a.size ≤ l.capacity ∧
    s.vars .word (l.registers.register 0).name = a.size ∧
    (∀ i, i < a.size → s.heap (l.base + 2 * i) = (a[i]!).toNat ∧
      s.heap (l.base + (1 + 2 * i)) = (-(a[i]!)).toNat) ∧ c = 0
  locality := by
    rintro a r s t c agree ⟨rfl, hb, hn, ha, hc⟩
    refine ⟨rfl, hb, (agree _ (l.regOwned 0)).trans hn, ?_, hc⟩
    intro i hi
    exact ⟨(agree _ (l.heapOwned (by omega))).trans (ha i hi).1,
      (agree _ (l.heapOwned (by omega))).trans (ha i hi).2⟩

private theorem stage (l : Layout) (i : Fin 4) (hn : 0 ≠ i)
    (a r s c) (h : (representation l).holds a r s c) (b : Nat) :
    (representation l).holds a r (s.set (l.registers.register i) b) c ∧
      Writes r s (s.set (l.registers.register i) b) := by
  obtain ⟨rfl, hb, hs, ha, hc⟩ := h
  exact ⟨⟨rfl, hb, by simpa [Store.set, l.registers.ne hn] using hs, ha, hc⟩,
    Writes.set _ _ _ (l.regOwned i)⟩

private theorem update (l : Layout) (a r s c) (h : (representation l).holds a r s c)
    (i : Nat) (b : Int) (hi : i < a.size) :
    (representation l).holds (a.set! i b) r
      ((s.write (l.base + 2 * i) b.toNat).write (l.base + (1 + 2 * i)) (-b).toNat) c ∧
    Writes r s ((s.write (l.base + 2 * i) b.toNat).write (l.base + (1 + 2 * i)) (-b).toNat) := by
  obtain ⟨rfl, hb, hn, ha, hc⟩ := h
  refine ⟨⟨rfl, by simpa, by simpa using hn, ?_, hc⟩,
    (Writes.write _ _ _ (l.heapOwned (by omega))).trans
      (Writes.write _ _ _ (l.heapOwned (by omega)))⟩
  intro j hj
  have hj' : j < a.size := by simpa using hj
  obtain ⟨hp, hm⟩ := ha j hj'
  by_cases eq : j = i
  · subst j
    simp [Store.write, Array.set!, getElem!_pos,
      hi]
  · have h2 : 2 * j ≠ 1 + 2 * i := by omega
    have h3 : 1 + 2 * j ≠ 2 * i := by omega
    simp [Store.write, Array.set!, getElem!_pos,
      hj', hp, hm, h2, h3, eq, Ne.symm eq]

instance (l : Layout) : MutableSignedArrayStorage (representation l) where
  positiveBase := l.base
  negativeBase := l.base + 1
  size := l.registers.register 0
  length _ _ _ _ h := h.2.2.1
  readPositive _ _ _ _ h i hi := by simpa using (h.2.2.2.1 i hi).1
  readNegative _ _ _ _ h i hi := by simpa [Nat.add_assoc] using (h.2.2.2.1 i hi).2
  temporaryIndex := l.registers.register 1
  temporaryPositive := l.registers.register 2
  temporaryNegative := l.registers.register 3
  indexPositiveDistinct := l.registers.ne (by decide)
  indexNegativeDistinct := l.registers.ne (by decide)
  valueDistinct := l.registers.ne (by decide)
  stageIndex := stage l 1 (by decide)
  stagePositive := stage l 2 (by decide)
  stageNegative := stage l 3 (by decide)
  finish := .seq
    (.write (.bin .offset (.lit l.base) (.bin .mul (.lit 2) (.var (l.registers.register 1))))
      (.var (l.registers.register 2)))
    (.write (.bin .offset (.lit (l.base + 1)) (.bin .mul (.lit 2) (.var (l.registers.register 1))))
      (.var (l.registers.register 3)))
  finishCorrect a r s c h i b hi idx pos neg := by
    obtain ⟨post, writes⟩ := update l a r s c h i b hi
    refine ⟨14, _, .seq (i := 7) (j := 7)
      (u := s.write (l.base + 2 * i) b.toNat) ?_ ?_, post, writes, by decide⟩
    · simpa [Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, idx, pos] using
        Eval.write (.bin .offset (.lit l.base) (.bin .mul (.lit 2) (.var (l.registers.register 1))))
          (.var (l.registers.register 2)) s
    · simpa [Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, Store.write,
        idx, neg, Nat.add_assoc] using
        Eval.write (.bin .offset (.lit (l.base + 1))
          (.bin .mul (.lit 2) (.var (l.registers.register 1))))
          (.var (l.registers.register 3)) (s.write (l.base + 2 * i) b.toNat)

instance (l : Layout) : Decoder (representation l) where
  decode s := Array.ofFn (fun i : Fin (s.vars .word (l.registers.register 0).name) =>
    (s.heap (l.base + 2 * i) : Int) - s.heap (l.base + (1 + 2 * i)))
  correct a r s c h := by
    apply Array.ext
    · simpa using h.2.2.1
    · intro i hi hj
      obtain ⟨hp, hn⟩ := h.2.2.2.1 i hj
      simp [getElem!_pos, hj, hp, hn]

def encoder (l : Layout) : Encoder (representation l) where
  footprint := l.footprint
  requires a := a.size ≤ l.capacity
  saved _ := 0
  store a := ⟨fun _ _ => a.size, fun i =>
    if (i - l.base) % 2 = 0 then (a.getD ((i - l.base) / 2) 0).toNat
    else (-(a.getD ((i - l.base) / 2) 0)).toNat⟩
  correct a h := ⟨rfl, h, rfl, fun i hi => by
    simp [Array.getElem!_eq_getD, Nat.add_div, Nat.add_mod], rfl⟩

end AlgoLib.Experimental.RAM.Prototype.Composition.SignedArrays

namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

instance (Q : Representation L) [p : MutableSignedArrayStorage P] :
    MutableSignedArrayStorage (P.hide Q) where
  positiveBase := p.positiveBase
  negativeBase := p.negativeBase
  size := p.size
  temporaryIndex := p.temporaryIndex
  temporaryPositive := p.temporaryPositive
  temporaryNegative := p.temporaryNegative
  indexPositiveDistinct := p.indexPositiveDistinct
  indexNegativeDistinct := p.indexNegativeDistinct
  valueDistinct := p.valueDistinct
  length a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.length _ _ _ _ hp
  readPositive a r s c h i hi := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.readPositive _ _ _ _ hp i hi
  readNegative a r s c h i hi := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.readNegative _ _ _ _ hp i hi
  stageIndex a r s c h b := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨hp', hw⟩ := p.stageIndex _ _ _ _ hp b
    exact ⟨⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp', Q.frame hq hd hw⟩,
      hw.mono Finset.subset_union_left⟩
  stagePositive a r s c h b := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨hp', hw⟩ := p.stagePositive _ _ _ _ hp b
    exact ⟨⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp', Q.frame hq hd hw⟩,
      hw.mono Finset.subset_union_left⟩
  stageNegative a r s c h b := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨hp', hw⟩ := p.stageNegative _ _ _ _ hp b
    exact ⟨⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp', Q.frame hq hd hw⟩,
      hw.mono Finset.subset_union_left⟩
  finish := p.finish
  finishCorrect a r s c h i b hi idx hp hn := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, ha, hq⟩ := h
    obtain ⟨k, t, exec, post, writes, cost⟩ :=
      p.finishCorrect _ _ _ _ ha i b hi idx hp hn
    exact ⟨k, t, exec, ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, post,
      Q.frame hq hd writes⟩, writes.mono Finset.subset_union_left, cost⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
