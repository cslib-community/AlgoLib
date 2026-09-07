/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Natural.Encoding
import AlgoLib.Experimental.RAM.Implementations.Natural.SignedImplementation

/-!
# Private canonical signed scalar representation

The current compiler intermediate uses four separately owned natural registers:
two canonical value lanes and two staging lanes. The staging lanes have no logical
meaning and may change while preserving the abstract integer. The Int-RAM backend
executes the resulting instructions. No representation facts appear in client VCs.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.SignedStorageImpl
open Checked.Language

structure Layout where
  register : Fin 4 → Var .word
  distinct : Function.Injective (fun i => (register i).name)

def Layout.named (stem : String) : Layout where
  register := ![⟨stem ++ ".positive"⟩, ⟨stem ++ ".negative"⟩,
    ⟨stem ++ ".temporaryPositive"⟩, ⟨stem ++ ".temporaryNegative"⟩]
  distinct := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

theorem Layout.ne (l : Layout) {i j : Fin 4} (h : i ≠ j) :
    (l.register i).name ≠ (l.register j).name := fun eq => h (l.distinct eq)

def Layout.footprint (l : Layout) : Footprint :=
  Finset.univ.image (fun i => Location.register .word (l.register i).name)

theorem Layout.owned (l : Layout) (i : Fin 4) :
    Location.register .word (l.register i).name ∈ l.footprint :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

def representation (l : Layout) : Representation Int where
  holds a r s c := r = l.footprint ∧ s.vars .word (l.register 0).name = a.toNat ∧
    s.vars .word (l.register 1).name = (-a).toNat ∧ c = 0
  locality := by
    rintro a r s t c agree ⟨rfl, hp, hn, hc⟩
    exact ⟨rfl, (agree _ (l.owned 0)).trans hp, (agree _ (l.owned 1)).trans hn, hc⟩

private theorem stage (l : Layout) (i : Fin 4) (h0 : 0 ≠ i) (h1 : 1 ≠ i)
    (a r s c) (h : (representation l).holds a r s c) (b : Nat) :
    (representation l).holds a r (s.set (l.register i) b) c ∧
      Writes r s (s.set (l.register i) b) := by
  obtain ⟨rfl, hp, hn, hc⟩ := h
  exact ⟨⟨rfl, by simpa [Store.set, l.ne h0] using hp,
    by simpa [Store.set, l.ne h1] using hn, hc⟩, Writes.set _ _ _ (l.owned i)⟩

instance (l : Layout) : SignedStorage (representation l) where
  positive := l.register 0
  negative := l.register 1
  temporaryPositive := l.register 2
  temporaryNegative := l.register 3
  temporaryDistinct := l.ne (by decide)
  readPositive _ _ _ _ h := h.2.1
  readNegative _ _ _ _ h := h.2.2.1
  stagePositive := stage l 2 (by decide) (by decide)
  stageNegative := stage l 3 (by decide) (by decide)
  finish := .seq (.assign (l.register 0) (.var (l.register 2)))
    (.assign (l.register 1) (.var (l.register 3)))
  finishCorrect a r s c h b hp hn := by
    obtain ⟨rfl, _, _, hc⟩ := h
    refine ⟨4, (s.set (l.register 0) b.toNat).set (l.register 1) (-b).toNat,
      .seq (u := s.set (l.register 0) b.toNat) (i := 2) (j := 2) ?_ ?_, ⟨rfl, ?_, ?_, hc⟩,
      (Writes.set _ _ _ (l.owned 0)).trans (Writes.set _ _ _ (l.owned 1)), by decide⟩
    · simpa [Expr.eval, hp] using Eval.assign (l.register 0) (.var (l.register 2)) s
    · simpa [Expr.eval, Store.set, l.ne (show (3 : Fin 4) ≠ 0 by decide), hn] using
        Eval.assign (l.register 1) (.var (l.register 3)) (s.set (l.register 0) b.toNat)
    · simp [Store.set, l.ne (show (0 : Fin 4) ≠ 1 by decide)]
    · simp [Store.set]

instance (l : Layout) : Decoder (representation l) where
  decode s := (s.vars .word (l.register 0).name : Int) - s.vars .word (l.register 1).name
  correct _ _ _ _ h := by rw [h.2.1, h.2.2.1]; exact SignedArithmetic.difference _

instance (l : Layout) : Initialize (representation l) where
  code := .seq (.assign (l.register 0) (.lit 0)) (.assign (l.register 1) (.lit 0))
  correct a r s c h := by
    obtain ⟨rfl, _, _, hc⟩ := h
    refine ⟨4, _, .seq (.assign _ _ _) (.assign _ _ _), ⟨rfl, ?_, ?_, hc⟩,
      (Writes.set _ _ _ (l.owned 0)).trans (Writes.set _ _ _ (l.owned 1)), by decide⟩
    · simp [Store.set, Expr.eval, l.ne (show (0 : Fin 4) ≠ 1 by decide), Locals.initial]
    · simp [Store.set, Expr.eval, Locals.initial]

def encoder (l : Layout) : Encoder (representation l) where
  footprint := l.footprint
  requires _ := True
  saved _ := 0
  store a := ⟨fun _ name => if name = (l.register 0).name then a.toNat
    else if name = (l.register 1).name then (-a).toNat else 0, fun _ => 0⟩
  correct a _ := ⟨rfl, by simp, by simp [l.ne (show (1 : Fin 4) ≠ 0 by decide)], rfl⟩

end AlgoLib.Experimental.RAM.Prototype.Composition.SignedStorageImpl

namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

/-- Default signed scalar input/output storage, with private staging lanes. -/
abbrev signedEncoder (name : String) :=
  SignedStorageImpl.encoder (SignedStorageImpl.Layout.named name)

instance (Q : Representation L) [p : SignedStorage P] : SignedStorage (P.hide Q) where
  positive := p.positive
  negative := p.negative
  temporaryPositive := p.temporaryPositive
  temporaryNegative := p.temporaryNegative
  temporaryDistinct := p.temporaryDistinct
  readPositive a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.readPositive _ _ _ _ hp
  readNegative a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.readNegative _ _ _ _ hp
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
  finishCorrect a r s c h b hp hn := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, ha, hq⟩ := h
    obtain ⟨k, t, exec, post, writes, cost⟩ := p.finishCorrect _ _ _ _ ha b hp hn
    exact ⟨k, t, exec, ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, post,
      Q.frame hq hd writes⟩, writes.mono Finset.subset_union_left, cost⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
