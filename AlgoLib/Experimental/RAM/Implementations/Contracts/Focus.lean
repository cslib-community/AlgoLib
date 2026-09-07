/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Contracts.Ownership
import AlgoLib.Experimental.RAM.Language.Expressions

/-!
# Shared ownership-directed path focusing

A source path borrows a component and reconstructs the surrounding representation
after a local update. The same law works for natural and native integer stores;
unrelated values and their saved potential remain private.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Ownership
open Prototype.Composition (Path)
variable {M : Model}

/-- A typed path borrows a represented component and can put an updated component back. -/
class Focus (P : Representation M S) (p : Path S A) (Q : outParam (Representation M A)) where
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

instance (P : Representation M A) [f : Focus Q p T] : Focus (P.sep Q) (.right p) T where
  open_ a r s saved rep := by
    obtain ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨r, c, hr, restore⟩ := f.open_ a.2 r₂ s c₂ hq
    refine ⟨r, c, hr, ?_⟩
    intro b t left hb hw
    obtain ⟨total, ht, hw', hc⟩ := restore b t left hb hw
    exact ⟨c₁ + total, ⟨r₁, r₂, c₁, total, hd, rfl, rfl, P.frame hp hd.symm hw', ht⟩,
      hw'.mono Finset.subset_union_right, by omega⟩

end AlgoLib.Experimental.RAM.Ownership
