/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Native.ScalarStorage
import AlgoLib.Experimental.RAM.Prototype.Composition.Native.ArrayStorage
import AlgoLib.Experimental.RAM.Prototype.Composition.LocalRefinement

/-!
# Private native local storage

Both Nat and Int locals initialize with a direct native assignment. The shared
scope contracts retain the existing source allowances and automatically frame
other storage. Array and scalar interfaces remain available through hidden locals,
so source expressions and procedure calls can compose without layout obligations.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Native
open Prototype.Composition (Locals)

abbrev Representation.hide (P : Representation S) (Q : Representation L) : Representation S :=
  Ownership.Representation.hide P Q

abbrev Initialize (Q : Representation L) [Locals L] :=
  Ownership.Initialize implementationBackend Q

instance (v : Var .word) : Initialize (naturalScalar v) where
  code := .assign v (.lit 0)
  correct a r s c h := by
    obtain ⟨hp, hw⟩ := ScalarStorage.update a r s c h 0
    exact ⟨2, _, .assign _ _ _, hp, hw, by decide⟩

instance (v : Var .integer) : Initialize (signedScalar v) where
  code := .assign v (.lit 0)
  correct a r s c h := by
    obtain ⟨hp, hw⟩ := SignedStorage.update a r s c h 0
    exact ⟨2, _, .assign _ _ _, hp, hw, by decide⟩

instance (Q : Representation L) [p : ScalarStorage P] : ScalarStorage (P.hide Q) where
  register := p.register
  read a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.read a r₁ s c₁ hp
  update a r s c h b := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨hp', hw⟩ := p.update a r₁ s c₁ hp b
    exact ⟨⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp', Q.frame hq hd hw⟩,
      hw.mono Finset.subset_union_left⟩

instance (Q : Representation L) [p : SignedStorage P] : SignedStorage (P.hide Q) where
  register := p.register
  read a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.read a r₁ s c₁ hp
  update a r s c h b := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨hp', hw⟩ := p.update a r₁ s c₁ hp b
    exact ⟨⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp', Q.frame hq hd hw⟩,
      hw.mono Finset.subset_union_left⟩

instance {A : Type} [Inhabited A] (encode : A → Int) (P : Representation (Array A)) (Q : Representation L)
    [p : ArrayStorage encode P] : ArrayStorage encode (P.hide Q) where
  base := p.base
  size := p.size
  length a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.length a r₁ s c₁ hp
  read a r s c h i hi := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.read a r₁ s c₁ hp i hi
  update a r s c h i b hi := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨hp', hw⟩ := p.update a r₁ s c₁ hp i b hi
    exact ⟨⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp', Q.frame hq hd hw⟩,
      hw.mono Finset.subset_union_left⟩

end AlgoLib.Experimental.RAM.Native
