/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Natural.Storage
import AlgoLib.Experimental.RAM.Implementations.Contracts.LocalRefinement

/-!
# Private method-local storage

Scratch values are existentially hidden at a method boundary. Initialization is
executable and paid for; leaving the method forgets only their mathematical values,
not ownership or saved potential. Clients never pass initial local values or see
local variables in their result type. This is fixed private storage, not allocation.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

abbrev Representation.hide (P : Representation S) (Q : Representation L) : Representation S :=
  Ownership.Representation.hide P Q

abbrev Initialize (Q : Representation L) [Locals L] :=
  Ownership.Initialize implementationBackend Q

instance (v : Var .word) : Initialize (Storage.scalar v) where
  code := .assign v (.lit 0)
  correct a r s c h := by
    obtain ⟨hp, hw⟩ := ScalarStorage.update a r s c h 0
    exact ⟨2, _, .assign _ _ _, hp, hw, by decide⟩

/-- Direct indexing can surround calls with their own private local storage. -/
instance (Q : Representation L) [p : ArrayStorage P] : ArrayStorage (P.hide Q) where
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

end AlgoLib.Experimental.RAM.Prototype.Composition
