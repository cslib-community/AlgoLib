/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Storage

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

def Representation.hide (P : Representation S) (Q : Representation L) : Representation S where
  holds a r s c := ∃ locals, (P.sep Q).holds (a, locals) r s c
  locality h rep := by
    obtain ⟨locals, rep⟩ := rep
    exact ⟨locals, (P.sep Q).locality h rep⟩

class Initialize (Q : Representation L) [locals : Locals L] where
  code : Cmd
  correct : ∀ a r s c, Q.holds a r s c → ∃ k t,
    Eval code s k t ∧ Q.holds locals.initial r t c ∧ Writes r s t ∧ k ≤ locals.credits

instance (v : Var .word) : Initialize (Storage.scalar v) where
  code := .assign v (.lit 0)
  correct a r s c h := by
    obtain ⟨hp, hw⟩ := ScalarStorage.update a r s c h 0
    exact ⟨2, _, .assign _ _ _, hp, hw, by decide⟩

instance [a : Locals A] [b : Locals B] (P : Representation A) (Q : Representation B)
    [p : Initialize P] [q : Initialize Q] :
    Initialize (P.sep Q) where
  code := .seq p.code q.code
  correct pair r s c h := by
    obtain ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨i, t, he, hp', hw, hi⟩ := p.correct pair.1 r₁ s c₁ hp
    obtain ⟨j, u, hf, hq', hv, hj⟩ := q.correct pair.2 r₂ t c₂ (Q.frame hq hd hw)
    exact ⟨i+j, u, .seq he hf,
      ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, P.frame hp' hd.symm hv, hq'⟩,
      (hw.mono Finset.subset_union_left).trans (hv.mono Finset.subset_union_right),
      Nat.add_le_add hi hj⟩

instance (P : Representation S) (Q : Representation L)
    [locals : Locals L] [q : Initialize Q] :
    Primitive 24 (P.hide Q) (enterLocals S L) (P.sep Q) where
  code := q.code
  correct a _ r s saved rep := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨k, t, he, hq', hw, hk⟩ := q.correct scratch r₂ s c₂ hq
    exact ⟨k, t, c₁+c₂, he,
      ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, P.frame hp hd.symm hw, hq'⟩,
      hw.mono Finset.subset_union_right, by simp only [enterLocals]; omega⟩

instance (P : Representation S) (Q : Representation L) :
    Primitive rate (P.sep Q) (leaveLocals S L) (P.hide Q) where
  code := .skip
  correct a _ r s c h := ⟨0, s, c, .skip s, ⟨a.2, h⟩, Writes.refl _ _, by simp [leaveLocals]⟩

instance [p : Decoder P] : Decoder (P.hide Q) where
  decode := p.decode
  correct a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.correct _ _ _ _ hp

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
