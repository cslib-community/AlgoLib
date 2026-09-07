/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.ResourceRefinement
import AlgoLib.Experimental.RAM.Prototype.Composition.Expressions

/-!
# Shared private-local initialization and framing

Local initialization uses the unchanged structural source allowance. Hidden local
ownership is existential; entering and leaving a scope preserves unrelated storage
and potential. These proofs are shared by legacy and native implementations.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Ownership
open Prototype.Composition (Locals enterLocals leaveLocals associate unassociate)
variable {backend : Backend} {M : Model}

def Representation.hide (P : Representation M S) (Q : Representation M L) : Representation M S where
  holds a r s c := ∃ locals, (P.sep Q).holds (a, locals) r s c
  locality h rep := by
    obtain ⟨locals, rep⟩ := rep
    exact ⟨locals, (P.sep Q).locality h rep⟩

class Initialize (backend : Backend) (Q : Representation backend.memory L) [locals : Locals L] where
  code : backend.Command
  correct : ∀ a r s c, Q.holds a r s c → ∃ k t,
    backend.Eval code s k t ∧ Q.holds locals.initial r t c ∧ Writes r s t ∧ k ≤ locals.credits

instance [a : Locals A] [b : Locals B] (P : Representation backend.memory A) (Q : Representation backend.memory B)
    [p : Initialize backend P] [q : Initialize backend Q] :
    Initialize backend (P.sep Q) where
  code := backend.seq p.code q.code
  correct pair r s c h := by
    obtain ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := h
    obtain ⟨i, t, he, hp', hw, hi⟩ := p.correct pair.1 r₁ s c₁ hp
    obtain ⟨j, u, hf, hq', hv, hj⟩ := q.correct pair.2 r₂ t c₂ (Q.frame hq hd hw)
    exact ⟨i+j, u, backend.seq_sound he hf,
      ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, P.frame hp' hd.symm hv, hq'⟩,
      (hw.mono Finset.subset_union_left).trans (hv.mono Finset.subset_union_right),
      Nat.add_le_add hi hj⟩

instance (P : Representation backend.memory S) (Q : Representation backend.memory L)
    [locals : Locals L] [q : Initialize backend Q] :
    Primitive backend 24 (P.hide Q) (enterLocals S L) (P.sep Q) where
  code := q.code
  correct a _ r s saved rep := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, hd, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨k, t, he, hq', hw, hk⟩ := q.correct scratch r₂ s c₂ hq
    exact ⟨k, t, c₁+c₂, he,
      ⟨r₁, r₂, c₁, c₂, hd, rfl, rfl, P.frame hp hd.symm hw, hq'⟩,
      hw.mono Finset.subset_union_right, by simp only [enterLocals]; omega⟩

instance (P : Representation backend.memory S) (Q : Representation backend.memory L) :
    Primitive backend rate (P.sep Q) (leaveLocals S L) (P.hide Q) where
  code := backend.skip
  correct a _ r s c h := ⟨0, s, c, backend.skip_sound s, ⟨a.2, h⟩, Writes.refl _ _, by simp [leaveLocals]⟩

instance (P : Representation backend.memory A) (Q : Representation backend.memory B) (R : Representation backend.memory C) :
    Primitive backend rate ((P.sep Q).sep R) (associate A B C) (P.sep (Q.sep R)) where
  code := backend.skip
  correct a _ r s c h := ⟨0, s, c, backend.skip_sound s,
    (Representation.sep_assoc P Q R).mp h, Writes.refl _ _, by simp [associate]⟩

instance (P : Representation backend.memory A) (Q : Representation backend.memory B) (R : Representation backend.memory C) :
    Primitive backend rate (P.sep (Q.sep R)) (unassociate A B C) ((P.sep Q).sep R) where
  code := backend.skip
  correct a _ r s c h := ⟨0, s, c, backend.skip_sound s,
    (Representation.sep_assoc P Q R).mpr h, Writes.refl _ _, by simp [unassociate]⟩

end AlgoLib.Experimental.RAM.Ownership
