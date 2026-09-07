/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Contracts.LocalRefinement

/-!
# Shared resident-input encoders

Encoders assemble separately owned inputs and private locals. A store model provides
an overlay operation preserving each side's cells; the functional and potential
composition proofs are independent of the value representation or RAM compiler.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Ownership
open Prototype.Composition (Locals)
variable {M : Model}

class Overlay (M : Model) where
  overlay : Footprint M → M.State → M.State → M.State
  left : ∀ r s t, Agree r s (overlay r s t)
  right : ∀ r f s t, Disjoint r f → Agree f t (overlay r s t)

structure Encoder (P : Representation M A) where
  footprint : Footprint M
  requires : A → Prop
  saved : A → Nat
  store : A → M.State
  correct : ∀ a, requires a → P.holds a footprint (store a) (saved a)

/-- Recover an encoder's representation without repeating its generated local layout. -/
abbrev Encoder.representation {A : Type} {P : Representation M A} (_ : Encoder P) := P

def Encoder.sep [Overlay M] {P : Representation M A} {Q : Representation M B} (p : Encoder P) (q : Encoder Q) (hd : Disjoint p.footprint q.footprint) :
    Encoder (P.sep Q) where
  footprint := p.footprint ∪ q.footprint
  requires a := p.requires a.1 ∧ q.requires a.2
  saved a := p.saved a.1 + q.saved a.2
  store a := Overlay.overlay p.footprint (p.store a.1) (q.store a.2)
  correct a h := ⟨p.footprint, q.footprint, p.saved a.1, q.saved a.2, hd, rfl, rfl,
    P.locality (Overlay.left _ _ _) (p.correct _ h.1),
    Q.locality (Overlay.right _ _ _ _ hd) (q.correct _ h.2)⟩

def Encoder.hide [Overlay M] {P : Representation M A} {Q : Representation M L} (p : Encoder P) (q : Encoder Q) [l : Locals L]
    (hq : q.requires l.initial) (hd : Disjoint p.footprint q.footprint) : Encoder (P.hide Q) where
  footprint := p.footprint ∪ q.footprint
  requires := p.requires
  saved a := p.saved a + q.saved l.initial
  store a := (p.sep q hd).store (a, l.initial)
  correct _ h := ⟨l.initial, (p.sep q hd).correct _ ⟨h, hq⟩⟩

/- Encoder metadata is a simplification API; callers need not unfold assembled stores. -/
@[simp] theorem Encoder.sep_footprint [Overlay M] {P : Representation M A} {Q : Representation M B}
    (p : Encoder P) (q : Encoder Q) (hd : Disjoint p.footprint q.footprint) :
    (p.sep q hd).footprint = p.footprint ∪ q.footprint := rfl

@[simp] theorem Encoder.sep_requires [Overlay M] {P : Representation M A} {Q : Representation M B}
    (p : Encoder P) (q : Encoder Q) (hd : Disjoint p.footprint q.footprint) (a : A × B) :
    (p.sep q hd).requires a ↔ p.requires a.1 ∧ q.requires a.2 := Iff.rfl

@[simp] theorem Encoder.sep_saved [Overlay M] {P : Representation M A} {Q : Representation M B}
    (p : Encoder P) (q : Encoder Q) (hd : Disjoint p.footprint q.footprint) (a : A × B) :
    (p.sep q hd).saved a = p.saved a.1 + q.saved a.2 := rfl

@[simp] theorem Encoder.hide_footprint [Overlay M] {P : Representation M A} {Q : Representation M L}
    (p : Encoder P) (q : Encoder Q) [l : Locals L] (hq : q.requires l.initial)
    (hd : Disjoint p.footprint q.footprint) : (p.hide q hq hd).footprint =
      p.footprint ∪ q.footprint := rfl

@[simp] theorem Encoder.hide_requires [Overlay M] {P : Representation M A} {Q : Representation M L}
    (p : Encoder P) (q : Encoder Q) [l : Locals L] (hq : q.requires l.initial)
    (hd : Disjoint p.footprint q.footprint) (a : A) :
    (p.hide q hq hd).requires a ↔ p.requires a := Iff.rfl

@[simp] theorem Encoder.hide_saved [Overlay M] {P : Representation M A} {Q : Representation M L}
    (p : Encoder P) (q : Encoder Q) [l : Locals L] (hq : q.requires l.initial)
    (hd : Disjoint p.footprint q.footprint) (a : A) :
    (p.hide q hq hd).saved a = p.saved a + q.saved l.initial := rfl

class Decoder (Q : Representation M B) where
  decode : M.State → B
  correct : ∀ b r s left, Q.holds b r s left → decode s = b

instance [p : Decoder P] [q : Decoder Q] : Decoder (Representation.sep P Q) where
  decode s := (p.decode s, q.decode s)
  correct b r s left h := by
    obtain ⟨r₁, r₂, p₁, p₂, _, _, _, hp, hq⟩ := h
    exact Prod.ext (p.correct _ _ _ _ hp) (q.correct _ _ _ _ hq)

instance [p : Decoder P] : Decoder (P.hide Q) where
  decode := p.decode
  correct a r s c h := by
    obtain ⟨scratch, r₁, r₂, c₁, c₂, _, _, _, hp, _⟩ := h
    exact p.correct _ _ _ _ hp

end AlgoLib.Experimental.RAM.Ownership
