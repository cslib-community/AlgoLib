/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Linking
import AlgoLib.Experimental.RAM.Prototype.Composition.Loom

/-!
# Link once, execute actual RAM, recover ordinary mathematical outputs

The existing verified Method runner supplies execution without fuel. A decoder is
an observation of resident output storage; it cannot manufacture an output unrelated
to the final represented value. Product decoders compose automatically.
Initial potential is explicitly included in the derived bound. Encoding and decoding
are host-side views, as in the existing RAM interfaces, not charged conversion code.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

/-- The same linking law can be applied directly to actual upstream Loom WP. -/
theorem loom_linking {A B : Type} {rate : Nat} {P : Representation A}
    {Q : Representation B} {p : Program A B} (supported : Supported rate P Q p)
    (post : B → Prop) (a : A) (budget : Nat)
    (proof : _root_.wp (denote p a) (fun b _ _ => post b) () budget)
    (r : Footprint) (machine : Checked.State) (saved : Nat)
    (rep : P.holds a r (observe machine) saved) :
    ∃ steps final b left, Checked.Exec supported.compile.code.compile machine steps final ∧
      Q.holds b r (observe final) left ∧ post b ∧ Writes r (observe machine) (observe final) ∧
      steps + left ≤ rate * budget + saved := by
  rw [loom_wp_eq] at proof
  obtain ⟨k, _, b, run, hk, hb⟩ := proof
  obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := supported.compile.sound run r _ saved rep
  obtain ⟨final, ram, equal⟩ := exec.compile machine rfl
  exact ⟨steps, final, b, left, ram, equal ▸ hQ, hb, equal ▸ hw,
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _)⟩

/-- Link a previously specified procedure using its public contract, without reopening VCs. -/
theorem procedure_linking {A B : Type} {rate : Nat} {P : Representation A}
    {Q : Representation B} (proc : Procedure A B)
    (supported : Supported rate P Q proc.body) (a : A) (valid : proc.requires a)
    (r : Footprint) (machine : Checked.State) (saved : Nat)
    (rep : P.holds a r (observe machine) saved) :
    ∃ steps final b left, Checked.Exec supported.compile.code.compile machine steps final ∧
      Q.holds b r (observe final) left ∧ proc.ensures a b ∧
      Writes r (observe machine) (observe final) ∧
      steps + left ≤ rate * proc.credits a + saved := by
  obtain ⟨k, b, run, hb, hk⟩ := proc.correct a valid
  obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := supported.compile.sound run r _ saved rep
  obtain ⟨final, ram, equal⟩ := exec.compile machine rfl
  exact ⟨steps, final, b, left, ram, equal ▸ hQ, hb, equal ▸ hw,
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _)⟩

class Decoder (Q : Representation B) where
  decode : Store → B
  correct : ∀ b r s left, Q.holds b r s left → decode s = b

instance [p : Decoder P] [q : Decoder Q] : Decoder (Representation.sep P Q) where
  decode s := (p.decode s, q.decode s)
  correct b r s left h := by
    obtain ⟨r₁, r₂, p₁, p₂, _, _, _, hp, hq⟩ := h
    exact Prod.ext (p.correct _ _ _ _ hp) (q.correct _ _ _ _ hq)

/-- The public runner's proof depends only on the logical theorem and linked leaves. -/
def executable {A B : Type} {rate : Nat} {P : Representation A} {Q : Representation B}
    {p : Program A B} [linked : Linked rate P p Q] (a : A) (budget : Nat) (post : B → Prop)
    (proof : VC p (fun b _ => post b) a budget) (r : Footprint) (saved : Nat) : Method where
  body := linked.supported.compile.code
  requires s := P.holds a r s saved
  ensures s t := ∃ b left, Q.holds b r t left ∧ post b ∧ Writes r s t
  budget _ := rate * budget + saved
  verification s rep := by
    obtain ⟨k, b, run, hk, hb⟩ := VC.sound p _ a budget proof
    obtain ⟨steps, t, left, exec, hQ, hw, hc⟩ := linked.supported.compile.sound run r s saved rep
    exact ⟨steps, t, exec, ⟨b, left, hQ, hb, hw⟩, by nlinarith⟩

structure Result (B : Type) where
  value : B
  steps : Nat
  deriving Repr

def run {A B : Type} {rate : Nat} {P : Representation A} {Q : Representation B}
    {p : Program A B} [Linked rate P p Q] [decoder : Decoder Q]
    (a : A) (budget : Nat) (post : B → Prop) (proof : VC p (fun b _ => post b) a budget)
    (r : Footprint) (s : Store) (saved : Nat) (initial : P.holds a r s saved) : Result B :=
  let result := (executable (rate := rate) (P := P) (Q := Q) (p := p)
    a budget post proof r saved).run s initial
  ⟨decoder.decode result.2, result.1⟩

theorem run_correct {A B : Type} {rate : Nat} {P : Representation A} {Q : Representation B}
    {p : Program A B} [Linked rate P p Q] [decoder : Decoder Q]
    (a : A) (budget : Nat) (post : B → Prop) (proof : VC p (fun b _ => post b) a budget)
    (r : Footprint) (s : Store) (saved : Nat) (initial : P.holds a r s saved) :
    post (run (rate := rate) (P := P) (Q := Q) (p := p)
      a budget post proof r s saved initial).value ∧
      (run (rate := rate) (P := P) (Q := Q) (p := p)
        a budget post proof r s saved initial).steps ≤ rate * budget + saved := by
  have h := (executable (rate := rate) (P := P) (Q := Q) (p := p)
    a budget post proof r saved).correct s initial
  obtain ⟨b, left, hQ, hb, _⟩ := h.2.1
  constructor
  · change post (decoder.decode ((executable (rate := rate) (P := P) (Q := Q)
      (p := p) a budget post proof r saved).run s initial).2)
    rw [decoder.correct _ _ _ _ hQ]
    exact hb
  · exact h.2.2

end AlgoLib.Experimental.RAM.Prototype.Composition
