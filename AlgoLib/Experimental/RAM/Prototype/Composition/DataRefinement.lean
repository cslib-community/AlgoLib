/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Encoding

/-!
# Implement abstract operations using already verified owned programs

An implementation hides a concrete mathematical state and a private potential.
Its body is an ordinary supported program; the existing compiler reconstructs its
RAM simulation. The implementation author proves only a functional refinement and
an amortized logical inequality. The resulting primitive includes actual RAM cost,
ownership preservation, and saved potential. Clients continue to use the abstract
operation. This is a small data-refinement rule in the direction of Sepref; it does
not introduce a trusted evaluator or an alternative execution semantics.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- A library-private observation, invariant, and amortization strategy. -/
structure DataView (C A : Type) where
  model : C → A
  valid : C → Prop
  potential : C → Nat

/-- Saved source credits are calibrated once, then owned as private RAM potential. -/
def DataView.representation (v : DataView C A) (rate : Nat) (P : Representation C) :
    Representation A where
  holds a r s saved := ∃ c left, P.holds c r s left ∧ v.valid c ∧
    v.model c = a ∧ saved = left + rate * v.potential c
  locality := by
    rintro a r s t saved agree ⟨c, left, rep, valid, model, paid⟩
    exact ⟨c, left, P.locality agree rep, valid, model, paid⟩

/-- A borrowed value remains separate from the implementation's private state. -/
def DataView.borrow (v : DataView C A) (B : Type) : DataView (C × B) (A × B) where
  model c := (v.model c.1, c.2)
  valid c := v.valid c.1
  potential c := v.potential c.1

theorem DataView.borrow_holds (v : DataView C A) (P : Representation C)
    (Q : Representation B) (rate : Nat) (a : A × B) (r s saved) :
    ((v.representation rate P).sep Q).holds a r s saved ↔
      ((v.borrow B).representation rate (P.sep Q)).holds a r s saved := by
  constructor
  · rintro ⟨rp, rq, cp, cq, disjoint, rfl, rfl, hp, hq⟩
    obtain ⟨c, left, hc, valid, model, rfl⟩ := hp
    refine ⟨(c, a.2), left + cq, ⟨rp, rq, left, cq, disjoint, rfl, rfl, hc, hq⟩,
      valid, Prod.ext model rfl, ?_⟩
    simp [borrow]; omega
  · rintro ⟨⟨c,b⟩, left, hp, valid, model, rfl⟩
    obtain ⟨rp, rq, cp, cq, disjoint, rfl, rfl, hc, hq⟩ := hp
    have ha := congrArg Prod.fst model
    have hb := congrArg Prod.snd model
    refine ⟨rp, rq, cp + rate * v.potential c, cq, disjoint, rfl, ?_,
      ⟨c, cp, hc, valid, ha, rfl⟩, ?_⟩
    · simp [borrow]; omega
    · simpa using hb ▸ hq

/-- Reconstruction rule: every concrete leaf still needs its existing RAM certificate. -/
@[reducible] def DataView.realize (v : DataView C A) (op : Operation A A) (body : Program C C)
    [linked : Linked rate P body P]
    (proof : ∀ c, v.valid c → op.requires (v.model c) →
      ∃ k d, Run body c k d ∧ v.valid d ∧ v.model d = op.effect (v.model c) ∧
        k + v.potential d ≤ op.charge (v.model c) + v.potential c) :
    Primitive rate (v.representation rate P) op (v.representation rate P) where
  code := linked.supported.compile.code
  correct a pre r s saved rep := by
    obtain ⟨c, initial, hc, valid, rfl, rfl⟩ := rep
    obtain ⟨k, d, run, valid', model, bound⟩ := proof c valid pre
    obtain ⟨steps, t, left, exec, hd, writes, paid⟩ :=
      linked.supported.compile.sound run r s initial hc
    refine ⟨steps, t, left + rate * v.potential d, exec,
      ⟨d, left, hd, valid', model, rfl⟩, writes, ?_⟩
    have scaled := Nat.mul_le_mul_left rate bound
    nlinarith

/-- Use the same rule while keeping the borrowed scalar's ordinary ownership interface. -/
@[reducible] def DataView.realizeBorrowed (v : DataView C A) (op : Operation (A × B) (A × B))
    (body : Program (C × B) (C × B)) [Linked rate (P.sep Q) body (P.sep Q)]
    (proof : ∀ c, (v.borrow B).valid c → op.requires ((v.borrow B).model c) →
      ∃ k d, Run body c k d ∧ (v.borrow B).valid d ∧
        (v.borrow B).model d = op.effect ((v.borrow B).model c) ∧
        k + (v.borrow B).potential d ≤
          op.charge ((v.borrow B).model c) + (v.borrow B).potential c) :
    Primitive rate ((v.representation rate P).sep Q) op ((v.representation rate P).sep Q) where
  code := ((v.borrow B).realize op body proof).code
  correct a pre r s saved rep := by
    obtain ⟨steps, t, left, exec, post, writes, cost⟩ :=
      ((v.borrow B).realize op body proof).correct a pre r s saved
        ((v.borrow_holds P Q rate a r s saved).mp rep)
    exact ⟨steps, t, left, exec, (v.borrow_holds P Q rate _ _ _ _).mpr post, writes, cost⟩

instance (v : DataView C A) [d : Decoder P] : Decoder (v.representation rate P) where
  decode s := v.model (d.decode s)
  correct a r s saved h := by
    obtain ⟨c, left, rep, _, model, _⟩ := h
    rw [d.correct c r s left rep]
    exact model

end AlgoLib.Experimental.RAM.Prototype.Composition
