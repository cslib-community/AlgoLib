/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Counting helpers

Shared counting arguments for Monte-Carlo soundness proofs
(Mathlib-only, no framework imports).

* `two_mul_card_filter_le_of_involutive`: the involution pairing
  principle: if an involution pairs every accepting element with a
  rejecting one, at most half the elements accept. This is the
  combinatorial core of `Freivalds`' 1/2 soundness bound (flip one bit
  of the witness column), and of any error bound proved by pairing
  good with bad random choices.
-/

namespace AlgoLib

/-- Involution pairing. If `ι` is an involution and every accepting
element (`P x`) is paired with a rejecting one (`¬ P (ι x)`), then at
most half of the elements accept: `2 · #accepting ≤ #β`. -/
theorem two_mul_card_filter_le_of_involutive {β : Type*} [Fintype β]
    [DecidableEq β] (P : β → Bool) (ι : β → β)
    (hinv : Function.Involutive ι)
    (hflip : ∀ x, P x = true → ¬ P (ι x) = true) :
    2 * (Finset.univ.filter fun x => P x).card ≤ Fintype.card β := by
  classical
  have hmaps : ∀ x ∈ Finset.univ.filter fun x => P x,
      ι x ∈ Finset.univ.filter fun x => ¬ P x = true := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hflip x hx
  have hcard := Finset.card_le_card_of_injOn ι hmaps
    (hinv.injective.injOn)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset β)) (p := fun x => P x = true)
  rw [Finset.card_univ] at hsplit
  omega

end AlgoLib
