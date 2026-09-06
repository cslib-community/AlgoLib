/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Nondeterministic

/-!
# Ordinary Loom correctness transported to RAM outcomes

This bridge uses Loom's actual total, demonic weakest precondition for `VelvetM`.
It is distinct from the costed algebra on the RAM authoring representation. An
ordinary `prove_correct` result can establish the source premise here. A checked
translation then transfers its postcondition to every target execution.

Finite-outcome equivalence does not transfer must-termination: that requires a
separate divergence-sensitive compiler theorem. This module transfers functional
correctness, and optionally a separately proved universal RAM execution bound.
Credit for the weakest-precondition semantics belongs to Loom (vendor/README.md).
-/
namespace AlgoLib.Experimental.RAM.Prototype.VelvetSemantics
open TotalCorrectness TotalCorrectness.DemonicChoice

private theorem lift_prop (p : Prop) : (⌜p⌝ : Prop) = p := by simp [LE.pure]

/-- Every successful outcome satisfies the ordinary total, demonic Loom WP. -/
private theorem Returns.satisfies_wpAux {α : Type} {p : VelvetM α} {x : α}
    (run : Returns p x) : ∀ post : α → Prop, NonDetT.wp p post → post x := by
  induction run with
  | pure x => intro post h; exact h
  | vis run ih =>
    intro post h
    apply ih post
    simpa [NonDetT.wp, _root_.wp, MAlg.lift, MAlgOrdered.μ, Functor.map, LE.pure,
      liftM, monadLift, MonadLift.monadLift] using h
  | pick hx run ih =>
    intro post h
    simp only [NonDetT.wp, inf_Prop_eq, iInf_Prop_eq, lift_prop] at h
    exact ih post (h.2 _ hx)
  | stop run next ihBody ihNext =>
    intro post h
    simp only [NonDetT.wp, iSup_Prop_eq, inf_Prop_eq, lift_prop,
      spec, Pi.le_def, le_Prop_eq] at h
    obtain ⟨inv, measure, preservation, initial, finish⟩ := h
    have result := ihBody _ (preservation _ initial)
    exact ihNext post (finish _ result)
  | step run next ihBody ihNext =>
    intro post h
    simp only [NonDetT.wp, iSup_Prop_eq, inf_Prop_eq, lift_prop,
      spec, Pi.le_def, le_Prop_eq] at h
    obtain ⟨inv, measure, preservation, initial, finish⟩ := h
    have nextInv := (ihBody _ (preservation _ initial)).1
    apply ihNext post
    simp only [NonDetT.wp, iSup_Prop_eq, inf_Prop_eq, lift_prop,
      spec, Pi.le_def, le_Prop_eq]
    exact ⟨inv, measure, preservation, nextInv, finish⟩

/-- Every successful outcome satisfies the ordinary total, demonic Loom WP. -/
theorem Returns.satisfies_wp {α : Type} {p : VelvetM α} {x : α}
    (run : Returns p x) (post : α → Prop) (proof : wp p post) : post x :=
  run.satisfies_wpAux post ((NonDetT.wp_eq_wp p post).mp proof)

/-- One source proof gives correctness of every target execution. -/
theorem loom_to_ram {Input Output : Type} {source : Input → VelvetM Output}
    (translation : Nondeterministic.Translation source) (input : Input)
    (valid : translation.valid input) (post : Output → Prop)
    (proof : wp (source input) post) {steps : Nat} {final : Checked.State}
    (run : Nondeterministic.ExecIn translation.procedures translation.code
      (translation.encode input) steps final) :
    post (translation.decode final) :=
  translation.correct input valid post (fun _ outcome => outcome.satisfies_wp post proof) run

end AlgoLib.Experimental.RAM.Prototype.VelvetSemantics
