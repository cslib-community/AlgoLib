/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Velvet.Std
import AlgoLib.Experimental.RAM.Machine.Machine

/-!
# All-outcome semantics for ordinary Velvet methods

This semantics observes the actual upstream `VelvetM` value produced by an ordinary
`method` declaration. In particular, a `pickCont` ranges over every value satisfying
its predicate; it does not call `Findable.find` or the deterministic extractor.
Loops have their finite operational meaning. Divergence has no terminating outcome.

A compiler preserving this semantics needs a nondeterministic target. The final
theorem below proves that a deterministic RAM program cannot implement two distinct
source outcomes through one deterministic output decoder.
-/
namespace AlgoLib.Experimental.RAM.Prototype.VelvetSemantics

/-- Finite successful outcomes of the actual upstream free-monadic program. -/
inductive Returns : {α : Type} → VelvetM α → α → Prop where
  | pure {α : Type} (x : α) : Returns (.pure x) x
  | vis {α β : Type} {x : α} {f : α → VelvetM β} {y : β} :
      Returns (f x) y → Returns (.vis (.res x) f) y
  | pick {α β : Type} {p : α → Prop} [Findable p] {f : α → VelvetM β} {x : α} {y : β} :
      p x → Returns (f x) y → Returns (.pickCont α p f) y
  | stop {α β : Type} {s t : α} {body : α → VelvetM (ForInStep α)} {next : α → VelvetM β} {y : β} :
      Returns (body s) (.done t) → Returns (next t) y →
      Returns (.repeatCont s body next) y
  | step {α β : Type} {s t : α} {body : α → VelvetM (ForInStep α)} {next : α → VelvetM β} {y : β} :
      Returns (body s) (.yield t) → Returns (.repeatCont t body next) y →
      Returns (.repeatCont s body next) y

variable {α β : Type}

/-- `pure` has exactly its stated result. -/
@[simp] theorem returns_pure {x y : α} : Returns (.pure x) y ↔ y = x := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .pure _

/-- Divergence in the base monad cannot manufacture an output. -/
theorem no_divergent_outcome {f : α → VelvetM β} {y : β} :
    ¬ Returns (.vis DivM.div f) y := by intro h; cases h

/-- All-outcome equivalence requires both preservation and reflection. -/
def Equivalent (p q : VelvetM α) : Prop := ∀ y, Returns p y ↔ Returns q y

/-- A deterministic target cannot preserve two distinct nondeterministic outcomes. -/
theorem deterministic_target_impossible {α : Type} (p : VelvetM α) (x y : α)
    (hx : Returns p x) (hy : Returns p y) (different : x ≠ y)
    (code : Checked.Code) (input : Checked.State) (decode : Checked.State → α) :
    ¬ (∀ z, Returns p z ↔ ∃ k t, Checked.Exec code input k t ∧ decode t = z) := by
  intro equivalent
  obtain ⟨i, s, hs, hxs⟩ := (equivalent x).mp hx
  obtain ⟨j, t, ht, hyt⟩ := (equivalent y).mp hy
  have same := (hs.deterministic ht).2
  subst t
  exact different (hxs.symm.trans hyt)

end AlgoLib.Experimental.RAM.Prototype.VelvetSemantics
