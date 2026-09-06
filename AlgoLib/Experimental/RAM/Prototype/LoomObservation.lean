/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Verification
import Loom.MonadAlgebras.WP.Basic

/-!
# The RAM observation as an actual Loom algebra

The vendored upstream Loom hierarchy supplies `MAlgOrdered`, the derived monadic
observation, transformer instances and WP rules. This module instantiates that
hierarchy for finite costed state executions. `loom_wp_eq` identifies Loom's WP
with the previously checked credit observation; `Plan.loom_sound` connects generated
conditions to that actual Loom WP. Compiler certificates and execution stay unchanged.

Credit: Loom and its authors; see vendor/README.md for the pinned upstream version,
license, Lean compatibility changes, and exclusion of trusted solver/admission paths.
-/
namespace AlgoLib.Experimental.RAM.Prototype

instance {State : Type} : Monad (Computation State) where
  pure := Computation.pure
  bind := Computation.bind

instance {State : Type} : LawfulMonad (Computation State) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  · intro α x
    exact Computation.bind_pure x
  · intro α β x f
    exact Computation.pure_bind x f
  · intro α β γ x f g
    exact Computation.bind_assoc x f g

/-- A real Loom algebra: assertions describe state and available credits. -/
instance {State : Type} : MAlgOrdered (Computation State) (State → Nat → Prop) where
  μ m := m.wp (fun post => post)
  μ_ord_pure post := by
    funext s c
    exact propext (Computation.wp_pure post _ s c)
  μ_ord_bind f g h x := by
    intro s c
    change (Computation.bind x f).wp (fun post => post) s c →
      (Computation.bind x g).wp (fun post => post) s c
    rw [Computation.wp_bind, Computation.wp_bind]
    exact Computation.wp_mono (fun a t d ha => h a t d ha)

/-- Loom's independently defined WP is exactly the costed state observation. -/
theorem loom_wp_eq {State α : Type} (m : Computation State α)
    (Q : α → State → Nat → Prop) : _root_.wp m Q = m.wp Q := by
  funext s c
  change (Computation.bind m (fun a => Computation.pure (Q a))).wp
    (fun post => post) s c = m.wp Q s c
  apply propext
  rw [Computation.wp_bind]
  constructor
  · exact Computation.wp_mono (fun a t d h =>
      (Computation.wp_pure (Q a) (fun post => post) t d).mp h)
  · exact Computation.wp_mono (fun a t d h =>
      (Computation.wp_pure (Q a) (fun post => post) t d).mpr h)

/-- The frontend's generated obligations prove an actual upstream Loom WP. -/
theorem Plan.loom_sound {State : Type} {M : Authoring.Model State}
    {p : Authoring.Program M} (plan : Plan p) (Q : State → Nat → Prop)
    (s : State) (c : Nat) (h : plan.vc Q s c) :
    _root_.wp (denote p) (fun _ => Q) s c := by
  rw [loom_wp_eq]
  exact plan.sound Q s c h

end AlgoLib.Experimental.RAM.Prototype
