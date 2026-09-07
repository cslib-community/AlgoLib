/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Verification.Plan

/-!
# Annotated algorithms and completion

An Algorithm combines a body, its proof plan, and its mathematical interface.
Algorithm.Obligations is the author-facing proposition; Algorithm.certify assembles
a reusable procedure using Plan.sound. No implementation backend is imported.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- A method contains one body, its indexed annotations and its mathematical interface. -/
structure Algorithm (A B : Type) where
  body : Program A B
  annotations : A → Plan body
  requires : A → Prop
  ensures : A → B → Prop
  credits : A → Nat

def Algorithm.Obligations (m : Algorithm A B) : Prop :=
  SourceForall "input" (fun a => m.requires a →
    (m.annotations a).vc (fun b _ => m.ensures a b) a (m.credits a))

/-- Reconstruct a reusable procedure from source-level obligations only. -/
@[reducible] def Algorithm.certify (m : Algorithm A B)
    (proof : m.Obligations) : Procedure A B where
  body := m.body
  requires := m.requires
  ensures := m.ensures
  credits := m.credits
  correct a pre := by
    obtain ⟨k, b, left, run, paid, post⟩ := (m.annotations a).sound _ a _ (proof a pre)
    exact ⟨k, b, run, post, by omega⟩


end AlgoLib.Experimental.RAM.Prototype.Composition
