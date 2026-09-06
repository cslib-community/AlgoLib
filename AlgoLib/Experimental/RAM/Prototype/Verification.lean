/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalVerification
import AlgoLib.Experimental.RAM.Prototype.Interpretation
import AlgoLib.Experimental.RAM.Authoring.Methods

/-!
# Attaching a RAM backend to logical verification conditions

All program/annotation semantics and the VCG live in LogicalVerification, without
RAM imports. This compatibility layer binds the pure proof to an executable adapter.
Supported-language evidence is automatically reconstructed before accepting a method.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring
variable {State Input Output : Type} {M : Model State}

/-- Input/output and logical credit obligations. Proof annotations are separate from input. -/
def Obligations {api : Interface M Input Output} (method : Method api)
    (plan : Input → Plan method.body) : Prop :=
  ∀ i, method.requires i →
    (plan i).vc (fun t _ => ∀ out, api.Observes t out → method.ensures i out)
      (api.initial i) (method.credits i)

/-- Reconstruct a backend certificate, entirely inside Lean's kernel. -/
theorem reconstruct {api : Interface M Input Output} {method : Method api}
    {plan : Input → Plan method.body} (proof : Obligations method plan) : method.VCs := by
  intro i hi
  have hp := proof i hi
  obtain ⟨k, t, u, ht, hk, hQ⟩ := (plan i).sound _ _ _ hp
  cases u
  exact Run.vc _ (denote_run _ ht) _ _ hk hQ

/-- The executable is the existing verified RAM runner, not a host list implementation. -/
def certify {api : Interface M Input Output} (method : Method api)
    {plan : Input → Plan method.body} (proof : Obligations method plan)
    (supported : Supported M method.body := by ram_supported) : VerifiedMethod api :=
  method.certify (reconstruct proof) supported

/-- Proof annotations cannot change the compiled body. -/
theorem certify_body {api : Interface M Input Output} (method : Method api)
    {plan : Input → Plan method.body} (proof : Obligations method plan)
    (supported : Supported M method.body) :
    (certify method proof supported).method.body = method.body := rfl

/-- Substitute logical contracts and propagate credits, leaving invariants to the user. -/
macro "prototype_steps" " [" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Plan.vc, paper_simps, $ds,*] at *)

end AlgoLib.Experimental.RAM.Prototype
