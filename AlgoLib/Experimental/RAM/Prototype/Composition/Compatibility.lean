/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Language
import AlgoLib.Experimental.RAM.Authoring.Contracts

/-!
# Preserve existing frontend programs and logical proofs

This structural embedding turns the existing Authoring.Program into a typed client.
Its VCs are equal to the old VCs, so existing invariants and credit proofs are reused
without edits. To link with ownership, its primitive operations still require local
implementation contracts: old whole-store certificates do not automatically prove
non-interference. The existing frontend and compiler are retained, not replaced by
an unrelated unchecked translation.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

def ofAction (a : Authoring.Action State) : Operation State State :=
  ⟨a.requires, a.effect, a.work⟩

def ofProgram : Authoring.Program State → Program State State
  | .skip => .identity
  | .action a => .invoke (ofAction a)
  | .seq p q => .seq (ofProgram p) (ofProgram q)
  | .branch test p q => .branch test.test (ofProgram p) (ofProgram q)
  | .loop test p => .loop test.test (ofProgram p)

/-- Proof reuse is an equality of VCs for all programs, not a demo-specific implication. -/
theorem ofProgram_vc (p : Authoring.Program State) (Q : State → Nat → Prop) :
    VC (ofProgram p) Q = Authoring.VC p Q := by
  induction p generalizing Q with
  | skip => rfl
  | action a => rfl
  | seq p q ihp ihq =>
    change VC (ofProgram p) (VC (ofProgram q) Q) = Authoring.VC p (Authoring.VC q Q)
    rw [ihp, ihq]
  | branch test p q ihp ihq =>
    funext s c
    simp only [ofProgram, VC, Authoring.VC, ihp, ihq]
  | loop test p ih =>
    funext s c
    simp only [ofProgram, VC, Authoring.VC, ih]

/-- Existing paper-style frontend proofs enter the new linker unchanged. -/
theorem reuse_specification (spec : Authoring.Specification State Input Output)
    (proof : spec.VCs) (input : Input) (valid : spec.requires input) :
    VC (ofProgram spec.body)
      (fun t _ => ∀ out, spec.observes t out → spec.ensures input out)
      (spec.initial input) (spec.credits input) := by
  rw [ofProgram_vc]
  exact proof input valid

end AlgoLib.Experimental.RAM.Prototype.Composition
