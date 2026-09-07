/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Natural.Encoding

/-!
# Certified executable package for natural-valued implementation contracts

This is an explicit compatibility implementation interface, not part of standard
native method assembly. Existing declaration names and certificates are preserved.
The packaged code still executes on Int-RAM.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- A backend package retains its interpretation certificates, not an arbitrary runner.
Execution, the bound, and their theorem are derived definitions below. -/
structure CertifiedExecutable (proc : Procedure A B) where
  input : A → Representation A
  output : A → Representation B
  encoder : ∀ a, Encoder (input a)
  rate : Nat
  linked : ∀ a, Linked rate (input a) proc.body (output a)
  decoder : ∀ a, Decoder (output a)
  resident : ∀ a, proc.requires a → (encoder a).requires a
  codeIndependent : ∀ a b,
    (linked a).supported.compile.code = (linked b).supported.compile.code

/-- Generic assembly: logical proofs are unchanged when the verified backend changes. -/
def CertifiedExecutable.ofEncoded (proc : Procedure A B)
    (P : A → Representation A) (Q : A → Representation B)
    (encoder : ∀ a, Encoder (P a)) (rate : Nat)
    [linked : ∀ a, Linked rate (P a) proc.body (Q a)] [decoder : ∀ a, Decoder (Q a)]
    (resident : ∀ a, proc.requires a → (encoder a).requires a)
    (fixed : ∀ a b, (linked a).supported.compile.code = (linked b).supported.compile.code) :
    CertifiedExecutable proc :=
  ⟨P, Q, encoder, rate, linked, decoder, resident, fixed⟩

/-- Always execute the linked RAM code, with the existing proof-directed termination. -/
def CertifiedExecutable.run {proc : Procedure A B} (e : CertifiedExecutable proc)
    (a : A) (h : proc.requires a) :
    Result B :=
  letI := e.linked a
  letI := e.decoder a
  runEncoded (rate := e.rate) (Q := e.output a) proc (e.encoder a) a h (e.resident a h)

/-- The selected backend supplies the conversion rate and any initial private potential. -/
def CertifiedExecutable.bound {proc : Procedure A B} (e : CertifiedExecutable proc) (a : A) : Nat :=
  2 * (e.rate * proc.credits a + (e.encoder a).saved a)

/-- Functional correctness and the RAM bound refer to this exact executable. -/
theorem CertifiedExecutable.correct {proc : Procedure A B} (e : CertifiedExecutable proc)
    (a : A) (h : proc.requires a) :
    proc.ensures a (e.run a h).value ∧ (e.run a h).steps ≤ e.bound a := by
  letI := e.linked a
  letI := e.decoder a
  exact runEncoded_correct (rate := e.rate) (Q := e.output a)
    proc (e.encoder a) a h (e.resident a h)

end AlgoLib.Experimental.RAM.Prototype.Composition
