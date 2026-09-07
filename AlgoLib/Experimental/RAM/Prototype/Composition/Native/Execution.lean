/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Native.Encoding
import AlgoLib.Experimental.RAM.Prototype.Composition.Execution

/-!
# Native execution of certified source procedures

The source procedure proof and the shared linker supply termination, correctness,
ownership, and costs. The runner executes native integer code directly and returns
ordinary Lean values via certified resident-output observations. The public bound
retains the existing conservative factor two during migration.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Native
open Prototype.Composition (Procedure Result)

private theorem encoded_terminates (proc : Procedure A B) (encoder : Encoder P)
    [linked : Linked rate P proc.body Q] (a : A)
    (valid : proc.requires a) (resident : encoder.requires a) :
    ∃ k t, Eval linked.supported.compile.code (encoder.store a) k t := by
  obtain ⟨k, b, run, _, _⟩ := proc.correct a valid
  obtain ⟨steps, t, left, he, _, _, _⟩ := linked.supported.compile.sound run
    encoder.footprint (encoder.store a) (encoder.saved a) (encoder.correct a resident)
  exact ⟨steps, t, he⟩

def runEncoded (proc : Procedure A B) (encoder : Encoder P)
    [linked : Linked rate P proc.body Q] [decoder : Decoder Q] (a : A)
    (valid : proc.requires a) (resident : encoder.requires a) : Result B :=
  let result := Native.run linked.supported.compile.code (encoder.store a)
    (encoded_terminates proc encoder a valid resident)
  ⟨decoder.decode result.2, result.1⟩

theorem runEncoded_correct (proc : Procedure A B) (encoder : Encoder P)
    [linked : Linked rate P proc.body Q] [decoder : Decoder Q] (a : A)
    (valid : proc.requires a) (resident : encoder.requires a) :
    proc.ensures a (runEncoded (rate := rate) proc encoder a valid resident).value ∧
      (runEncoded (rate := rate) proc encoder a valid resident).steps ≤
        2 * (rate * proc.credits a + encoder.saved a) := by
  obtain ⟨k, b, source, post, budget⟩ := proc.correct a valid
  obtain ⟨steps, t, left, he, represented, _, paid⟩ := linked.supported.compile.sound source
    encoder.footprint (encoder.store a) (encoder.saved a) (encoder.correct a resident)
  simp only [runEncoded, Native.run_eq he]
  rw [decoder.correct _ _ _ _ represented]
  exact ⟨post, by nlinarith⟩

end AlgoLib.Experimental.RAM.Native
