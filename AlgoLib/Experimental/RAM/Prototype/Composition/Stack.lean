/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Buffer

/-!
# Bounded stack contracts

The list model is in bottom-to-top order. Push reuses the existing bounded-buffer
contract. Pop returns the last element through a separately owned scalar. The
two-stack queue uses these contracts without inspecting their RAM implementation.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Stack

def pop : Operation (List Nat × Nat) (List Nat × Nat) where
  requires q := q.1 ≠ []
  effect q := (q.1.dropLast, q.1.getLastD 0)
  charge _ := 2

namespace API
abbrev push := Buffer.API.appendFrom
abbrev clear := Buffer.API.clear
@[reducible] def pop : Procedure (List Nat × Nat) (List Nat × Nat) :=
  Procedure.verify (.invoke Stack.pop) (fun q => q.1 ≠ [])
    (fun q result => result = (q.1.dropLast, q.1.getLastD 0)) (fun _ => 2)
    (by simp [VC, Stack.pop])
instance : UniformCredits pop := ⟨2, fun _ => Nat.le_refl _⟩
end API
end AlgoLib.Experimental.RAM.Prototype.Composition.Stack
