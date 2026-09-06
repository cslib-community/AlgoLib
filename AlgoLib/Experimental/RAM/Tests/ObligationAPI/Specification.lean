/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend

/-!
# Specification-only obligation API fixture

No proof or backend is imported. The generated propositions, source binding metadata,
and assembly theorem are reusable from other modules.
-/
namespace AlgoLib.Experimental.RAM.Tests.ObligationAPI
open Prototype.Frontend Prototype.Composition

@[irreducible] def Known (n : Nat) : Prop := n ≤ n

theorem known (n : Nat) : Known n := by unfold Known; omega

ram method countdown (mut _counter : Nat) return (result : Nat)
  require True
  ensures _counter = 0
  do
    while 0 < _counter named count
      invariant "known" Known _counter
      iterations_at_most _counter
      do
        _counter := _counter - 1

generate_obligations countdown

end AlgoLib.Experimental.RAM.Tests.ObligationAPI
