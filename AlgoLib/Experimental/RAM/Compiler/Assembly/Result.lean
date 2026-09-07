/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Init

/-!
# Observed execution result

Both implementation interfaces return an ordinary value and an instruction count.
This carrier chooses no backend and contains no logical-credit or encoding policy.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition

structure Result (B : Type) where
  value : B
  steps : Nat
  deriving Repr

end AlgoLib.Experimental.RAM.Prototype.Composition
