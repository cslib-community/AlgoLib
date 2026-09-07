/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Init

/-!
# Shared natural arithmetic operations

The typed natural implementation view and historical instruction semantics share
this stateless operation vocabulary. It defines no machine state or execution.
-/
namespace AlgoLib.Experimental.RAM.Checked

inductive BinOp where
  | add | sub | mul
  deriving DecidableEq, Repr

def BinOp.eval : BinOp → Nat → Nat → Nat
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

end AlgoLib.Experimental.RAM.Checked
