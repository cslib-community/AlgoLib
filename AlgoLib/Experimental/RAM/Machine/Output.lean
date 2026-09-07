/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.List.Basic

/-!
# Shared observed output values

Bitmap and Execution are mathematical output containers. They neither choose a
machine nor import historical instructions. Bitmap enumeration is host-side display.
-/
namespace AlgoLib.Experimental.RAM.Checked

/-- A returned bitmap view, without copying or enumerating its cells. -/
structure Bitmap where
  length : Nat
  memory : Nat → Nat
  stride : Nat
  offset : Nat

def Bitmap.contains (b : Bitmap) (v : Nat) : Bool :=
  decide (v < b.length) && (b.memory (b.stride * v + b.offset) == 1)

/-- Host-side display/serialization, separate from the procedure's RAM count. -/
def Bitmap.toList (b : Bitmap) : List Nat := (List.range b.length).filter b.contains

structure Execution (α : Type) where
  output : α
  steps : Nat

end AlgoLib.Experimental.RAM.Checked
