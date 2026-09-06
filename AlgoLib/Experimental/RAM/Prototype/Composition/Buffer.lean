/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Language

/-!
# Abstract bounded buffers: one client, two private clearing strategies

The public model is a list. Append consumes constant logical credits; clear consumes
one credit even though an implementation may erase every occupied cell. No
representation, erase-loop invariant, or saved-potential function is imported here.
Typed argument preparation is explicit in the program and its charge is included.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Buffer

def argument (value : Nat) : Operation (List Nat) (List Nat × Nat) where
  requires _ := True
  effect xs := (xs, value)
  charge _ := 1

def append (capacity : Nat) : Operation (List Nat × Nat) (List Nat) where
  requires input := input.1.length < capacity
  effect input := input.1 ++ [input.2]
  charge _ := 1

def clear : Operation (List Nat) (List Nat) where
  requires _ := True
  effect _ := []
  charge _ := 1

/-- Arguments/results have different types; composition checks the call boundary. -/
abbrev push (capacity value : Nat) : Program (List Nat) (List Nat) :=
  .seq (.invoke (argument value)) (.invoke (append capacity))

/-- A reusable logical procedure contract. -/
def pushProcedure (capacity value : Nat) : Procedure (List Nat) (List Nat) :=
  Procedure.verify (push capacity value) (fun xs => xs.length < capacity)
    (fun xs ys => ys = xs ++ [value]) (fun _ => 2) (by
      intro xs hx
      simpa [VC, argument, append] using hx)

/-- Abstract query; a selected implementation must certify its test code. -/
def nonempty (xs : List Nat) : Bool := !xs.isEmpty

end AlgoLib.Experimental.RAM.Prototype.Composition.Buffer
