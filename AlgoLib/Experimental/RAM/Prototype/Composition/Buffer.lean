/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Contracts

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
@[reducible] def pushProcedure (capacity value : Nat) : Procedure (List Nat) (List Nat) :=
  Procedure.verify (push capacity value) (fun xs => xs.length < capacity)
    (fun xs ys => ys = xs ++ [value]) (fun _ => 2) (by
      intro xs hx
      simpa [VC, argument, append] using hx)

/-- Abstract query; a selected implementation must certify its test code. -/
def nonempty (xs : List Nat) : Bool := !xs.isEmpty

/- Public receiver-call API. Only these summaries are needed in client proofs. -/
namespace API

@[reducible] def append (capacity value : Nat) : Procedure (List Nat) (List Nat) :=
  pushProcedure capacity value

@[reducible] def clear : Procedure (List Nat) (List Nat) :=
  Procedure.verify (.invoke Buffer.clear) (fun _ => True) (fun _ ys => ys = [])
    (fun _ => 1) (by simp [VC, Buffer.clear])

@[simp] theorem append_requires (capacity value : Nat) (xs : List Nat) :
    (append capacity value).requires xs ↔ xs.length < capacity := Iff.rfl
@[simp] theorem append_ensures (capacity value : Nat) (xs ys : List Nat) :
    (append capacity value).ensures xs ys ↔ ys = xs ++ [value] := Iff.rfl
@[simp] theorem append_credits (capacity value : Nat) (xs : List Nat) :
    (append capacity value).credits xs = 2 := rfl
@[simp] theorem clear_requires (xs : List Nat) : clear.requires xs ↔ True := Iff.rfl
@[simp] theorem clear_ensures (xs ys : List Nat) : clear.ensures xs ys ↔ ys = [] := Iff.rfl
@[simp] theorem clear_credits (xs : List Nat) : clear.credits xs = 1 := rfl

instance (capacity value : Nat) : UniformCredits (append capacity value) where
  amount := 2
  bound _ := Nat.le_refl _

instance : UniformCredits clear where
  amount := 1
  bound _ := Nat.le_refl _

end API

end AlgoLib.Experimental.RAM.Prototype.Composition.Buffer
