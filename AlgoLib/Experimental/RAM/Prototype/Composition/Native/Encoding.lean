/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Native.Locals
import AlgoLib.Experimental.RAM.Prototype.Composition.ResidentInputs

/-!
# Native resident inputs and ordinary output observations

Separately owned inputs combine using the same encoder laws as existing methods.
Array elements occupy consecutive integer cells; scalar registers and private local
registers compose with disjointness checked by the backend. Decoders observe resident
values and prove their agreement with the mathematical representation.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Native
open Prototype.Composition (Locals)

abbrev Encoder (P : Representation A) := Ownership.Encoder P
abbrev Decoder (P : Representation A) := Ownership.Decoder P

abbrev Encoder.representation {A : Type} {P : Representation A} (_ : Encoder P) := P

/-- Assemble resident inputs by copying exactly the selected footprint's cells. -/
def overlay (r : Footprint) (s t : Store) : Store where
  vars ty name := if .register ty name ∈ r then s.vars ty name else t.vars ty name
  heap i := if .heap i ∈ r then s.heap i else t.heap i

instance : Ownership.Overlay ownershipModel where
  overlay := overlay
  left r s t := by
    intro l hl
    cases l <;> simp_all [ownershipModel, cell, overlay]
  right r f s t h := by
    intro l hl
    have hn : l ∉ r := fun hr => Finset.disjoint_left.mp h hr hl
    cases l <;> simp_all [ownershipModel, cell, overlay]

abbrev Encoder.sep (p : Encoder P) (q : Encoder Q) (hd : Disjoint p.footprint q.footprint) :
    Encoder (P.sep Q) := Ownership.Encoder.sep p q hd

abbrev Encoder.hide {Q : Representation L} (p : Encoder P) (q : Encoder Q) [l : Locals L]
    (hq : q.requires l.initial) (hd : Disjoint p.footprint q.footprint) : Encoder (P.hide Q) :=
  Ownership.Encoder.hide p q hq hd

def naturalEncoder (v : Var .word) : Encoder (naturalScalar v) where
  footprint := {.register .word v.name}
  requires _ := True
  saved _ := 0
  store a := ⟨fun _ _ => a, fun _ => 0⟩
  correct _ _ := ⟨rfl, rfl, rfl⟩

def signedEncoder (v : Var .integer) : Encoder (signedScalar v) where
  footprint := {.register .integer v.name}
  requires _ := True
  saved _ := 0
  store a := ⟨fun _ _ => a, fun _ => 0⟩
  correct _ _ := ⟨rfl, rfl, rfl⟩

def arrayEncoder {A : Type} [Inhabited A] (encode : A → Int) (l : ArrayLayout) :
    Encoder (array encode l) where
  footprint := l.footprint
  requires a := a.size ≤ l.capacity
  saved _ := 0
  store a := ⟨fun _ _ => a.size, fun i => encode (a.getD (i-l.base) default)⟩
  correct a h := ⟨rfl, h, rfl,
    fun i hi => by simp [Array.getD, getElem!_pos, hi], rfl⟩

instance (v : Var .word) : Decoder (naturalScalar v) where
  decode s := (s.vars .word v.name).toNat
  correct _ _ _ _ h := by simp [h.2.1]

instance (v : Var .integer) : Decoder (signedScalar v) where
  decode s := s.vars .integer v.name
  correct _ _ _ _ h := h.2.1

instance (l : ArrayLayout) : Decoder (naturalArray l) where
  decode s := Array.ofFn (fun i : Fin (s.vars .word l.size.name).toNat =>
    (s.heap (l.base + i)).toNat)
  correct a r s c h := by
    apply Array.ext
    · simp [h.2.2.1]
    · intro i hi hj
      have hh := h.2.2.2.1 i hj
      simpa [getElem!_pos, hj] using congrArg Int.toNat hh

instance (l : ArrayLayout) : Decoder (signedArray l) where
  decode s := Array.ofFn (fun i : Fin (s.vars .word l.size.name).toNat => s.heap (l.base + i))
  correct a r s c h := by
    apply Array.ext
    · simp [h.2.2.1]
    · intro i hi hj
      simpa [getElem!_pos, hj] using h.2.2.2.1 i hj

open Lean Elab Term in
private partial def localStorage (stem : String) (ty : Lean.Expr) (index : Nat) :
    TermElabM (Term × Nat) := do
  let ty ← Lean.Meta.whnf ty
  if ty.isConstOf ``Nat then
    let name := quote (stem ++ "." ++ toString index)
    return (← `(Native.naturalEncoder ⟨$name⟩), index + 1)
  if ty.isConstOf ``Int then
    let name := quote (stem ++ "." ++ toString index)
    return (← `(Native.signedEncoder ⟨$name⟩), index + 1)
  if ty.isAppOfArity ``Prod 2 then
    let (left, next) ← localStorage stem ty.getAppArgs[0]! index
    let (right, next) ← localStorage stem ty.getAppArgs[1]! next
    return (← `(Native.Encoder.sep $left $right (by decide)), next)
  throwError "Private local storage supports finite products of Nat and Int"

/-- Internal layout synthesis for the standard native assembly commands. -/
syntax "native_local_storage%" str ":" term : term
open Lean Elab Term in
elab_rules : term
  | `(native_local_storage% $stem:str : $ty:term) => do
    let ty ← elabType ty
    let (code, _) ← localStorage stem.getString ty 0
    elabTerm code none

end AlgoLib.Experimental.RAM.Native
