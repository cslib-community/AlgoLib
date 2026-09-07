/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.LocalImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.ResidentInputs

/-!
# Compositional resident input interfaces

Encoding supplies a represented input store; it is host-side setup, as in the
existing runners. Separating encoders merge disjoint footprints and saved potential.
Private-local encoders hide scratch from users. Actual execution and decoding still
use the verified RAM runner, with no fuel and no source evaluator shortcut.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

abbrev Encoder (P : Representation A) := Ownership.Encoder P
abbrev Encoder.representation {A : Type} {P : Representation A} (_ : Encoder P) := P

/-- Copy only owned cells when assembling disjoint resident inputs. -/
def overlay (r : Footprint) (s t : Store) : Store where
  vars ty name := if .register ty name ∈ r then s.vars ty name else t.vars ty name
  heap i := if .heap i ∈ r then s.heap i else t.heap i

theorem overlay_left (r : Footprint) (s t : Store) : Agree r s (overlay r s t) := by
  intro l hl
  cases l <;> simp_all [cell, overlay]

theorem overlay_right (r f : Footprint) (s t : Store) (h : Disjoint r f) :
    Agree f t (overlay r s t) := by
  intro l hl
  have hn : l ∉ r := fun hr => Finset.disjoint_left.mp h hr hl
  cases l <;> simp_all [cell, overlay]

instance : Ownership.Overlay ownershipModel where
  overlay := overlay
  left := overlay_left
  right := overlay_right

abbrev Encoder.sep (p : Encoder P) (q : Encoder Q) (hd : Disjoint p.footprint q.footprint) :
    Encoder (P.sep Q) := Ownership.Encoder.sep p q hd

abbrev Encoder.hide {Q : Representation L} (p : Encoder P) (q : Encoder Q) [l : Locals L]
    (hq : q.requires l.initial) (hd : Disjoint p.footprint q.footprint) : Encoder (P.hide Q) :=
  Ownership.Encoder.hide p q hq hd

def scalarEncoder (v : Var .word) : Encoder (Storage.scalar v) where
  footprint := {.register .word v.name}
  requires _ := True
  saved _ := 0
  store a := { vars := fun _ _ => a, heap := fun _ => 0 }
  correct _ _ := ⟨rfl, rfl, rfl⟩

def arrayEncoder (l : Storage.ArrayLayout) : Encoder (Storage.array l) where
  footprint := l.footprint
  requires a := a.size ≤ l.capacity
  saved _ := 0
  store a := { vars := fun _ _ => a.size, heap := fun i => a.getD (i-l.base) 0 }
  correct a h := ⟨rfl, h, rfl, fun i _ => by simp [Array.getElem!_eq_getD], rfl⟩

/-- Library runners need only ordinary inputs and their advertised preconditions. -/
def runEncoded (proc : Procedure A B) (encoder : Encoder P)
    [Linked rate P proc.body Q] [Decoder Q] (a : A)
    (valid : proc.requires a) (resident : encoder.requires a) : Result B :=
  runProcedure (rate := rate) (P := P) proc a valid encoder.footprint (encoder.store a)
    (encoder.saved a) (encoder.correct a resident)

theorem runEncoded_correct (proc : Procedure A B) (encoder : Encoder P)
    [Linked rate P proc.body Q] [Decoder Q] (a : A)
    (valid : proc.requires a) (resident : encoder.requires a) :
    proc.ensures a (runEncoded (rate := rate) proc encoder a valid resident).value ∧
      (runEncoded (rate := rate) proc encoder a valid resident).steps ≤
        2 * (rate * proc.credits a + encoder.saved a) :=
  runProcedure_correct (rate := rate) (P := P) proc a valid encoder.footprint
    (encoder.store a) (encoder.saved a) (encoder.correct a resident)

open Lean Elab Term in
private partial def localStorage (stem : String) (ty : Lean.Expr) (index : Nat) :
    TermElabM (Term × Nat) := do
  let ty ← Lean.Meta.whnf ty
  if ty.isConstOf ``Nat then
    let name := quote (stem ++ "." ++ toString index)
    return (← `(scalarEncoder ⟨$name⟩), index + 1)
  if ty.isConstOf ``Int then
    let name := quote (stem ++ "." ++ toString index)
    let constructor := mkIdent `AlgoLib.Experimental.RAM.Prototype.Composition.signedEncoder
    return (← `($constructor $name), index + 1)
  if ty.isAppOfArity ``Prod 2 then
    let (left, next) ← localStorage stem ty.getAppArgs[0]! index
    let (right, next) ← localStorage stem ty.getAppArgs[1]! next
    return (← `(Encoder.sep $left $right (by decide)), next)
  throwError "Private local storage supports finite products of Nat and Int"

/-- Reconstruct the finite register layout from the generated local type. -/
syntax "local_storage%" str ":" term : term
open Lean Elab Term in
elab_rules : term
  | `(local_storage% $stem:str : $ty:term) => do
    let ty ← elabType ty
    let (code, _) ← localStorage stem.getString ty 0
    elabTerm code none

open Lean Elab Tactic

/-- Reconstruct large structural certificates without exposing typeclass tuning to clients. -/
elab "ram_link" : tactic => do
  evalTactic (← `(tactic| set_option synthInstance.maxSize 100000 in exact inferInstance))

/-- Compare executable constructors without first unifying their discarded ownership
indices. Every step reconstructs equality by reflexivity or congruence. -/
private partial def codeEquality (left right : Lean.Expr) : Lean.Meta.MetaM Lean.Expr := do
  if left == right then return ← Lean.Meta.mkEqRefl left
  let l ← Lean.Meta.withTransparency .all (Lean.Meta.whnf left)
  let r ← Lean.Meta.withTransparency .all (Lean.Meta.whnf right)
  if l == r then return ← Lean.Meta.mkEqRefl l
  match l, r with
  | .app f x, .app g y =>
    let hf ← codeEquality f g
    let hx ← codeEquality x y
    Lean.Meta.mkAppM ``congr #[hf, hx]
  | _, _ => throwError "Different executable code: {l} and {r}"

/-- Backend-only code equality certificate reconstruction. There is no unchecked
comparison or solver axiom: the elaborator emits an ordinary kernel-checked proof. -/
elab "ram_code_eq" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← goal.getType).eq? | throwError "Expected code equality"
  goal.assign (← codeEquality lhs rhs)
  replaceMainGoal []

end AlgoLib.Experimental.RAM.Prototype.Composition
