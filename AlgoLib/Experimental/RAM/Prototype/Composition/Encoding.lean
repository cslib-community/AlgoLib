/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.LocalImplementation

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

structure Encoder (P : Representation A) where
  footprint : Footprint
  requires : A → Prop
  saved : A → Nat
  store : A → Store
  correct : ∀ a, requires a → P.holds a footprint (store a) (saved a)

/-- Recover an encoder's representation without repeating its generated local layout. -/
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

def Encoder.sep (p : Encoder P) (q : Encoder Q) (hd : Disjoint p.footprint q.footprint) :
    Encoder (P.sep Q) where
  footprint := p.footprint ∪ q.footprint
  requires a := p.requires a.1 ∧ q.requires a.2
  saved a := p.saved a.1 + q.saved a.2
  store a := overlay p.footprint (p.store a.1) (q.store a.2)
  correct a h := ⟨p.footprint, q.footprint, p.saved a.1, q.saved a.2, hd, rfl, rfl,
    P.locality (overlay_left _ _ _) (p.correct _ h.1),
    Q.locality (overlay_right _ _ _ _ hd) (q.correct _ h.2)⟩

def Encoder.hide {Q : Representation L} (p : Encoder P) (q : Encoder Q) [l : Locals L]
    (hq : q.requires l.initial) (hd : Disjoint p.footprint q.footprint) : Encoder (P.hide Q) where
  footprint := p.footprint ∪ q.footprint
  requires := p.requires
  saved a := p.saved a + q.saved l.initial
  store a := (p.sep q hd).store (a, l.initial)
  correct _ h := ⟨l.initial, (p.sep q hd).correct _ ⟨h, hq⟩⟩

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
  store a := { vars := fun _ _ => a.size, heap := fun i => a[i-l.base]! }
  correct a h := ⟨rfl, h, rfl, fun i _ => by simp, rfl⟩

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
        rate * proc.credits a + encoder.saved a :=
  runProcedure_correct (rate := rate) (P := P) proc a valid encoder.footprint
    (encoder.store a) (encoder.saved a) (encoder.correct a resident)

open Lean Elab Term in
private partial def localStorage (stem : String) (ty : Lean.Expr) (index : Nat) :
    TermElabM (Term × Nat) := do
  let ty ← Lean.Meta.whnf ty
  if ty.isConstOf ``Nat then
    let name := quote (stem ++ "." ++ toString index)
    return (← `(scalarEncoder ⟨$name⟩), index + 1)
  if ty.isAppOfArity ``Prod 2 then
    let (left, next) ← localStorage stem ty.getAppArgs[0]! index
    let (right, next) ← localStorage stem ty.getAppArgs[1]! next
    return (← `(Encoder.sep $left $right (by decide)), next)
  throwError "Private local storage supports finite products of Nat"

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

end AlgoLib.Experimental.RAM.Prototype.Composition
