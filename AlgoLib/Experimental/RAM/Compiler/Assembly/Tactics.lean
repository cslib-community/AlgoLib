/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Lean

/-!
# Shared certificate reconstruction tactics

`ram_link` and `ram_code_eq` reconstruct kernel-checked evidence. They inspect
Lean goals only and depend on no memory representation or execution backend.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition

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
