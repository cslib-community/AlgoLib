/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend
import AlgoLib.Experimental.RAM.Prototype.Mutable
import AlgoLib.Experimental.RAM.Prototype.MultipleArrays
import AlgoLib.Experimental.RAM.Prototype.Verification

/-!
# Optional default RAM backend for the pure mutable frontend

`ram method` and `prove_algorithm` live in LogicalFrontend with no RAM imports.
`prove_ram` is a convenience: prove that same logical algorithm, then attach the
standard array backend. Alternative backends use `Interface.realize` on the exact
same specification and proof. Acceptance reconstructs Supported evidence.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Meta Parser Authoring

syntax "prove_ram" ident "by" tacticSeq : command
elab_rules : command
  | `(command| prove_ram $name:ident by $proof:tacticSeq) => do
    elabCommand (← `(command| prove_algorithm $name by $proof))
    let checked := mkIdent (name.getId.appendAfter "Correct")
    let verified := mkIdent (name.getId.appendAfter "Verified")
    let api ← Command.runTermElabM fun _ => do
      let specExpr ← elabTerm name none
      let type ← instantiateMVars (← inferType specExpr)
      let state ← whnf type.getAppArgs[0]!
      if state.isConstOf ``Mutable.State then `(Mutable.interface)
      else if state.isAppOfArity ``MultipleArrays.State 1 then
        let number ← whnf state.getAppArgs[0]!
        let .lit (.natVal n) := number | throwError "Expected a fixed array count, got {number}"
        let count := quote n
        `(MultipleArrays.interface $count)
      else throwError "Choose an implementation using Interface.realize"
    elabCommand (← `(command| def $verified := ($api).realize $name $checked))

end AlgoLib.Experimental.RAM.Prototype.Frontend
