/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LegacyArrayFrontend
import AlgoLib.Experimental.RAM.Prototype.Mutable
import AlgoLib.Experimental.RAM.Prototype.MultipleArrays
import AlgoLib.Experimental.RAM.Prototype.Verification

/-!
# Compatibility backend for historical array methods

`prove_ram` attaches the old array backend to an explicitly declared `legacy_ram`
method. It is retained for existing compiler/substitution regressions. New methods
use Composition's unified frontend and Composition.Encoding for backend attachment.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Meta Parser Authoring

syntax "prove_ram" ident "by" tacticSeq : command
elab_rules : command
  | `(command| prove_ram $name:ident by $proof:tacticSeq) => do
    elabCommand (← `(command| prove_legacy_algorithm $name by $proof))
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
