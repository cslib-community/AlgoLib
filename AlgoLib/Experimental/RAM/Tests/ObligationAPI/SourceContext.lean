/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend

/-!
# Source contexts use explicit roles and product routes

A tuple-valued configuration stays a single mathematical parameter. It must not be
split and renamed as if it were a pair of mutable program variables.
-/
namespace AlgoLib.Experimental.RAM.Tests.ObligationAPI.SourceContext
open Prototype.Frontend Prototype.Composition

ram method preserve (configuration : Nat × Nat) (mut counter : Nat) return (result : Nat)
  require configuration.1 ≤ counter
  ensures counter = counterOld
  do
    counter := counter

generate_obligations preserve
complete_algorithm preserve

open Lean Elab Command in
run_cmd do
  let info ← liftCoreM <| getConstInfo
    ``preserve.ObligationAPI.result
  let some body := info.value? | throwError "Expected a generated proposition"
  unless (body.find? fun e => match e with
      | .forallE name type _ _ => name == `configuration && type.isAppOfArity ``Prod 2
      | _ => false).isSome do
    throwError "The source configuration tuple was lost or mistaken for mutable state"

end AlgoLib.Experimental.RAM.Tests.ObligationAPI.SourceContext
