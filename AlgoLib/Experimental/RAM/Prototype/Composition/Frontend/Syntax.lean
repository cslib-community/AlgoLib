/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Velvet.Syntax
import AlgoLib.Experimental.RAM.Prototype.Composition.Expressions

/-!
# Surface grammar and public contract selection

Declares owned-method statement and loop syntax. This module does not route resources or
generate methods.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
open Lean Elab Command Term Meta Parser

syntax (name := receiverCall) ident noWs "(" term,* ")" : doElem
declare_syntax_cat loopCost
syntax "iterations_at_most" Term.termBeforeDo : loopCost
syntax "amortized_potential" Term.termBeforeDo : loopCost
syntax (name := workPotential) "amortized_work" Term.termBeforeDo : loopCost
syntax (name := boundedWork)
  "amortized_work" Term.termBeforeDo "initially_at_most" Term.termBeforeDo : loopCost
syntax "at_loop_entry" "(" term ")" : term
syntax (name := paperWhile) "while " term
  ("invariant " (str)? term)* loopCost
  ("done_with " term)? ("decreasing " term)? " do " doSeq : doElem

/-- Named loops keep proof identities stable when source locations change. -/
syntax (name := namedWhile) "while " term " named " ident
  ("invariant " (str)? term)* loopCost
  ("done_with " term)? ("decreasing " term)? " do " doSeq : doElem
syntax (name := namedStatements) "named " ident " do " doSeq : doElem

syntax (name := pairCall) "(" ident "," ident ")" " := " term : doElem

/-- Use a library's uniform allowance when available; dependent contracts need no adapter. -/
syntax "contract% " term:max : term
elab_rules : term
  | `(contract% $proc:term) => do
    let p ← elabTerm proc none
    let type ← mkAppM ``UniformCredits #[p]
    if let some _ ← synthInstance? type then
      elabTerm (← `(Procedure.uniform $proc)) none
    else pure p


end AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
