/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Frontend

/-!
# Public mutable method frontend

Every `ram method` uses the owned, typed program language: scalars, indexed arrays,
and modular calls may be combined in one body. `prove_algorithm` discharges the
indexed contract plan; the same body is interpreted by Loom and the verified linker.

The explicitly named `legacy_ram` command remains for historical array-substitution
regressions. It is never selected by argument types or invoked by this frontend.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Parser

def termBeforeCost := withForbidden "credits" (withForbidden "time" termBeforeReqEnsDo)
attribute [run_builtin_parser_attribute_hooks] termBeforeCost
builtin_initialize register_parser_alias termBeforeCost

declare_syntax_cat ramRequire
declare_syntax_cat ramEnsures
declare_syntax_cat ramCredits
declare_syntax_cat ramTime
syntax "require" termBeforeCost : ramRequire
syntax "ensures" termBeforeCost : ramEnsures
syntax "credits" termBeforeCost : ramCredits
syntax "time" Term.termBeforeDo : ramTime
syntax "ram" "method" ident leafny_binder* "return" "(" ident ":" term ")"
  ramRequire* ramEnsures* (ramCredits)? (ramTime)? "do" Term.doSeq : command

elab_rules : command
  | `(command| ram method $name:ident $binders:leafny_binder* return ($ret:ident : $retTy:term)
      $pres:ramRequire* $posts:ramEnsures* $[$creditClause:ramCredits]? $[$timeClause:ramTime]?
      do $body:doSeq) => do
    if let some clause := timeClause then
      throwErrorAt clause "RAM time is inferred from logical credits; remove the time clause"
    Composition.Frontend.declareMethod name binders ret retTy
      (pres.map (fun x => ⟨x.raw[1]⟩)) (posts.map (fun x => ⟨x.raw[1]⟩))
      (creditClause.map (fun c => ⟨c.raw[1]⟩)) body

/-- Generate owned call obligations using only public summaries and mathematical views. -/
macro "contract_vc" : tactic =>
  `(tactic| (dsimp only [Composition.Algorithm.Obligations, Composition.Plan.vc,
    Composition.Procedure.uniform, Composition.testLeft, Composition.testRight,
    Composition.assign, Composition.write, Composition.compare, Composition.Relation.eval,
    Composition.Value.eval, Composition.Value.Safe, Composition.Value.credits,
    Composition.Arithmetic.eval, Composition.Path.get, Composition.Path.set,
    Composition.enterLocals, Composition.leaveLocals, Composition.Locals.initial,
    Composition.associate, Composition.unassociate,
    Composition.Locals.credits] at *; simp (config := { maxSteps := 1000000 }) at *))

/-- Normalize framework plumbing, then use only mathematical lemmas supplied by the author. -/
macro "contract_solve" "[" rules:Lean.Parser.Tactic.grindParam,* "]" : tactic =>
  `(tactic| (
    contract_vc
    repeat' (first | (with_reducible intro) | (apply And.intro) | (split))
    all_goals grind only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
      Array.size_setIfInBounds, $rules,*]))

syntax "prove_algorithm" ident "by" tacticSeq : command
elab_rules : command
  | `(command| prove_algorithm $name:ident by $proof:tacticSeq) => do
    let owned := mkIdent (name.getId.appendAfter "Obligations")
    let checked := mkIdent (name.getId.appendAfter "Verification")
    let certified := mkIdent (name.getId.appendAfter "Procedure")
    let certificate := mkIdent (name.getId.appendAfter "Certificate")
    elabCommand (← `(command|
      theorem $checked : $owned := by
        unfold $owned $name
        ($proof)))
    elabCommand (← `(command| @[reducible] def $certified := $certificate $checked))

end AlgoLib.Experimental.RAM.Prototype.Frontend
