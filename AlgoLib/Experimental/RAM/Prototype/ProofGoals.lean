/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Frontend

/-!
# Mathematical verification-goal normalization

This module removes source-language plumbing while preserving labelled propositions.
Positional tactics are maintained internal machinery for library proofs and regression
fixtures. New author-facing commands consume the generated obligation API.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Frontend
open Lean Elab Command Term Parser

/-- Generate owned call obligations using only public summaries and mathematical views. -/
macro "contract_vc" : tactic =>
  `(tactic| (dsimp only [Composition.Algorithm.Obligations, Composition.Plan.vc,
    Composition.SourceForall, Composition.InvariantFact,
    Composition.Obligation, Composition.ObligationAt,
    Composition.Procedure.uniform,
    Composition.UniformCredits.amount,
    Composition.testLeft, Composition.testRight,
    Composition.assign, Composition.signedAssign, Composition.signedWrite,
    Composition.compareSigned,
    Composition.SignedValue.eval, Composition.SignedValue.Safe,
    Composition.SignedValue.credits, Composition.SignedValue.costs,
    Composition.Arithmetic.evalInt, Composition.Relation.evalInt,
    Composition.write, Composition.compare, Composition.Relation.eval,
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

/-- Keep source labels while eliminating program, path, and contract-plan machinery. -/
macro "paper_unfold" : tactic =>
  `(tactic| (dsimp only [Composition.Algorithm.Obligations, Composition.Plan.vc,
    Composition.Procedure.uniform,
    Composition.UniformCredits.amount, Composition.testLeft, Composition.testRight,
    Composition.assign, Composition.signedAssign, Composition.signedWrite,
    Composition.compareSigned,
    Composition.SignedValue.eval, Composition.SignedValue.Safe,
    Composition.SignedValue.credits, Composition.SignedValue.costs,
    Composition.Arithmetic.evalInt, Composition.Relation.evalInt,
    Composition.write, Composition.compare, Composition.Relation.eval,
    Composition.Value.eval, Composition.Value.Safe, Composition.Value.credits,
    Composition.Arithmetic.eval, Composition.Path.get, Composition.Path.set,
    Composition.enterLocals, Composition.leaveLocals, Composition.Locals.initial,
    Composition.associate, Composition.unassociate,
    Composition.Locals.credits] at *))

/-- Simplification for the legacy positional interface. -/
macro "paper_normalize" : tactic =>
  `(tactic| (paper_unfold; simp (config := { maxSteps := 1000000 }) at *))

open Meta Tactic in
private partial def splitPaperGoal (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    if ty.isAppOfArity ``Composition.Obligation 2 ||
        ty.isAppOfArity ``Composition.ObligationAt 3 then
      let args := ty.getAppArgs
      let mut label := match ← whnf args[0]! with
        | .lit (.strVal s) => s
        | _ => "source obligation"
      if args.size == 3 then
        if let .lit (.strVal site) ← whnf args[1]! then
          label := label ++ " at " ++ site
      goal.setTag (Name.str .anonymous label)
      let goal ← goal.change args.back!
      splitPaperGoal goal
    else if ty.isForall then
      let (_, goal) ← goal.intro1
      splitPaperGoal goal
    else if ty.isAppOfArity ``And 2 then
      let tag ← goal.getTag
      let children ← goal.apply (mkConst ``And.intro)
      if tag.toString.contains " at " then
        for child in children do child.setTag tag
      return (← children.mapM splitPaperGoal).flatten
    else if ty.isAppOf ``ite || ty.isAppOf ``dite then
      setGoals [goal]
      evalTactic (← `(tactic| split))
      return (← (← getGoals).mapM splitPaperGoal).flatten
    else
      let reduced ← withTransparency .reducible (whnf ty)
      if reduced != ty then
        splitPaperGoal (← goal.change reduced)
      else
        return [goal]

/-- Open named mathematical goals. All generated compiler terms are normalized internally. -/
elab "paper_vc" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| paper_normalize))
  let goals ← Lean.Elab.Tactic.getGoals
  Lean.Elab.Tactic.setGoals (← goals.flatMapM splitPaperGoal)
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    all_goals (try simp only [Composition.InvariantFact, Composition.Obligation,
      Composition.ObligationAt] at *; try omega)))

/-- Solve paper VCs using the author's mathematical lemmas; failures keep source labels. -/
macro "paper_solve" "[" rules:Lean.Parser.Tactic.grindParam,* "]" : tactic =>
  `(tactic| (
    paper_vc
    all_goals (try (first | omega | grind only [Array.set!_eq_setIfInBounds,
      Array.toList_setIfInBounds, Array.size_setIfInBounds, $rules,*]))))

end AlgoLib.Experimental.RAM.Prototype.Frontend
