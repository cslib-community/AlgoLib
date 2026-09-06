/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Semantics
import AlgoLib.Experimental.RAM.Backend.Language.VC

/-!
# Separate RAM realizations of logical credit contracts

`Action` and `Program` belong to the backend-independent credit logic. This module
provides implementations indexed by those exact contracts. Library instances pay
for concrete instructions and preserve representation; composition assembles them
without introducing compiler obligations into algorithmic proofs.

A logical program can have multiple realizations, each with its own representation,
code, and credit-to-instruction conversion. Its `Correct` proof is reused unchanged.
The public executable time bound includes preparation plus the realization's proved
conversion of the logical credit budget. Logical credits are never RAM instructions.
-/
namespace AlgoLib.Experimental.RAM.Authoring
open Checked Checked.Language

/-- A RAM representation and its uniform upper bound in instructions per logical credit. -/
structure Model (State : Type) where
  Represents : State → Store → Prop
  overhead : Nat

/-- A separately registered implementation of one logical action. -/
class ActionImplementation {State : Type} (M : Model State) (a : Action State) where
  implementation : Cmd
  correct : ∀ x s, M.Represents x s → a.requires x →
    ∃ k t, Eval implementation s k t ∧ M.Represents (a.effect x) t ∧
      k ≤ M.overhead * a.work x

class GuardImplementation {State : Type} (M : Model State) (q : Guard State) where
  implementation : Condition
  correct : ∀ a s, M.Represents a s → implementation.eval s = q.test a
  cost : implementation.cost ≤ M.overhead

/-- Reconstructed composition certificate, indexed by the exact logical program. -/
class Compilation {State : Type} (M : Model State) (p : Program State) where
  source : Cmd
  refinement : ∀ {a b : State} {k : Nat}, Run p a k b → ∀ s, M.Represents a s →
    ∃ j t, Eval source s j t ∧ M.Represents b t ∧ j ≤ M.overhead * k

instance compileSkip {State : Type} (M : Model State) : Compilation M .skip where
  source := .skip
  refinement h s hs := by cases h; exact ⟨0, s, .skip s, hs, by omega⟩

instance compileAction {State : Type} (M : Model State) (a : Action State)
    [impl : ActionImplementation M a] : Compilation M (.action a) where
  source := impl.implementation
  refinement h s hs := by cases h with | action _ _ valid => exact impl.correct _ _ hs valid

instance compileSeq {State : Type} (M : Model State) (a b : Program State)
    [ca : Compilation M a] [cb : Compilation M b] : Compilation M (.seq a b) where
  source := .seq ca.source cb.source
  refinement h s hs := by
    cases h with
    | seq ha hb =>
      obtain ⟨i, u, hu, hr, hi⟩ := ca.refinement ha s hs
      obtain ⟨j, t, ht, hr', hj⟩ := cb.refinement hb u hr
      exact ⟨_, t, .seq hu ht, hr', by nlinarith⟩

instance compileBranch {State : Type} (M : Model State) (q : Guard State) (a b : Program State)
    [cq : GuardImplementation M q] [ca : Compilation M a] [cb : Compilation M b] :
    Compilation M (.branch q a b) where
  source := .branch cq.implementation ca.source cb.source
  refinement h s hs := by
    cases h with
    | ifTrue hq ha =>
      obtain ⟨i, t, ht, hr, hi⟩ := ca.refinement ha s hs
      exact ⟨_, t, .ifTrue ((cq.correct _ _ hs).trans hq) ht, hr,
        by have := cq.cost; nlinarith⟩
    | ifFalse hq hb =>
      obtain ⟨i, t, ht, hr, hi⟩ := cb.refinement hb s hs
      exact ⟨_, t, .ifFalse ((cq.correct _ _ hs).trans hq) ht, hr,
        by have := cq.cost; nlinarith⟩

instance compileLoop {State : Type} (M : Model State) (q : Guard State) (b : Program State)
    [cq : GuardImplementation M q] [cb : Compilation M b] : Compilation M (.loop q b) where
  source := .loop cq.implementation cb.source
  refinement h s hs := by
    generalize he : Program.loop q b = p at h
    induction h generalizing s with
    | whileFalse hq =>
      cases he
      exact ⟨_, s, .whileFalse ((cq.correct _ _ hs).trans hq), hs, by simpa using cq.cost⟩
    | whileTrue hq hb hl _ ih =>
      cases he
      obtain ⟨i, u, hu, hr, hi⟩ := cb.refinement hb s hs
      obtain ⟨j, t, ht, hr', hj⟩ := ih u hr rfl
      exact ⟨_, t, .whileTrue ((cq.correct _ _ hs).trans hq) hu ht, hr',
        by have := cq.cost; nlinarith⟩
    | _ => cases he

instance compileProcedure {State : Type} (M : Model State) (p : Procedure State)
    [c : Compilation M p.body] : ActionImplementation M p.call where
  implementation := c.source
  correct a s hs ha := by
    obtain ⟨k, b, hb, he, hk⟩ := p.verification a ha
    subst b
    obtain ⟨j, t, ht, hr, hj⟩ := c.refinement hb s hs
    exact ⟨j, t, ht, hr, hj.trans (Nat.mul_le_mul_left _ hk)⟩

open Lean Meta Elab Tactic in
/-- Reconstruct a kernel-checked implementation certificate from the program tree.
Only program constructors are unfolded; primitive implementations must be registered.
Failure cannot introduce an implementation or a proof assumption. -/
partial def compilationTerm (state model program : Expr) : MetaM Expr := do
  let target := mkAppN (mkConst ``Compilation) #[state, model, program]
  if let some proof ← synthInstance? target then return proof
  let body ← withTransparency .default <| whnf program
  let args := body.getAppArgs
  let primitive (className : Name) (op : Expr) : MetaM Expr := do
    let target := mkAppN (mkConst className) #[state, model, op]
    match ← synthInstance? target with
    | some proof => return proof
    | none => throwError "No registered implementation for {target}"
  match body.getAppFn.constName? with
  | some ``Program.skip => return mkAppN (mkConst ``compileSkip) #[state, model]
  | some ``Program.action =>
    let op := args[1]!
    let impl ← if op.isAppOfArity ``Procedure.call 2 then do
        let proc := op.getAppArgs[1]!
        let body := mkAppN (mkConst ``Procedure.body) #[state, proc]
        pure <| mkAppN (mkConst ``compileProcedure)
          #[state, model, proc, ← compilationTerm state model body]
      else primitive ``ActionImplementation op
    return mkAppN (mkConst ``compileAction) #[state, model, op, impl]
  | some ``Program.seq =>
    let a := args[1]!
    let b := args[2]!
    return mkAppN (mkConst ``compileSeq)
      #[state, model, a, b, ← compilationTerm state model a, ← compilationTerm state model b]
  | some ``Program.branch =>
    let q := args[1]!
    let a := args[2]!
    let b := args[3]!
    return mkAppN (mkConst ``compileBranch) #[state, model, q, a, b,
      ← primitive ``GuardImplementation q,
      ← compilationTerm state model a, ← compilationTerm state model b]
  | some ``Program.loop =>
    let q := args[1]!
    let b := args[2]!
    return mkAppN (mkConst ``compileLoop) #[state, model, q, b,
      ← primitive ``GuardImplementation q, ← compilationTerm state model b]
  | _ => throwError "Cannot compile this logical program: {program}"

/-- Internal certificate assembly; the resulting proof term is checked by Lean. -/
elab "ram_compile" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic fun goal => do
    goal.withContext do
      let target ← Lean.instantiateMVars (← goal.getType)
      unless target.isAppOfArity ``Compilation 3 do
        throwError "Expected a Compilation certificate"
      let args := target.getAppArgs
      goal.assign (← compilationTerm args[0]! args[1]! args[2]!)
      pure []

def Program.source {State : Type} (p : Program State) (M : Model State)
    (c : Compilation M p := by ram_compile) : Cmd := c.source

theorem Run.refines {State : Type} {M : Model State} {p : Program State}
    [c : Compilation M p] {a b : State} {k : Nat} (h : Run p a k b)
    (s : Store) (hs : M.Represents a s) :
    ∃ j t, Eval (p.source M c) s j t ∧ M.Represents b t ∧ j ≤ M.overhead * k :=
  c.refinement h s hs

/-- Backend transport of an existing logical proof. No new algorithm proof is required. -/
def Correct.method {State : Type} {M : Model State} {p : Program State} [Compilation M p]
    {P : State → Prop} {Q : State → State → Prop} {budget : State → Nat}
    (h : Correct p P Q budget) (a : State) (ha : P a) : Checked.Language.Method where
  body := p.source M inferInstance
  requires := M.Represents a
  ensures _ t := ∃ b, Q a b ∧ M.Represents b t
  budget _ := M.overhead * budget a
  verification s hs := by
    obtain ⟨k, b, hb, hQ, hk⟩ := h a ha
    obtain ⟨j, t, ht, hr, hj⟩ := hb.refines s hs
    exact ⟨j, t, ht, ⟨b, hQ, hr⟩, hj.trans (Nat.mul_le_mul_left _ hk)⟩

end AlgoLib.Experimental.RAM.Authoring
