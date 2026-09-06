/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Velvet.Syntax
import AlgoLib.Experimental.RAM.Prototype.LoomObservation

/-!
# Typed, compositional procedures over certified data-structure interfaces

`ram_do (entry, state, remaining) do ...` uses Velvet's annotated-loop grammar.
`perform op` invokes a certified primitive; `call procedure` invokes a separately
verified relational/cost contract. Both emit the actual implementation, never an
uncharged host computation. Procedures share a typed model and inline at compilation;
there is no runtime call stack. This frontend complements mutable `ram method` with
abstract graph/queue/cursor interfaces and works for any certified `Model`.

The entry state and current state are mathematical views used only in annotations.
Only certified guards, primitives, and procedure bodies occur in executable code.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring Lean Elab Term Parser

/-- Procedure contracts also establish the actual Loom observation. -/
theorem Routine.loom_correct {State : Type} {M : Model State} (p : Routine M)
    (s : State) (hs : p.requires s) :
    _root_.wp (denote p.body) (fun _ t _ => p.ensures s t) s (p.work s) := by
  rw [loom_wp_eq]
  obtain ⟨k, t, run, post, cost⟩ := p.verification s hs
  exact ⟨k, t, (), run_denote run, cost, post⟩

syntax "call " term : doElem
syntax "perform " term : doElem

private def items (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Parser.Term.doSeqBracketed then stx[1].getArgs.map (·[0])
  else if stx.getKind == ``Parser.Term.doSeqIndent then stx[0].getArgs.map (·[0])
  else #[]

private structure Code where
  body : Term
  plan : Term

private partial def lower (state credit : Ident) (body : TSyntax ``Parser.Term.doSeq) :
    TermElabM Code := do
  let mut result : Code := ⟨← `(Program.skip), ← `(Plan.skip)⟩
  for stx in (items body.raw).reverse do
    let part ← step state credit ⟨stx⟩
    result := ⟨← `(Program.seq $(part.body) $(result.body)),
      ← `(Plan.seq $(part.plan) $(result.plan))⟩
  return result
where
  step (state credit : Ident) (stx : TSyntax `doElem) : TermElabM Code := withRef stx do
    match stx with
    | `(doElem| perform $op:term) =>
      return ⟨← `(Program.action $op), ← `(Plan.action $op)⟩
    | `(doElem| call $proc:term) =>
      return ⟨← `(Routine.body $proc), ← `(Plan.call $proc)⟩
    | `(doElem| while $guard:term
        $[invariant $[$label:str]? $inv:term
        ]*
        $[done_with $done]?
        $[decreasing $measure]?
        do $body:doSeq) =>
      let part ← lower state credit body
      let mut predicate ← `(True)
      for fact in inv.reverse do predicate ← `($fact ∧ $predicate)
      let invariantTerm ← `(fun $state $credit => $predicate)
      let plan ← match measure with
        | none => `(Plan.loop $guard $invariantTerm $(part.plan))
        | some n =>
          `(Plan.loopVariant $guard $invariantTerm (fun $state => ($n : Nat)) $(part.plan))
      let plan ← match done with
        | none => pure plan
        | some post => `(Plan.ensure (fun $state => $post) $plan)
      return ⟨← `(Program.loop $guard $(part.body)), plan⟩
    | `(doElem| if $guard:term then $yes:doSeq else $no:doSeq) =>
      let yes ← lower state credit yes
      let no ← lower state credit no
      return ⟨← `(Program.branch $guard $(yes.body) $(no.body)),
        ← `(Plan.branch $guard $(yes.plan) $(no.plan))⟩
    | `(doElem| assert $p:term) =>
      return ⟨← `(Program.skip), ← `(Plan.assert (fun $state => $p))⟩
    | `(doElem| pure ()) => return ⟨← `(Program.skip), ← `(Plan.skip)⟩
    | _ => throwErrorAt stx
      "Expected a certified primitive, procedure call, or annotated loop"

syntax (name := ramDo) "ram_do" "(" ident "," ident "," ident ")" "do" Term.doSeq : term

@[term_elab ramDo] def elabRamDo : TermElab := fun stx expectedType? => do
  match stx with
  | `(ram_do ($entry:ident, $state:ident, $credit:ident) do $body:doSeq) => do
    if entry.getId == state.getId || entry.getId == credit.getId || state.getId == credit.getId then
      throwError "Entry state, current state, and credit names must be distinct"
    let code ← lower state credit body
    let term ← `(Annotated.mk $(code.body) (Plan.atEntry (fun $entry => $(code.plan))))
    elabTerm term expectedType?
  | _ => throwUnsupportedSyntax

/-- Open procedure VCs without unfolding implementation or compiler certificates. -/
macro "procedure_vc" "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Plan.vc, paper_simps, $rules,*] at *)

end AlgoLib.Experimental.RAM.Prototype
