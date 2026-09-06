/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly
import AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.SortingExecution

/-!
# Acceptance tests for the paper loop interface

These tests cover a potential whose individual counters may increase, modular
repricing without changing a client proof, bounds that must be rejected, and actual
fuel-free RAM execution. Insertion sort supplies the dependent nested-loop test.
Only the small backend package below deals with storage; source proofs do not.
-/
namespace AlgoLib.Experimental.RAM.Tests.PaperLoops
open Prototype.Composition Prototype.Frontend

/- `pending` may increase; the aggregate amount of outstanding work decreases. -/
ram method worklist (mut jobs : Nat) (mut pending : Nat) return (u : Unit)
  require True
  ensures jobs = 0 ∧ pending = 0
  do
    while 0 < jobs + pending
      invariant True
      amortized_potential 2 * jobs + pending
      do
        if 0 < pending then
          pending := pending - 1
        else
          jobs := jobs - 1
          pending := 1

prove_algorithm worklist by paper_solve []

/-- Implement different amounts of real work behind the same functional summary. -/
@[reducible] def clearBody : Nat → Program (List Nat) (List Nat)
  | 0 => .invoke Buffer.clear
  | extra + 1 => .seq (.invoke Buffer.clear) (clearBody extra)

/-- Every additional clear is present in the source semantics and compiled RAM. -/
theorem clearBody_run (extra : Nat) (xs : List Nat) : Run (clearBody extra) xs (extra + 1) [] := by
  induction extra generalizing xs with
  | zero => exact Run.invoke Buffer.clear xs trivial
  | succ extra ih =>
    have h := Run.seq (Run.invoke Buffer.clear xs trivial) (ih [])
    simpa [clearBody, Buffer.clear, Nat.add_comm] using h

/-- Replacing the implementation changes its allowance, but not its functional contract. -/
@[reducible] def clearing (extra : Nat) : Procedure (List Nat) (List Nat) where
  body := clearBody extra
  requires _ := True
  «ensures» _ ys := ys = []
  «credits» _ := extra + 1
  correct xs _ := ⟨extra + 1, [], clearBody_run extra xs, rfl, Nat.le_refl _⟩

@[simp] theorem clearing_requires (extra : Nat) (xs : List Nat) :
    (clearing extra).requires xs ↔ True := Iff.rfl

instance (extra : Nat) : UniformCredits (clearing extra) where
  amount := extra + 1
  bound _ := Nat.le_refl _

/- A single proof for every advertised allowance, with no manual credit invariant. -/
ram method repeatedClear (extra : Nat) (mut buffer : List Nat) (mut count : Nat)
    return (u : Unit)
  require True
  ensures count = 0
  do
    while 0 < count
      invariant True
      iterations_at_most count
      do
        buffer := clearing extra
        count := count - 1

prove_algorithm repeatedClear by paper_solve []

/-- Repricing the callee changes the inferred total by exactly one increase per iteration. -/
example (extra : Nat) (xs : List Nat) (n : Nat) :
    (repeatedClear extra).credits (xs, n) = (repeatedClear 0).credits (xs, n) + extra * n := by
  simp [UniformCredits.amount, Value.credits, Locals.credits]
  ring

/- An initial total bound is insufficient if it is not a decreasing remaining bound. -/
ram method badBound (mut x : Nat) return (u : Unit)
  require x = 1
  ensures x = 0
  do
    while 0 < x
      invariant x ≤ 1
      iterations_at_most 0
      do
        x := x - 1

example : ¬badBoundObligations := by
  intro h
  have h := h 1 ⟨rfl, trivial⟩
  have zero : ∀ a ≤ 1, a = 0 := by
    simpa [Plan.vc, Obligation, ObligationAt, assign, Value.eval, Value.credits, Value.Safe,
      Path.get, Path.set, enterLocals, leaveLocals, Locals.initial, Locals.credits,
      Prototype.Composition.compare, Relation.eval] using h
  have := zero 1 (by decide)
  omega

/- A bound cannot manufacture termination for a loop that makes no progress. -/
ram method noProgress (mut x : Nat) return (u : Unit)
  require x = 1
  ensures x = 0
  do
    while 0 < x
      invariant x = 1
      iterations_at_most x
      do
        x := x

example : ¬noProgressObligations := by
  intro h
  have h := h 1 ⟨rfl, trivial⟩
  simp [Plan.vc, Obligation, ObligationAt, assign, Value.eval,
    Value.credits, Value.Safe, Path.get, Path.set, enterLocals, leaveLocals,
    Locals.initial, Locals.credits, Prototype.Composition.compare, Relation.eval] at h

private abbrev clearLayout : BufferImplementation.Layout := ⟨"clear.buffer", 0, 2⟩
private abbrev clearScratch := local_storage% "clear.locals" : repeatedClearLocals
private abbrev clearEncoder :=
  ((BufferImplementation.encoder clearLayout false).sep (scalarEncoder ⟨"clear.count"⟩)
    (by dsimp [BufferImplementation.encoder, scalarEncoder, clearLayout]; decide)).hide clearScratch
      (by simp [clearScratch, Encoder.sep, scalarEncoder])
      (by dsimp [BufferImplementation.encoder, scalarEncoder, clearLayout,
        clearScratch, Encoder.sep]
          decide)

private instance : Linked 24 clearEncoder.representation (repeatedClearProcedure 0).body
    clearEncoder.representation := by ram_link
private instance : Linked 24 clearEncoder.representation (repeatedClearProcedure 2).body
    clearEncoder.representation := by ram_link

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 5 do
    let input := ([7, 8], n)
    let fast := runEncoded (rate := 24) (Q := clearEncoder.representation)
      (repeatedClearProcedure 0) clearEncoder input (by trivial) (by change 2 ≤ 2 ∧ True; decide)
    let slow := runEncoded (rate := 24) (Q := clearEncoder.representation)
      (repeatedClearProcedure 2) clearEncoder input (by trivial) (by change 2 ≤ 2 ∧ True; decide)
    unless fast.value == slow.value && slow.steps == fast.steps + 4 * n do
      throw <| IO.userError "procedure substitution / inferred repeated-call cost"
    unless fast.steps ≤ 24 * (repeatedClear 0).credits input &&
        slow.steps ≤ 24 * (repeatedClear 2).credits input do
      throw <| IO.userError "repriced procedure bound"

/- Diagnostics are tested without asserting an unprovable theorem or introducing an admission. -/
open Lean Elab Command in
elab "#check_paper_diagnostic " name:ident " contains " expected:str : command =>
  Command.runTermElabM fun _ => do
    let obligations := mkIdent (name.getId.appendAfter "Obligations")
    let type ← Term.elabType (← `($obligations))
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar type
    let goals ← Tactic.run goal.mvarId! do
      Tactic.evalTactic (← `(tactic| unfold $obligations $name; paper_vc))
    unless ← goals.anyM (fun goal => return (← goal.getTag).toString.contains expected.getString) do
      throwError "Missing source diagnostic: {expected.getString}"
    for goal in goals do
      let type ← goal.getType
      if (type.find? fun e => e.isConst &&
          ([``Plan.vc, ``Program, ``Path.get, ``Path.set, ``Value.eval].contains
            e.constName!)).isSome then
        throwError "Internal program representation leaked into a paper VC"

ram method badIndex (mut arr : Array Nat) return (u : Unit)
  require True
  ensures True
  do
    let value := arr[arr.size]!
    return

ram method badInvariant (mut x : Nat) return (u : Unit)
  require x = 1
  ensures x = 0
  do
    while 0 < x
      invariant "positive counter" x = 1
      iterations_at_most x
      do
        x := x - 1

set_option linter.hashCommand false in
#check_paper_diagnostic badBound contains "iteration bound positive"
set_option linter.hashCommand false in
#check_paper_diagnostic noProgress contains "iteration bound decreases"
set_option linter.hashCommand false in
#check_paper_diagnostic badIndex contains "array index within bounds"
set_option linter.hashCommand false in
#check_paper_diagnostic badInvariant contains "positive counter"

/- The combined student command also works when the method needs no local storage. -/
ram method unchanged (mut arr : Array Nat) return (u : Unit)
  require True
  ensures arr = arrOld
  do
    return

verify_array_method unchanged by paper_solve []

private abbrev scratch := local_storage% "paper.worklist" : worklistLocals
private abbrev encoder := ((scalarEncoder ⟨"jobs"⟩).sep (scalarEncoder ⟨"pending"⟩)
  (by decide)).hide scratch
    (by simp [scratch, Encoder.sep, scalarEncoder])
    (by simp [scratch, Encoder.sep, scalarEncoder, Finset.disjoint_left])

private instance : Linked 24 encoder.representation worklistProcedure.body
    encoder.representation := by ram_link

/-- The generic assembly API also supports product inputs and outputs. -/
def worklistExecutable : CertifiedExecutable worklistProcedure :=
  .ofEncoded worklistProcedure (fun _ => encoder.representation)
    (fun _ => encoder.representation) (fun _ => encoder) 24
    (by intros; trivial) (by intros; rfl)

set_option linter.hashCommand false in
#eval show IO Unit from do
  for jobs in List.range 6 do
    for pending in List.range 6 do
      let r := worklistExecutable.run (jobs, pending) (by trivial)
      unless r.value == (0, 0) && r.steps ≤ worklistExecutable.bound (jobs, pending) do
        throw <| IO.userError "weighted work potential / assembled execution"
  unless (unchangedRun [2, 1]).value == [2, 1] && unchangedBound [2, 1] == 0 do
    throw <| IO.userError "combined assembly without local storage"
  unless (Sorting.insertionSortRun [4, 1, 3, 1, 2]).value == [1, 1, 2, 3, 4] do
    throw <| IO.userError "automatically assembled insertion sort"

end AlgoLib.Experimental.RAM.Tests.PaperLoops
