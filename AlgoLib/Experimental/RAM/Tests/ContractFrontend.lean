/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Demo

/-!
# End-to-end contract/frontend regressions

The same source proof executes through all buffer choices. Test affine allowances,
body-independent summaries, generic procedure parameters, three owned resources,
loop/branch calls, actual Loom WP, and unsupported callee rejection. No frontend
metaprogram or solver result is trusted without reconstructed Lean proofs.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Tests.ContractFrontend
open Prototype.Composition
open Prototype.Composition.Buffer.API
open Prototype.Composition.Buffer (nonempty)
open Prototype.Composition.BufferImplementation

/-- The actual body uses zero credits. Reserving five must not imply it spends five. -/
def generousIdentity : Procedure Nat Nat where
  body := .identity
  «requires» _ := True
  «ensures» a b := b = a
  «credits» _ := 5
  correct a _ := ⟨0, a, Run.identity a, rfl, by omega⟩

example : (Plan.call generousIdentity).vc (fun b left => b = 3 ∧ left = 0) 3 5 := by
  simp [Plan.vc, generousIdentity]

/-- Even a non-monotone leftover-credit assertion is sound with explicit discarding. -/
example : ∃ k b left, Run (.call generousIdentity.body) 3 k b ∧
    k + left ≤ 5 ∧ b = 3 ∧ left = 0 :=
  (Plan.call generousIdentity).sound _ _ _ (by simp [Plan.vc, generousIdentity])

example (contract : Contract A B) (p q : Program A B) (hp hq)
    (post : B → Nat → Prop) :
    (Plan.call (contract.implement p hp)).vc post =
      (Plan.call (contract.implement q hq)).vc post :=
  Plan.call_implementation_independent contract p q hp hq post

/- The client proof is parametric in the entire procedure, including its opaque body. -/
ram method useProcedure (proc : Procedure (List Nat) (List Nat))
  (mut left : List Nat) (mut right : List Nat)
  return (result : List Nat × List Nat)
  require proc.requires left
  ensures proc.ensures leftOld left
  ensures right = rightOld
  credits proc.credits left
  do
    left := proc

prove_algorithm useProcedure by
  contract_vc

ram method threeBuffers (capacity : Nat)
  (mut first : List Nat) (mut second : List Nat) (mut third : List Nat)
  return (result : Unit)
  require third.length < capacity
  ensures first = firstOld
  ensures second = []
  ensures third = thirdOld ++ [42]
  do
    third.append(capacity, 42)
    second.clear()

prove_algorithm threeBuffers by
  contract_vc

/-- Source contracts connect directly to actual upstream Loom reasoning. -/
example (capacity : Nat) (xs ys : List Nat)
    (hx : xs.length + 2 ≤ capacity) (hy : ys.length + 2 ≤ capacity) :
    _root_.wp (denote (BufferAlgorithms.recycle capacity).body (xs, ys))
      (fun out _ _ => (BufferAlgorithms.recycle capacity).ensures (xs, ys) out) ()
      ((BufferAlgorithms.recycle capacity).credits (xs, ys)) :=
  (BufferAlgorithms.recycle capacity).loom_correct
    (BufferAlgorithms.recycleVerification capacity) (xs, ys) ⟨hx, hy, trivial⟩

/-- Both logical bodies implement this exact public contract. -/
def resetContract : Contract (List Nat) (List Nat) where
  «requires» _ := True
  «ensures» _ ys := ys = []
  «credits» _ := 2

@[reducible] def resetOnce : Procedure (List Nat) (List Nat) :=
  resetContract.implement (.invoke Buffer.clear) (by
    intro xs _
    exact ⟨1, [], Run.invoke Buffer.clear xs trivial, rfl, by simp [resetContract]⟩)

@[reducible] def resetTwice : Procedure (List Nat) (List Nat) :=
  resetContract.implement (.seq (.invoke Buffer.clear) (.invoke Buffer.clear)) (by
    intro xs _
    exact ⟨2, [], Run.seq (Run.invoke Buffer.clear xs trivial)
      (Run.invoke Buffer.clear [] trivial), rfl, by simp [resetContract]⟩)

/-- The entire mutable client's obligations are unchanged when its callee body changes. -/
example : (useProcedure resetOnce).Obligations = (useProcedure resetTwice).Obligations := rfl

/-- The same generated client proof links either callee to actual RAM. -/
def replacementRun (reset : Procedure (List Nat) (List Nat))
    [Linked 24 (representation (Demo.left 4) false) reset.body
      (representation (Demo.left 4) false)] (pre : reset.requires [1, 2]) :
    Result (List Nat × List Nat) :=
  runProcedure (rate := 24)
    (P := (representation (Demo.left 4) false).sep (representation (Demo.right 4) false))
    (Q := (representation (Demo.left 4) false).sep (representation (Demo.right 4) false))
    (useProcedureProcedure reset) ([1, 2], [3]) ⟨pre, trivial⟩
    (Demo.owned 4) (Demo.encode 4 [1, 2] [3]) 0
    (Demo.initial 4 [1, 2] [3] (by decide) (by decide) false false)

/-- No algorithm-specific certificate is required, including for the third resource. -/
example : Linked 24
    ((representation ⟨"a", 0, 5⟩ false).sep
      ((representation ⟨"b", 5, 5⟩ true).sep (representation ⟨"c", 10, 5⟩ false)))
    (threeBuffersProcedure 5).body
    ((representation ⟨"a", 0, 5⟩ false).sep
      ((representation ⟨"b", 5, 5⟩ true).sep (representation ⟨"c", 10, 5⟩ false))) :=
  inferInstance

def unimplemented : Operation (List Nat) (List Nat) := ⟨fun _ => True, id, fun _ => 0⟩

@[reducible] def unimplementedProcedure : Procedure (List Nat) (List Nat) :=
  Procedure.verify (.invoke unimplemented) (fun _ => True) (fun a b => b = a)
    (fun _ => 0) (by simp [VC, unimplemented])

example : True := by
  fail_if_success
    have : Linked 24 (representation ⟨"a", 0, 5⟩ false)
        (.branch nonempty .identity (.call unimplementedProcedure.body))
        (representation ⟨"a", 0, 5⟩ false) := inferInstance
  trivial

example : ¬ (Plan.call clear).vc (fun _ _ => True) ([] : List Nat) 0 := by
  simp [Plan.vc]

set_option linter.hashCommand false in
#eval show IO Unit from do
  let once := replacementRun resetOnce trivial
  let twice := replacementRun resetTwice trivial
  unless once.value == ([], [3]) && twice.value == once.value &&
      once.steps == 2 && twice.steps == 4 do
    throw <| IO.userError "changing an opaque procedure body broke the unchanged client"
  for n in List.range 7 do
    for m in List.range 7 do
      let xs := (List.range n).map (· % 3)
      let ys := (List.range m).map (· % 4)
      for eagerLeft in [false, true] do
        for eagerRight in [false, true] do
          let r := Demo.execute eagerLeft eagerRight (n + m + 2) xs ys
            (by simp [xs]) (by simp [ys])
          let expected := 44 + (if eagerLeft then 12 * (n + 2) + 3 else 2) +
            (if eagerRight then 12 * (m + 2) + 3 else 2)
          unless r.value == ([], []) && r.steps == expected do
            throw <| IO.userError "contract frontend changed the buffer program or execution"
          let loop := Demo.executeLoop eagerLeft eagerRight (n + m) xs ys
            (by simp [xs]) (by simp [ys])
          let expectedLoop := if n == 0 then 3 else
            9 + (if eagerLeft then 12 * n + 3 else 2)
          unless loop.value == ([], ys) && loop.steps == expectedLoop do
            throw <| IO.userError "nested contract call or automatic frame failed"

set_option linter.hashCommand false in
/-- error: Procedure arguments describe fixed code. Runtime input 'left' must pass through a certified typed operation -/
#guard_msgs in
ram method rejectRuntimeSpecialization (mut left : List Nat) return (result : Unit)
  do
    left := (if left.isEmpty then clear else clear)

end AlgoLib.Experimental.RAM.Tests.ContractFrontend
