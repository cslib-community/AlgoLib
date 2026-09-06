/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend

/-!
# Negative checks for remaining-work annotations

An initial upper bound is a verification condition, not trusted metadata. Neither
an insufficient allowance nor a non-decreasing work measure can certify a loop.
BFS supplies the positive, data-dependent nested-loop acceptance test.
-/
namespace AlgoLib.Experimental.RAM.Tests.WorkAccounting
open Prototype.Composition Prototype.Frontend

ram method unpaid (mut x : Nat) return (result : Nat)
  require x = 1
  ensures x = 0
  do
    while 0 < x
      invariant x ≤ 1
      amortized_work x initially_at_most 0
      do
        x := x - 1

theorem unpaid_rejected : ¬unpaidObligations := by
  intro h
  have h := h 1 ⟨rfl, trivial⟩
  simp [Plan.vc, Obligation, ObligationAt, assign, Value.eval, Value.credits, Value.Safe,
    Path.get, Path.set, enterLocals, leaveLocals, Locals.initial, Locals.credits,
    Prototype.Composition.compare, Relation.eval] at h

ram method stationary (mut x : Nat) return (result : Nat)
  require x = 1
  ensures x = 0
  do
    while 0 < x
      invariant x = 1
      amortized_work x
      do
        x := x

theorem stationary_rejected : ¬stationaryObligations := by
  intro h
  have h := h 1 ⟨rfl, trivial⟩
  simp [Plan.vc, Obligation, ObligationAt, assign, Value.eval, Value.credits, Value.Safe,
    Path.get, Path.set, enterLocals, leaveLocals, Locals.initial, Locals.credits,
    Prototype.Composition.compare, Relation.eval] at h

end AlgoLib.Experimental.RAM.Tests.WorkAccounting
