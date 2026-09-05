/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Programs.Examples

/-!
# Explicit method contracts: acceptance and rejection tests

Exercise the theorem-first public API and check that a method cannot evade its
preparation cost or certify an impossible output. Existing Paper tests cover
exhaustive small compiled executions and independent reference comparisons.
-/
namespace AlgoLib.Experimental.RAM.Tests.Methods
open Authoring Experimental.RAM.BFS

/-- The procedure's displayed body is exactly the insertion loop being verified. -/
example : Programs.Sorting.insertionSort.body =
    Program.loop Insertion.more (.action Insertion.insertNext) := rfl

/-- The complete sorting target is obtained from the same named executable. -/
example : Programs.Sorting.Claim Programs.Sorting.run := Programs.Sorting.main

/-- Connectivity is stated as equality of sets, including exclusion of extra vertices. -/
example {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    Connected G ↔
      Programs.Connectivity.vertices (Programs.Connectivity.run i).value = G.vertexSet :=
  (Programs.Connectivity.main i).2.1

/-- Empty code still cannot erase the certified cost of input preparation. -/
def unpayable : Method Insertion.interface :=
  ram_method (_xs : List Nat) returns (_ys : List Nat)
    using Insertion.interface;
    requires True;
    ensures True;
    credits 0;
    time 0;
  do {}

example : ¬ unpayable.VCs := by
  intro h
  have payment := (h [] trivial).2
  norm_num [unpayable, method_simps] at payment

/-- A postcondition must be justified; it is not a display-only annotation. -/
def impossibleOutput : Method Insertion.interface :=
  ram_method (_xs : List Nat) returns (_ys : List Nat)
    using Insertion.interface;
    requires True;
    ensures False;
    credits 0;
    time 5;
  do {}

example : ¬ impossibleOutput.VCs := by
  intro h
  have output := (h [] trivial).1
  change ∀ out, Insertion.interface.Observes (Insertion.initial []) out → False at output
  exact output [] (by simp [method_simps, Insertion.initial])

/- The header's host input is not available in the fixed program body. -/
set_option linter.hashCommand false in
/-- error: Unknown identifier `xs.isEmpty` -/
#guard_msgs in
def cannotSpecialize : Method Insertion.interface :=
  ram_method (xs : List Nat) returns (ys : List Nat)
    using Insertion.interface;
    requires True;
    ensures True;
    credits 0;
    time 5;
  do {
    call (if xs.isEmpty then Insertion.insertNext else Insertion.insertNext);
  }

end AlgoLib.Experimental.RAM.Tests.Methods
