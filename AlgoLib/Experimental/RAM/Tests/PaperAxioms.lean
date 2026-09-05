/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Programs.Examples

/-!
# Regression checks: PaperAxioms

Checks the relevant executable, proof, or compiler guarantees against regressions. Expected-output
assertions and theorem checks are part of the test, not extra algorithm implementations.

See Tests/README.md for coverage and build commands. Canonical programs live exclusively under
Programs.

## Further details

Fail CI if a soundness or end-to-end theorem acquires an unexpected axiom.
-/
set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.VC.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.VC.sound

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.Run.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.Run.refines

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.Interface.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.Interface.correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Programs.Sorting.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Programs.Sorting.run_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Programs.Sorting.quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Programs.Sorting.quadratic

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Programs.Connectivity.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Programs.Connectivity.run_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Programs.Connectivity.linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Programs.Connectivity.linear

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Programs.Connectivity.connected_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Programs.Connectivity.connected_iff

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.VerifiedMethod.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.VerifiedMethod.correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Programs.Sorting.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Programs.Sorting.main

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Programs.Connectivity.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Programs.Connectivity.main
