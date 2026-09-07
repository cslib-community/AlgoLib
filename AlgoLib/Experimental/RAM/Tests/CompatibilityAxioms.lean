/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Natural.SignedArrays
import AlgoLib.Experimental.RAM.Implementations.Natural.Language.IntegerExecution

/-!
# Trust guards for explicit compatibility implementation contracts

Keep the paired signed representation and natural-valued execution adapter checked
without importing them through the standard native frontend. These are the unchanged
axiom assertions previously colocated with native frontend tests.
-/
namespace AlgoLib.Experimental.RAM.Tests.CompatibilityAxioms

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Checked.Language.Method.integerRun_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Checked.Language.Method.integerRun_exec

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Checked.Language.Method.integerCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Checked.Language.Method.integerCorrect

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.SignedArithmetic.correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Prototype.Composition.SignedArithmetic.correct


end AlgoLib.Experimental.RAM.Tests.CompatibilityAxioms
