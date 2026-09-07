/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.SignedFrontend

/-!
# Trusted dependencies of signed source compilation

The arithmetic representation and assembled executable theorems retain the existing
axiom allowlist. Generated certificates must not introduce sorryAx or native_decide.
-/
namespace AlgoLib.Experimental.RAM.Tests.SignedFrontend

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.SignedArithmetic.correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Prototype.Composition.SignedArithmetic.correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.SignedFrontend.subtractFiveCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms subtractFiveCorrect

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.SignedFrontend.shiftArrayCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shiftArrayCorrect

end AlgoLib.Experimental.RAM.Tests.SignedFrontend
