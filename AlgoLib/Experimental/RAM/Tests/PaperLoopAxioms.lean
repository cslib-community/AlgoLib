/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.PaperLoops

/-!
# Trust guards for paper loop accounting and generated executables

Keep the existing core axiom checks unchanged. The new end-to-end paths must use
only Lean's standard axioms, without admissions, native-decision axioms or trusted
external solver results. The generated runtime is the verified RAM interpreter.
-/
open AlgoLib.Experimental.RAM.Prototype.Composition

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.CertifiedExecutable.correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedExecutable.correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Sorting.insertionSortVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Sorting.insertionSortVerification

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Sorting.insertionSortCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Sorting.insertionSortCorrect

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.PaperLoops.worklistVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Tests.PaperLoops.worklistVerification

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.PaperLoops.repeatedClearVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Tests.PaperLoops.repeatedClearVerification
