/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.MixedFrontend
import AlgoLib.Experimental.RAM.Prototype.Composition.SortingExecution

/-!
# Trust regression for the unified frontend and actual linked executions

Pin the dependencies of source verification, generic execution soundness, and the
concrete linked sorter. No admission or external decision/solver axiom is allowed.
-/
open AlgoLib.Experimental.RAM.Prototype.Composition

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.runEncoded_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms runEncoded_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.MixedAlgorithms.nestedVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MixedAlgorithms.nestedVerification

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Sorting.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sorting.main

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.MixedFrontend.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Tests.MixedFrontend.execute

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation.appendBorrowedImplementation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BufferImplementation.appendBorrowedImplementation
