/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.Composition

/-!
# Trust checks for local ownership, private resources, and concrete client linking

Pin dependencies of the generic laws and actual eager-buffer implementation/runner.
These checks reject admissions and trusted solver/native-decision axioms while
retaining Lean's standard logical axioms. Execution tests are in Composition.lean.
-/

open AlgoLib.Experimental.RAM.Prototype.Composition

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.VC.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VC.sound

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Representation.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Representation.frame

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Representation.sep_assoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Representation.sep_assoc

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Supported.compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Supported.compile

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.client_linking' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms client_linking

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.loom_linking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loom_linking

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.procedure_linking' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms procedure_linking

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.ofProgram_vc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ofProgram_vc

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation.erase_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BufferImplementation.erase_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation.clearImplementation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BufferImplementation.clearImplementation

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Demo.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Demo.execute

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.Demo.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Demo.correct
