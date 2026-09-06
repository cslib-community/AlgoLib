/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.OwnedBFS

/-!
# Trust audit for owned BFS and implementation substitution

These checks cover source verification, Loom reasoning, actual RAM execution,
linear instruction costs, and the hidden-potential refinement rule. Existing
axiom guards are retained; no admission or native-decision axiom is permitted.
-/
open AlgoLib.Experimental.RAM.Prototype.Composition
set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst.bfsVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BreadthFirst.bfsVerification

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst.loom_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BreadthFirst.loom_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst.search_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BreadthFirst.search_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst.linear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BreadthFirst.linear

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst.same_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BreadthFirst.same_result

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst.code_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BreadthFirst.code_independent

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Composition.DataView.realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms DataView.realize
