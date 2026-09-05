/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Paper.Examples

/-! Fail CI if a soundness or end-to-end theorem acquires an unexpected axiom. -/

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.VC.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.VC.sound

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.Run.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.Run.refines

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.Interface.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.Interface.correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.Insertion.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.Insertion.run_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.Insertion.quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.Insertion.quadratic

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.BFS.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.BFS.run_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.BFS.linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.BFS.linear

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Paper.BFS.connected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Paper.BFS.connected_iff
