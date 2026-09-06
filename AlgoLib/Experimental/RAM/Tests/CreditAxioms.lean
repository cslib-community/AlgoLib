/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.BackendReuse

/-!
# Trust checks for unbundled credits and reconstructed compilation

Guard both generic composition proofs and a concrete assembled executable. Checking
only `Run.refines` would test a certificate projection, so these guards also inspect
the actual sequence, branch, loop, procedure, and two-backend certificates. Exact
axiom lists preserve the standard kernel trust boundary; no solver oracle is accepted.
-/

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.compileSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.compileSeq

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.compileBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.compileBranch

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.compileLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.compileLoop

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.compileProcedure' does not depend on any axioms -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.compileProcedure

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.CreditLogic.four_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Tests.CreditLogic.four_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.BackendReuse.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Tests.BackendReuse.certified

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.BackendReuse.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Tests.BackendReuse.correct
