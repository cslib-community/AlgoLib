/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.BFS
import AlgoLib.Experimental.RAM.Prototype.InsertionSort
import AlgoLib.Experimental.RAM.Prototype.FrameworkTests
import AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests
import AlgoLib.Experimental.RAM.Prototype.VelvetArrayTranslation
import AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation

/-!
# Axiom regression checks for the actual Loom/Velvet integration

Each guard pins the actual kernel dependencies. Existing production checks remain
unchanged; these extend the same trust policy to the new observation, VCG, bridge,
reconstructed certificate, and executable theorem. No external solver is trusted.
-/

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Computation.pure_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Computation.pure_bind

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Computation.bind_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Computation.bind_pure

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Computation.bind_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Computation.bind_assoc

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Computation.wp_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Computation.wp_bind

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Computation.wp_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Computation.wp_loop

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.denote_iff_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.denote_iff_run

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.denote_deterministic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.denote_deterministic

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.compilation_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.compilation_sound

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Plan.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Plan.sound

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.reconstruct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.reconstruct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.InsertionSort.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.InsertionSort.main

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.InsertionSort.quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.InsertionSort.quadratic

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.InsertionSort.exists_sort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.InsertionSort.exists_sort

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.loom_wp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.loom_wp_eq

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Plan.loom_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Plan.loom_sound

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Mutable.represents_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Mutable.represents_write

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.InsertionSort.loom_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.InsertionSort.loom_correct

set_option linter.hashCommand false in
/-- info: 'NonDetT.runDivM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NonDetT.runDivM_eq

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.FrameworkTests.counter_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.FrameworkTests.counter_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.FrameworkTests.callCounter_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.FrameworkTests.callCounter_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Annotated.verify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Annotated.verify

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Routine.loom_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Routine.loom_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Graph.scanVerification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Graph.scanVerification

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Graph.processVerification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Graph.processVerification

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.BFS.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.BFS.main

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.BFS.loom_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.BFS.loom_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetSemantics.Returns.satisfies_wp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetSemantics.Returns.satisfies_wp

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetSemantics.loom_to_ram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetSemantics.loom_to_ram

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetSemantics.deterministic_target_impossible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetSemantics.deterministic_target_impossible

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Nondeterministic.Translation.correct_and_cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Nondeterministic.Translation.correct_and_cost

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Nondeterministic.ExecIn.trace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Nondeterministic.ExecIn.trace

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Nondeterministic.Trace.exec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Nondeterministic.Trace.exec

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Nondeterministic.run_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.Nondeterministic.run_correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.Nondeterministic.ExecutableTranslation.run_correct_and_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  AlgoLib.Experimental.RAM.Prototype.Nondeterministic.ExecutableTranslation.run_correct_and_cost

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.MultipleArrays.represents_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.MultipleArrays.represents_write

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.MultipleArrays.represents_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.MultipleArrays.represents_initial

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.method_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.method_execution

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetArrayTranslation.translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetArrayTranslation.translation

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetArrayTranslation.correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetArrayTranslation.correct

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests.chooseWordTranslation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests.chooseWordTranslation

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests.relayTranslation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests.relayTranslation

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests.every_word_executable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests.every_word_executable

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation.translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation.translation

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation.budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation.budget

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation.run_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation.run_correct
