/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.ArraySubstitution

/-!
# Exact trust checks for supported compilation and implementation substitution

Check the total compiler, Loom-to-RAM theorem, physical table/write contracts,
and concrete executables. The latter checks include the actual primitive proofs
and algorithm proof, rather than merely a projection from an assumed certificate.
-/

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.Supported.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.Supported.compile

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Authoring.Supported.vc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Authoring.Supported.vc_sound

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.loom_to_supported_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.loom_to_supported_ram

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.IndirectArrays.table_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.IndirectArrays.table_frame

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.IndirectArrays.represents_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.IndirectArrays.represents_write

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.ArraySubstitution.indirectSort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.ArraySubstitution.indirectSort

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.ArraySubstitution.indirectZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.ArraySubstitution.indirectZero

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Prototype.ArraySubstitution.sorting_outputs_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgoLib.Experimental.RAM.Prototype.ArraySubstitution.sorting_outputs_equal
