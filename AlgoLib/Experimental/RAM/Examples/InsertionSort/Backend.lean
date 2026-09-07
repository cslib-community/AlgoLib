/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Examples.InsertionSort.Program
import AlgoLib.Experimental.RAM.Compiler.Assembly

/-!
# Cached insertion-sort RAM certificates

This module deliberately imports no sorting proof. Layout construction, register
correspondence, linking, and code independence depend only on the program body.
Rechecking `Examples/InsertionSort/Proofs` must leave this module's artifacts unchanged.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting

compile_array_backend insertionSort

end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
