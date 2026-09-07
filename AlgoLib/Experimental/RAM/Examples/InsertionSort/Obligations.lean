/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Examples.InsertionSort.Program

/-!
# Generated Sorting obligation API

This module freezes the source propositions and caches routine proofs. The program
and backend can be imported without running this generation step. Student proofs
import this API; they do not regenerate it.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting

open Frontend SortingFacts

-- Suggestions are mathematical library metadata, not extra proof assumptions.
obligation_lemmas Hole for "initialize" => [enter]
obligation_lemmas Hole for "preserve" => [swap, keep]
obligation_lemmas Prefix for "preserve" => [exit]

generate_obligations insertionSort

end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
