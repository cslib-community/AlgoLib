/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.SortingSpec

/-!
# Insertion-sort proofs against the generated obligation API

Edit these mathematical blocks without regenerating VCs or reconstructing RAM code.
Each selected responsibility becomes a separate Lean theorem. The specification and
backend certificates are imported from independent modules.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
open Frontend SortingFacts

-- During authoring: #named_goals insertionSort only outer.inner.preserve
prove_obligation insertionSort.ObligationAPI.outer.initialize.prefix by
  simp [Prefix]

prove_obligation insertionSort.ObligationAPI.outer.inner.initialize.hole by
  grind only [enter]

prove_obligation insertionSort.ObligationAPI.outer.inner.preserve.hole by
  first
  | apply swap <;> first | assumption | omega
  | apply keep <;> first | assumption | omega

prove_obligation insertionSort.ObligationAPI.outer.inner.preserve.permutation by
  grind only [swap_preserves_permutation]

prove_obligation insertionSort.ObligationAPI.outer.preserve.prefix by
  grind only [exit]

prove_obligation insertionSort.ObligationAPI.outer.exit by
  grind only [SortedPermutation, sorted]

-- Routine safety, termination, and accounting evidence is cached in the API.
complete_algorithm insertionSort

end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
