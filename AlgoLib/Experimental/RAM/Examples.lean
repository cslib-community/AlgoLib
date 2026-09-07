/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Examples.InsertionSort.Execution
import AlgoLib.Experimental.RAM.Examples.BFS.Execution
import AlgoLib.Experimental.RAM.Examples.BFS.Inputs

/-!
# Examples: supported public entry point

Import this module for the documented examples API. Layer-aligned exported
names are the preferred spelling for new clients; the original names remain valid
compatibility spellings. Exports refer to the same definitions and checked proofs,
not copied implementations. See Examples/README.md and docs/PUBLIC-API.md.
-/

namespace AlgoLib.Experimental.RAM.Examples.InsertionSort
export AlgoLib.Experimental.RAM.Prototype.Composition.Sorting (insertionSort insertionSortProcedure insertionSortBound run main quadratic bound_eq)
end AlgoLib.Experimental.RAM.Examples.InsertionSort

namespace AlgoLib.Experimental.RAM.Examples.BFS
export AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst (bfs bfsProcedure search search_correct connected linear same_result)
end AlgoLib.Experimental.RAM.Examples.BFS
