/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.OwnedBFS

/-!
# Private-layout substitution through unchanged BFS assembly

The relocated backend renames the queue's private registers and pads its heap by
17 cells. It satisfies the same public region and empty-input contracts. These
checks use the existing generic BFS runner, source certificate, assembly proof,
and inferred RAM bound; there is no relocated client or special assembly proof.
The finite tests compare with an independent reachability oracle as well.
-/
namespace AlgoLib.Experimental.RAM.Tests.EncoderLayout
open Prototype.Composition Experimental.RAM.BFS

/-- The substitution changes real owned locations, not just a backend label. -/
example : (BFSStorage.queueEncoder .circular 100 4).footprint ≠
    (BFSStorage.queueEncoder .relocated 100 4).footprint := by decide

/-- Universal substitution, obtained solely from the unchanged public runner theorem. -/
theorem relocated_same_result (input : EdgeInput) (s : Fin input.n) :
    (BreadthFirst.search .relocated input s).value =
      (BreadthFirst.search .circular input s).value := by
  apply Finset.ext
  intro v
  rw [BreadthFirst.search_correct, BreadthFirst.search_correct]

/-- The unchanged resource proof applies to the changed private layout. -/
example (input : EdgeInput) (s : Fin input.n) :
    (BreadthFirst.search .relocated input s).steps ≤ 2448 * (input.n + input.edges.length) :=
  BreadthFirst.linear .relocated input s

/-- A public region contract cannot make overlapping ownership disjoint. -/
example : ¬Disjoint BFSStorage.source.footprint BFSStorage.source.footprint := by
  simp [BFSStorage.source, scalarEncoder]

set_option linter.hashCommand false in
#eval show IO Unit from do
  for mask in List.range 64 do
    let graph := smallGraph mask
    for s in List.finRange 4 do
      let r := BreadthFirst.search .relocated graph s
      unless r.value == (reference graph s.val).toFinset do
        throw <| IO.userError s!"relocated queue BFS: mask={mask}, source={s.val}"
      unless r.steps ≤ 2448 * (graph.n + graph.edges.length) do
        throw <| IO.userError "relocated queue BFS: RAM bound"
  for graph in [Legacy.Examples.singleton, Legacy.Examples.splitGraph,
      Legacy.Examples.diamond, Legacy.Examples.multigraph] do
    for s in List.finRange graph.n do
      let r := BreadthFirst.search .relocated graph s
      unless r.value == (reference graph s.val).toFinset &&
          r.steps ≤ 2448 * (graph.n + graph.edges.length) do
        throw <| IO.userError "relocated queue BFS: loops/parallel edges/isolated vertices"

end AlgoLib.Experimental.RAM.Tests.EncoderLayout
