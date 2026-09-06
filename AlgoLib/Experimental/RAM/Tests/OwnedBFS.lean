/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.BFSExecution
import AlgoLib.Experimental.RAM.Tests.Algorithms
import AlgoLib.Experimental.RAM.Tests.WorkAccounting

/-!
# One BFS proof, two actual RAM queue implementations

Exhaust all simple undirected graphs on four vertices and all sources. Compare
both compiled runners with an independent finite-reachability oracle, then check
the inferred instruction bound. Additional cases include isolated vertices,
loops, and parallel edges. Step counts must differ for at least one input, so
this is not two names for the same executable.
-/
namespace AlgoLib.Experimental.RAM.Tests.OwnedBFS
open Prototype.Composition Experimental.RAM.BFS

set_option linter.hashCommand false in
#eval show IO Unit from do
  let mut differentCosts := false
  for mask in List.range 64 do
    let graph := smallGraph mask
    for s in List.finRange 4 do
      let ring := BreadthFirst.search .circular graph s
      let twoStacks := BreadthFirst.search .twoStacks graph s
      let expected := (reference graph s.val).toFinset
      unless ring.value == expected && twoStacks.value == expected do
        throw <| IO.userError s!"owned BFS reachability: mask={mask}, source={s.val}"
      unless ring.steps ≤ 2448 * (graph.n + graph.edges.length) &&
          twoStacks.steps ≤ 2448 * (graph.n + graph.edges.length) do
        throw <| IO.userError s!"owned BFS linear RAM bound: mask={mask}, source={s.val}"
      differentCosts := differentCosts || ring.steps != twoStacks.steps
  unless differentCosts do
    throw <| IO.userError "the two FIFO backends did not produce different RAM costs"
  for graph in [Legacy.Examples.singleton, Legacy.Examples.splitGraph,
      Legacy.Examples.diamond, Legacy.Examples.multigraph] do
    for s in List.finRange graph.n do
      for backend in [BFSStorage.FIFO.circular, .twoStacks] do
        let r := BreadthFirst.search backend graph s
        unless r.value == (reference graph s.val).toFinset do
          throw <| IO.userError "owned BFS isolated/loops/parallel edges"
        unless r.steps ≤ 2448 * (graph.n + graph.edges.length) do
          throw <| IO.userError "owned BFS multigraph bound"

/-- Both instantiations refer to the exact same source certificate. -/
example (input : EdgeInput) (s : Fin input.n) :
    (BreadthFirst.search .circular input s).value =
      (BreadthFirst.search .twoStacks input s).value := BreadthFirst.same_result input s

/-- Equality reconstruction refuses different instruction trees. -/
example : (Checked.Language.Cmd.skip) ≠ .seq .skip .skip := by
  intro h
  fail_if_success
    have bad : (Checked.Language.Cmd.skip) = .seq .skip .skip := by ram_code_eq
  cases h

end AlgoLib.Experimental.RAM.Tests.OwnedBFS
