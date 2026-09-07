/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Examples.InsertionSort.Obligations
import AlgoLib.Experimental.RAM.Examples.BFS.Obligations

/-!
# Sorting and BFS explorer acceptance

Imported specifications retain their vocabulary and source contexts. The explorer
works without completed proofs or RAM assembly. The exact two sorting paths remain
one responsibility; BFS discovers public mathematical accounting lemmas.
-/
namespace AlgoLib.Experimental.RAM.Tests.ObligationAPI.ExplorerExamples
open Prototype.Frontend Prototype.Composition Lean Elab Command

run_cmd do
  let sorting ← liftCoreM <| explorerEntries ``Sorting.insertionSort "outer.inner.preserve.hole"
  let entry := sorting[0]!
  unless entry.contexts.size == 2 do throwError "Lost a sorting branch"
  let hints ← liftCoreM <| obligationSuggestions entry
  unless hints.contains ``Prototype.SortingFacts.swap &&
      hints.contains ``Prototype.SortingFacts.keep do
    throwError "Imported sorting vocabulary was not discovered"
  unless entry.contexts.any (fun xs => xs.any (fun x =>
      x.name == `hInvariant_hole && x.role == "invariant hypothesis")) do
    throwError "The source invariant label was lost"
  unless entry.contexts.any (fun xs => xs.any (fun x => x.name == `arrState2)) do
    throwError "Nested loop snapshot metadata was not retained"
  let bfs ← liftCoreM <| explorerEntries ``BreadthFirst.bfs "search.account.iteration"
  unless (← liftCoreM <| obligationSuggestions bfs[0]!).contains ``BFSFacts.scan_work do
    throwError "Imported BFS work vocabulary was not discovered"

-- The displayed invariant label is usable directly in a checked mathematical block.
open Prototype.SortingFacts in
example : Sorting.insertionSort.ObligationAPI.outer.inner.preserve.hole := by
  obligation_proof by
    first
    | apply swap <;> first | exact hInvariant_hole | assumption | omega
    | apply keep <;> first | exact hInvariant_hole | assumption | omega

open Sorting in
set_option linter.hashCommand false in
#guard_msgs (drop info) in
#explain_obligation insertionSort only outer.inner.preserve.hole

open BreadthFirst in
set_option linter.hashCommand false in
#guard_msgs (drop info) in
#explain_obligation bfs only search.account.iteration

end AlgoLib.Experimental.RAM.Tests.ObligationAPI.ExplorerExamples
