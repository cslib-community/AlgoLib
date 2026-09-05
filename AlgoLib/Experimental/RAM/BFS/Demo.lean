/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.GraphInput
import AlgoLib.Experimental.RAM.BFS.GraphBridge

/-!
# A paper-style BFS demo

Read `Program.bfsSource` for the imperative program, `Invariant.process` for
maintenance, `Invariant.exit` for completeness, and `potential_process` for
the linear-time argument. Memory and compiler lemmas are reusable infrastructure.

The executable consumes adjacency-list memory and returns a visited bitmap.
`report` below merely formats that bitmap for display; the reported time is the
RAM routine's instruction count, including initialization. Input encoding and
host-side pretty-printing are outside that count.
-/
namespace AlgoLib.Experimental.RAM.BFS.Demo

/-- Edges are `(label, u, v)`. -/
def path : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2), (2, 2, 3)]
  distinct := by decide
  valid := by decide

/-- Vertex 3 is isolated. -/
def splitGraph : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2)]
  distinct := by decide
  valid := by decide

def singleton : EdgeInput where
  n := 1
  edges := []
  distinct := by decide
  valid := by decide

/-- Reaching vertex 3 through two parents must enqueue it only once. -/
def diamond : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 0, 2), (2, 1, 3), (3, 2, 3)]
  distinct := by decide
  valid := by decide

/-- Two parallel 0–1 edges and two loops exercise incidence multiplicities. -/
def multigraph : EdgeInput where
  n := 3
  edges := [(0, 0, 0), (1, 0, 1), (2, 0, 1), (3, 1, 2), (4, 2, 2)]
  distinct := by decide
  valid := by decide

/-- Human-readable output; formatting does not form part of the RAM program. -/
def report (input : EdgeInput) (source : Nat) (hs : source < input.n) : List Nat × Nat :=
  let result := (input.fromSource source hs).run
  ((List.range input.n).filter (fun v => result.2.memory (5 * v + 1) == 1), result.1)

/-- The displayed vertex list refines the graph specification directly. -/
theorem report_correct (input : EdgeInput) (source : Nat) (hs : source < input.n) (v : Nat) :
    v ∈ (report input source hs).1 ↔ Reachable input.graph source v := by
  change v ∈ (List.range input.n).filter
    (fun w => (input.fromSource source hs).run.2.memory (5 * w + 1) == 1) ↔ _
  rw [List.mem_filter, List.mem_range]
  simpa only [beq_iff_eq] using (input.fromSource source hs).correct.2.1 v

/-- A client-facing connectivity statement, with no memory addresses in sight. -/
theorem report_connected (input : EdgeInput) (source : Nat) (hs : source < input.n) :
    (∀ v ∈ input.graph.vertexSet, v ∈ (report input source hs).1) ↔ Connected input.graph :=
  visits_all_iff_connected hs (report_correct input source hs)

/-- No fuel argument and no pointer-layout proofs at a call site. -/
def search := path.fromSource 0 (by decide)

/-- The specification uses the repository's `Graph`, with exact reachability. -/
theorem correctness : ReturnsReachable path.graph 0
    (fun v => v < 4 ∧ search.run.2.memory (5 * v + 1) = 1) := search.correct.2.1

/-- One search decides connectivity; a valid source supplies nonemptiness. -/
theorem connectivity :
    (∀ v < 4, search.run.2.memory (5 * v + 1) = 1) ↔ Connected path.graph :=
  search.connected_iff

/-- The general theorem is stronger than an asymptotic statement: one fixed
constant works for every valid input graph and every source. -/
theorem linear_time (input : EdgeInput) (s : Nat) (hs : s < input.n) :
    (input.fromSource s hs).run.1 ≤ 32 * (input.n + input.edges.length) := by
  have h := (input.fromSource s hs).linear
  simpa [EdgeInput.fromSource, Represents.input, EdgeInput.represents,
    EdgeInput.adjacency, Finset.card_image_of_injective _ labelled_injective,
    List.toFinset_card_of_nodup input.distinct] using h

/-- info: ([0, 1, 2, 3], 142) -/
#guard_msgs in
#eval report path 0 (by decide)
/-- info: ([0, 1, 2], 107) -/
#guard_msgs in
#eval report splitGraph 0 (by decide)
/-- info: ([3], 37) -/
#guard_msgs in
#eval report splitGraph 3 (by decide)
/-- info: ([0, 1, 2], 168) -/
#guard_msgs in
#eval report multigraph 0 (by decide)

end AlgoLib.Experimental.RAM.BFS.Demo
