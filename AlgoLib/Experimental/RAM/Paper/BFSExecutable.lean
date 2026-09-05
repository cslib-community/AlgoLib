/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Paper.BFS
import AlgoLib.Experimental.RAM.Internal.SearchInput

/-! Input/output binding for the paper BFS proof. The executable is assembled
by the generic interface, including initialization and compilation. -/
namespace AlgoLib.Experimental.RAM.Paper.BFS
open Experimental.RAM.BFS

private theorem initially {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    invariant a G i.source (Search.initial i.source) := by
  refine ⟨by simp [Search.initial, discovered], rfl, ?_⟩
  refine ⟨by simp [Search.initial], by simp [Search.initial], by simp [Search.initial],
    ?_, by simp [Search.initial], ?_, by simp [Search.initial]⟩
  · intro v hv
    have : v = i.source := by simpa [Search.initial] using hv
    exact this ▸ i.source_valid
  · intro v hv
    have : v = i.source := by simpa [Search.initial] using hv
    subst v
    exact .refl ((i.representation.vertices i.source).mpr i.source_valid)

/-- Input: a certified adjacency list and source. Output: visited bitmap and RAM steps. -/
def run {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) : Result Checked.Bitmap :=
  (Search.interface a G).run (correct i.representation i.source) i (initially i)

theorem run_correct {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) (v : Nat) :
    (run i).value.contains v = true ↔ Reachable G i.source v := by
  obtain ⟨⟨g, hg, ho⟩, _⟩ := (Search.interface a G).correct
    (correct i.representation i.source) i (initially i)
  rw [show (run i).value.contains v = true ↔ v < a.n ∧ v ∈ g.seen from ho v, hg v]
  exact ⟨And.right, fun hr => ⟨(i.representation.vertices v).mp hr.right_mem, hr⟩⟩

theorem connected_iff {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    (∀ v ∈ G.vertexSet, (run i).value.contains v = true) ↔ Connected G :=
  visits_all_iff_connected ((i.representation.vertices i.source).mpr i.source_valid) (run_correct i)

/-- A bound for actual compiled instructions, including clearing visited flags. -/
theorem linear {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    (run i).steps ≤ 370 * (a.n + i.representation.edges.card) := by
  have h := ((Search.interface a G).correct
    (correct i.representation i.source) i (initially i)).2
  have initialCost : potential a (Search.initial i.source) = 3 * a.n + 2 * a.entries := by
    simp [potential, Search.initial, Credits.remaining, Adjacency.entries,
      Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]
  change (run i).steps ≤ 25 * a.n + 45 + 75 * (potential a (Search.initial i.source) + 1) at h
  rw [initialCost] at h
  have := i.representation.incidenceBound
  have := i.source_valid
  omega

end AlgoLib.Experimental.RAM.Paper.BFS
