/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Weixuan Yuan
-/
import GraphLib.Graph.Finite

/-!
# Matchings

This file defines matchings of general graphs using complete bundled actual edges. The finite
cardinality API requires finiteness explicitly; `Set.ncard` is not used as an accidental total
cardinality for infinite matching sets.
-/

namespace GraphLib

open scoped GraphLib

variable {α β : Type*}

/-! ## Matchings -/

/-- A set of pairwise vertex-disjoint actual edges of a general graph. -/
structure Matching (G : Graph α β) where
  /-- The complete bundled actual edges belonging to the matching. -/
  edgeSet : Set (Edge α β)
  /-- Every matching edge is an active actual edge of the graph. -/
  edgeSet_subset : edgeSet ⊆ E(G)
  /-- Distinct matching edges share no endpoint. -/
  disjoint : ∀ e ∈ edgeSet, ∀ f ∈ edgeSet, e ≠ f →
    ∀ v, v ∈ e.endpoints → v ∉ f.endpoints

namespace Matching

/-- A matching in a graph with finitely many actual edges is finite. -/
instance instFiniteEdgeSet {G : Graph α β} (M : Matching G) [Finite E(G)] :
    Finite M.edgeSet :=
  (G.edgeSet_finite.subset M.edgeSet_subset).to_subtype

/-- A finite matching's actual edges as a noncomputable finset. -/
noncomputable def edgeFinset {G : Graph α β} (M : Matching G) [Finite M.edgeSet] :
    Finset (Edge α β) := (Set.toFinite M.edgeSet).toFinset

@[simp] theorem mem_edgeFinset {G : Graph α β} (M : Matching G) [Finite M.edgeSet]
    (e : Edge α β) : e ∈ M.edgeFinset ↔ e ∈ M.edgeSet := by
  simp [edgeFinset]

/-- The number of actual edges in a finite matching. -/
noncomputable def size {G : Graph α β} (M : Matching G) [Finite M.edgeSet] : ℕ :=
  M.edgeFinset.card

@[simp] theorem size_eq_ncard {G : Graph α β} (M : Matching G) [Finite M.edgeSet] :
    M.size = M.edgeSet.ncard := by
  rw [size, Set.ncard_eq_toFinset_card M.edgeSet (Set.toFinite M.edgeSet)]
  rfl

end Matching

/-!
The remaining matching operations listed above are intentionally left for a
future implementation instead of being exposed as declarations without types
or definitions.
-/

end GraphLib
