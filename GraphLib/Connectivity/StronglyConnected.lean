/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Connectivity.Reachability

/-!
# Strong connectivity

Strong connectivity is mutual directed reachability. Strongly connected components are exposed
as mathematical sets; executable SCC enumeration and quotient component carriers are deferred.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ δ : Type*}

namespace SimpleDiGraph

/-- Two vertices of a simple digraph are strongly connected when each is reachable from the
other. -/
def StronglyConnected (G : SimpleDiGraph α) (u v : α) : Prop :=
  G.Reachable u v ∧ G.Reachable v u

/-- A simple digraph is strongly connected when it is nonempty and every pair of graph vertices
is mutually reachable. -/
def IsStronglyConnected (G : SimpleDiGraph α) : Prop :=
  V(G).Nonempty ∧ ∀ u ∈ V(G), ∀ v ∈ V(G), G.StronglyConnected u v

/-- The strongly connected component rooted at an ambient vertex, as a mathematical set. -/
def stronglyConnectedComponentSet (G : SimpleDiGraph α) (v : α) : Set α :=
  {u | G.StronglyConnected v u}

theorem stronglyConnected_iff (G : SimpleDiGraph α) (u v : α) :
    G.StronglyConnected u v ↔ G.Reachable u v ∧ G.Reachable v u :=
  Iff.rfl

namespace StronglyConnected

theorem refl {G : SimpleDiGraph α} {v : α} (hv : v ∈ V(G)) :
    G.StronglyConnected v v :=
  ⟨Reachable.refl hv, Reachable.refl hv⟩

@[symm] theorem symm {G : SimpleDiGraph α} {u v : α}
    (h : G.StronglyConnected u v) : G.StronglyConnected v u :=
  ⟨h.2, h.1⟩

@[trans] theorem trans {G : SimpleDiGraph α} {u v w : α}
    (huv : G.StronglyConnected u v) (hvw : G.StronglyConnected v w) :
    G.StronglyConnected u w :=
  ⟨huv.1.trans hvw.1, hvw.2.trans huv.2⟩

theorem left_mem {G : SimpleDiGraph α} {u v : α}
    (h : G.StronglyConnected u v) : u ∈ V(G) :=
  h.1.left_mem

theorem right_mem {G : SimpleDiGraph α} {u v : α}
    (h : G.StronglyConnected u v) : v ∈ V(G) :=
  h.1.right_mem

end StronglyConnected

@[simp] theorem mem_stronglyConnectedComponentSet (G : SimpleDiGraph α) (u v : α) :
    u ∈ G.stronglyConnectedComponentSet v ↔ G.StronglyConnected v u :=
  Iff.rfl

theorem mem_stronglyConnectedComponentSet_self {G : SimpleDiGraph α} {v : α}
    (hv : v ∈ V(G)) : v ∈ G.stronglyConnectedComponentSet v :=
  StronglyConnected.refl hv

theorem stronglyConnectedComponentSet_subset_vertexSet (G : SimpleDiGraph α) (v : α) :
    G.stronglyConnectedComponentSet v ⊆ V(G) :=
  fun _ h => h.right_mem

theorem stronglyConnectedComponentSet_eq_of_stronglyConnected
    {G : SimpleDiGraph α} {u v : α} (h : G.StronglyConnected u v) :
    G.stronglyConnectedComponentSet u = G.stronglyConnectedComponentSet v := by
  ext x
  constructor
  · exact fun hux => h.symm.trans hux
  · exact fun hvx => h.trans hvx

theorem stronglyConnectedComponentSet_eq_iff {G : SimpleDiGraph α} {u v : α}
    (hu : u ∈ V(G)) :
    G.stronglyConnectedComponentSet u = G.stronglyConnectedComponentSet v ↔
      G.StronglyConnected u v := by
  constructor
  · intro hsets
    have huv : u ∈ G.stronglyConnectedComponentSet v :=
      hsets ▸ mem_stronglyConnectedComponentSet_self hu
    exact huv.symm
  · exact stronglyConnectedComponentSet_eq_of_stronglyConnected

theorem stronglyConnectedComponentSet_eq_or_disjoint (G : SimpleDiGraph α) (u v : α) :
    G.stronglyConnectedComponentSet u = G.stronglyConnectedComponentSet v ∨
      Disjoint (G.stronglyConnectedComponentSet u) (G.stronglyConnectedComponentSet v) := by
  by_cases hmeet : ∃ x,
      x ∈ G.stronglyConnectedComponentSet u ∧ x ∈ G.stronglyConnectedComponentSet v
  · obtain ⟨x, hux, hvx⟩ := hmeet
    exact Or.inl
      (stronglyConnectedComponentSet_eq_of_stronglyConnected (hux.trans hvx.symm))
  · right
    rw [Set.disjoint_left]
    intro x hux hvx
    exact hmeet ⟨x, hux, hvx⟩

theorem isStronglyConnected_iff_component_eq_vertexSet (G : SimpleDiGraph α) {v : α}
    (hv : v ∈ V(G)) :
    G.IsStronglyConnected ↔ G.stronglyConnectedComponentSet v = V(G) := by
  constructor
  · rintro ⟨_, hstrong⟩
    apply Set.Subset.antisymm (G.stronglyConnectedComponentSet_subset_vertexSet v)
    intro u hu
    exact hstrong v hv u hu
  · intro hcomponent
    refine ⟨⟨v, hv⟩, ?_⟩
    intro u hu w hw
    have hvu : G.StronglyConnected v u :=
      show u ∈ G.stronglyConnectedComponentSet v from hcomponent.symm ▸ hu
    have hvw : G.StronglyConnected v w :=
      show w ∈ G.stronglyConnectedComponentSet v from hcomponent.symm ▸ hw
    exact hvu.symm.trans hvw

@[simp] theorem reverse_stronglyConnected (G : SimpleDiGraph α) (u v : α) :
    G.reverse.StronglyConnected u v ↔ G.StronglyConnected u v := by
  simp [StronglyConnected, and_comm]

@[simp] theorem stronglyConnectedComponentSet_reverse (G : SimpleDiGraph α) (v : α) :
    G.reverse.stronglyConnectedComponentSet v = G.stronglyConnectedComponentSet v := by
  ext u
  simp

@[simp] theorem reverse_isStronglyConnected (G : SimpleDiGraph α) :
    G.reverse.IsStronglyConnected ↔ G.IsStronglyConnected := by
  simp only [IsStronglyConnected, vertexSet_reverse, reverse_stronglyConnected]

@[simp] theorem relabelVertices_stronglyConnected (G : SimpleDiGraph α)
    (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).StronglyConnected (f u) (f v) ↔ G.StronglyConnected u v := by
  simp [StronglyConnected]

@[simp] theorem stronglyConnectedComponentSet_relabelVertices (G : SimpleDiGraph α)
    (f : α ≃ γ) (v : α) :
    (G.relabelVertices f).stronglyConnectedComponentSet (f v) =
      f '' G.stronglyConnectedComponentSet v := by
  ext x
  obtain ⟨u, rfl⟩ := f.surjective x
  simp

@[simp] theorem relabelVertices_isStronglyConnected (G : SimpleDiGraph α)
    (f : α ≃ γ) : (G.relabelVertices f).IsStronglyConnected ↔ G.IsStronglyConnected := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [vertexSet_relabelVertices, Set.image_nonempty] using h.1
    intro u hu' v hv'
    exact (G.relabelVertices_stronglyConnected f u v).1
      (h.2 (f u) ⟨u, hu', rfl⟩ (f v) ⟨v, hv', rfl⟩)
  · rintro ⟨⟨u, hu⟩, hstrong⟩
    refine ⟨⟨f u, ⟨u, hu, rfl⟩⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact (G.relabelVertices_stronglyConnected f v w).2 (hstrong v hv w hw)

end SimpleDiGraph

namespace DiGraph

/-- Two vertices of a general digraph are strongly connected when each is reachable from the
other through actual-arc-aware paths. -/
def StronglyConnected (G : DiGraph α β) (u v : α) : Prop :=
  G.Reachable u v ∧ G.Reachable v u

/-- A general digraph is strongly connected when it is nonempty and every pair of its vertices
is mutually reachable. -/
def IsStronglyConnected (G : DiGraph α β) : Prop :=
  V(G).Nonempty ∧ ∀ u ∈ V(G), ∀ v ∈ V(G), G.StronglyConnected u v

/-- The strongly connected component rooted at an ambient vertex, as a mathematical set. -/
def stronglyConnectedComponentSet (G : DiGraph α β) (v : α) : Set α :=
  {u | G.StronglyConnected v u}

theorem stronglyConnected_iff (G : DiGraph α β) (u v : α) :
    G.StronglyConnected u v ↔ G.Reachable u v ∧ G.Reachable v u :=
  Iff.rfl

namespace StronglyConnected

theorem refl {G : DiGraph α β} {v : α} (hv : v ∈ V(G)) : G.StronglyConnected v v :=
  ⟨Reachable.refl hv, Reachable.refl hv⟩

@[symm] theorem symm {G : DiGraph α β} {u v : α}
    (h : G.StronglyConnected u v) : G.StronglyConnected v u :=
  ⟨h.2, h.1⟩

@[trans] theorem trans {G : DiGraph α β} {u v w : α}
    (huv : G.StronglyConnected u v) (hvw : G.StronglyConnected v w) :
    G.StronglyConnected u w :=
  ⟨huv.1.trans hvw.1, hvw.2.trans huv.2⟩

theorem left_mem {G : DiGraph α β} {u v : α}
    (h : G.StronglyConnected u v) : u ∈ V(G) :=
  h.1.left_mem

theorem right_mem {G : DiGraph α β} {u v : α}
    (h : G.StronglyConnected u v) : v ∈ V(G) :=
  h.1.right_mem

end StronglyConnected

@[simp] theorem mem_stronglyConnectedComponentSet (G : DiGraph α β) (u v : α) :
    u ∈ G.stronglyConnectedComponentSet v ↔ G.StronglyConnected v u :=
  Iff.rfl

theorem mem_stronglyConnectedComponentSet_self {G : DiGraph α β} {v : α}
    (hv : v ∈ V(G)) : v ∈ G.stronglyConnectedComponentSet v :=
  StronglyConnected.refl hv

theorem stronglyConnectedComponentSet_subset_vertexSet (G : DiGraph α β) (v : α) :
    G.stronglyConnectedComponentSet v ⊆ V(G) :=
  fun _ h => h.right_mem

theorem stronglyConnectedComponentSet_eq_of_stronglyConnected
    {G : DiGraph α β} {u v : α} (h : G.StronglyConnected u v) :
    G.stronglyConnectedComponentSet u = G.stronglyConnectedComponentSet v := by
  ext x
  constructor
  · exact fun hux => h.symm.trans hux
  · exact fun hvx => h.trans hvx

theorem stronglyConnectedComponentSet_eq_iff {G : DiGraph α β} {u v : α}
    (hu : u ∈ V(G)) :
    G.stronglyConnectedComponentSet u = G.stronglyConnectedComponentSet v ↔
      G.StronglyConnected u v := by
  constructor
  · intro hsets
    have huv : u ∈ G.stronglyConnectedComponentSet v :=
      hsets ▸ mem_stronglyConnectedComponentSet_self hu
    exact huv.symm
  · exact stronglyConnectedComponentSet_eq_of_stronglyConnected

theorem stronglyConnectedComponentSet_eq_or_disjoint (G : DiGraph α β) (u v : α) :
    G.stronglyConnectedComponentSet u = G.stronglyConnectedComponentSet v ∨
      Disjoint (G.stronglyConnectedComponentSet u) (G.stronglyConnectedComponentSet v) := by
  by_cases hmeet : ∃ x,
      x ∈ G.stronglyConnectedComponentSet u ∧ x ∈ G.stronglyConnectedComponentSet v
  · obtain ⟨x, hux, hvx⟩ := hmeet
    exact Or.inl
      (stronglyConnectedComponentSet_eq_of_stronglyConnected (hux.trans hvx.symm))
  · right
    rw [Set.disjoint_left]
    intro x hux hvx
    exact hmeet ⟨x, hux, hvx⟩

theorem isStronglyConnected_iff_component_eq_vertexSet (G : DiGraph α β) {v : α}
    (hv : v ∈ V(G)) :
    G.IsStronglyConnected ↔ G.stronglyConnectedComponentSet v = V(G) := by
  constructor
  · rintro ⟨_, hstrong⟩
    apply Set.Subset.antisymm (G.stronglyConnectedComponentSet_subset_vertexSet v)
    intro u hu
    exact hstrong v hv u hu
  · intro hcomponent
    refine ⟨⟨v, hv⟩, ?_⟩
    intro u hu w hw
    have hvu : G.StronglyConnected v u :=
      show u ∈ G.stronglyConnectedComponentSet v from hcomponent.symm ▸ hu
    have hvw : G.StronglyConnected v w :=
      show w ∈ G.stronglyConnectedComponentSet v from hcomponent.symm ▸ hw
    exact hvu.symm.trans hvw

@[simp] theorem reverse_stronglyConnected (G : DiGraph α β) (u v : α) :
    G.reverse.StronglyConnected u v ↔ G.StronglyConnected u v := by
  simp [StronglyConnected, and_comm]

@[simp] theorem stronglyConnectedComponentSet_reverse (G : DiGraph α β) (v : α) :
    G.reverse.stronglyConnectedComponentSet v = G.stronglyConnectedComponentSet v := by
  ext u
  simp

@[simp] theorem reverse_isStronglyConnected (G : DiGraph α β) :
    G.reverse.IsStronglyConnected ↔ G.IsStronglyConnected := by
  simp only [IsStronglyConnected, vertexSet_reverse, reverse_stronglyConnected]

@[simp] theorem relabelVertices_stronglyConnected (G : DiGraph α β)
    (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).StronglyConnected (f u) (f v) ↔ G.StronglyConnected u v := by
  simp [StronglyConnected]

@[simp] theorem stronglyConnectedComponentSet_relabelVertices (G : DiGraph α β)
    (f : α ≃ γ) (v : α) :
    (G.relabelVertices f).stronglyConnectedComponentSet (f v) =
      f '' G.stronglyConnectedComponentSet v := by
  ext x
  obtain ⟨u, rfl⟩ := f.surjective x
  simp

@[simp] theorem relabelVertices_isStronglyConnected (G : DiGraph α β)
    (f : α ≃ γ) : (G.relabelVertices f).IsStronglyConnected ↔ G.IsStronglyConnected := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [vertexSet_relabelVertices, Set.image_nonempty] using h.1
    intro u hu' v hv'
    exact (G.relabelVertices_stronglyConnected f u v).1
      (h.2 (f u) ⟨u, hu', rfl⟩ (f v) ⟨v, hv', rfl⟩)
  · rintro ⟨⟨u, hu⟩, hstrong⟩
    refine ⟨⟨f u, ⟨u, hu, rfl⟩⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact (G.relabelVertices_stronglyConnected f v w).2 (hstrong v hv w hw)

@[simp] theorem relabelTags_stronglyConnected (G : DiGraph α β)
    (g : β ≃ δ) (u v : α) :
    (G.relabelTags g).StronglyConnected u v ↔ G.StronglyConnected u v := by
  simp [StronglyConnected]

@[simp] theorem stronglyConnectedComponentSet_relabelTags (G : DiGraph α β)
    (g : β ≃ δ) (v : α) :
    (G.relabelTags g).stronglyConnectedComponentSet v =
      G.stronglyConnectedComponentSet v := by
  ext u
  simp

@[simp] theorem relabelTags_isStronglyConnected (G : DiGraph α β)
    (g : β ≃ δ) : (G.relabelTags g).IsStronglyConnected ↔ G.IsStronglyConnected := by
  simp only [IsStronglyConnected, vertexSet_relabelTags, relabelTags_stronglyConnected]

end DiGraph

end GraphLib
