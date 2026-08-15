/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Connectivity.Reachability

/-!
# Undirected connectedness and connected-component sets

`Preconnected` is the vacuous all-pairs reachability property, while `Connected` additionally
requires a vertex. Thus the empty graph is preconnected but not connected. Components are
exposed as literal sets in this construction round; quotient component carriers are deferred.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ δ : Type*}

namespace SimpleGraph

/-- Every two vertices of a simple graph are reachable. This holds vacuously for the empty
graph. -/
def Preconnected (G : SimpleGraph α) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G), G.Reachable u v

/-- A simple graph is connected when it is nonempty and every two vertices are reachable. -/
def Connected (G : SimpleGraph α) : Prop :=
  V(G).Nonempty ∧ G.Preconnected

/-- The connected component rooted at an ambient vertex, as a mathematical set. A root outside
the graph has the empty component. -/
def connectedComponentSet (G : SimpleGraph α) (v : α) : Set α :=
  {u | G.Reachable v u}

@[simp] theorem mem_connectedComponentSet (G : SimpleGraph α) (u v : α) :
    u ∈ G.connectedComponentSet v ↔ G.Reachable v u :=
  Iff.rfl

theorem mem_connectedComponentSet_self {G : SimpleGraph α} {v : α} (hv : v ∈ V(G)) :
    v ∈ G.connectedComponentSet v :=
  Reachable.refl hv

theorem connectedComponentSet_subset_vertexSet (G : SimpleGraph α) (v : α) :
    G.connectedComponentSet v ⊆ V(G) :=
  fun _ h => h.right_mem

theorem connectedComponentSet_eq_of_reachable {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) : G.connectedComponentSet u = G.connectedComponentSet v := by
  ext x
  constructor
  · exact fun hux => h.symm.trans hux
  · exact fun hvx => h.trans hvx

/-- With the first root in the graph, two component sets agree exactly when their roots are
reachable. The hypothesis excludes equality between empty components rooted outside the graph. -/
theorem connectedComponentSet_eq_iff {G : SimpleGraph α} {u v : α}
    (hu : u ∈ V(G)) :
    G.connectedComponentSet u = G.connectedComponentSet v ↔ G.Reachable u v := by
  constructor
  · intro hsets
    have huv : u ∈ G.connectedComponentSet v := hsets ▸ mem_connectedComponentSet_self hu
    exact huv.symm
  · exact connectedComponentSet_eq_of_reachable

/-- Any two connected-component sets are equal or disjoint, including components rooted outside
the graph. -/
theorem connectedComponentSet_eq_or_disjoint (G : SimpleGraph α) (u v : α) :
    G.connectedComponentSet u = G.connectedComponentSet v ∨
      Disjoint (G.connectedComponentSet u) (G.connectedComponentSet v) := by
  by_cases hmeet : ∃ x, x ∈ G.connectedComponentSet u ∧ x ∈ G.connectedComponentSet v
  · obtain ⟨x, hux, hvx⟩ := hmeet
    exact Or.inl (connectedComponentSet_eq_of_reachable (hux.trans hvx.symm))
  · right
    rw [Set.disjoint_left]
    intro x hux hvx
    exact hmeet ⟨x, hux, hvx⟩

/-- With a chosen graph vertex, connectedness says exactly that its component is the full vertex
set. -/
theorem connected_iff_connectedComponentSet_eq_vertexSet (G : SimpleGraph α) {v : α}
    (hv : v ∈ V(G)) : G.Connected ↔ G.connectedComponentSet v = V(G) := by
  constructor
  · rintro ⟨_, hpre⟩
    apply Set.Subset.antisymm (G.connectedComponentSet_subset_vertexSet v)
    intro u hu
    exact hpre v hv u hu
  · intro hcomponent
    refine ⟨⟨v, hv⟩, ?_⟩
    intro u hu w hw
    have hvu : G.Reachable v u := by
      exact (show u ∈ G.connectedComponentSet v from hcomponent.symm ▸ hu)
    have hvw : G.Reachable v w := by
      exact (show w ∈ G.connectedComponentSet v from hcomponent.symm ▸ hw)
    exact hvu.symm.trans hvw

@[simp] theorem preconnected_bot : (⊥ : SimpleGraph α).Preconnected := by
  intro u hu
  simpa using hu

@[simp] theorem not_connected_bot : ¬(⊥ : SimpleGraph α).Connected := by
  rintro ⟨h, _⟩
  simpa using h

@[simp] theorem relabelVertices_preconnected (G : SimpleGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).Preconnected ↔ G.Preconnected := by
  constructor
  · intro h u hu v hv
    exact (G.relabelVertices_reachable f u v).1
      (h (f u) ⟨u, hu, rfl⟩ (f v) ⟨v, hv, rfl⟩)
  · rintro h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (G.relabelVertices_reachable f u v).2 (h u hu v hv)

@[simp] theorem connectedComponentSet_relabelVertices (G : SimpleGraph α)
    (f : α ≃ γ) (v : α) :
    (G.relabelVertices f).connectedComponentSet (f v) = f '' G.connectedComponentSet v := by
  ext x
  obtain ⟨u, rfl⟩ := f.surjective x
  simp

@[simp] theorem relabelVertices_connected (G : SimpleGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).Connected ↔ G.Connected := by
  simp only [Connected, relabelVertices_preconnected, vertexSet_relabelVertices,
    Set.image_nonempty]

end SimpleGraph

namespace Graph

/-- Every two vertices of a general graph are reachable. This is vacuous for an empty graph. -/
def Preconnected (G : Graph α β) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G), G.Reachable u v

/-- A general graph is connected when it is nonempty and preconnected. -/
def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ G.Preconnected

/-- The connected component rooted at an ambient vertex, as a mathematical set. -/
def connectedComponentSet (G : Graph α β) (v : α) : Set α :=
  {u | G.Reachable v u}

@[simp] theorem mem_connectedComponentSet (G : Graph α β) (u v : α) :
    u ∈ G.connectedComponentSet v ↔ G.Reachable v u :=
  Iff.rfl

theorem mem_connectedComponentSet_self {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    v ∈ G.connectedComponentSet v :=
  Reachable.refl hv

theorem connectedComponentSet_subset_vertexSet (G : Graph α β) (v : α) :
    G.connectedComponentSet v ⊆ V(G) :=
  fun _ h => h.right_mem

theorem connectedComponentSet_eq_of_reachable {G : Graph α β} {u v : α}
    (h : G.Reachable u v) : G.connectedComponentSet u = G.connectedComponentSet v := by
  ext x
  constructor
  · exact fun hux => h.symm.trans hux
  · exact fun hvx => h.trans hvx

theorem connectedComponentSet_eq_iff {G : Graph α β} {u v : α}
    (hu : u ∈ V(G)) :
    G.connectedComponentSet u = G.connectedComponentSet v ↔ G.Reachable u v := by
  constructor
  · intro hsets
    have huv : u ∈ G.connectedComponentSet v := hsets ▸ mem_connectedComponentSet_self hu
    exact huv.symm
  · exact connectedComponentSet_eq_of_reachable

theorem connectedComponentSet_eq_or_disjoint (G : Graph α β) (u v : α) :
    G.connectedComponentSet u = G.connectedComponentSet v ∨
      Disjoint (G.connectedComponentSet u) (G.connectedComponentSet v) := by
  by_cases hmeet : ∃ x, x ∈ G.connectedComponentSet u ∧ x ∈ G.connectedComponentSet v
  · obtain ⟨x, hux, hvx⟩ := hmeet
    exact Or.inl (connectedComponentSet_eq_of_reachable (hux.trans hvx.symm))
  · right
    rw [Set.disjoint_left]
    intro x hux hvx
    exact hmeet ⟨x, hux, hvx⟩

theorem connected_iff_connectedComponentSet_eq_vertexSet (G : Graph α β) {v : α}
    (hv : v ∈ V(G)) : G.Connected ↔ G.connectedComponentSet v = V(G) := by
  constructor
  · rintro ⟨_, hpre⟩
    apply Set.Subset.antisymm (G.connectedComponentSet_subset_vertexSet v)
    intro u hu
    exact hpre v hv u hu
  · intro hcomponent
    refine ⟨⟨v, hv⟩, ?_⟩
    intro u hu w hw
    have hvu : G.Reachable v u := by
      exact (show u ∈ G.connectedComponentSet v from hcomponent.symm ▸ hu)
    have hvw : G.Reachable v w := by
      exact (show w ∈ G.connectedComponentSet v from hcomponent.symm ▸ hw)
    exact hvu.symm.trans hvw

@[simp] theorem preconnected_bot : (⊥ : Graph α β).Preconnected := by
  intro u hu
  simpa using hu

@[simp] theorem not_connected_bot : ¬(⊥ : Graph α β).Connected := by
  rintro ⟨h, _⟩
  simpa using h

@[simp] theorem relabelVertices_preconnected (G : Graph α β) (f : α ≃ γ) :
    (G.relabelVertices f).Preconnected ↔ G.Preconnected := by
  constructor
  · intro h u hu v hv
    exact (G.relabelVertices_reachable f u v).1
      (h (f u) ⟨u, hu, rfl⟩ (f v) ⟨v, hv, rfl⟩)
  · rintro h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (G.relabelVertices_reachable f u v).2 (h u hu v hv)

@[simp] theorem connectedComponentSet_relabelVertices (G : Graph α β)
    (f : α ≃ γ) (v : α) :
    (G.relabelVertices f).connectedComponentSet (f v) = f '' G.connectedComponentSet v := by
  ext x
  obtain ⟨u, rfl⟩ := f.surjective x
  simp

@[simp] theorem relabelVertices_connected (G : Graph α β) (f : α ≃ γ) :
    (G.relabelVertices f).Connected ↔ G.Connected := by
  simp only [Connected, relabelVertices_preconnected, vertexSet_relabelVertices,
    Set.image_nonempty]

@[simp] theorem relabelTags_preconnected (G : Graph α β) (g : β ≃ δ) :
    (G.relabelTags g).Preconnected ↔ G.Preconnected := by
  simp only [Preconnected, vertexSet_relabelTags, relabelTags_reachable]

@[simp] theorem connectedComponentSet_relabelTags (G : Graph α β)
    (g : β ≃ δ) (v : α) :
    (G.relabelTags g).connectedComponentSet v = G.connectedComponentSet v := by
  ext u
  simp

@[simp] theorem relabelTags_connected (G : Graph α β) (g : β ≃ δ) :
    (G.relabelTags g).Connected ↔ G.Connected := by
  simp only [Connected, relabelTags_preconnected, vertexSet_relabelTags]

end Graph

end GraphLib
