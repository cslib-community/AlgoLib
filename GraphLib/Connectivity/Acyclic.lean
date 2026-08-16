/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Connectivity.Connected
import GraphLib.Walk.InSimpleGraph.Cycle
import GraphLib.Walk.InSimpleDiGraph.Cycle
import GraphLib.Walk.InGraph
import GraphLib.Walk.InDiGraph

/-!
# Acyclic graphs, forests, and trees

Cycle absence is stated using the direction- and identity-correct cycle carrier for each graph
kind. Forests are acyclic undirected graphs, and trees are nonempty connected acyclic graphs.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ δ : Type*}

/-! ## Simple undirected graphs -/

namespace SimpleGraph

/-- A simple graph has a simple cycle when one is realized in the graph. -/
@[grind] def HasSimpleCycle (G : SimpleGraph α) : Prop :=
  ∃ c : SimpleCycle α, G.IsSimpleCycleIn c

/-- A simple graph is acyclic when it has no simple cycle. -/
@[grind] def IsAcyclic (G : SimpleGraph α) : Prop :=
  ¬ G.HasSimpleCycle

/-- A forest is an acyclic undirected graph. -/
def IsForest (G : SimpleGraph α) : Prop := G.IsAcyclic

/-- A tree is a connected acyclic undirected graph. -/
def IsTree (G : SimpleGraph α) : Prop := G.Connected ∧ G.IsAcyclic

theorem hasSimpleCycle_iff (G : SimpleGraph α) :
    G.HasSimpleCycle ↔ ∃ c : SimpleCycle α, G.IsSimpleCycleIn c := Iff.rfl

theorem isAcyclic_iff (G : SimpleGraph α) :
    G.IsAcyclic ↔ ¬ ∃ c : SimpleCycle α, G.IsSimpleCycleIn c := Iff.rfl

lemma hasSimpleCycle_of_subgraph (G H : SimpleGraph α) (hsub : H ≤ G)
    (hH : H.HasSimpleCycle) : G.HasSimpleCycle := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨c, IsSimpleCycleIn.mono G H hc hsub⟩

lemma isAcyclic_of_subgraph (G H : SimpleGraph α) (hsub : H ≤ G)
    (hG : G.IsAcyclic) : H.IsAcyclic :=
  fun hH => hG (hasSimpleCycle_of_subgraph G H hsub hH)

@[grind →] lemma isAcyclic_of_no_edges (G : SimpleGraph α) (hE : E(G) = ∅) :
    G.IsAcyclic := by
  rintro ⟨c, hc⟩
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil c.edges c.edges_ne_nil
  simpa only [hE, Set.mem_empty_iff_false] using IsSimpleCycleIn.edge_mem G hc he

@[simp] theorem relabelVertices_hasSimpleCycle (G : SimpleGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).HasSimpleCycle ↔ G.HasSimpleCycle := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.relabelVertices f.symm, ?_⟩
    simpa using IsSimpleWalkIn.relabelVertices f.symm hc
  · rintro ⟨c, hc⟩
    exact ⟨c.relabelVertices f, IsSimpleWalkIn.relabelVertices f hc⟩

@[simp] theorem relabelVertices_isAcyclic (G : SimpleGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).IsAcyclic ↔ G.IsAcyclic := by
  simp [IsAcyclic]

theorem isForest_iff_isAcyclic (G : SimpleGraph α) : G.IsForest ↔ G.IsAcyclic := Iff.rfl

theorem isTree_iff_connected_and_isAcyclic (G : SimpleGraph α) :
    G.IsTree ↔ G.Connected ∧ G.IsAcyclic := Iff.rfl

namespace IsForest

/-- A simple forest is acyclic. -/
theorem isAcyclic {G : SimpleGraph α} (h : G.IsForest) : G.IsAcyclic := h

end IsForest

namespace IsTree

/-- A simple tree is connected. -/
theorem connected {G : SimpleGraph α} (h : G.IsTree) : G.Connected := h.1

/-- A simple tree is acyclic. -/
theorem isAcyclic {G : SimpleGraph α} (h : G.IsTree) : G.IsAcyclic := h.2

/-- A simple tree is a forest. -/
theorem isForest {G : SimpleGraph α} (h : G.IsTree) : G.IsForest := h.2

end IsTree

end SimpleGraph

/-! ## Simple directed graphs -/

namespace SimpleDiGraph

/-- A simple digraph has a directed simple cycle when one is realized in the graph. -/
def HasSimpleCycle (G : SimpleDiGraph α) : Prop :=
  ∃ c : SimpleDiCycle α, G.IsSimpleDiCycleIn c

/-- A simple digraph is acyclic when it has no directed simple cycle. -/
def IsAcyclic (G : SimpleDiGraph α) : Prop := ¬ G.HasSimpleCycle

theorem hasSimpleCycle_iff (G : SimpleDiGraph α) :
    G.HasSimpleCycle ↔ ∃ c : SimpleDiCycle α, G.IsSimpleDiCycleIn c := Iff.rfl

theorem isAcyclic_iff (G : SimpleDiGraph α) :
    G.IsAcyclic ↔ ¬ ∃ c : SimpleDiCycle α, G.IsSimpleDiCycleIn c := Iff.rfl

lemma hasSimpleCycle_of_subgraph (G H : SimpleDiGraph α) (hsub : H ≤ G)
    (hH : H.HasSimpleCycle) : G.HasSimpleCycle := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨c, IsSimpleDiCycleIn.mono G H hc hsub⟩

lemma isAcyclic_of_subgraph (G H : SimpleDiGraph α) (hsub : H ≤ G)
    (hG : G.IsAcyclic) : H.IsAcyclic :=
  fun hH => hG (hasSimpleCycle_of_subgraph G H hsub hH)

@[grind →] lemma isAcyclic_of_no_edges (G : SimpleDiGraph α) (hE : E(G) = ∅) :
    G.IsAcyclic := by
  rintro ⟨c, hc⟩
  have harcs : c.arcs ≠ [] := by
    intro h
    have := c.two_le_length
    simpa [← VertexSeq.length_arcs, h] using this
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil c.arcs harcs
  simpa only [hE, Set.mem_empty_iff_false] using IsSimpleWalkIn.arc_mem G hc ha

@[simp] theorem reverse_hasSimpleCycle (G : SimpleDiGraph α) :
    G.reverse.HasSimpleCycle ↔ G.HasSimpleCycle := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.reverse, by simpa using IsSimpleDiCycleIn.reverse hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.reverse, IsSimpleDiCycleIn.reverse hc⟩

@[simp] theorem reverse_isAcyclic (G : SimpleDiGraph α) :
    G.reverse.IsAcyclic ↔ G.IsAcyclic := by simp [IsAcyclic]

@[simp] theorem relabelVertices_hasSimpleCycle (G : SimpleDiGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).HasSimpleCycle ↔ G.HasSimpleCycle := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.relabelVertices f.symm, ?_⟩
    simpa using IsSimpleWalkIn.relabelVertices f.symm hc
  · rintro ⟨c, hc⟩
    exact ⟨c.relabelVertices f, IsSimpleWalkIn.relabelVertices f hc⟩

@[simp] theorem relabelVertices_isAcyclic (G : SimpleDiGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).IsAcyclic ↔ G.IsAcyclic := by simp [IsAcyclic]

end SimpleDiGraph

/-! ## General undirected graphs -/

namespace Graph

/-- A general graph has a cycle when an identity-aware cycle is realized in it. -/
def HasCycle (G : Graph α β) : Prop := ∃ c : Cycle α β, G.IsCycleIn c

/-- A general graph is acyclic when it has no identity-aware cycle. -/
def IsAcyclic (G : Graph α β) : Prop := ¬ G.HasCycle

/-- A forest is an acyclic undirected general graph. -/
def IsForest (G : Graph α β) : Prop := G.IsAcyclic

/-- A tree is a connected acyclic undirected general graph. -/
def IsTree (G : Graph α β) : Prop := G.Connected ∧ G.IsAcyclic

theorem hasCycle_iff (G : Graph α β) : G.HasCycle ↔ ∃ c : Cycle α β, G.IsCycleIn c :=
  Iff.rfl

theorem isAcyclic_iff (G : Graph α β) :
    G.IsAcyclic ↔ ¬ ∃ c : Cycle α β, G.IsCycleIn c := Iff.rfl

lemma hasCycle_of_subgraph (G H : Graph α β) (hsub : H ≤ G) (hH : H.HasCycle) :
    G.HasCycle := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨c, hc.mono hsub⟩

lemma isAcyclic_of_subgraph (G H : Graph α β) (hsub : H ≤ G) (hG : G.IsAcyclic) :
    H.IsAcyclic := fun hH => hG (hasCycle_of_subgraph G H hsub hH)

@[grind →] lemma isAcyclic_of_no_edges (G : Graph α β) (hE : E(G) = ∅) :
    G.IsAcyclic := by
  rintro ⟨c, hc⟩
  have hedges : c.edges ≠ [] := by
    intro h
    have := c.length_pos
    simpa [← Walk.length_edges, h] using this
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil c.edges hedges
  simpa only [hE, Set.mem_empty_iff_false] using hc.edge_mem he

@[simp] theorem relabelVertices_hasCycle (G : Graph α β) (f : α ≃ γ) :
    (G.relabelVertices f).HasCycle ↔ G.HasCycle := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.relabelVertices f.symm, ?_⟩
    simpa using hc.relabelVertices f.symm
  · rintro ⟨c, hc⟩
    exact ⟨c.relabelVertices f, hc.relabelVertices f⟩

@[simp] theorem relabelTags_hasCycle (G : Graph α β) (g : β ≃ δ) :
    (G.relabelTags g).HasCycle ↔ G.HasCycle := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.relabelTags g.symm, ?_⟩
    simpa using hc.relabelTags g.symm
  · rintro ⟨c, hc⟩
    exact ⟨c.relabelTags g, hc.relabelTags g⟩

@[simp] theorem relabelVertices_isAcyclic (G : Graph α β) (f : α ≃ γ) :
    (G.relabelVertices f).IsAcyclic ↔ G.IsAcyclic := by simp [IsAcyclic]

@[simp] theorem relabelTags_isAcyclic (G : Graph α β) (g : β ≃ δ) :
    (G.relabelTags g).IsAcyclic ↔ G.IsAcyclic := by simp [IsAcyclic]

theorem isForest_iff_isAcyclic (G : Graph α β) : G.IsForest ↔ G.IsAcyclic := Iff.rfl

theorem isTree_iff_connected_and_isAcyclic (G : Graph α β) :
    G.IsTree ↔ G.Connected ∧ G.IsAcyclic := Iff.rfl

namespace IsForest

theorem isAcyclic {G : Graph α β} (h : G.IsForest) : G.IsAcyclic := h

end IsForest

namespace IsTree

theorem connected {G : Graph α β} (h : G.IsTree) : G.Connected := h.1

theorem isAcyclic {G : Graph α β} (h : G.IsTree) : G.IsAcyclic := h.2

theorem isForest {G : Graph α β} (h : G.IsTree) : G.IsForest := h.2

end IsTree

end Graph

/-! ## General directed graphs -/

namespace DiGraph

/-- A general digraph has a cycle when an actual-arc-aware cycle is realized in it. -/
def HasCycle (G : DiGraph α β) : Prop := ∃ c : DiCycle α β, G.IsCycleIn c

/-- A general digraph is acyclic when it has no actual-arc-aware cycle. -/
def IsAcyclic (G : DiGraph α β) : Prop := ¬ G.HasCycle

theorem hasCycle_iff (G : DiGraph α β) :
    G.HasCycle ↔ ∃ c : DiCycle α β, G.IsCycleIn c := Iff.rfl

theorem isAcyclic_iff (G : DiGraph α β) :
    G.IsAcyclic ↔ ¬ ∃ c : DiCycle α β, G.IsCycleIn c := Iff.rfl

lemma hasCycle_of_subgraph (G H : DiGraph α β) (hsub : H ≤ G) (hH : H.HasCycle) :
    G.HasCycle := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨c, hc.mono hsub⟩

lemma isAcyclic_of_subgraph (G H : DiGraph α β) (hsub : H ≤ G) (hG : G.IsAcyclic) :
    H.IsAcyclic := fun hH => hG (hasCycle_of_subgraph G H hsub hH)

@[grind →] lemma isAcyclic_of_no_edges (G : DiGraph α β) (hE : E(G) = ∅) :
    G.IsAcyclic := by
  rintro ⟨c, hc⟩
  have harcs : c.arcs ≠ [] := by
    intro h
    have := c.length_pos
    simpa [← Walk.length_arcs, h] using this
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil c.arcs harcs
  simpa only [hE, Set.mem_empty_iff_false] using hc.arc_mem ha

@[simp] theorem reverse_hasCycle (G : DiGraph α β) :
    G.reverse.HasCycle ↔ G.HasCycle := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.reverse, by simpa using hc.reverse⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.reverse, hc.reverse⟩

@[simp] theorem reverse_isAcyclic (G : DiGraph α β) :
    G.reverse.IsAcyclic ↔ G.IsAcyclic := by simp [IsAcyclic]

@[simp] theorem relabelVertices_hasCycle (G : DiGraph α β) (f : α ≃ γ) :
    (G.relabelVertices f).HasCycle ↔ G.HasCycle := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.relabelVertices f.symm, ?_⟩
    simpa using hc.relabelVertices f.symm
  · rintro ⟨c, hc⟩
    exact ⟨c.relabelVertices f, hc.relabelVertices f⟩

@[simp] theorem relabelTags_hasCycle (G : DiGraph α β) (g : β ≃ δ) :
    (G.relabelTags g).HasCycle ↔ G.HasCycle := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.relabelTags g.symm, ?_⟩
    simpa using hc.relabelTags g.symm
  · rintro ⟨c, hc⟩
    exact ⟨c.relabelTags g, hc.relabelTags g⟩

@[simp] theorem relabelVertices_isAcyclic (G : DiGraph α β) (f : α ≃ γ) :
    (G.relabelVertices f).IsAcyclic ↔ G.IsAcyclic := by simp [IsAcyclic]

@[simp] theorem relabelTags_isAcyclic (G : DiGraph α β) (g : β ≃ δ) :
    (G.relabelTags g).IsAcyclic ↔ G.IsAcyclic := by simp [IsAcyclic]

end DiGraph

end GraphLib
