/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Incidence

/-!
# Adjacency

Adjacency is derived from an actual edge or arc witness. It forgets which witness was used, but
does not redefine the edge carrier or collapse parallel actual values. For directed graphs,
`G.Adj u v` means that an actual arc runs from source `u` to target `v`.
-/

namespace GraphLib
variable {α β : Type*}

open scoped GraphLib

/-! ## Adjacency relations -/

/-- Vertices `u` and `v` are adjacent in a general graph when an actual edge links them. A loop
at `v` witnesses `G.Adj v v`. -/
@[grind] def Graph.Adj (G : Graph α β) (u v : α) : Prop :=
  ∃ e, G.IsLink e u v

/-- Vertices `u` and `v` are adjacent in a simple graph when an actual edge links them. -/
@[grind] def SimpleGraph.Adj (G : SimpleGraph α) (u v : α) : Prop :=
  ∃ e, G.IsLink e u v

/-- There is directed adjacency from `u` to `v` when an actual arc has source `u` and target
`v`. A loop at `v` witnesses `G.Adj v v`. -/
@[grind] def DiGraph.Adj (G : DiGraph α β) (u v : α) : Prop :=
  ∃ a, G.IsArc a u v

/-- There is directed adjacency from `u` to `v` in a simple directed graph when an actual arc
has source `u` and target `v`. -/
@[grind] def SimpleDiGraph.Adj (G : SimpleDiGraph α) (u v : α) : Prop :=
  ∃ a, G.IsArc a u v

theorem Graph.adj_iff_exists_isLink (G : Graph α β) (u v : α) :
    G.Adj u v ↔ ∃ e, G.IsLink e u v := Iff.rfl

theorem SimpleGraph.adj_iff_exists_isLink (G : SimpleGraph α) (u v : α) :
    G.Adj u v ↔ ∃ e, G.IsLink e u v := Iff.rfl

theorem DiGraph.adj_iff_exists_isArc (G : DiGraph α β) (u v : α) :
    G.Adj u v ↔ ∃ a, G.IsArc a u v := Iff.rfl

theorem SimpleDiGraph.adj_iff_exists_isArc (G : SimpleDiGraph α) (u v : α) :
    G.Adj u v ↔ ∃ a, G.IsArc a u v := Iff.rfl

/-- In a simple graph, adjacency is equivalent to direct endpoint-pair membership. -/
@[simp, grind =] theorem SimpleGraph.adj_iff (G : SimpleGraph α) (u v : α) :
    G.Adj u v ↔ s(u, v) ∈ E(G) := by
  constructor
  · rintro ⟨e, he, hends⟩
    rwa [hends] at he
  · intro h
    exact ⟨s(u, v), h, rfl⟩

/-- In a simple directed graph, adjacency is equivalent to direct ordered-pair membership. -/
@[simp, grind =] theorem SimpleDiGraph.adj_iff (G : SimpleDiGraph α) (u v : α) :
    G.Adj u v ↔ (u, v) ∈ E(G) := by
  constructor
  · rintro ⟨a, ha, hs, ht⟩
    rcases a with ⟨x, y⟩
    simp only at hs ht
    subst x
    subst y
    exact ha
  · intro h
    exact ⟨(u, v), h, rfl, rfl⟩

/-! ## Witness extraction and introduction -/

theorem Graph.Adj.exists_isLink {G : Graph α β} {u v : α} (h : G.Adj u v) :
    ∃ e, G.IsLink e u v := h

theorem SimpleGraph.Adj.exists_isLink {G : SimpleGraph α} {u v : α} (h : G.Adj u v) :
    ∃ e, G.IsLink e u v := h

theorem DiGraph.Adj.exists_isArc {G : DiGraph α β} {u v : α} (h : G.Adj u v) :
    ∃ a, G.IsArc a u v := h

theorem SimpleDiGraph.Adj.exists_isArc {G : SimpleDiGraph α} {u v : α} (h : G.Adj u v) :
    ∃ a, G.IsArc a u v := h

theorem Graph.IsLink.adj {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : G.Adj u v := ⟨e, h⟩

theorem SimpleGraph.IsLink.adj {G : SimpleGraph α} {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) : G.Adj u v := ⟨e, h⟩

theorem DiGraph.IsArc.adj {G : DiGraph α β} {a : Arc α β} {u v : α}
    (h : G.IsArc a u v) : G.Adj u v := ⟨a, h⟩

theorem SimpleDiGraph.IsArc.adj {G : SimpleDiGraph α} {a : α × α} {u v : α}
    (h : G.IsArc a u v) : G.Adj u v := ⟨a, h⟩

/-! ## Symmetry for undirected graphs -/

@[symm, grind →] theorem Graph.Adj.symm {G : Graph α β} {u v : α} (h : G.Adj u v) :
    G.Adj v u := by
  obtain ⟨e, hlink⟩ := h
  exact hlink.symm.adj

theorem Graph.adj_comm (G : Graph α β) (u v : α) : G.Adj u v ↔ G.Adj v u :=
  ⟨Adj.symm, Adj.symm⟩

@[symm, grind →] theorem SimpleGraph.Adj.symm {G : SimpleGraph α} {u v : α}
    (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨e, hlink⟩ := h
  exact hlink.symm.adj

theorem SimpleGraph.adj_comm (G : SimpleGraph α) (u v : α) : G.Adj u v ↔ G.Adj v u :=
  ⟨Adj.symm, Adj.symm⟩

/-! ## Looplessness for simple graphs -/

@[grind →] theorem SimpleGraph.Adj.ne {G : SimpleGraph α} {u v : α} (h : G.Adj u v) :
    u ≠ v := by
  have hnd := G.loopless s(u, v) ((G.adj_iff u v).mp h)
  rwa [Sym2.mk_isDiag_iff] at hnd

@[grind →] theorem SimpleDiGraph.Adj.ne {G : SimpleDiGraph α} {u v : α}
    (h : G.Adj u v) : u ≠ v :=
  G.loopless (u, v) ((G.adj_iff u v).mp h)

/-! ## Adjacent vertices belong to the graph -/

@[grind →] theorem Graph.Adj.left_mem {G : Graph α β} {u v : α} (h : G.Adj u v) :
    u ∈ V(G) := by
  obtain ⟨_, hlink⟩ := h
  exact hlink.left_mem

@[grind →] theorem Graph.Adj.right_mem {G : Graph α β} {u v : α} (h : G.Adj u v) :
    v ∈ V(G) := by
  obtain ⟨_, hlink⟩ := h
  exact hlink.right_mem

@[grind →] theorem SimpleGraph.Adj.left_mem {G : SimpleGraph α} {u v : α}
    (h : G.Adj u v) : u ∈ V(G) := by
  obtain ⟨_, hlink⟩ := h
  exact hlink.left_mem

@[grind →] theorem SimpleGraph.Adj.right_mem {G : SimpleGraph α} {u v : α}
    (h : G.Adj u v) : v ∈ V(G) := by
  obtain ⟨_, hlink⟩ := h
  exact hlink.right_mem

@[grind →] theorem DiGraph.Adj.source_mem {G : DiGraph α β} {u v : α} (h : G.Adj u v) :
    u ∈ V(G) := by
  obtain ⟨_, harc⟩ := h
  exact harc.source_mem

@[grind →] theorem DiGraph.Adj.target_mem {G : DiGraph α β} {u v : α} (h : G.Adj u v) :
    v ∈ V(G) := by
  obtain ⟨_, harc⟩ := h
  exact harc.target_mem

@[grind →] theorem SimpleDiGraph.Adj.source_mem {G : SimpleDiGraph α} {u v : α}
    (h : G.Adj u v) : u ∈ V(G) := by
  obtain ⟨_, harc⟩ := h
  exact harc.source_mem

@[grind →] theorem SimpleDiGraph.Adj.target_mem {G : SimpleDiGraph α} {u v : α}
    (h : G.Adj u v) : v ∈ V(G) := by
  obtain ⟨_, harc⟩ := h
  exact harc.target_mem

end GraphLib
