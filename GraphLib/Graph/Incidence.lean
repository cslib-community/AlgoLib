/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Basic

/-!
# Edge and arc incidence

This file defines graph-relative endpoint relations for all four GraphLib graph types. General
relations retain the full bundled `Edge` or `Arc` value: tags are not treated as identities and
parallel actual edges are never merged by an incidence collection.

For directed graphs, `IsArc a u v` is oriented from source `u` to target `v`. The
`outIncidenceSet` and `inIncidenceSet` collections retain actual arcs, and a loop belongs to both.
-/

namespace GraphLib
variable {α β : Type*}

open scoped GraphLib

/-! ## Endpoint relations -/

/-- The actual edge `e` of a general graph links `u` and `v`. -/
@[grind] def Graph.IsLink (G : Graph α β) (e : Edge α β) (u v : α) : Prop :=
  e ∈ E(G) ∧ e.endpoints = s(u, v)

/-- The actual edge `e` of a simple graph links `u` and `v`. -/
@[grind] def SimpleGraph.IsLink (G : SimpleGraph α) (e : Sym2 α) (u v : α) : Prop :=
  e ∈ E(G) ∧ e = s(u, v)

/-- The actual arc `a` of a general directed graph has source `u` and target `v`. -/
@[grind] def DiGraph.IsArc (G : DiGraph α β) (a : Arc α β) (u v : α) : Prop :=
  a ∈ E(G) ∧ a.source = u ∧ a.target = v

/-- The actual arc `a` of a simple directed graph has source `u` and target `v`. -/
@[grind] def SimpleDiGraph.IsArc (G : SimpleDiGraph α) (a : α × α) (u v : α) : Prop :=
  a ∈ E(G) ∧ a.1 = u ∧ a.2 = v

/-- The actual edge `e` is incident with `v` in a general graph. -/
@[grind] def Graph.Inc (G : Graph α β) (e : Edge α β) (v : α) : Prop :=
  e ∈ E(G) ∧ v ∈ e.endpoints

/-- The actual edge `e` is incident with `v` in a simple graph. -/
@[grind] def SimpleGraph.Inc (G : SimpleGraph α) (e : Sym2 α) (v : α) : Prop :=
  e ∈ E(G) ∧ v ∈ e

/-- The actual arc `a` is incident with `v` as either source or target in a general directed
graph. -/
@[grind] def DiGraph.Inc (G : DiGraph α β) (a : Arc α β) (v : α) : Prop :=
  a ∈ E(G) ∧ (a.source = v ∨ a.target = v)

/-- The actual arc `a` is incident with `v` as either source or target in a simple directed
graph. -/
@[grind] def SimpleDiGraph.Inc (G : SimpleDiGraph α) (a : α × α) (v : α) : Prop :=
  a ∈ E(G) ∧ (a.1 = v ∨ a.2 = v)

/-! ## Undirected `IsLink` API -/

@[simp] theorem Graph.isLink_iff (G : Graph α β) (e : Edge α β) (u v : α) :
    G.IsLink e u v ↔ e ∈ E(G) ∧ e.endpoints = s(u, v) := Iff.rfl

theorem Graph.IsLink.edge_mem {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : e ∈ E(G) := h.1

theorem Graph.IsLink.endpoints_eq {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : e.endpoints = s(u, v) := h.2

@[grind →] theorem Graph.IsLink.left_mem {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : u ∈ V(G) := by
  exact G.endpoints_mem e h.edge_mem u (by rw [h.endpoints_eq]; simp)

@[grind →] theorem Graph.IsLink.right_mem {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : v ∈ V(G) := by
  exact G.endpoints_mem e h.edge_mem v (by rw [h.endpoints_eq]; simp)

@[symm, grind →] theorem Graph.IsLink.symm {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : G.IsLink e v u := by
  refine ⟨h.edge_mem, ?_⟩
  rw [show s(v, u) = s(u, v) from Sym2.eq_swap]
  exact h.endpoints_eq

theorem Graph.isLink_comm (G : Graph α β) (e : Edge α β) (u v : α) :
    G.IsLink e u v ↔ G.IsLink e v u := ⟨IsLink.symm, IsLink.symm⟩

theorem Graph.IsLink.inc_left {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : G.Inc e u :=
  ⟨h.edge_mem, by rw [h.endpoints_eq]; simp⟩

theorem Graph.IsLink.inc_right {G : Graph α β} {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) : G.Inc e v :=
  ⟨h.edge_mem, by rw [h.endpoints_eq]; simp⟩

@[simp] theorem SimpleGraph.isLink_iff (G : SimpleGraph α) (e : Sym2 α) (u v : α) :
    G.IsLink e u v ↔ e ∈ E(G) ∧ e = s(u, v) := Iff.rfl

theorem SimpleGraph.IsLink.edge_mem {G : SimpleGraph α} {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) : e ∈ E(G) := h.1

theorem SimpleGraph.IsLink.endpoints_eq {G : SimpleGraph α} {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) : e = s(u, v) := h.2

@[grind →] theorem SimpleGraph.IsLink.left_mem {G : SimpleGraph α} {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) : u ∈ V(G) := by
  exact G.endpoints_mem e h.edge_mem u (by rw [h.endpoints_eq]; simp)

@[grind →] theorem SimpleGraph.IsLink.right_mem {G : SimpleGraph α} {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) : v ∈ V(G) := by
  exact G.endpoints_mem e h.edge_mem v (by rw [h.endpoints_eq]; simp)

@[symm, grind →] theorem SimpleGraph.IsLink.symm {G : SimpleGraph α}
    {e : Sym2 α} {u v : α} (h : G.IsLink e u v) : G.IsLink e v u := by
  refine ⟨h.edge_mem, ?_⟩
  rw [show s(v, u) = s(u, v) from Sym2.eq_swap]
  exact h.endpoints_eq

theorem SimpleGraph.isLink_comm (G : SimpleGraph α) (e : Sym2 α) (u v : α) :
    G.IsLink e u v ↔ G.IsLink e v u := ⟨IsLink.symm, IsLink.symm⟩

theorem SimpleGraph.IsLink.inc_left {G : SimpleGraph α} {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) : G.Inc e u :=
  ⟨h.edge_mem, by rw [h.endpoints_eq]; simp⟩

theorem SimpleGraph.IsLink.inc_right {G : SimpleGraph α} {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) : G.Inc e v :=
  ⟨h.edge_mem, by rw [h.endpoints_eq]; simp⟩

/-! ## Directed `IsArc` API -/

@[simp] theorem DiGraph.isArc_iff (G : DiGraph α β) (a : Arc α β) (u v : α) :
    G.IsArc a u v ↔ a ∈ E(G) ∧ a.source = u ∧ a.target = v := Iff.rfl

theorem DiGraph.IsArc.edge_mem {G : DiGraph α β} {a : Arc α β} {u v : α}
    (h : G.IsArc a u v) : a ∈ E(G) := h.1

theorem DiGraph.IsArc.source_eq {G : DiGraph α β} {a : Arc α β} {u v : α}
    (h : G.IsArc a u v) : a.source = u := h.2.1

theorem DiGraph.IsArc.target_eq {G : DiGraph α β} {a : Arc α β} {u v : α}
    (h : G.IsArc a u v) : a.target = v := h.2.2

@[grind →] theorem DiGraph.IsArc.source_mem {G : DiGraph α β}
    {a : Arc α β} {u v : α} (h : G.IsArc a u v) : u ∈ V(G) := by
  rw [← h.source_eq]
  exact G.source_mem a h.edge_mem

@[grind →] theorem DiGraph.IsArc.target_mem {G : DiGraph α β}
    {a : Arc α β} {u v : α} (h : G.IsArc a u v) : v ∈ V(G) := by
  rw [← h.target_eq]
  exact G.target_mem a h.edge_mem

theorem DiGraph.IsArc.inc_source {G : DiGraph α β} {a : Arc α β} {u v : α}
    (h : G.IsArc a u v) : G.Inc a u := ⟨h.edge_mem, Or.inl h.source_eq⟩

theorem DiGraph.IsArc.inc_target {G : DiGraph α β} {a : Arc α β} {u v : α}
    (h : G.IsArc a u v) : G.Inc a v := ⟨h.edge_mem, Or.inr h.target_eq⟩

@[simp] theorem SimpleDiGraph.isArc_iff (G : SimpleDiGraph α) (a : α × α) (u v : α) :
    G.IsArc a u v ↔ a ∈ E(G) ∧ a.1 = u ∧ a.2 = v := Iff.rfl

theorem SimpleDiGraph.IsArc.edge_mem {G : SimpleDiGraph α} {a : α × α} {u v : α}
    (h : G.IsArc a u v) : a ∈ E(G) := h.1

theorem SimpleDiGraph.IsArc.source_eq {G : SimpleDiGraph α} {a : α × α} {u v : α}
    (h : G.IsArc a u v) : a.1 = u := h.2.1

theorem SimpleDiGraph.IsArc.target_eq {G : SimpleDiGraph α} {a : α × α} {u v : α}
    (h : G.IsArc a u v) : a.2 = v := h.2.2

@[grind →] theorem SimpleDiGraph.IsArc.source_mem {G : SimpleDiGraph α}
    {a : α × α} {u v : α} (h : G.IsArc a u v) : u ∈ V(G) := by
  rw [← h.source_eq]
  exact G.source_mem a h.edge_mem

@[grind →] theorem SimpleDiGraph.IsArc.target_mem {G : SimpleDiGraph α}
    {a : α × α} {u v : α} (h : G.IsArc a u v) : v ∈ V(G) := by
  rw [← h.target_eq]
  exact G.target_mem a h.edge_mem

theorem SimpleDiGraph.IsArc.inc_source {G : SimpleDiGraph α} {a : α × α} {u v : α}
    (h : G.IsArc a u v) : G.Inc a u := ⟨h.edge_mem, Or.inl h.source_eq⟩

theorem SimpleDiGraph.IsArc.inc_target {G : SimpleDiGraph α} {a : α × α} {u v : α}
    (h : G.IsArc a u v) : G.Inc a v := ⟨h.edge_mem, Or.inr h.target_eq⟩

/-! ## Incidence API -/

theorem Graph.Inc.edge_mem {G : Graph α β} {e : Edge α β} {v : α} (h : G.Inc e v) :
    e ∈ E(G) := h.1

@[grind →] theorem Graph.Inc.vertex_mem {G : Graph α β} {e : Edge α β} {v : α}
    (h : G.Inc e v) : v ∈ V(G) := G.endpoints_mem e h.edge_mem v h.2

theorem SimpleGraph.Inc.edge_mem {G : SimpleGraph α} {e : Sym2 α} {v : α}
    (h : G.Inc e v) : e ∈ E(G) := h.1

@[grind →] theorem SimpleGraph.Inc.vertex_mem {G : SimpleGraph α} {e : Sym2 α} {v : α}
    (h : G.Inc e v) : v ∈ V(G) := G.endpoints_mem e h.edge_mem v h.2

theorem DiGraph.Inc.edge_mem {G : DiGraph α β} {a : Arc α β} {v : α} (h : G.Inc a v) :
    a ∈ E(G) := h.1

@[grind →] theorem DiGraph.Inc.vertex_mem {G : DiGraph α β} {a : Arc α β} {v : α}
    (h : G.Inc a v) : v ∈ V(G) := by
  rcases h.2 with hs | ht
  · rw [← hs]
    exact G.source_mem a h.edge_mem
  · rw [← ht]
    exact G.target_mem a h.edge_mem

theorem SimpleDiGraph.Inc.edge_mem {G : SimpleDiGraph α} {a : α × α} {v : α}
    (h : G.Inc a v) : a ∈ E(G) := h.1

@[grind →] theorem SimpleDiGraph.Inc.vertex_mem {G : SimpleDiGraph α}
    {a : α × α} {v : α} (h : G.Inc a v) : v ∈ V(G) := by
  rcases h.2 with hs | ht
  · rw [← hs]
    exact G.source_mem a h.edge_mem
  · rw [← ht]
    exact G.target_mem a h.edge_mem

theorem Graph.inc_iff_exists_isLink (G : Graph α β) (e : Edge α β) (v : α) :
    G.Inc e v ↔ ∃ w, G.IsLink e v w := by
  constructor
  · rintro ⟨he, hv⟩
    rcases e with ⟨tag, endpoints⟩
    induction endpoints with
    | h x y =>
      simp only [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨y, he, rfl⟩
      · exact ⟨x, he, Sym2.eq_swap⟩
  · rintro ⟨w, hlink⟩
    exact hlink.inc_left

theorem SimpleGraph.inc_iff_exists_isLink (G : SimpleGraph α) (e : Sym2 α) (v : α) :
    G.Inc e v ↔ ∃ w, G.IsLink e v w := by
  constructor
  · rintro ⟨he, hv⟩
    induction e with
    | h x y =>
      simp only [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨y, he, rfl⟩
      · exact ⟨x, he, Sym2.eq_swap⟩
  · rintro ⟨w, hlink⟩
    exact hlink.inc_left

theorem DiGraph.inc_iff_exists_isArc (G : DiGraph α β) (a : Arc α β) (v : α) :
    G.Inc a v ↔ ∃ w, G.IsArc a v w ∨ G.IsArc a w v := by
  constructor
  · rintro ⟨ha, hs | ht⟩
    · exact ⟨a.target, Or.inl ⟨ha, hs, rfl⟩⟩
    · exact ⟨a.source, Or.inr ⟨ha, rfl, ht⟩⟩
  · rintro ⟨w, h | h⟩
    · exact h.inc_source
    · exact h.inc_target

theorem SimpleDiGraph.inc_iff_exists_isArc (G : SimpleDiGraph α) (a : α × α) (v : α) :
    G.Inc a v ↔ ∃ w, G.IsArc a v w ∨ G.IsArc a w v := by
  constructor
  · rintro ⟨ha, hs | ht⟩
    · exact ⟨a.2, Or.inl ⟨ha, hs, rfl⟩⟩
    · exact ⟨a.1, Or.inr ⟨ha, rfl, ht⟩⟩
  · rintro ⟨w, h | h⟩
    · exact h.inc_source
    · exact h.inc_target

/-! ## Undirected incidence collections -/

/-- The set of actual edges incident with `v` in a general graph. -/
def Graph.incidenceSet (G : Graph α β) (v : α) : Set (Edge α β) := {e | G.Inc e v}

/-- The set of actual loops at `v` in a general graph. -/
def Graph.loopSet (G : Graph α β) (v : α) : Set (Edge α β) := {e | G.IsLink e v v}

/-- The set of actual edges incident with `v` in a simple graph. -/
def SimpleGraph.incidenceSet (G : SimpleGraph α) (v : α) : Set (Sym2 α) := {e | G.Inc e v}

/-- The set of actual loops at `v` in a simple graph; this set is empty by looplessness. -/
def SimpleGraph.loopSet (G : SimpleGraph α) (v : α) : Set (Sym2 α) := {e | G.IsLink e v v}

@[simp] theorem Graph.mem_incidenceSet (G : Graph α β) (v : α) (e : Edge α β) :
    e ∈ G.incidenceSet v ↔ G.Inc e v := Iff.rfl

@[simp] theorem Graph.mem_loopSet (G : Graph α β) (v : α) (e : Edge α β) :
    e ∈ G.loopSet v ↔ G.IsLink e v v := Iff.rfl

theorem Graph.incidenceSet_subset_edgeSet (G : Graph α β) (v : α) :
    G.incidenceSet v ⊆ E(G) := fun _ h => h.edge_mem

theorem Graph.loopSet_subset_edgeSet (G : Graph α β) (v : α) :
    G.loopSet v ⊆ E(G) := fun _ h => h.edge_mem

theorem Graph.loopSet_subset_incidenceSet (G : Graph α β) (v : α) :
    G.loopSet v ⊆ G.incidenceSet v := fun _ h => h.inc_left

@[simp] theorem SimpleGraph.mem_incidenceSet (G : SimpleGraph α) (v : α) (e : Sym2 α) :
    e ∈ G.incidenceSet v ↔ G.Inc e v := Iff.rfl

@[simp] theorem SimpleGraph.mem_loopSet (G : SimpleGraph α) (v : α) (e : Sym2 α) :
    e ∈ G.loopSet v ↔ G.IsLink e v v := Iff.rfl

theorem SimpleGraph.incidenceSet_subset_edgeSet (G : SimpleGraph α) (v : α) :
    G.incidenceSet v ⊆ E(G) := fun _ h => h.edge_mem

theorem SimpleGraph.loopSet_subset_edgeSet (G : SimpleGraph α) (v : α) :
    G.loopSet v ⊆ E(G) := fun _ h => h.edge_mem

theorem SimpleGraph.loopSet_subset_incidenceSet (G : SimpleGraph α) (v : α) :
    G.loopSet v ⊆ G.incidenceSet v := fun _ h => h.inc_left

/-! ## Directed incidence collections -/

/-- The set of actual arcs whose source is `v` in a general directed graph. -/
def DiGraph.outIncidenceSet (G : DiGraph α β) (v : α) : Set (Arc α β) :=
  {a | a ∈ E(G) ∧ a.source = v}

/-- The set of actual arcs whose target is `v` in a general directed graph. -/
def DiGraph.inIncidenceSet (G : DiGraph α β) (v : α) : Set (Arc α β) :=
  {a | a ∈ E(G) ∧ a.target = v}

/-- The set of actual loops at `v` in a general directed graph. -/
def DiGraph.loopSet (G : DiGraph α β) (v : α) : Set (Arc α β) := {a | G.IsArc a v v}

/-- The set of actual arcs whose source is `v` in a simple directed graph. -/
def SimpleDiGraph.outIncidenceSet (G : SimpleDiGraph α) (v : α) : Set (α × α) :=
  {a | a ∈ E(G) ∧ a.1 = v}

/-- The set of actual arcs whose target is `v` in a simple directed graph. -/
def SimpleDiGraph.inIncidenceSet (G : SimpleDiGraph α) (v : α) : Set (α × α) :=
  {a | a ∈ E(G) ∧ a.2 = v}

/-- The set of actual loops at `v` in a simple directed graph; this set is empty by
looplessness. -/
def SimpleDiGraph.loopSet (G : SimpleDiGraph α) (v : α) : Set (α × α) :=
  {a | G.IsArc a v v}

@[simp] theorem DiGraph.mem_outIncidenceSet (G : DiGraph α β) (v : α) (a : Arc α β) :
    a ∈ G.outIncidenceSet v ↔ a ∈ E(G) ∧ a.source = v := Iff.rfl

@[simp] theorem DiGraph.mem_inIncidenceSet (G : DiGraph α β) (v : α) (a : Arc α β) :
    a ∈ G.inIncidenceSet v ↔ a ∈ E(G) ∧ a.target = v := Iff.rfl

@[simp] theorem DiGraph.mem_loopSet (G : DiGraph α β) (v : α) (a : Arc α β) :
    a ∈ G.loopSet v ↔ G.IsArc a v v := Iff.rfl

theorem DiGraph.mem_outIncidenceSet_iff_exists_isArc
    (G : DiGraph α β) (v : α) (a : Arc α β) :
    a ∈ G.outIncidenceSet v ↔ ∃ w, G.IsArc a v w := by
  constructor
  · rintro ⟨ha, hs⟩
    exact ⟨a.target, ha, hs, rfl⟩
  · rintro ⟨w, h⟩
    exact ⟨h.edge_mem, h.source_eq⟩

theorem DiGraph.mem_inIncidenceSet_iff_exists_isArc
    (G : DiGraph α β) (v : α) (a : Arc α β) :
    a ∈ G.inIncidenceSet v ↔ ∃ u, G.IsArc a u v := by
  constructor
  · rintro ⟨ha, ht⟩
    exact ⟨a.source, ha, rfl, ht⟩
  · rintro ⟨u, h⟩
    exact ⟨h.edge_mem, h.target_eq⟩

theorem DiGraph.outIncidenceSet_subset_edgeSet (G : DiGraph α β) (v : α) :
    G.outIncidenceSet v ⊆ E(G) := fun _ h => h.1

theorem DiGraph.inIncidenceSet_subset_edgeSet (G : DiGraph α β) (v : α) :
    G.inIncidenceSet v ⊆ E(G) := fun _ h => h.1

theorem DiGraph.loopSet_subset_edgeSet (G : DiGraph α β) (v : α) :
    G.loopSet v ⊆ E(G) := fun _ h => h.edge_mem

theorem DiGraph.loopSet_subset_outIncidenceSet (G : DiGraph α β) (v : α) :
    G.loopSet v ⊆ G.outIncidenceSet v := fun _ h => ⟨h.edge_mem, h.source_eq⟩

theorem DiGraph.loopSet_subset_inIncidenceSet (G : DiGraph α β) (v : α) :
    G.loopSet v ⊆ G.inIncidenceSet v := fun _ h => ⟨h.edge_mem, h.target_eq⟩

@[simp] theorem SimpleDiGraph.mem_outIncidenceSet
    (G : SimpleDiGraph α) (v : α) (a : α × α) :
    a ∈ G.outIncidenceSet v ↔ a ∈ E(G) ∧ a.1 = v := Iff.rfl

@[simp] theorem SimpleDiGraph.mem_inIncidenceSet
    (G : SimpleDiGraph α) (v : α) (a : α × α) :
    a ∈ G.inIncidenceSet v ↔ a ∈ E(G) ∧ a.2 = v := Iff.rfl

@[simp] theorem SimpleDiGraph.mem_loopSet (G : SimpleDiGraph α) (v : α) (a : α × α) :
    a ∈ G.loopSet v ↔ G.IsArc a v v := Iff.rfl

theorem SimpleDiGraph.mem_outIncidenceSet_iff_exists_isArc
    (G : SimpleDiGraph α) (v : α) (a : α × α) :
    a ∈ G.outIncidenceSet v ↔ ∃ w, G.IsArc a v w := by
  constructor
  · rintro ⟨ha, hs⟩
    exact ⟨a.2, ha, hs, rfl⟩
  · rintro ⟨w, h⟩
    exact ⟨h.edge_mem, h.source_eq⟩

theorem SimpleDiGraph.mem_inIncidenceSet_iff_exists_isArc
    (G : SimpleDiGraph α) (v : α) (a : α × α) :
    a ∈ G.inIncidenceSet v ↔ ∃ u, G.IsArc a u v := by
  constructor
  · rintro ⟨ha, ht⟩
    exact ⟨a.1, ha, rfl, ht⟩
  · rintro ⟨u, h⟩
    exact ⟨h.edge_mem, h.target_eq⟩

theorem SimpleDiGraph.outIncidenceSet_subset_edgeSet (G : SimpleDiGraph α) (v : α) :
    G.outIncidenceSet v ⊆ E(G) := fun _ h => h.1

theorem SimpleDiGraph.inIncidenceSet_subset_edgeSet (G : SimpleDiGraph α) (v : α) :
    G.inIncidenceSet v ⊆ E(G) := fun _ h => h.1

theorem SimpleDiGraph.loopSet_subset_edgeSet (G : SimpleDiGraph α) (v : α) :
    G.loopSet v ⊆ E(G) := fun _ h => h.edge_mem

theorem SimpleDiGraph.loopSet_subset_outIncidenceSet (G : SimpleDiGraph α) (v : α) :
    G.loopSet v ⊆ G.outIncidenceSet v := fun _ h => ⟨h.edge_mem, h.source_eq⟩

theorem SimpleDiGraph.loopSet_subset_inIncidenceSet (G : SimpleDiGraph α) (v : α) :
    G.loopSet v ⊆ G.inIncidenceSet v := fun _ h => ⟨h.edge_mem, h.target_eq⟩

end GraphLib
