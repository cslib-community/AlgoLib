/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Delete

/-!
# Vertex maps, relabeling, and graph conversions

Arbitrary vertex maps on general graphs retain the complete source edge or arc as the target
tag. This provenance makes the actual-edge map injective even when the vertex function is
constant. Arbitrary maps on simple graphs are intentionally lossy: they discard newly created
loops and merge endpoint pairs that become equal.

Vertex and tag relabeling require equivalences. The conversions in this file are explicit;
`underlyingSimple` drops loops and merges parallel values, while direction-forgetting may merge
antiparallel simple arcs.
-/

namespace GraphLib
variable {α β γ δ : Type*}

open scoped GraphLib

/-! ## Edge and arc transformations -/

namespace Edge

/-- Map an edge's endpoints while retaining the complete source edge as provenance in its tag. -/
def mapVertices (f : α → γ) (e : Edge α β) : Edge γ (Edge α β) :=
  ⟨e, Sym2.map f e.endpoints⟩

@[simp] theorem tag_mapVertices (f : α → γ) (e : Edge α β) :
    (e.mapVertices f).tag = e := rfl

@[simp] theorem endpoints_mapVertices (f : α → γ) (e : Edge α β) :
    (e.mapVertices f).endpoints = Sym2.map f e.endpoints := rfl

/-- Provenance makes endpoint mapping injective even when the vertex map is not injective. -/
theorem mapVertices_injective (f : α → γ) : Function.Injective (mapVertices f : Edge α β → _) :=
  fun _ _ h => congrArg Edge.tag h

/-- Relabel an edge's vertices through an equivalence, preserving its tag. -/
def relabelVertices (f : α ≃ γ) : Edge α β ≃ Edge γ β where
  toFun e := ⟨e.tag, Sym2.map f e.endpoints⟩
  invFun e := ⟨e.tag, Sym2.map f.symm e.endpoints⟩
  left_inv e := by
    apply Edge.ext <;> simp [Sym2.map_map]
  right_inv e := by
    apply Edge.ext <;> simp [Sym2.map_map]

/-- Relabel an edge's tag through an equivalence, preserving its endpoints. -/
def relabelTags (g : β ≃ δ) : Edge α β ≃ Edge α δ where
  toFun e := ⟨g e.tag, e.endpoints⟩
  invFun e := ⟨g.symm e.tag, e.endpoints⟩
  left_inv e := by ext <;> simp
  right_inv e := by ext <;> simp

@[simp] theorem tag_relabelVertices (f : α ≃ γ) (e : Edge α β) :
    (relabelVertices f e).tag = e.tag := rfl

@[simp] theorem endpoints_relabelVertices (f : α ≃ γ) (e : Edge α β) :
    (relabelVertices f e).endpoints = Sym2.map f e.endpoints := rfl

@[simp] theorem tag_relabelTags (g : β ≃ δ) (e : Edge α β) :
    (relabelTags g e).tag = g e.tag := rfl

@[simp] theorem endpoints_relabelTags (g : β ≃ δ) (e : Edge α β) :
    (relabelTags g e).endpoints = e.endpoints := rfl

@[simp] theorem relabelVertices_refl (e : Edge α β) :
    relabelVertices (Equiv.refl α) e = e := by ext <;> simp

@[simp] theorem relabelVertices_trans (f : α ≃ γ) (g : γ ≃ δ) (e : Edge α β) :
    relabelVertices g (relabelVertices f e) = relabelVertices (f.trans g) e := by
  apply Edge.ext <;> simp [Sym2.map_map]

@[simp] theorem relabelVertices_symm (f : α ≃ γ) (e : Edge α β) :
    relabelVertices f.symm (relabelVertices f e) = e := by simp

@[simp] theorem relabelTags_refl (e : Edge α β) :
    relabelTags (Equiv.refl β) e = e := by ext <;> simp

@[simp] theorem relabelTags_trans (f : β ≃ γ) (g : γ ≃ δ) (e : Edge α β) :
    relabelTags g (relabelTags f e) = relabelTags (f.trans g) e := by ext <;> simp

@[simp] theorem relabelTags_symm (g : β ≃ δ) (e : Edge α β) :
    relabelTags g.symm (relabelTags g e) = e := by simp

end Edge

namespace Arc

/-- Map an arc's endpoints while retaining the complete source arc as provenance in its tag. -/
def mapVertices (f : α → γ) (a : Arc α β) : Arc γ (Arc α β) :=
  ⟨a, (f a.source, f a.target)⟩

@[simp] theorem tag_mapVertices (f : α → γ) (a : Arc α β) :
    (a.mapVertices f).tag = a := rfl

@[simp] theorem source_mapVertices (f : α → γ) (a : Arc α β) :
    (a.mapVertices f).source = f a.source := rfl

@[simp] theorem target_mapVertices (f : α → γ) (a : Arc α β) :
    (a.mapVertices f).target = f a.target := rfl

@[simp] theorem endpoints_mapVertices (f : α → γ) (a : Arc α β) :
    (a.mapVertices f).endpoints = (f a.source, f a.target) := rfl

/-- Provenance makes endpoint mapping injective even when the vertex map is not injective. -/
theorem mapVertices_injective (f : α → γ) : Function.Injective (mapVertices f : Arc α β → _) :=
  fun _ _ h => congrArg Arc.tag h

/-- Relabel an arc's vertices through an equivalence, preserving its tag. -/
def relabelVertices (f : α ≃ γ) : Arc α β ≃ Arc γ β where
  toFun a := ⟨a.tag, (f a.source, f a.target)⟩
  invFun a := ⟨a.tag, (f.symm a.source, f.symm a.target)⟩
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp

/-- Relabel an arc's tag through an equivalence, preserving its source and target. -/
def relabelTags (g : β ≃ δ) : Arc α β ≃ Arc α δ where
  toFun a := ⟨g a.tag, a.endpoints⟩
  invFun a := ⟨g.symm a.tag, a.endpoints⟩
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp

@[simp] theorem tag_relabelVertices (f : α ≃ γ) (a : Arc α β) :
    (relabelVertices f a).tag = a.tag := rfl

@[simp] theorem source_relabelVertices (f : α ≃ γ) (a : Arc α β) :
    (relabelVertices f a).source = f a.source := rfl

@[simp] theorem target_relabelVertices (f : α ≃ γ) (a : Arc α β) :
    (relabelVertices f a).target = f a.target := rfl

@[simp] theorem endpoints_relabelVertices (f : α ≃ γ) (a : Arc α β) :
    (relabelVertices f a).endpoints = (f a.source, f a.target) := rfl

@[simp] theorem tag_relabelTags (g : β ≃ δ) (a : Arc α β) :
    (relabelTags g a).tag = g a.tag := rfl

@[simp] theorem source_relabelTags (g : β ≃ δ) (a : Arc α β) :
    (relabelTags g a).source = a.source := rfl

@[simp] theorem target_relabelTags (g : β ≃ δ) (a : Arc α β) :
    (relabelTags g a).target = a.target := rfl

@[simp] theorem endpoints_relabelTags (g : β ≃ δ) (a : Arc α β) :
    (relabelTags g a).endpoints = a.endpoints := rfl

@[simp] theorem relabelVertices_refl (a : Arc α β) :
    relabelVertices (Equiv.refl α) a = a := by ext <;> simp

@[simp] theorem relabelVertices_trans (f : α ≃ γ) (g : γ ≃ δ) (a : Arc α β) :
    relabelVertices g (relabelVertices f a) = relabelVertices (f.trans g) a := by
  ext <;> simp

@[simp] theorem relabelVertices_symm (f : α ≃ γ) (a : Arc α β) :
    relabelVertices f.symm (relabelVertices f a) = a := by simp

@[simp] theorem relabelTags_refl (a : Arc α β) :
    relabelTags (Equiv.refl β) a = a := by ext <;> simp

@[simp] theorem relabelTags_trans (f : β ≃ γ) (g : γ ≃ δ) (a : Arc α β) :
    relabelTags g (relabelTags f a) = relabelTags (f.trans g) a := by ext <;> simp

@[simp] theorem relabelTags_symm (g : β ≃ δ) (a : Arc α β) :
    relabelTags g.symm (relabelTags g a) = a := by simp

end Arc

/-! ## Arbitrary vertex maps -/

/-- Map a general graph's vertices. Each target edge is tagged by its complete source edge, so
distinct actual source edges remain distinct under every vertex function. -/
def Graph.mapVertices (G : Graph α β) (f : α → γ) : Graph γ (Edge α β) where
  vertexSet := f '' V(G)
  edgeSet := Edge.mapVertices f '' E(G)
  endpoints_mem := by
    rintro _ ⟨e, he, rfl⟩ v hv
    obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hv
    exact ⟨u, G.endpoints_mem e he u hu, rfl⟩

/-- Map a general directed graph's vertices. Each target arc is tagged by its complete source
arc, so distinct actual source arcs remain distinct under every vertex function. -/
def DiGraph.mapVertices (G : DiGraph α β) (f : α → γ) : DiGraph γ (Arc α β) where
  vertexSet := f '' V(G)
  edgeSet := Arc.mapVertices f '' E(G)
  source_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a.source, G.source_mem a ha, rfl⟩
  target_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a.target, G.target_mem a ha, rfl⟩

/-- Map a simple graph's vertices. Equal endpoint images are merged and newly created loops are
dropped, so this operation is intentionally lossy. -/
def SimpleGraph.mapVertices (G : SimpleGraph α) (f : α → γ) : SimpleGraph γ where
  vertexSet := f '' V(G)
  edgeSet := (Sym2.map f '' E(G)) ∩ {e | ¬ e.IsDiag}
  endpoints_mem := by
    rintro e ⟨⟨d, hd, rfl⟩, _⟩ v hv
    obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hv
    exact ⟨u, G.endpoints_mem d hd u hu, rfl⟩
  loopless := by rintro _ ⟨_, h⟩; exact h

/-- Map a simple directed graph's vertices. Equal ordered endpoint images are merged and newly
created loops are dropped, so this operation is intentionally lossy. -/
def SimpleDiGraph.mapVertices (G : SimpleDiGraph α) (f : α → γ) : SimpleDiGraph γ where
  vertexSet := f '' V(G)
  edgeSet := (fun a => (f a.1, f a.2)) '' E(G) ∩ {a | a.1 ≠ a.2}
  source_mem := by rintro _ ⟨⟨a, ha, rfl⟩, _⟩; exact ⟨a.1, G.source_mem a ha, rfl⟩
  target_mem := by rintro _ ⟨⟨a, ha, rfl⟩, _⟩; exact ⟨a.2, G.target_mem a ha, rfl⟩
  loopless := by rintro _ ⟨_, h⟩; exact h

namespace Graph

@[simp] theorem vertexSet_mapVertices (G : Graph α β) (f : α → γ) :
    V(G.mapVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_mapVertices (G : Graph α β) (f : α → γ) :
    E(G.mapVertices f) = Edge.mapVertices f '' E(G) := rfl

@[simp] theorem mem_edgeSet_mapVertices (G : Graph α β) (f : α → γ)
    (e' : Edge γ (Edge α β)) :
    e' ∈ E(G.mapVertices f) ↔ ∃ e ∈ E(G), Edge.mapVertices f e = e' := Iff.rfl

@[simp] theorem mapVertices_edge_mem (G : Graph α β) (f : α → γ) (e : Edge α β) :
    Edge.mapVertices f e ∈ E(G.mapVertices f) ↔ e ∈ E(G) := by
  constructor
  · rintro ⟨e', he', h⟩
    exact (Edge.mapVertices_injective f h).symm ▸ he'
  · exact fun he => ⟨e, he, rfl⟩

theorem mapVertices_isLink (G : Graph α β) (f : α → γ) {e : Edge α β} {u v : α}
    (h : G.IsLink e u v) :
    (G.mapVertices f).IsLink (Edge.mapVertices f e) (f u) (f v) := by
  refine ⟨(G.mapVertices_edge_mem f e).2 h.edge_mem, ?_⟩
  simp [h.endpoints_eq]

theorem mapVertices_adj (G : Graph α β) (f : α → γ) {u v : α} (h : G.Adj u v) :
    (G.mapVertices f).Adj (f u) (f v) := by
  obtain ⟨e, he⟩ := h
  exact (G.mapVertices_isLink f he).adj

end Graph

namespace DiGraph

@[simp] theorem vertexSet_mapVertices (G : DiGraph α β) (f : α → γ) :
    V(G.mapVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_mapVertices (G : DiGraph α β) (f : α → γ) :
    E(G.mapVertices f) = Arc.mapVertices f '' E(G) := rfl

@[simp] theorem mem_edgeSet_mapVertices (G : DiGraph α β) (f : α → γ)
    (a' : Arc γ (Arc α β)) :
    a' ∈ E(G.mapVertices f) ↔ ∃ a ∈ E(G), Arc.mapVertices f a = a' := Iff.rfl

@[simp] theorem mapVertices_edge_mem (G : DiGraph α β) (f : α → γ) (a : Arc α β) :
    Arc.mapVertices f a ∈ E(G.mapVertices f) ↔ a ∈ E(G) := by
  constructor
  · rintro ⟨a', ha', h⟩
    exact (Arc.mapVertices_injective f h).symm ▸ ha'
  · exact fun ha => ⟨a, ha, rfl⟩

theorem mapVertices_isArc (G : DiGraph α β) (f : α → γ) {a : Arc α β} {u v : α}
    (h : G.IsArc a u v) :
    (G.mapVertices f).IsArc (Arc.mapVertices f a) (f u) (f v) := by
  exact ⟨(G.mapVertices_edge_mem f a).2 h.edge_mem,
    congrArg f h.source_eq, congrArg f h.target_eq⟩

theorem mapVertices_adj (G : DiGraph α β) (f : α → γ) {u v : α} (h : G.Adj u v) :
    (G.mapVertices f).Adj (f u) (f v) := by
  obtain ⟨a, ha⟩ := h
  exact (G.mapVertices_isArc f ha).adj

end DiGraph

namespace SimpleGraph

@[simp] theorem vertexSet_mapVertices (G : SimpleGraph α) (f : α → γ) :
    V(G.mapVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_mapVertices (G : SimpleGraph α) (f : α → γ) :
    E(G.mapVertices f) = (Sym2.map f '' E(G)) ∩ {e | ¬ e.IsDiag} := rfl

@[simp] theorem mem_edgeSet_mapVertices (G : SimpleGraph α) (f : α → γ) (e : Sym2 γ) :
    e ∈ E(G.mapVertices f) ↔
      (∃ d ∈ E(G), Sym2.map f d = e) ∧ ¬ e.IsDiag := Iff.rfl

/-- A simple edge survives a vertex map when its endpoint images remain distinct. -/
theorem mapVertices_isLink (G : SimpleGraph α) (f : α → γ) {e : Sym2 α} {u v : α}
    (h : G.IsLink e u v) (hne : f u ≠ f v) :
    (G.mapVertices f).IsLink (Sym2.map f e) (f u) (f v) := by
  refine ⟨⟨⟨e, h.edge_mem, rfl⟩, ?_⟩, ?_⟩
  · simpa [h.endpoints_eq] using hne
  · simp [h.endpoints_eq]

theorem mapVertices_adj (G : SimpleGraph α) (f : α → γ) {u v : α}
    (h : G.Adj u v) (hne : f u ≠ f v) : (G.mapVertices f).Adj (f u) (f v) := by
  obtain ⟨e, he⟩ := h
  exact (G.mapVertices_isLink f he hne).adj

end SimpleGraph

namespace SimpleDiGraph

@[simp] theorem vertexSet_mapVertices (G : SimpleDiGraph α) (f : α → γ) :
    V(G.mapVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_mapVertices (G : SimpleDiGraph α) (f : α → γ) :
    E(G.mapVertices f) = (fun a => (f a.1, f a.2)) '' E(G) ∩ {a | a.1 ≠ a.2} := rfl

@[simp] theorem mem_edgeSet_mapVertices (G : SimpleDiGraph α) (f : α → γ) (a : γ × γ) :
    a ∈ E(G.mapVertices f) ↔
      (∃ b ∈ E(G), (f b.1, f b.2) = a) ∧ a.1 ≠ a.2 := Iff.rfl

/-- A simple arc survives a vertex map when its source and target images remain distinct. -/
theorem mapVertices_isArc (G : SimpleDiGraph α) (f : α → γ) {a : α × α} {u v : α}
    (h : G.IsArc a u v) (hne : f u ≠ f v) :
    (G.mapVertices f).IsArc (f a.1, f a.2) (f u) (f v) := by
  exact ⟨⟨⟨a, h.edge_mem, rfl⟩, by simpa [h.source_eq, h.target_eq]⟩,
    by simp [h.source_eq], by simp [h.target_eq]⟩

theorem mapVertices_adj (G : SimpleDiGraph α) (f : α → γ) {u v : α}
    (h : G.Adj u v) (hne : f u ≠ f v) : (G.mapVertices f).Adj (f u) (f v) := by
  obtain ⟨a, ha⟩ := h
  exact (G.mapVertices_isArc f ha hne).adj

end SimpleDiGraph

/-! ## Equivalence-based relabeling -/

/-- Relabel every vertex of a general graph through an equivalence. -/
def Graph.relabelVertices (G : Graph α β) (f : α ≃ γ) : Graph γ β where
  vertexSet := f '' V(G)
  edgeSet := Edge.relabelVertices f '' E(G)
  endpoints_mem := by
    rintro _ ⟨e, he, rfl⟩ v hv
    obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hv
    exact ⟨u, G.endpoints_mem e he u hu, rfl⟩

/-- Relabel every vertex of a simple graph through an equivalence. -/
def SimpleGraph.relabelVertices (G : SimpleGraph α) (f : α ≃ γ) : SimpleGraph γ where
  vertexSet := f '' V(G)
  edgeSet := Sym2.map f '' E(G)
  endpoints_mem := by
    rintro _ ⟨e, he, rfl⟩ v hv
    obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hv
    exact ⟨u, G.endpoints_mem e he u hu, rfl⟩
  loopless := by
    rintro _ ⟨e, he, rfl⟩ hdiag
    exact G.loopless e he ((Sym2.isDiag_map f.injective).mp hdiag)

/-- Relabel every vertex of a general directed graph through an equivalence. -/
def DiGraph.relabelVertices (G : DiGraph α β) (f : α ≃ γ) : DiGraph γ β where
  vertexSet := f '' V(G)
  edgeSet := Arc.relabelVertices f '' E(G)
  source_mem := by rintro _ ⟨a, ha, rfl⟩; exact ⟨a.source, G.source_mem a ha, rfl⟩
  target_mem := by rintro _ ⟨a, ha, rfl⟩; exact ⟨a.target, G.target_mem a ha, rfl⟩

/-- Relabel every vertex of a simple directed graph through an equivalence. -/
def SimpleDiGraph.relabelVertices (G : SimpleDiGraph α) (f : α ≃ γ) : SimpleDiGraph γ where
  vertexSet := f '' V(G)
  edgeSet := (fun a => (f a.1, f a.2)) '' E(G)
  source_mem := by rintro _ ⟨a, ha, rfl⟩; exact ⟨a.1, G.source_mem a ha, rfl⟩
  target_mem := by rintro _ ⟨a, ha, rfl⟩; exact ⟨a.2, G.target_mem a ha, rfl⟩
  loopless := by rintro _ ⟨a, ha, rfl⟩ h; exact G.loopless a ha (f.injective h)

/-- Relabel every tag of a general graph through an equivalence. -/
def Graph.relabelTags (G : Graph α β) (g : β ≃ δ) : Graph α δ where
  vertexSet := V(G)
  edgeSet := Edge.relabelTags g '' E(G)
  endpoints_mem := by rintro _ ⟨e, he, rfl⟩; exact G.endpoints_mem e he

/-- Relabel every tag of a general directed graph through an equivalence. -/
def DiGraph.relabelTags (G : DiGraph α β) (g : β ≃ δ) : DiGraph α δ where
  vertexSet := V(G)
  edgeSet := Arc.relabelTags g '' E(G)
  source_mem := by rintro _ ⟨a, ha, rfl⟩; exact G.source_mem a ha
  target_mem := by rintro _ ⟨a, ha, rfl⟩; exact G.target_mem a ha

namespace Graph

@[simp] theorem vertexSet_relabelVertices (G : Graph α β) (f : α ≃ γ) :
    V(G.relabelVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_relabelVertices (G : Graph α β) (f : α ≃ γ) :
    E(G.relabelVertices f) = Edge.relabelVertices f '' E(G) := rfl

@[simp] theorem relabelVertices_edge_mem (G : Graph α β) (f : α ≃ γ) (e : Edge α β) :
    Edge.relabelVertices f e ∈ E(G.relabelVertices f) ↔ e ∈ E(G) := by
  constructor
  · rintro ⟨d, hd, h⟩
    exact (Edge.relabelVertices f).injective h |>.symm ▸ hd
  · exact fun h => ⟨e, h, rfl⟩

@[simp] theorem relabelVertices_isLink (G : Graph α β) (f : α ≃ γ)
    (e : Edge α β) (u v : α) :
    (G.relabelVertices f).IsLink (Edge.relabelVertices f e) (f u) (f v) ↔
      G.IsLink e u v := by
  simp only [Graph.IsLink, relabelVertices_edge_mem, Edge.endpoints_relabelVertices]
  constructor
  · rintro ⟨he, hends⟩
    refine ⟨he, Sym2.map.injective f.injective ?_⟩
    simpa using hends
  · rintro ⟨he, hends⟩
    exact ⟨he, by simpa using congrArg (Sym2.map f) hends⟩

@[simp] theorem relabelVertices_adj (G : Graph α β) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Adj (f u) (f v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨e', he'⟩
    obtain ⟨e, he, rfl⟩ := he'.edge_mem
    exact ⟨e, (G.relabelVertices_isLink f e u v).1 he'⟩
  · rintro ⟨e, he⟩
    exact ⟨Edge.relabelVertices f e, (G.relabelVertices_isLink f e u v).2 he⟩

@[simp] theorem relabelVertices_inc (G : Graph α β) (f : α ≃ γ)
    (e : Edge α β) (v : α) :
    (G.relabelVertices f).Inc (Edge.relabelVertices f e) (f v) ↔ G.Inc e v := by
  simp only [Graph.Inc, relabelVertices_edge_mem, Edge.endpoints_relabelVertices,
    Sym2.mem_map]
  constructor
  · rintro ⟨he, u, hu, huv⟩
    exact ⟨he, f.injective huv ▸ hu⟩
  · rintro ⟨he, hv⟩
    exact ⟨he, v, hv, rfl⟩

/-- Vertex relabeling preserves and reflects the subgraph order. -/
theorem relabelVertices_le_relabelVertices {G H : Graph α β} (f : α ≃ γ) :
    G.relabelVertices f ≤ H.relabelVertices f ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨fun v hv => ?_, fun e he => ?_⟩
    · have hm := h.vertexSet_subset (show f v ∈ V(G.relabelVertices f) from ⟨v, hv, rfl⟩)
      obtain ⟨w, hw, heq⟩ := hm
      exact f.injective heq ▸ hw
    · have hm := h.edgeSet_subset ((G.relabelVertices_edge_mem f e).2 he)
      exact (H.relabelVertices_edge_mem f e).1 hm
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, h.vertexSet_subset hv, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨e, h.edgeSet_subset he, rfl⟩

@[simp] theorem relabelVertices_id (G : Graph α β) :
    G.relabelVertices (Equiv.refl α) = G := by ext <;> simp [Graph.relabelVertices]

@[simp] theorem relabelVertices_comp (G : Graph α β) (f : α ≃ γ) (g : γ ≃ δ) :
    (G.relabelVertices f).relabelVertices g = G.relabelVertices (f.trans g) := by
  apply Graph.ext
  · simp only [vertexSet_relabelVertices, Set.image_image]
    rfl
  · simp only [edgeSet_relabelVertices, Set.image_image]
    apply congrArg (fun h => h '' E(G))
    funext e
    exact Edge.relabelVertices_trans f g e

@[simp] theorem relabelVertices_inverse (G : Graph α β) (f : α ≃ γ) :
    (G.relabelVertices f).relabelVertices f.symm = G := by simp

@[simp] theorem vertexSet_relabelTags (G : Graph α β) (g : β ≃ δ) :
    V(G.relabelTags g) = V(G) := rfl

@[simp] theorem edgeSet_relabelTags (G : Graph α β) (g : β ≃ δ) :
    E(G.relabelTags g) = Edge.relabelTags g '' E(G) := rfl

@[simp] theorem relabelTags_edge_mem (G : Graph α β) (g : β ≃ δ) (e : Edge α β) :
    Edge.relabelTags g e ∈ E(G.relabelTags g) ↔ e ∈ E(G) := by
  constructor
  · rintro ⟨d, hd, h⟩
    exact (Edge.relabelTags g).injective h |>.symm ▸ hd
  · exact fun h => ⟨e, h, rfl⟩

@[simp] theorem relabelTags_isLink (G : Graph α β) (g : β ≃ δ)
    (e : Edge α β) (u v : α) :
    (G.relabelTags g).IsLink (Edge.relabelTags g e) u v ↔ G.IsLink e u v := by
  simp [Graph.IsLink]

@[simp] theorem relabelTags_adj (G : Graph α β) (g : β ≃ δ) (u v : α) :
    (G.relabelTags g).Adj u v ↔ G.Adj u v := by
  constructor
  · rintro ⟨e', he'⟩
    obtain ⟨e, he, rfl⟩ := he'.edge_mem
    exact ⟨e, (G.relabelTags_isLink g e u v).1 he'⟩
  · rintro ⟨e, he⟩
    exact ⟨Edge.relabelTags g e, (G.relabelTags_isLink g e u v).2 he⟩

@[simp] theorem relabelTags_inc (G : Graph α β) (g : β ≃ δ)
    (e : Edge α β) (v : α) :
    (G.relabelTags g).Inc (Edge.relabelTags g e) v ↔ G.Inc e v := by
  simp [Graph.Inc]

/-- Tag relabeling preserves and reflects the subgraph order. -/
theorem relabelTags_le_relabelTags {G H : Graph α β} (g : β ≃ δ) :
    G.relabelTags g ≤ H.relabelTags g ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨h.vertexSet_subset, fun e he => ?_⟩
    have hm := h.edgeSet_subset ((G.relabelTags_edge_mem g e).2 he)
    exact (H.relabelTags_edge_mem g e).1 hm
  · refine ⟨h.vertexSet_subset, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, h.edgeSet_subset he, rfl⟩

@[simp] theorem relabelTags_id (G : Graph α β) : G.relabelTags (Equiv.refl β) = G := by
  ext <;> simp [Graph.relabelTags]

@[simp] theorem relabelTags_comp (G : Graph α β) (f : β ≃ γ) (g : γ ≃ δ) :
    (G.relabelTags f).relabelTags g = G.relabelTags (f.trans g) := by
  apply Graph.ext
  · rfl
  · simp only [edgeSet_relabelTags, Set.image_image]
    apply congrArg (fun h => h '' E(G))
    funext e
    exact Edge.relabelTags_trans f g e

@[simp] theorem relabelTags_inverse (G : Graph α β) (g : β ≃ δ) :
    (G.relabelTags g).relabelTags g.symm = G := by simp

end Graph

namespace DiGraph

@[simp] theorem vertexSet_relabelVertices (G : DiGraph α β) (f : α ≃ γ) :
    V(G.relabelVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_relabelVertices (G : DiGraph α β) (f : α ≃ γ) :
    E(G.relabelVertices f) = Arc.relabelVertices f '' E(G) := rfl

@[simp] theorem relabelVertices_edge_mem (G : DiGraph α β) (f : α ≃ γ) (a : Arc α β) :
    Arc.relabelVertices f a ∈ E(G.relabelVertices f) ↔ a ∈ E(G) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact (Arc.relabelVertices f).injective h |>.symm ▸ hb
  · exact fun h => ⟨a, h, rfl⟩

@[simp] theorem relabelVertices_isArc (G : DiGraph α β) (f : α ≃ γ)
    (a : Arc α β) (u v : α) :
    (G.relabelVertices f).IsArc (Arc.relabelVertices f a) (f u) (f v) ↔
      G.IsArc a u v := by
  simp [DiGraph.IsArc, f.injective.eq_iff]

@[simp] theorem relabelVertices_adj (G : DiGraph α β) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Adj (f u) (f v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a', ha'⟩
    obtain ⟨a, ha, rfl⟩ := ha'.edge_mem
    exact ⟨a, (G.relabelVertices_isArc f a u v).1 ha'⟩
  · rintro ⟨a, ha⟩
    exact ⟨Arc.relabelVertices f a, (G.relabelVertices_isArc f a u v).2 ha⟩

@[simp] theorem relabelVertices_inc (G : DiGraph α β) (f : α ≃ γ)
    (a : Arc α β) (v : α) :
    (G.relabelVertices f).Inc (Arc.relabelVertices f a) (f v) ↔ G.Inc a v := by
  simp [DiGraph.Inc, f.injective.eq_iff]

theorem relabelVertices_le_relabelVertices {G H : DiGraph α β} (f : α ≃ γ) :
    G.relabelVertices f ≤ H.relabelVertices f ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨fun v hv => ?_, fun a ha => ?_⟩
    · have hm := h.vertexSet_subset (show f v ∈ V(G.relabelVertices f) from ⟨v, hv, rfl⟩)
      obtain ⟨w, hw, heq⟩ := hm
      exact f.injective heq ▸ hw
    · have hm := h.edgeSet_subset ((G.relabelVertices_edge_mem f a).2 ha)
      exact (H.relabelVertices_edge_mem f a).1 hm
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, h.vertexSet_subset hv, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, h.edgeSet_subset ha, rfl⟩

@[simp] theorem relabelVertices_id (G : DiGraph α β) :
    G.relabelVertices (Equiv.refl α) = G := by ext <;> simp [DiGraph.relabelVertices]

@[simp] theorem relabelVertices_comp (G : DiGraph α β) (f : α ≃ γ) (g : γ ≃ δ) :
    (G.relabelVertices f).relabelVertices g = G.relabelVertices (f.trans g) := by
  apply DiGraph.ext
  · simp only [vertexSet_relabelVertices, Set.image_image]
    rfl
  · simp only [edgeSet_relabelVertices, Set.image_image]
    apply congrArg (fun h => h '' E(G))
    funext a
    exact Arc.relabelVertices_trans f g a

@[simp] theorem relabelVertices_inverse (G : DiGraph α β) (f : α ≃ γ) :
    (G.relabelVertices f).relabelVertices f.symm = G := by simp

@[simp] theorem vertexSet_relabelTags (G : DiGraph α β) (g : β ≃ δ) :
    V(G.relabelTags g) = V(G) := rfl

@[simp] theorem edgeSet_relabelTags (G : DiGraph α β) (g : β ≃ δ) :
    E(G.relabelTags g) = Arc.relabelTags g '' E(G) := rfl

@[simp] theorem relabelTags_edge_mem (G : DiGraph α β) (g : β ≃ δ) (a : Arc α β) :
    Arc.relabelTags g a ∈ E(G.relabelTags g) ↔ a ∈ E(G) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact (Arc.relabelTags g).injective h |>.symm ▸ hb
  · exact fun h => ⟨a, h, rfl⟩

@[simp] theorem relabelTags_isArc (G : DiGraph α β) (g : β ≃ δ)
    (a : Arc α β) (u v : α) :
    (G.relabelTags g).IsArc (Arc.relabelTags g a) u v ↔ G.IsArc a u v := by
  simp [DiGraph.IsArc]

@[simp] theorem relabelTags_adj (G : DiGraph α β) (g : β ≃ δ) (u v : α) :
    (G.relabelTags g).Adj u v ↔ G.Adj u v := by
  constructor
  · rintro ⟨a', ha'⟩
    obtain ⟨a, ha, rfl⟩ := ha'.edge_mem
    exact ⟨a, (G.relabelTags_isArc g a u v).1 ha'⟩
  · rintro ⟨a, ha⟩
    exact ⟨Arc.relabelTags g a, (G.relabelTags_isArc g a u v).2 ha⟩

@[simp] theorem relabelTags_inc (G : DiGraph α β) (g : β ≃ δ)
    (a : Arc α β) (v : α) :
    (G.relabelTags g).Inc (Arc.relabelTags g a) v ↔ G.Inc a v := by
  simp [DiGraph.Inc]

theorem relabelTags_le_relabelTags {G H : DiGraph α β} (g : β ≃ δ) :
    G.relabelTags g ≤ H.relabelTags g ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨h.vertexSet_subset, fun a ha => ?_⟩
    have hm := h.edgeSet_subset ((G.relabelTags_edge_mem g a).2 ha)
    exact (H.relabelTags_edge_mem g a).1 hm
  · refine ⟨h.vertexSet_subset, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, h.edgeSet_subset ha, rfl⟩

@[simp] theorem relabelTags_id (G : DiGraph α β) : G.relabelTags (Equiv.refl β) = G := by
  ext <;> simp [DiGraph.relabelTags]

@[simp] theorem relabelTags_comp (G : DiGraph α β) (f : β ≃ γ) (g : γ ≃ δ) :
    (G.relabelTags f).relabelTags g = G.relabelTags (f.trans g) := by
  apply DiGraph.ext
  · rfl
  · simp only [edgeSet_relabelTags, Set.image_image]
    apply congrArg (fun h => h '' E(G))
    funext a
    exact Arc.relabelTags_trans f g a

@[simp] theorem relabelTags_inverse (G : DiGraph α β) (g : β ≃ δ) :
    (G.relabelTags g).relabelTags g.symm = G := by simp

end DiGraph

namespace SimpleGraph

@[simp] theorem vertexSet_relabelVertices (G : SimpleGraph α) (f : α ≃ γ) :
    V(G.relabelVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_relabelVertices (G : SimpleGraph α) (f : α ≃ γ) :
    E(G.relabelVertices f) = Sym2.map f '' E(G) := rfl

@[simp] theorem relabelVertices_edge_mem (G : SimpleGraph α) (f : α ≃ γ) (e : Sym2 α) :
    Sym2.map f e ∈ E(G.relabelVertices f) ↔ e ∈ E(G) := by
  constructor
  · rintro ⟨d, hd, h⟩
    exact Sym2.map.injective f.injective h |>.symm ▸ hd
  · exact fun h => ⟨e, h, rfl⟩

@[simp] theorem relabelVertices_isLink (G : SimpleGraph α) (f : α ≃ γ)
    (e : Sym2 α) (u v : α) :
    (G.relabelVertices f).IsLink (Sym2.map f e) (f u) (f v) ↔ G.IsLink e u v := by
  simp only [SimpleGraph.IsLink, SimpleGraph.relabelVertices]
  constructor
  · rintro ⟨⟨d, hd, hde⟩, he⟩
    have hde' : d = e := Sym2.map.injective f.injective hde
    subst d
    refine ⟨hd, Sym2.map.injective f.injective ?_⟩
    simpa using he
  · rintro ⟨he, hends⟩
    exact ⟨⟨e, he, rfl⟩, by simpa using congrArg (Sym2.map f) hends⟩

@[simp] theorem relabelVertices_adj (G : SimpleGraph α) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Adj (f u) (f v) ↔ G.Adj u v := by
  simp only [SimpleGraph.adj_iff, SimpleGraph.relabelVertices]
  constructor
  · rintro ⟨e, he, hmap⟩
    have heq : e = s(u, v) := Sym2.map.injective f.injective (by simpa using hmap)
    simpa [heq] using he
  · intro h
    exact ⟨s(u, v), h, by simp⟩

@[simp] theorem relabelVertices_inc (G : SimpleGraph α) (f : α ≃ γ)
    (e : Sym2 α) (v : α) :
    (G.relabelVertices f).Inc (Sym2.map f e) (f v) ↔ G.Inc e v := by
  simp only [SimpleGraph.Inc, relabelVertices_edge_mem, Sym2.mem_map]
  constructor
  · rintro ⟨he, u, hu, huv⟩
    exact ⟨he, f.injective huv ▸ hu⟩
  · rintro ⟨he, hv⟩
    exact ⟨he, v, hv, rfl⟩

theorem relabelVertices_le_relabelVertices {G H : SimpleGraph α} (f : α ≃ γ) :
    G.relabelVertices f ≤ H.relabelVertices f ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨fun v hv => ?_, fun e he => ?_⟩
    · have hm := h.vertexSet_subset (show f v ∈ V(G.relabelVertices f) from ⟨v, hv, rfl⟩)
      obtain ⟨w, hw, heq⟩ := hm
      exact f.injective heq ▸ hw
    · have hm := h.edgeSet_subset ((G.relabelVertices_edge_mem f e).2 he)
      exact (H.relabelVertices_edge_mem f e).1 hm
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, h.vertexSet_subset hv, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨e, h.edgeSet_subset he, rfl⟩

@[simp] theorem relabelVertices_id (G : SimpleGraph α) :
    G.relabelVertices (Equiv.refl α) = G := by ext <;> simp [SimpleGraph.relabelVertices]

@[simp] theorem relabelVertices_comp (G : SimpleGraph α) (f : α ≃ γ) (g : γ ≃ δ) :
    (G.relabelVertices f).relabelVertices g = G.relabelVertices (f.trans g) := by
  apply SimpleGraph.ext
  · change g '' (f '' V(G)) = (f.trans g) '' V(G)
    rw [Set.image_image]
    rfl
  · change Sym2.map g '' (Sym2.map f '' E(G)) = Sym2.map (f.trans g) '' E(G)
    rw [Set.image_image]
    apply congrArg (fun h => h '' E(G))
    funext e
    exact Sym2.map_map e

@[simp] theorem relabelVertices_inverse (G : SimpleGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).relabelVertices f.symm = G := by simp

end SimpleGraph

namespace SimpleDiGraph

@[simp] theorem vertexSet_relabelVertices (G : SimpleDiGraph α) (f : α ≃ γ) :
    V(G.relabelVertices f) = f '' V(G) := rfl

@[simp] theorem edgeSet_relabelVertices (G : SimpleDiGraph α) (f : α ≃ γ) :
    E(G.relabelVertices f) = (fun a => (f a.1, f a.2)) '' E(G) := rfl

@[simp] theorem relabelVertices_edge_mem (G : SimpleDiGraph α) (f : α ≃ γ) (a : α × α) :
    (f a.1, f a.2) ∈ E(G.relabelVertices f) ↔ a ∈ E(G) := by
  constructor
  · rintro ⟨b, hb, h⟩
    have hba : b = a := Prod.ext
      (f.injective (congrArg Prod.fst h))
      (f.injective (congrArg Prod.snd h))
    exact hba ▸ hb
  · exact fun h => ⟨a, h, rfl⟩

@[simp] theorem relabelVertices_isArc (G : SimpleDiGraph α) (f : α ≃ γ)
    (a : α × α) (u v : α) :
    (G.relabelVertices f).IsArc (f a.1, f a.2) (f u) (f v) ↔ G.IsArc a u v := by
  simp only [SimpleDiGraph.IsArc, SimpleDiGraph.relabelVertices]
  constructor
  · rintro ⟨⟨b, hb, hba⟩, hs, ht⟩
    have hb1 : b.1 = a.1 := f.injective (congrArg Prod.fst hba)
    have hb2 : b.2 = a.2 := f.injective (congrArg Prod.snd hba)
    have hba' : b = a := Prod.ext hb1 hb2
    subst b
    exact ⟨hb, f.injective hs, f.injective ht⟩
  · rintro ⟨ha, hs, ht⟩
    exact ⟨⟨a, ha, rfl⟩, congrArg f hs, congrArg f ht⟩

@[simp] theorem relabelVertices_adj (G : SimpleDiGraph α) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Adj (f u) (f v) ↔ G.Adj u v := by
  simp [SimpleDiGraph.adj_iff, SimpleDiGraph.relabelVertices, Set.mem_image,
    f.injective.eq_iff]

@[simp] theorem relabelVertices_inc (G : SimpleDiGraph α) (f : α ≃ γ)
    (a : α × α) (v : α) :
    (G.relabelVertices f).Inc (f a.1, f a.2) (f v) ↔ G.Inc a v := by
  simp [SimpleDiGraph.Inc, f.injective.eq_iff]

theorem relabelVertices_le_relabelVertices {G H : SimpleDiGraph α} (f : α ≃ γ) :
    G.relabelVertices f ≤ H.relabelVertices f ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨fun v hv => ?_, fun a ha => ?_⟩
    · have hm := h.vertexSet_subset (show f v ∈ V(G.relabelVertices f) from ⟨v, hv, rfl⟩)
      obtain ⟨w, hw, heq⟩ := hm
      exact f.injective heq ▸ hw
    · have hm := h.edgeSet_subset ((G.relabelVertices_edge_mem f a).2 ha)
      exact (H.relabelVertices_edge_mem f a).1 hm
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, h.vertexSet_subset hv, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, h.edgeSet_subset ha, rfl⟩

@[simp] theorem relabelVertices_id (G : SimpleDiGraph α) :
    G.relabelVertices (Equiv.refl α) = G := by ext <;> simp [SimpleDiGraph.relabelVertices]

@[simp] theorem relabelVertices_comp (G : SimpleDiGraph α) (f : α ≃ γ) (g : γ ≃ δ) :
    (G.relabelVertices f).relabelVertices g = G.relabelVertices (f.trans g) := by
  apply SimpleDiGraph.ext
  · change g '' (f '' V(G)) = (f.trans g) '' V(G)
    rw [Set.image_image]
    rfl
  · change (fun a => (g a.1, g a.2)) ''
        ((fun a => (f a.1, f a.2)) '' E(G)) =
        (fun a => ((f.trans g) a.1, (f.trans g) a.2)) '' E(G)
    rw [Set.image_image]
    rfl

@[simp] theorem relabelVertices_inverse (G : SimpleDiGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).relabelVertices f.symm = G := by simp

end SimpleDiGraph

/-! ## Relabeling and same-carrier transformations -/

namespace Graph

@[simp] theorem relabelVertices_induce (G : Graph α β) (f : α ≃ γ) (S : Set α) :
    (G.induce S).relabelVertices f = (G.relabelVertices f).induce (f '' S) := by
  apply Graph.ext
  · ext x
    simp [Graph.relabelVertices]
  · ext e'
    let e := (Edge.relabelVertices f).symm e'
    have heq : Edge.relabelVertices f e = e' := (Edge.relabelVertices f).apply_symm_apply e'
    rw [← heq]
    simp only [relabelVertices_edge_mem, mem_edgeSet_induce,
      Edge.endpoints_relabelVertices]
    constructor
    · rintro ⟨he, hS⟩
      refine ⟨he, fun x hx => ?_⟩
      obtain ⟨v, hv, rfl⟩ := Sym2.mem_map.mp hx
      exact ⟨v, hS v hv, rfl⟩
    · rintro ⟨he, hS⟩
      refine ⟨he, fun v hv => ?_⟩
      obtain ⟨w, hw, hwv⟩ := hS (f v) (Sym2.mem_map.mpr ⟨v, hv, rfl⟩)
      exact f.injective hwv ▸ hw

@[simp] theorem relabelVertices_restrictEdges (G : Graph α β) (f : α ≃ γ)
    (F : Set (Edge α β)) :
    (G.restrictEdges F).relabelVertices f =
      (G.relabelVertices f).restrictEdges (Edge.relabelVertices f '' F) := by
  apply Graph.ext
  · rfl
  · change Edge.relabelVertices f '' (E(G) ∩ F) =
      (Edge.relabelVertices f '' E(G)) ∩ (Edge.relabelVertices f '' F)
    exact Set.image_inter (Edge.relabelVertices f).injective

@[simp] theorem relabelVertices_deleteEdges (G : Graph α β) (f : α ≃ γ)
    (F : Set (Edge α β)) :
    (G.deleteEdges F).relabelVertices f =
      (G.relabelVertices f).deleteEdges (Edge.relabelVertices f '' F) := by
  apply Graph.ext
  · rfl
  · change Edge.relabelVertices f '' (E(G) \ F) =
      (Edge.relabelVertices f '' E(G)) \ (Edge.relabelVertices f '' F)
    exact Set.image_diff (Edge.relabelVertices f).injective E(G) F

@[simp] theorem relabelVertices_deleteEdge (G : Graph α β) (f : α ≃ γ) (e : Edge α β) :
    (G.deleteEdge e).relabelVertices f =
      (G.relabelVertices f).deleteEdge (Edge.relabelVertices f e) := by
  simp [deleteEdge]

@[simp] theorem relabelVertices_deleteVerts (G : Graph α β) (f : α ≃ γ) (S : Set α) :
    (G.deleteVerts S).relabelVertices f = (G.relabelVertices f).deleteVerts (f '' S) := by
  change (G.induce Sᶜ).relabelVertices f = (G.relabelVertices f).induce (f '' S)ᶜ
  rw [relabelVertices_induce]
  congr 1
  ext x
  simp

@[simp] theorem relabelVertices_deleteVert (G : Graph α β) (f : α ≃ γ) (v : α) :
    (G.deleteVert v).relabelVertices f = (G.relabelVertices f).deleteVert (f v) := by
  simp [deleteVert]

@[simp] theorem relabelTags_induce (G : Graph α β) (g : β ≃ δ) (S : Set α) :
    (G.induce S).relabelTags g = (G.relabelTags g).induce S := by
  apply Graph.ext
  · rfl
  · ext e'
    let e := (Edge.relabelTags g).symm e'
    have heq : Edge.relabelTags g e = e' := (Edge.relabelTags g).apply_symm_apply e'
    rw [← heq]
    simp only [relabelTags_edge_mem, mem_edgeSet_induce, Edge.endpoints_relabelTags]

@[simp] theorem relabelTags_restrictEdges (G : Graph α β) (g : β ≃ δ)
    (F : Set (Edge α β)) :
    (G.restrictEdges F).relabelTags g =
      (G.relabelTags g).restrictEdges (Edge.relabelTags g '' F) := by
  apply Graph.ext
  · rfl
  · change Edge.relabelTags g '' (E(G) ∩ F) =
      (Edge.relabelTags g '' E(G)) ∩ (Edge.relabelTags g '' F)
    exact Set.image_inter (Edge.relabelTags g).injective

@[simp] theorem relabelTags_deleteEdges (G : Graph α β) (g : β ≃ δ)
    (F : Set (Edge α β)) :
    (G.deleteEdges F).relabelTags g =
      (G.relabelTags g).deleteEdges (Edge.relabelTags g '' F) := by
  apply Graph.ext
  · rfl
  · change Edge.relabelTags g '' (E(G) \ F) =
      (Edge.relabelTags g '' E(G)) \ (Edge.relabelTags g '' F)
    exact Set.image_diff (Edge.relabelTags g).injective E(G) F

@[simp] theorem relabelTags_deleteEdge (G : Graph α β) (g : β ≃ δ) (e : Edge α β) :
    (G.deleteEdge e).relabelTags g =
      (G.relabelTags g).deleteEdge (Edge.relabelTags g e) := by
  simp [deleteEdge]

@[simp] theorem relabelTags_deleteVerts (G : Graph α β) (g : β ≃ δ) (S : Set α) :
    (G.deleteVerts S).relabelTags g = (G.relabelTags g).deleteVerts S := by
  simp [deleteVerts]

end Graph

namespace DiGraph

@[simp] theorem relabelVertices_induce (G : DiGraph α β) (f : α ≃ γ) (S : Set α) :
    (G.induce S).relabelVertices f = (G.relabelVertices f).induce (f '' S) := by
  apply DiGraph.ext
  · ext x
    simp [DiGraph.relabelVertices]
  · ext a'
    let a := (Arc.relabelVertices f).symm a'
    have ha : Arc.relabelVertices f a = a' := (Arc.relabelVertices f).apply_symm_apply a'
    rw [← ha]
    simp only [relabelVertices_edge_mem, mem_edgeSet_induce,
      Arc.source_relabelVertices, Arc.target_relabelVertices]
    constructor
    · rintro ⟨haG, hs, ht⟩
      exact ⟨haG, ⟨a.source, hs, rfl⟩, a.target, ht, rfl⟩
    · rintro ⟨haG, ⟨u, hu, hsu⟩, v, hv, htv⟩
      exact ⟨haG, f.injective hsu ▸ hu, f.injective htv ▸ hv⟩

@[simp] theorem relabelVertices_restrictEdges (G : DiGraph α β) (f : α ≃ γ)
    (F : Set (Arc α β)) :
    (G.restrictEdges F).relabelVertices f =
      (G.relabelVertices f).restrictEdges (Arc.relabelVertices f '' F) := by
  apply DiGraph.ext
  · rfl
  · change Arc.relabelVertices f '' (E(G) ∩ F) =
      (Arc.relabelVertices f '' E(G)) ∩ (Arc.relabelVertices f '' F)
    exact Set.image_inter (Arc.relabelVertices f).injective

@[simp] theorem relabelVertices_deleteEdges (G : DiGraph α β) (f : α ≃ γ)
    (F : Set (Arc α β)) :
    (G.deleteEdges F).relabelVertices f =
      (G.relabelVertices f).deleteEdges (Arc.relabelVertices f '' F) := by
  apply DiGraph.ext
  · rfl
  · change Arc.relabelVertices f '' (E(G) \ F) =
      (Arc.relabelVertices f '' E(G)) \ (Arc.relabelVertices f '' F)
    exact Set.image_diff (Arc.relabelVertices f).injective E(G) F

@[simp] theorem relabelVertices_deleteEdge (G : DiGraph α β) (f : α ≃ γ) (a : Arc α β) :
    (G.deleteEdge a).relabelVertices f =
      (G.relabelVertices f).deleteEdge (Arc.relabelVertices f a) := by
  simp [deleteEdge]

@[simp] theorem relabelVertices_deleteVerts (G : DiGraph α β) (f : α ≃ γ) (S : Set α) :
    (G.deleteVerts S).relabelVertices f = (G.relabelVertices f).deleteVerts (f '' S) := by
  change (G.induce Sᶜ).relabelVertices f = (G.relabelVertices f).induce (f '' S)ᶜ
  rw [relabelVertices_induce]
  congr 1
  ext x
  simp

@[simp] theorem relabelVertices_deleteVert (G : DiGraph α β) (f : α ≃ γ) (v : α) :
    (G.deleteVert v).relabelVertices f = (G.relabelVertices f).deleteVert (f v) := by
  simp [deleteVert]

@[simp] theorem relabelTags_induce (G : DiGraph α β) (g : β ≃ δ) (S : Set α) :
    (G.induce S).relabelTags g = (G.relabelTags g).induce S := by
  apply DiGraph.ext
  · rfl
  · ext a'
    let a := (Arc.relabelTags g).symm a'
    have ha : Arc.relabelTags g a = a' := (Arc.relabelTags g).apply_symm_apply a'
    rw [← ha]
    simp only [relabelTags_edge_mem, mem_edgeSet_induce,
      Arc.source_relabelTags, Arc.target_relabelTags]

@[simp] theorem relabelTags_restrictEdges (G : DiGraph α β) (g : β ≃ δ)
    (F : Set (Arc α β)) :
    (G.restrictEdges F).relabelTags g =
      (G.relabelTags g).restrictEdges (Arc.relabelTags g '' F) := by
  apply DiGraph.ext
  · rfl
  · change Arc.relabelTags g '' (E(G) ∩ F) =
      (Arc.relabelTags g '' E(G)) ∩ (Arc.relabelTags g '' F)
    exact Set.image_inter (Arc.relabelTags g).injective

@[simp] theorem relabelTags_deleteEdges (G : DiGraph α β) (g : β ≃ δ)
    (F : Set (Arc α β)) :
    (G.deleteEdges F).relabelTags g =
      (G.relabelTags g).deleteEdges (Arc.relabelTags g '' F) := by
  apply DiGraph.ext
  · rfl
  · change Arc.relabelTags g '' (E(G) \ F) =
      (Arc.relabelTags g '' E(G)) \ (Arc.relabelTags g '' F)
    exact Set.image_diff (Arc.relabelTags g).injective E(G) F

@[simp] theorem relabelTags_deleteEdge (G : DiGraph α β) (g : β ≃ δ) (a : Arc α β) :
    (G.deleteEdge a).relabelTags g =
      (G.relabelTags g).deleteEdge (Arc.relabelTags g a) := by
  simp [deleteEdge]

@[simp] theorem relabelTags_deleteVerts (G : DiGraph α β) (g : β ≃ δ) (S : Set α) :
    (G.deleteVerts S).relabelTags g = (G.relabelTags g).deleteVerts S := by
  simp [deleteVerts]

end DiGraph

namespace SimpleGraph

@[simp] theorem relabelVertices_induce (G : SimpleGraph α) (f : α ≃ γ) (S : Set α) :
    (G.induce S).relabelVertices f = (G.relabelVertices f).induce (f '' S) := by
  apply SimpleGraph.ext
  · ext x
    simp [SimpleGraph.relabelVertices]
  · ext e'
    let e := Sym2.map f.symm e'
    have heq : Sym2.map f e = e' := by simp [e, Sym2.map_map]
    rw [← heq]
    simp only [relabelVertices_edge_mem, mem_edgeSet_induce]
    constructor
    · rintro ⟨he, hS⟩
      refine ⟨he, fun x hx => ?_⟩
      obtain ⟨v, hv, rfl⟩ := Sym2.mem_map.mp hx
      exact ⟨v, hS v hv, rfl⟩
    · rintro ⟨he, hS⟩
      refine ⟨he, fun v hv => ?_⟩
      obtain ⟨w, hw, hwv⟩ := hS (f v) (Sym2.mem_map.mpr ⟨v, hv, rfl⟩)
      exact f.injective hwv ▸ hw

@[simp] theorem relabelVertices_restrictEdges (G : SimpleGraph α) (f : α ≃ γ)
    (F : Set (Sym2 α)) :
    (G.restrictEdges F).relabelVertices f =
      (G.relabelVertices f).restrictEdges (Sym2.map f '' F) := by
  apply SimpleGraph.ext
  · rfl
  · change Sym2.map f '' (E(G) ∩ F) = (Sym2.map f '' E(G)) ∩ (Sym2.map f '' F)
    exact Set.image_inter (Sym2.map.injective f.injective)

@[simp] theorem relabelVertices_deleteEdges (G : SimpleGraph α) (f : α ≃ γ)
    (F : Set (Sym2 α)) :
    (G.deleteEdges F).relabelVertices f =
      (G.relabelVertices f).deleteEdges (Sym2.map f '' F) := by
  apply SimpleGraph.ext
  · rfl
  · change Sym2.map f '' (E(G) \ F) = (Sym2.map f '' E(G)) \ (Sym2.map f '' F)
    exact Set.image_diff (Sym2.map.injective f.injective) E(G) F

@[simp] theorem relabelVertices_deleteEdge (G : SimpleGraph α) (f : α ≃ γ) (e : Sym2 α) :
    (G.deleteEdge e).relabelVertices f =
      (G.relabelVertices f).deleteEdge (Sym2.map f e) := by
  simp [deleteEdge]

@[simp] theorem relabelVertices_deleteVerts (G : SimpleGraph α) (f : α ≃ γ) (S : Set α) :
    (G.deleteVerts S).relabelVertices f = (G.relabelVertices f).deleteVerts (f '' S) := by
  change (G.induce Sᶜ).relabelVertices f = (G.relabelVertices f).induce (f '' S)ᶜ
  rw [relabelVertices_induce]
  congr 1
  ext x
  simp

@[simp] theorem relabelVertices_deleteVert (G : SimpleGraph α) (f : α ≃ γ) (v : α) :
    (G.deleteVert v).relabelVertices f = (G.relabelVertices f).deleteVert (f v) := by
  simp [deleteVert]

end SimpleGraph

namespace SimpleDiGraph

private theorem pairMap_injective (f : α ≃ γ) :
    Function.Injective (fun a : α × α => (f a.1, f a.2)) := by
  intro a b h
  exact Prod.ext (f.injective (congrArg Prod.fst h))
    (f.injective (congrArg Prod.snd h))

@[simp] theorem relabelVertices_induce (G : SimpleDiGraph α) (f : α ≃ γ) (S : Set α) :
    (G.induce S).relabelVertices f = (G.relabelVertices f).induce (f '' S) := by
  apply SimpleDiGraph.ext
  · ext x
    simp [SimpleDiGraph.relabelVertices]
  · ext a'
    let a := (f.symm a'.1, f.symm a'.2)
    have ha : (f a.1, f a.2) = a' := by ext <;> simp [a]
    rw [← ha]
    simp only [relabelVertices_edge_mem, mem_edgeSet_induce]
    constructor
    · rintro ⟨haG, hs, ht⟩
      exact ⟨haG, ⟨a.1, hs, rfl⟩, a.2, ht, rfl⟩
    · rintro ⟨haG, ⟨u, hu, hsu⟩, v, hv, htv⟩
      exact ⟨haG, f.injective hsu ▸ hu, f.injective htv ▸ hv⟩

@[simp] theorem relabelVertices_restrictEdges (G : SimpleDiGraph α) (f : α ≃ γ)
    (F : Set (α × α)) :
    (G.restrictEdges F).relabelVertices f =
      (G.relabelVertices f).restrictEdges ((fun a => (f a.1, f a.2)) '' F) := by
  apply SimpleDiGraph.ext
  · rfl
  · change (fun a => (f a.1, f a.2)) '' (E(G) ∩ F) =
      ((fun a => (f a.1, f a.2)) '' E(G)) ∩ ((fun a => (f a.1, f a.2)) '' F)
    exact Set.image_inter (pairMap_injective f)

@[simp] theorem relabelVertices_deleteEdges (G : SimpleDiGraph α) (f : α ≃ γ)
    (F : Set (α × α)) :
    (G.deleteEdges F).relabelVertices f =
      (G.relabelVertices f).deleteEdges ((fun a => (f a.1, f a.2)) '' F) := by
  apply SimpleDiGraph.ext
  · rfl
  · change (fun a => (f a.1, f a.2)) '' (E(G) \ F) =
      ((fun a => (f a.1, f a.2)) '' E(G)) \ ((fun a => (f a.1, f a.2)) '' F)
    exact Set.image_diff (pairMap_injective f) E(G) F

@[simp] theorem relabelVertices_deleteEdge (G : SimpleDiGraph α) (f : α ≃ γ)
    (a : α × α) :
    (G.deleteEdge a).relabelVertices f =
      (G.relabelVertices f).deleteEdge (f a.1, f a.2) := by
  simp [deleteEdge]

@[simp] theorem relabelVertices_deleteVerts (G : SimpleDiGraph α) (f : α ≃ γ)
    (S : Set α) :
    (G.deleteVerts S).relabelVertices f = (G.relabelVertices f).deleteVerts (f '' S) := by
  change (G.induce Sᶜ).relabelVertices f = (G.relabelVertices f).induce (f '' S)ᶜ
  rw [relabelVertices_induce]
  congr 1
  ext x
  simp

@[simp] theorem relabelVertices_deleteVert (G : SimpleDiGraph α) (f : α ≃ γ) (v : α) :
    (G.deleteVert v).relabelVertices f = (G.relabelVertices f).deleteVert (f v) := by
  simp [deleteVert]

end SimpleDiGraph

/-! ## Explicit conversions -/

/-- Forget loops and parallel-edge identity, retaining only distinct endpoint pairs. -/
def Graph.underlyingSimple (G : Graph α β) : SimpleGraph α where
  vertexSet := V(G)
  edgeSet := G.edgeEndpointPairSet ∩ {e | ¬ e.IsDiag}
  endpoints_mem := by
    rintro p ⟨⟨e, he, rfl⟩, _⟩ v hv
    exact G.endpoints_mem e he v hv
  loopless := by rintro _ ⟨_, h⟩; exact h

/-- Forget loops and parallel-arc identity, retaining only distinct ordered endpoint pairs. -/
def DiGraph.underlyingSimple (G : DiGraph α β) : SimpleDiGraph α where
  vertexSet := V(G)
  edgeSet := G.arcEndpointPairSet ∩ {a | a.1 ≠ a.2}
  source_mem := by
    rintro _ ⟨⟨a, ha, rfl⟩, _⟩
    exact G.source_mem a ha
  target_mem := by
    rintro _ ⟨⟨a, ha, rfl⟩, _⟩
    exact G.target_mem a ha
  loopless := by rintro _ ⟨_, h⟩; exact h

/-- Forget the orientation of a general directed graph. The complete source arc becomes the tag
of its undirected image, so antiparallel and parallel actual arcs remain distinct. -/
def DiGraph.forgetDirection (G : DiGraph α β) : Graph α (Arc α β) where
  vertexSet := V(G)
  edgeSet := (fun a => Edge.mk a s(a.source, a.target)) '' E(G)
  endpoints_mem := by
    rintro _ ⟨a, ha, rfl⟩ v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact G.source_mem a ha
    · exact G.target_mem a ha

/-- Forget the orientation of a simple directed graph. Antiparallel arcs map to the same
undirected edge and are therefore merged. -/
def SimpleDiGraph.forgetDirection (G : SimpleDiGraph α) : SimpleGraph α where
  vertexSet := V(G)
  edgeSet := (fun a => s(a.1, a.2)) '' E(G)
  endpoints_mem := by
    rintro _ ⟨a, ha, rfl⟩ v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact G.source_mem a ha
    · exact G.target_mem a ha
  loopless := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using G.loopless a ha

namespace Graph

@[simp] theorem vertexSet_underlyingSimple (G : Graph α β) : V(G.underlyingSimple) = V(G) := rfl

@[simp] theorem edgeSet_underlyingSimple (G : Graph α β) :
    E(G.underlyingSimple) = G.edgeEndpointPairSet ∩ {e | ¬ e.IsDiag} := rfl

@[simp] theorem mem_edgeSet_underlyingSimple (G : Graph α β) (p : Sym2 α) :
    p ∈ E(G.underlyingSimple) ↔ p ∈ G.edgeEndpointPairSet ∧ ¬ p.IsDiag := Iff.rfl

@[simp] theorem underlyingSimple_adj (G : Graph α β) (u v : α) :
    G.underlyingSimple.Adj u v ↔ G.Adj u v ∧ u ≠ v := by
  simp only [SimpleGraph.adj_iff, mem_edgeSet_underlyingSimple,
    mem_edgeEndpointPairSet, Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨⟨e, he, hends⟩, hne⟩
    exact ⟨⟨e, he, hends⟩, hne⟩
  · rintro ⟨⟨e, he, hends⟩, hne⟩
    exact ⟨⟨e, he, hends⟩, hne⟩

end Graph

namespace DiGraph

@[simp] theorem vertexSet_underlyingSimple (G : DiGraph α β) :
    V(G.underlyingSimple) = V(G) := rfl

@[simp] theorem edgeSet_underlyingSimple (G : DiGraph α β) :
    E(G.underlyingSimple) = G.arcEndpointPairSet ∩ {a | a.1 ≠ a.2} := rfl

@[simp] theorem mem_edgeSet_underlyingSimple (G : DiGraph α β) (p : α × α) :
    p ∈ E(G.underlyingSimple) ↔ p ∈ G.arcEndpointPairSet ∧ p.1 ≠ p.2 := Iff.rfl

@[simp] theorem underlyingSimple_adj (G : DiGraph α β) (u v : α) :
    G.underlyingSimple.Adj u v ↔ G.Adj u v ∧ u ≠ v := by
  simp only [SimpleDiGraph.adj_iff, mem_edgeSet_underlyingSimple,
    mem_arcEndpointPairSet]
  constructor
  · rintro ⟨⟨a, ha, hends⟩, hne⟩
    rcases a with ⟨tag, ⟨x, y⟩⟩
    cases hends
    exact ⟨⟨_, ha, rfl, rfl⟩, hne⟩
  · rintro ⟨⟨a, ha, hs, ht⟩, hne⟩
    exact ⟨⟨a, ha, by ext <;> assumption⟩, hne⟩

@[simp] theorem vertexSet_forgetDirection (G : DiGraph α β) :
    V(G.forgetDirection) = V(G) := rfl

@[simp] theorem edgeSet_forgetDirection (G : DiGraph α β) :
    E(G.forgetDirection) = (fun a => Edge.mk a s(a.source, a.target)) '' E(G) := rfl

@[simp] theorem forgetDirection_edge_mem (G : DiGraph α β) (a : Arc α β) :
    Edge.mk a s(a.source, a.target) ∈ E(G.forgetDirection) ↔ a ∈ E(G) := by
  constructor
  · rintro ⟨b, hb, h⟩
    have hba : b = a := congrArg Edge.tag h
    simpa [hba] using hb
  · exact fun h => ⟨a, h, rfl⟩

@[simp] theorem forgetDirection_isLink (G : DiGraph α β) (a : Arc α β) (u v : α) :
    G.forgetDirection.IsLink (Edge.mk a s(a.source, a.target)) u v ↔
      G.IsArc a u v ∨ G.IsArc a v u := by
  simp only [Graph.IsLink, forgetDirection_edge_mem, DiGraph.IsArc]
  rw [Sym2.eq, Sym2.rel_iff']
  simp only [Prod.mk.injEq, Prod.swap_prod_mk]
  tauto

@[simp] theorem forgetDirection_adj (G : DiGraph α β) (u v : α) :
    G.forgetDirection.Adj u v ↔ G.Adj u v ∨ G.Adj v u := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨a, ha, rfl⟩ := he.edge_mem
    rcases (G.forgetDirection_isLink a u v).1 he with h | h
    · exact Or.inl h.adj
    · exact Or.inr h.adj
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨_, (G.forgetDirection_isLink a u v).2 (Or.inl ha)⟩
    · exact ⟨_, (G.forgetDirection_isLink a u v).2 (Or.inr ha)⟩

end DiGraph

namespace SimpleDiGraph

@[simp] theorem vertexSet_forgetDirection (G : SimpleDiGraph α) :
    V(G.forgetDirection) = V(G) := rfl

@[simp] theorem edgeSet_forgetDirection (G : SimpleDiGraph α) :
    E(G.forgetDirection) = (fun a => s(a.1, a.2)) '' E(G) := rfl

@[simp] theorem forgetDirection_adj (G : SimpleDiGraph α) (u v : α) :
    G.forgetDirection.Adj u v ↔ G.Adj u v ∨ G.Adj v u := by
  simp only [SimpleGraph.adj_iff, SimpleDiGraph.adj_iff, edgeSet_forgetDirection]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [Sym2.eq, Sym2.rel_iff'] at h
    simp only [Prod.mk.injEq, Prod.swap_prod_mk] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have haeq : a = (u, v) := Prod.ext h1 h2
      exact Or.inl (haeq ▸ ha)
    · have haeq : a = (v, u) := Prod.ext h1 h2
      exact Or.inr (haeq ▸ ha)
  · rintro (h | h)
    · exact ⟨(u, v), h, rfl⟩
    · exact ⟨(v, u), h, Sym2.eq_swap⟩

end SimpleDiGraph

end GraphLib
