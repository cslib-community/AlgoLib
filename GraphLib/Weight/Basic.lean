/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Reverse

/-!
# Attached graph data

Weights, costs, and capacities are total functions on the ambient vertex or actual-edge
carrier. Their values matter only on the active carrier of the graph. In particular, data on a
general graph is indexed by the complete bundled `Edge` or `Arc`, never by its tag alone.

Same-carrier operations such as `induce`, restriction, and deletion reuse these functions
unchanged. Relabeling and directed reversal use explicit carrier equivalences, while arbitrary
general vertex maps transport edge data through the complete source edge stored as provenance.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ δ ε ζ W : Type*}

/-! ## Carrier equivalences for simple graphs -/

namespace SimpleGraph

/-- Relabel unordered actual edges through a vertex equivalence. -/
def edgeRelabelEquiv (f : α ≃ γ) : Sym2 α ≃ Sym2 γ where
  toFun := Sym2.map f
  invFun := Sym2.map f.symm
  left_inv e := by
    induction e using Sym2.ind with
    | _ u v => simp
  right_inv e := by
    induction e using Sym2.ind with
    | _ u v => simp

@[simp] theorem edgeRelabelEquiv_apply (f : α ≃ γ) (e : Sym2 α) :
    edgeRelabelEquiv f e = Sym2.map f e := rfl

end SimpleGraph

namespace SimpleDiGraph

/-- Relabel ordered actual arcs through a vertex equivalence. -/
def arcRelabelEquiv (f : α ≃ γ) : (α × α) ≃ (γ × γ) := f.prodCongr f

@[simp] theorem arcRelabelEquiv_apply (f : α ≃ γ) (a : α × α) :
    arcRelabelEquiv f a = (f a.1, f a.2) := rfl

/-- Reverse an ordered actual arc by swapping its source and target. -/
def arcReverseEquiv : (α × α) ≃ (α × α) := Equiv.prodComm α α

@[simp] theorem arcReverseEquiv_apply (a : α × α) :
    (arcReverseEquiv : (α × α) ≃ (α × α)) a = (a.2, a.1) := rfl

end SimpleDiGraph

/-! ## Attached-data aliases -/

namespace Graph

/-- Vertex-attached data on a general graph. Values outside `V(G)` are irrelevant. -/
abbrev VertexWeight (_G : Graph α β) (W : Type*) := α → W

/-- Edge-attached data on a general graph, indexed by complete bundled actual edges. -/
abbrev EdgeWeight (_G : Graph α β) (W : Type*) := Edge α β → W

/-- Edge costs on a general graph, indexed by complete bundled actual edges. -/
abbrev Cost (_G : Graph α β) (W : Type*) := Edge α β → W

end Graph

namespace SimpleGraph

/-- Vertex-attached data on a simple graph. Values outside `V(G)` are irrelevant. -/
abbrev VertexWeight (_G : SimpleGraph α) (W : Type*) := α → W

/-- Edge-attached data on a simple graph, indexed by its actual unordered endpoint pairs. -/
abbrev EdgeWeight (_G : SimpleGraph α) (W : Type*) := Sym2 α → W

/-- Edge costs on a simple graph, indexed by its actual unordered endpoint pairs. -/
abbrev Cost (_G : SimpleGraph α) (W : Type*) := Sym2 α → W

end SimpleGraph

namespace DiGraph

/-- Vertex-attached data on a general directed graph. Values outside `V(G)` are irrelevant. -/
abbrev VertexWeight (_G : DiGraph α β) (W : Type*) := α → W

/-- Edge-attached data on a general directed graph, indexed by complete bundled actual arcs. -/
abbrev EdgeWeight (_G : DiGraph α β) (W : Type*) := Arc α β → W

/-- Arc costs on a general directed graph, indexed by complete bundled actual arcs. -/
abbrev Cost (_G : DiGraph α β) (W : Type*) := Arc α β → W

/-- Capacities on a general directed graph, indexed by complete bundled actual arcs. -/
abbrev Capacity (_G : DiGraph α β) (W : Type*) := Arc α β → W

end DiGraph

namespace SimpleDiGraph

/-- Vertex-attached data on a simple directed graph. Values outside `V(G)` are irrelevant. -/
abbrev VertexWeight (_G : SimpleDiGraph α) (W : Type*) := α → W

/-- Edge-attached data on a simple directed graph, indexed by its actual ordered arc pairs. -/
abbrev EdgeWeight (_G : SimpleDiGraph α) (W : Type*) := (α × α) → W

/-- Arc costs on a simple directed graph, indexed by its actual ordered arc pairs. -/
abbrev Cost (_G : SimpleDiGraph α) (W : Type*) := (α × α) → W

/-- Capacities on a simple directed graph, indexed by its actual ordered arc pairs. -/
abbrev Capacity (_G : SimpleDiGraph α) (W : Type*) := (α × α) → W

end SimpleDiGraph

/-! ## Vertex-weight equality and transport -/

namespace Graph.VertexWeight

/-- Equality of vertex weights where they matter on the graph. -/
abbrev EqOn (G : Graph α β) (weight₁ weight₂ : G.VertexWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ V(G)

/-- Transport vertex weights through a vertex equivalence. -/
def transport (G : Graph α β) (H : Graph γ δ) (f : α ≃ γ)
    (weight : G.VertexWeight W) : H.VertexWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : Graph α β) (H : Graph γ δ) (f : α ≃ γ)
    (weight : G.VertexWeight W) (v : γ) :
    transport G H f weight v = weight (f.symm v) := rfl

@[simp] theorem transport_id (G H : Graph α β) (weight : G.VertexWeight W) :
    transport G H (Equiv.refl α) weight = weight := rfl

theorem transport_comp (G : Graph α β) (H : Graph γ δ) (K : Graph ε ζ)
    (f : α ≃ γ) (g : γ ≃ ε) (weight : G.VertexWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext v
  simp [transport]

theorem transport_inverse (G : Graph α β) (H : Graph γ δ) (f : α ≃ γ)
    (weight : G.VertexWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext v
  simp [transport]

/-- Transport a vertex weight to a vertex-relabelled graph. -/
def transportRelabelVertices (G : Graph α β) (f : α ≃ γ) (weight : G.VertexWeight W) :
    (G.relabelVertices f).VertexWeight W := transport G (G.relabelVertices f) f weight

@[simp] theorem transportRelabelVertices_apply (G : Graph α β) (f : α ≃ γ)
    (weight : G.VertexWeight W) (v : α) :
    transportRelabelVertices G f weight (f v) = weight v := by simp [transportRelabelVertices]

/-- Vertex relabeling preserves equality on the active vertex set. -/
theorem transportRelabelVertices_congr (G : Graph α β) (f : α ≃ γ)
    {weight₁ weight₂ : G.VertexWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨v, hv, rfl⟩
  simpa using h hv

end Graph.VertexWeight

namespace SimpleGraph.VertexWeight

/-- Equality of vertex weights where they matter on the graph. -/
abbrev EqOn (G : SimpleGraph α) (weight₁ weight₂ : G.VertexWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ V(G)

/-- Transport vertex weights through a vertex equivalence. -/
def transport (G : SimpleGraph α) (H : SimpleGraph γ) (f : α ≃ γ)
    (weight : G.VertexWeight W) : H.VertexWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : SimpleGraph α) (H : SimpleGraph γ) (f : α ≃ γ)
    (weight : G.VertexWeight W) (v : γ) : transport G H f weight v = weight (f.symm v) := rfl

@[simp] theorem transport_id (G H : SimpleGraph α) (weight : G.VertexWeight W) :
    transport G H (Equiv.refl α) weight = weight := rfl

theorem transport_comp (G : SimpleGraph α) (H : SimpleGraph γ) (K : SimpleGraph ε)
    (f : α ≃ γ) (g : γ ≃ ε) (weight : G.VertexWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext v
  simp [transport]

theorem transport_inverse (G : SimpleGraph α) (H : SimpleGraph γ) (f : α ≃ γ)
    (weight : G.VertexWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext v
  simp [transport]

/-- Transport a vertex weight to a vertex-relabelled simple graph. -/
def transportRelabelVertices (G : SimpleGraph α) (f : α ≃ γ)
    (weight : G.VertexWeight W) : (G.relabelVertices f).VertexWeight W :=
  transport G (G.relabelVertices f) f weight

@[simp] theorem transportRelabelVertices_apply (G : SimpleGraph α) (f : α ≃ γ)
    (weight : G.VertexWeight W) (v : α) :
    transportRelabelVertices G f weight (f v) = weight v := by simp [transportRelabelVertices]

/-- Vertex relabeling preserves equality on the active vertex set. -/
theorem transportRelabelVertices_congr (G : SimpleGraph α) (f : α ≃ γ)
    {weight₁ weight₂ : G.VertexWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨v, hv, rfl⟩
  simpa using h hv

end SimpleGraph.VertexWeight

namespace DiGraph.VertexWeight

/-- Equality of vertex weights where they matter on the directed graph. -/
abbrev EqOn (G : DiGraph α β) (weight₁ weight₂ : G.VertexWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ V(G)

/-- Transport vertex weights through a vertex equivalence. -/
def transport (G : DiGraph α β) (H : DiGraph γ δ) (f : α ≃ γ)
    (weight : G.VertexWeight W) : H.VertexWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : DiGraph α β) (H : DiGraph γ δ) (f : α ≃ γ)
    (weight : G.VertexWeight W) (v : γ) : transport G H f weight v = weight (f.symm v) := rfl

@[simp] theorem transport_id (G H : DiGraph α β) (weight : G.VertexWeight W) :
    transport G H (Equiv.refl α) weight = weight := rfl

theorem transport_comp (G : DiGraph α β) (H : DiGraph γ δ) (K : DiGraph ε ζ)
    (f : α ≃ γ) (g : γ ≃ ε) (weight : G.VertexWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext v
  simp [transport]

theorem transport_inverse (G : DiGraph α β) (H : DiGraph γ δ) (f : α ≃ γ)
    (weight : G.VertexWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext v
  simp [transport]

/-- Transport a vertex weight to a vertex-relabelled directed graph. -/
def transportRelabelVertices (G : DiGraph α β) (f : α ≃ γ)
    (weight : G.VertexWeight W) : (G.relabelVertices f).VertexWeight W :=
  transport G (G.relabelVertices f) f weight

@[simp] theorem transportRelabelVertices_apply (G : DiGraph α β) (f : α ≃ γ)
    (weight : G.VertexWeight W) (v : α) :
    transportRelabelVertices G f weight (f v) = weight v := by simp [transportRelabelVertices]

/-- Vertex relabeling preserves equality on the active vertex set. -/
theorem transportRelabelVertices_congr (G : DiGraph α β) (f : α ≃ γ)
    {weight₁ weight₂ : G.VertexWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨v, hv, rfl⟩
  simpa using h hv

end DiGraph.VertexWeight

namespace SimpleDiGraph.VertexWeight

/-- Equality of vertex weights where they matter on the directed graph. -/
abbrev EqOn (G : SimpleDiGraph α) (weight₁ weight₂ : G.VertexWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ V(G)

/-- Transport vertex weights through a vertex equivalence. -/
def transport (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (f : α ≃ γ)
    (weight : G.VertexWeight W) : H.VertexWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : SimpleDiGraph α) (H : SimpleDiGraph γ)
    (f : α ≃ γ) (weight : G.VertexWeight W) (v : γ) :
    transport G H f weight v = weight (f.symm v) := rfl

@[simp] theorem transport_id (G H : SimpleDiGraph α) (weight : G.VertexWeight W) :
    transport G H (Equiv.refl α) weight = weight := rfl

theorem transport_comp (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (K : SimpleDiGraph ε)
    (f : α ≃ γ) (g : γ ≃ ε) (weight : G.VertexWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext v
  simp [transport]

theorem transport_inverse (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (f : α ≃ γ)
    (weight : G.VertexWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext v
  simp [transport]

/-- Transport a vertex weight to a vertex-relabelled simple directed graph. -/
def transportRelabelVertices (G : SimpleDiGraph α) (f : α ≃ γ)
    (weight : G.VertexWeight W) : (G.relabelVertices f).VertexWeight W :=
  transport G (G.relabelVertices f) f weight

@[simp] theorem transportRelabelVertices_apply (G : SimpleDiGraph α) (f : α ≃ γ)
    (weight : G.VertexWeight W) (v : α) :
    transportRelabelVertices G f weight (f v) = weight v := by simp [transportRelabelVertices]

/-- Vertex relabeling preserves equality on the active vertex set. -/
theorem transportRelabelVertices_congr (G : SimpleDiGraph α) (f : α ≃ γ)
    {weight₁ weight₂ : G.VertexWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨v, hv, rfl⟩
  simpa using h hv

end SimpleDiGraph.VertexWeight

/-! ## Actual-edge weights on general graphs -/

namespace Graph.EdgeWeight

/-- Equality of edge weights on the active bundled actual edges of a graph. -/
abbrev EqOn (G : Graph α β) (weight₁ weight₂ : G.EdgeWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ E(G)

/-- Transport edge weights by pulling back along an explicit actual-edge equivalence. -/
def transport (G : Graph α β) (H : Graph γ δ) (f : Edge α β ≃ Edge γ δ)
    (weight : G.EdgeWeight W) : H.EdgeWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : Graph α β) (H : Graph γ δ)
    (f : Edge α β ≃ Edge γ δ) (weight : G.EdgeWeight W) (e : Edge γ δ) :
    transport G H f weight e = weight (f.symm e) := rfl

@[simp] theorem transport_id (G H : Graph α β) (weight : G.EdgeWeight W) :
    transport G H (Equiv.refl (Edge α β)) weight = weight := rfl

theorem transport_comp (G : Graph α β) (H : Graph γ δ) (K : Graph ε ζ)
    (f : Edge α β ≃ Edge γ δ) (g : Edge γ δ ≃ Edge ε ζ)
    (weight : G.EdgeWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext e
  simp [transport]

theorem transport_inverse (G : Graph α β) (H : Graph γ δ)
    (f : Edge α β ≃ Edge γ δ) (weight : G.EdgeWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext e
  simp [transport]

/-- Transport weights to a vertex-relabelled graph. -/
def transportRelabelVertices (G : Graph α β) (f : α ≃ γ) (weight : G.EdgeWeight W) :
    (G.relabelVertices f).EdgeWeight W :=
  transport G (G.relabelVertices f) (Edge.relabelVertices f) weight

/-- Transport weights to a tag-relabelled graph. -/
def transportRelabelTags (G : Graph α β) (f : β ≃ δ) (weight : G.EdgeWeight W) :
    (G.relabelTags f).EdgeWeight W :=
  transport G (G.relabelTags f) (Edge.relabelTags f) weight

/-- Transport weights through an arbitrary provenance-preserving general vertex map. -/
def transportMapVertices (G : Graph α β) (f : α → γ) (weight : G.EdgeWeight W) :
    (G.mapVertices f).EdgeWeight W := fun e => weight e.tag

@[simp] theorem transportRelabelVertices_apply (G : Graph α β) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (e : Edge α β) :
    transportRelabelVertices G f weight (Edge.relabelVertices f e) = weight e := by
  simp [transportRelabelVertices]

@[simp] theorem transportRelabelTags_apply (G : Graph α β) (f : β ≃ δ)
    (weight : G.EdgeWeight W) (e : Edge α β) :
    transportRelabelTags G f weight (Edge.relabelTags f e) = weight e := by
  simp [transportRelabelTags]

@[simp] theorem transportMapVertices_apply (G : Graph α β) (f : α → γ)
    (weight : G.EdgeWeight W) (e : Edge α β) :
    transportMapVertices G f weight (Edge.mapVertices f e) = weight e := rfl

/-- Vertex relabeling preserves equality of weights on active actual edges. -/
theorem transportRelabelVertices_congr (G : Graph α β) (f : α ≃ γ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨e, he, rfl⟩
  simpa using h he

/-- Tag relabeling preserves equality of weights on active actual edges. -/
theorem transportRelabelTags_congr (G : Graph α β) (f : β ≃ δ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelTags f) (transportRelabelTags G f weight₁)
      (transportRelabelTags G f weight₂) := by
  rintro _ ⟨e, he, rfl⟩
  simpa using h he

/-- Provenance-preserving vertex maps preserve equality of weights on active actual edges. -/
theorem transportMapVertices_congr (G : Graph α β) (f : α → γ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.mapVertices f) (transportMapVertices G f weight₁)
      (transportMapVertices G f weight₂) := by
  rintro _ ⟨e, he, rfl⟩
  exact h he

end Graph.EdgeWeight

namespace DiGraph.EdgeWeight

/-- Equality of edge weights on the active bundled actual arcs of a directed graph. -/
abbrev EqOn (G : DiGraph α β) (weight₁ weight₂ : G.EdgeWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ E(G)

/-- Transport arc weights by pulling back along an explicit actual-arc equivalence. -/
def transport (G : DiGraph α β) (H : DiGraph γ δ) (f : Arc α β ≃ Arc γ δ)
    (weight : G.EdgeWeight W) : H.EdgeWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : DiGraph α β) (H : DiGraph γ δ)
    (f : Arc α β ≃ Arc γ δ) (weight : G.EdgeWeight W) (a : Arc γ δ) :
    transport G H f weight a = weight (f.symm a) := rfl

@[simp] theorem transport_id (G H : DiGraph α β) (weight : G.EdgeWeight W) :
    transport G H (Equiv.refl (Arc α β)) weight = weight := rfl

theorem transport_comp (G : DiGraph α β) (H : DiGraph γ δ) (K : DiGraph ε ζ)
    (f : Arc α β ≃ Arc γ δ) (g : Arc γ δ ≃ Arc ε ζ)
    (weight : G.EdgeWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext a
  simp [transport]

theorem transport_inverse (G : DiGraph α β) (H : DiGraph γ δ)
    (f : Arc α β ≃ Arc γ δ) (weight : G.EdgeWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext a
  simp [transport]

/-- Transport weights to a vertex-relabelled directed graph. -/
def transportRelabelVertices (G : DiGraph α β) (f : α ≃ γ) (weight : G.EdgeWeight W) :
    (G.relabelVertices f).EdgeWeight W :=
  transport G (G.relabelVertices f) (Arc.relabelVertices f) weight

/-- Transport weights to a tag-relabelled directed graph. -/
def transportRelabelTags (G : DiGraph α β) (f : β ≃ δ) (weight : G.EdgeWeight W) :
    (G.relabelTags f).EdgeWeight W := transport G (G.relabelTags f) (Arc.relabelTags f) weight

/-- Transport weights to the reversed directed graph. -/
def transportReverse (G : DiGraph α β) (weight : G.EdgeWeight W) :
    G.reverse.EdgeWeight W := transport G G.reverse Arc.reverseEquiv weight

/-- Transport weights through an arbitrary provenance-preserving directed vertex map. -/
def transportMapVertices (G : DiGraph α β) (f : α → γ) (weight : G.EdgeWeight W) :
    (G.mapVertices f).EdgeWeight W := fun a => weight a.tag

@[simp] theorem transportRelabelVertices_apply (G : DiGraph α β) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (a : Arc α β) :
    transportRelabelVertices G f weight (Arc.relabelVertices f a) = weight a := by
  simp [transportRelabelVertices]

@[simp] theorem transportRelabelTags_apply (G : DiGraph α β) (f : β ≃ δ)
    (weight : G.EdgeWeight W) (a : Arc α β) :
    transportRelabelTags G f weight (Arc.relabelTags f a) = weight a := by
  simp [transportRelabelTags]

@[simp] theorem transportReverse_apply (G : DiGraph α β) (weight : G.EdgeWeight W)
    (a : Arc α β) : transportReverse G weight a.reverse = weight a := by
  simp [transportReverse, transport, Arc.reverseEquiv]

@[simp] theorem transportMapVertices_apply (G : DiGraph α β) (f : α → γ)
    (weight : G.EdgeWeight W) (a : Arc α β) :
    transportMapVertices G f weight (Arc.mapVertices f a) = weight a := rfl

/-- Vertex relabeling preserves equality of weights on active actual arcs. -/
theorem transportRelabelVertices_congr (G : DiGraph α β) (f : α ≃ γ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨a, ha, rfl⟩
  simpa using h ha

/-- Tag relabeling preserves equality of weights on active actual arcs. -/
theorem transportRelabelTags_congr (G : DiGraph α β) (f : β ≃ δ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelTags f) (transportRelabelTags G f weight₁)
      (transportRelabelTags G f weight₂) := by
  rintro _ ⟨a, ha, rfl⟩
  simpa using h ha

/-- Directed reversal preserves equality of weights on active actual arcs. -/
theorem transportReverse_congr (G : DiGraph α β)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn G.reverse (transportReverse G weight₁) (transportReverse G weight₂) := by
  intro a ha
  change weight₁ a.reverse = weight₂ a.reverse
  exact h ((G.mem_edgeSet_reverse a).mp ha)

/-- Provenance-preserving vertex maps preserve equality of weights on active actual arcs. -/
theorem transportMapVertices_congr (G : DiGraph α β) (f : α → γ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.mapVertices f) (transportMapVertices G f weight₁)
      (transportMapVertices G f weight₂) := by
  rintro _ ⟨a, ha, rfl⟩
  exact h ha

end DiGraph.EdgeWeight

/-! ## Actual-edge weights on simple graphs -/

namespace SimpleGraph.EdgeWeight

/-- Equality of edge weights on the active actual edges of a simple graph. -/
abbrev EqOn (G : SimpleGraph α) (weight₁ weight₂ : G.EdgeWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ E(G)

/-- Transport simple-edge weights along an explicit actual-edge equivalence. -/
def transport (G : SimpleGraph α) (H : SimpleGraph γ) (f : Sym2 α ≃ Sym2 γ)
    (weight : G.EdgeWeight W) : H.EdgeWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : SimpleGraph α) (H : SimpleGraph γ)
    (f : Sym2 α ≃ Sym2 γ) (weight : G.EdgeWeight W) (e : Sym2 γ) :
    transport G H f weight e = weight (f.symm e) := rfl

@[simp] theorem transport_id (G H : SimpleGraph α) (weight : G.EdgeWeight W) :
    transport G H (Equiv.refl (Sym2 α)) weight = weight := rfl

theorem transport_comp (G : SimpleGraph α) (H : SimpleGraph γ) (K : SimpleGraph ε)
    (f : Sym2 α ≃ Sym2 γ) (g : Sym2 γ ≃ Sym2 ε) (weight : G.EdgeWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext e
  simp [transport]

theorem transport_inverse (G : SimpleGraph α) (H : SimpleGraph γ)
    (f : Sym2 α ≃ Sym2 γ) (weight : G.EdgeWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext e
  simp [transport]

/-- Transport weights to a vertex-relabelled simple graph. -/
def transportRelabelVertices (G : SimpleGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) : (G.relabelVertices f).EdgeWeight W :=
  transport G (G.relabelVertices f) (SimpleGraph.edgeRelabelEquiv f) weight

@[simp] theorem transportRelabelVertices_apply (G : SimpleGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (e : Sym2 α) :
    transportRelabelVertices G f weight (Sym2.map f e) = weight e := by
  change weight ((SimpleGraph.edgeRelabelEquiv f).symm
    (SimpleGraph.edgeRelabelEquiv f e)) = weight e
  rw [Equiv.symm_apply_apply]

/-- Vertex relabeling preserves equality of weights on active simple edges. -/
theorem transportRelabelVertices_congr (G : SimpleGraph α) (f : α ≃ γ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨e, he, rfl⟩
  simpa using h he

end SimpleGraph.EdgeWeight

namespace SimpleDiGraph.EdgeWeight

/-- Equality of edge weights on the active actual arcs of a simple directed graph. -/
abbrev EqOn (G : SimpleDiGraph α) (weight₁ weight₂ : G.EdgeWeight W) : Prop :=
  Set.EqOn weight₁ weight₂ E(G)

/-- Transport simple arc weights along an explicit actual-arc equivalence. -/
def transport (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (f : (α × α) ≃ (γ × γ))
    (weight : G.EdgeWeight W) : H.EdgeWeight W := weight ∘ f.symm

@[simp] theorem transport_apply (G : SimpleDiGraph α) (H : SimpleDiGraph γ)
    (f : (α × α) ≃ (γ × γ)) (weight : G.EdgeWeight W) (a : γ × γ) :
    transport G H f weight a = weight (f.symm a) := rfl

@[simp] theorem transport_id (G H : SimpleDiGraph α) (weight : G.EdgeWeight W) :
    transport G H (Equiv.refl (α × α)) weight = weight := rfl

theorem transport_comp (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (K : SimpleDiGraph ε)
    (f : (α × α) ≃ (γ × γ)) (g : (γ × γ) ≃ (ε × ε)) (weight : G.EdgeWeight W) :
    transport H K g (transport G H f weight) = transport G K (f.trans g) weight := by
  funext a
  simp [transport]

theorem transport_inverse (G : SimpleDiGraph α) (H : SimpleDiGraph γ)
    (f : (α × α) ≃ (γ × γ)) (weight : G.EdgeWeight W) :
    transport H G f.symm (transport G H f weight) = weight := by
  funext a
  simp [transport]

/-- Transport weights to a vertex-relabelled simple directed graph. -/
def transportRelabelVertices (G : SimpleDiGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) : (G.relabelVertices f).EdgeWeight W :=
  transport G (G.relabelVertices f) (SimpleDiGraph.arcRelabelEquiv f) weight

/-- Transport weights to the reversed simple directed graph. -/
def transportReverse (G : SimpleDiGraph α) (weight : G.EdgeWeight W) :
    G.reverse.EdgeWeight W := transport G G.reverse SimpleDiGraph.arcReverseEquiv weight

@[simp] theorem transportRelabelVertices_apply (G : SimpleDiGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (a : α × α) :
    transportRelabelVertices G f weight (f a.1, f a.2) = weight a := by
  simp [transportRelabelVertices, transport, SimpleDiGraph.arcRelabelEquiv]

@[simp] theorem transportReverse_apply (G : SimpleDiGraph α) (weight : G.EdgeWeight W)
    (a : α × α) : transportReverse G weight (a.2, a.1) = weight a := by
  simp [transportReverse, transport, SimpleDiGraph.arcReverseEquiv]

/-- Vertex relabeling preserves equality of weights on active simple directed arcs. -/
theorem transportRelabelVertices_congr (G : SimpleDiGraph α) (f : α ≃ γ)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn (G.relabelVertices f) (transportRelabelVertices G f weight₁)
      (transportRelabelVertices G f weight₂) := by
  rintro _ ⟨a, ha, rfl⟩
  simpa using h ha

/-- Directed reversal preserves equality of weights on active simple arcs. -/
theorem transportReverse_congr (G : SimpleDiGraph α)
    {weight₁ weight₂ : G.EdgeWeight W} (h : EqOn G weight₁ weight₂) :
    EqOn G.reverse (transportReverse G weight₁) (transportReverse G weight₂) := by
  intro a ha
  change weight₁ (a.2, a.1) = weight₂ (a.2, a.1)
  exact h ((G.mem_edgeSet_reverse a).mp ha)

end SimpleDiGraph.EdgeWeight

/-! ## Costs and capacities -/

namespace Graph.Cost

/-- Equality of costs on the active actual edges. -/
abbrev EqOn (G : Graph α β) (cost₁ cost₂ : G.Cost W) : Prop := Set.EqOn cost₁ cost₂ E(G)

/-- Transport costs along an explicit actual-edge equivalence. -/
def transport (G : Graph α β) (H : Graph γ δ) (f : Edge α β ≃ Edge γ δ)
    (cost : G.Cost W) : H.Cost W := Graph.EdgeWeight.transport G H f cost

/-- Transport costs to a vertex-relabelled graph. -/
def transportRelabelVertices (G : Graph α β) (f : α ≃ γ) (cost : G.Cost W) :
    (G.relabelVertices f).Cost W := Graph.EdgeWeight.transportRelabelVertices G f cost

/-- Transport costs to a tag-relabelled graph. -/
def transportRelabelTags (G : Graph α β) (f : β ≃ δ) (cost : G.Cost W) :
    (G.relabelTags f).Cost W := Graph.EdgeWeight.transportRelabelTags G f cost

/-- Transport costs through an arbitrary provenance-preserving general vertex map. -/
def transportMapVertices (G : Graph α β) (f : α → γ) (cost : G.Cost W) :
    (G.mapVertices f).Cost W := Graph.EdgeWeight.transportMapVertices G f cost

@[simp] theorem transport_apply (G : Graph α β) (H : Graph γ δ)
    (f : Edge α β ≃ Edge γ δ) (cost : G.Cost W) (e : Edge γ δ) :
    transport G H f cost e = cost (f.symm e) := rfl

@[simp] theorem transport_id (G H : Graph α β) (cost : G.Cost W) :
    transport G H (Equiv.refl (Edge α β)) cost = cost := rfl

theorem transport_comp (G : Graph α β) (H : Graph γ δ) (K : Graph ε ζ)
    (f : Edge α β ≃ Edge γ δ) (g : Edge γ δ ≃ Edge ε ζ) (cost : G.Cost W) :
    transport H K g (transport G H f cost) = transport G K (f.trans g) cost :=
  Graph.EdgeWeight.transport_comp G H K f g cost

theorem transport_inverse (G : Graph α β) (H : Graph γ δ)
    (f : Edge α β ≃ Edge γ δ) (cost : G.Cost W) :
    transport H G f.symm (transport G H f cost) = cost :=
  Graph.EdgeWeight.transport_inverse G H f cost

@[simp] theorem transportRelabelVertices_apply (G : Graph α β) (f : α ≃ γ)
    (cost : G.Cost W) (e : Edge α β) :
    transportRelabelVertices G f cost (Edge.relabelVertices f e) = cost e := by
  simp [transportRelabelVertices]

@[simp] theorem transportRelabelTags_apply (G : Graph α β) (f : β ≃ δ)
    (cost : G.Cost W) (e : Edge α β) :
    transportRelabelTags G f cost (Edge.relabelTags f e) = cost e := by simp [transportRelabelTags]

@[simp] theorem transportMapVertices_apply (G : Graph α β) (f : α → γ)
    (cost : G.Cost W) (e : Edge α β) :
    transportMapVertices G f cost (Edge.mapVertices f e) = cost e := rfl

end Graph.Cost

namespace SimpleGraph.Cost

/-- Equality of costs on the active actual edges. -/
abbrev EqOn (G : SimpleGraph α) (cost₁ cost₂ : G.Cost W) : Prop :=
  Set.EqOn cost₁ cost₂ E(G)

/-- Transport costs along an explicit actual-edge equivalence. -/
def transport (G : SimpleGraph α) (H : SimpleGraph γ) (f : Sym2 α ≃ Sym2 γ)
    (cost : G.Cost W) : H.Cost W := SimpleGraph.EdgeWeight.transport G H f cost

/-- Transport costs to a vertex-relabelled simple graph. -/
def transportRelabelVertices (G : SimpleGraph α) (f : α ≃ γ) (cost : G.Cost W) :
    (G.relabelVertices f).Cost W := SimpleGraph.EdgeWeight.transportRelabelVertices G f cost

@[simp] theorem transport_apply (G : SimpleGraph α) (H : SimpleGraph γ)
    (f : Sym2 α ≃ Sym2 γ) (cost : G.Cost W) (e : Sym2 γ) :
    transport G H f cost e = cost (f.symm e) := rfl

@[simp] theorem transport_id (G H : SimpleGraph α) (cost : G.Cost W) :
    transport G H (Equiv.refl (Sym2 α)) cost = cost := rfl

theorem transport_comp (G : SimpleGraph α) (H : SimpleGraph γ) (K : SimpleGraph ε)
    (f : Sym2 α ≃ Sym2 γ) (g : Sym2 γ ≃ Sym2 ε) (cost : G.Cost W) :
    transport H K g (transport G H f cost) = transport G K (f.trans g) cost :=
  SimpleGraph.EdgeWeight.transport_comp G H K f g cost

theorem transport_inverse (G : SimpleGraph α) (H : SimpleGraph γ)
    (f : Sym2 α ≃ Sym2 γ) (cost : G.Cost W) :
    transport H G f.symm (transport G H f cost) = cost :=
  SimpleGraph.EdgeWeight.transport_inverse G H f cost

@[simp] theorem transportRelabelVertices_apply (G : SimpleGraph α) (f : α ≃ γ)
    (cost : G.Cost W) (e : Sym2 α) :
    transportRelabelVertices G f cost (Sym2.map f e) = cost e := by simp [transportRelabelVertices]

end SimpleGraph.Cost

namespace DiGraph.Cost

/-- Equality of costs on the active actual arcs. -/
abbrev EqOn (G : DiGraph α β) (cost₁ cost₂ : G.Cost W) : Prop := Set.EqOn cost₁ cost₂ E(G)

/-- Transport costs along an explicit actual-arc equivalence. -/
def transport (G : DiGraph α β) (H : DiGraph γ δ) (f : Arc α β ≃ Arc γ δ)
    (cost : G.Cost W) : H.Cost W := DiGraph.EdgeWeight.transport G H f cost

/-- Transport costs to a vertex-relabelled directed graph. -/
def transportRelabelVertices (G : DiGraph α β) (f : α ≃ γ) (cost : G.Cost W) :
    (G.relabelVertices f).Cost W := DiGraph.EdgeWeight.transportRelabelVertices G f cost

/-- Transport costs to a tag-relabelled directed graph. -/
def transportRelabelTags (G : DiGraph α β) (f : β ≃ δ) (cost : G.Cost W) :
    (G.relabelTags f).Cost W := DiGraph.EdgeWeight.transportRelabelTags G f cost

/-- Transport costs to the reversed directed graph. -/
def transportReverse (G : DiGraph α β) (cost : G.Cost W) : G.reverse.Cost W :=
  DiGraph.EdgeWeight.transportReverse G cost

/-- Transport costs through an arbitrary provenance-preserving directed vertex map. -/
def transportMapVertices (G : DiGraph α β) (f : α → γ) (cost : G.Cost W) :
    (G.mapVertices f).Cost W := DiGraph.EdgeWeight.transportMapVertices G f cost

@[simp] theorem transport_apply (G : DiGraph α β) (H : DiGraph γ δ)
    (f : Arc α β ≃ Arc γ δ) (cost : G.Cost W) (a : Arc γ δ) :
    transport G H f cost a = cost (f.symm a) := rfl

@[simp] theorem transport_id (G H : DiGraph α β) (cost : G.Cost W) :
    transport G H (Equiv.refl (Arc α β)) cost = cost := rfl

theorem transport_comp (G : DiGraph α β) (H : DiGraph γ δ) (K : DiGraph ε ζ)
    (f : Arc α β ≃ Arc γ δ) (g : Arc γ δ ≃ Arc ε ζ) (cost : G.Cost W) :
    transport H K g (transport G H f cost) = transport G K (f.trans g) cost :=
  DiGraph.EdgeWeight.transport_comp G H K f g cost

theorem transport_inverse (G : DiGraph α β) (H : DiGraph γ δ)
    (f : Arc α β ≃ Arc γ δ) (cost : G.Cost W) :
    transport H G f.symm (transport G H f cost) = cost :=
  DiGraph.EdgeWeight.transport_inverse G H f cost

@[simp] theorem transportRelabelVertices_apply (G : DiGraph α β) (f : α ≃ γ)
    (cost : G.Cost W) (a : Arc α β) :
    transportRelabelVertices G f cost (Arc.relabelVertices f a) = cost a := by
  simp [transportRelabelVertices]

@[simp] theorem transportRelabelTags_apply (G : DiGraph α β) (f : β ≃ δ)
    (cost : G.Cost W) (a : Arc α β) :
    transportRelabelTags G f cost (Arc.relabelTags f a) = cost a := by simp [transportRelabelTags]

@[simp] theorem transportReverse_apply (G : DiGraph α β) (cost : G.Cost W)
    (a : Arc α β) : transportReverse G cost a.reverse = cost a := by simp [transportReverse]

@[simp] theorem transportMapVertices_apply (G : DiGraph α β) (f : α → γ)
    (cost : G.Cost W) (a : Arc α β) :
    transportMapVertices G f cost (Arc.mapVertices f a) = cost a := rfl

end DiGraph.Cost

namespace SimpleDiGraph.Cost

/-- Equality of costs on the active actual arcs. -/
abbrev EqOn (G : SimpleDiGraph α) (cost₁ cost₂ : G.Cost W) : Prop :=
  Set.EqOn cost₁ cost₂ E(G)

/-- Transport costs along an explicit actual-arc equivalence. -/
def transport (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (f : (α × α) ≃ (γ × γ))
    (cost : G.Cost W) : H.Cost W := SimpleDiGraph.EdgeWeight.transport G H f cost

/-- Transport costs to a vertex-relabelled simple directed graph. -/
def transportRelabelVertices (G : SimpleDiGraph α) (f : α ≃ γ) (cost : G.Cost W) :
    (G.relabelVertices f).Cost W := SimpleDiGraph.EdgeWeight.transportRelabelVertices G f cost

/-- Transport costs to the reversed simple directed graph. -/
def transportReverse (G : SimpleDiGraph α) (cost : G.Cost W) : G.reverse.Cost W :=
  SimpleDiGraph.EdgeWeight.transportReverse G cost

@[simp] theorem transport_apply (G : SimpleDiGraph α) (H : SimpleDiGraph γ)
    (f : (α × α) ≃ (γ × γ)) (cost : G.Cost W) (a : γ × γ) :
    transport G H f cost a = cost (f.symm a) := rfl

@[simp] theorem transport_id (G H : SimpleDiGraph α) (cost : G.Cost W) :
    transport G H (Equiv.refl (α × α)) cost = cost := rfl

theorem transport_comp (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (K : SimpleDiGraph ε)
    (f : (α × α) ≃ (γ × γ)) (g : (γ × γ) ≃ (ε × ε)) (cost : G.Cost W) :
    transport H K g (transport G H f cost) = transport G K (f.trans g) cost :=
  SimpleDiGraph.EdgeWeight.transport_comp G H K f g cost

theorem transport_inverse (G : SimpleDiGraph α) (H : SimpleDiGraph γ)
    (f : (α × α) ≃ (γ × γ)) (cost : G.Cost W) :
    transport H G f.symm (transport G H f cost) = cost :=
  SimpleDiGraph.EdgeWeight.transport_inverse G H f cost

@[simp] theorem transportRelabelVertices_apply (G : SimpleDiGraph α) (f : α ≃ γ)
    (cost : G.Cost W) (a : α × α) :
    transportRelabelVertices G f cost (f a.1, f a.2) = cost a := by simp [transportRelabelVertices]

@[simp] theorem transportReverse_apply (G : SimpleDiGraph α) (cost : G.Cost W)
    (a : α × α) : transportReverse G cost (a.2, a.1) = cost a := by simp [transportReverse]

end SimpleDiGraph.Cost

namespace DiGraph.Capacity

/-- Equality of capacities on the active bundled actual arcs. -/
abbrev EqOn (G : DiGraph α β) (capacity₁ capacity₂ : G.Capacity W) : Prop :=
  Set.EqOn capacity₁ capacity₂ E(G)

/-- Transport capacities along an explicit actual-arc equivalence. -/
def transport (G : DiGraph α β) (H : DiGraph γ δ) (f : Arc α β ≃ Arc γ δ)
    (capacity : G.Capacity W) : H.Capacity W := DiGraph.EdgeWeight.transport G H f capacity

/-- Transport capacities to a vertex-relabelled directed graph. -/
def transportRelabelVertices (G : DiGraph α β) (f : α ≃ γ) (capacity : G.Capacity W) :
    (G.relabelVertices f).Capacity W := transport G (G.relabelVertices f)
      (Arc.relabelVertices f) capacity

/-- Transport capacities to a tag-relabelled directed graph. -/
def transportRelabelTags (G : DiGraph α β) (f : β ≃ δ) (capacity : G.Capacity W) :
    (G.relabelTags f).Capacity W := transport G (G.relabelTags f) (Arc.relabelTags f) capacity

/-- Transport capacities to the reversed directed graph. -/
def transportReverse (G : DiGraph α β) (capacity : G.Capacity W) :
    G.reverse.Capacity W := transport G G.reverse Arc.reverseEquiv capacity

/-- Transport capacities through an arbitrary provenance-preserving directed vertex map. -/
def transportMapVertices (G : DiGraph α β) (f : α → γ) (capacity : G.Capacity W) :
    (G.mapVertices f).Capacity W := fun a => capacity a.tag

@[simp] theorem transport_apply (G : DiGraph α β) (H : DiGraph γ δ)
    (f : Arc α β ≃ Arc γ δ) (capacity : G.Capacity W) (a : Arc γ δ) :
    transport G H f capacity a = capacity (f.symm a) := rfl

@[simp] theorem transport_id (G H : DiGraph α β) (capacity : G.Capacity W) :
    transport G H (Equiv.refl (Arc α β)) capacity = capacity := rfl

theorem transport_comp (G : DiGraph α β) (H : DiGraph γ δ) (K : DiGraph ε ζ)
    (f : Arc α β ≃ Arc γ δ) (g : Arc γ δ ≃ Arc ε ζ) (capacity : G.Capacity W) :
    transport H K g (transport G H f capacity) = transport G K (f.trans g) capacity :=
  DiGraph.EdgeWeight.transport_comp G H K f g capacity

theorem transport_inverse (G : DiGraph α β) (H : DiGraph γ δ)
    (f : Arc α β ≃ Arc γ δ) (capacity : G.Capacity W) :
    transport H G f.symm (transport G H f capacity) = capacity :=
  DiGraph.EdgeWeight.transport_inverse G H f capacity

@[simp] theorem transportRelabelVertices_apply (G : DiGraph α β) (f : α ≃ γ)
    (capacity : G.Capacity W) (a : Arc α β) :
    transportRelabelVertices G f capacity (Arc.relabelVertices f a) = capacity a := by
  simp [transportRelabelVertices]

@[simp] theorem transportRelabelTags_apply (G : DiGraph α β) (f : β ≃ δ)
    (capacity : G.Capacity W) (a : Arc α β) :
    transportRelabelTags G f capacity (Arc.relabelTags f a) = capacity a := by
  simp [transportRelabelTags]

@[simp] theorem transportReverse_apply (G : DiGraph α β) (capacity : G.Capacity W)
    (a : Arc α β) : transportReverse G capacity a.reverse = capacity a := by
  simp [transportReverse, transport, Arc.reverseEquiv]

@[simp] theorem transportMapVertices_apply (G : DiGraph α β) (f : α → γ)
    (capacity : G.Capacity W) (a : Arc α β) :
    transportMapVertices G f capacity (Arc.mapVertices f a) = capacity a := rfl

end DiGraph.Capacity

namespace SimpleDiGraph.Capacity

/-- Equality of capacities on the active actual arcs. -/
abbrev EqOn (G : SimpleDiGraph α) (capacity₁ capacity₂ : G.Capacity W) : Prop :=
  Set.EqOn capacity₁ capacity₂ E(G)

/-- Transport capacities along an explicit actual-arc equivalence. -/
def transport (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (f : (α × α) ≃ (γ × γ))
    (capacity : G.Capacity W) : H.Capacity W := SimpleDiGraph.EdgeWeight.transport G H f capacity

/-- Transport capacities to a vertex-relabelled simple directed graph. -/
def transportRelabelVertices (G : SimpleDiGraph α) (f : α ≃ γ)
    (capacity : G.Capacity W) : (G.relabelVertices f).Capacity W :=
  transport G (G.relabelVertices f) (SimpleDiGraph.arcRelabelEquiv f) capacity

/-- Transport capacities to the reversed simple directed graph. -/
def transportReverse (G : SimpleDiGraph α) (capacity : G.Capacity W) :
    G.reverse.Capacity W := transport G G.reverse SimpleDiGraph.arcReverseEquiv capacity

@[simp] theorem transport_apply (G : SimpleDiGraph α) (H : SimpleDiGraph γ)
    (f : (α × α) ≃ (γ × γ)) (capacity : G.Capacity W) (a : γ × γ) :
    transport G H f capacity a = capacity (f.symm a) := rfl

@[simp] theorem transport_id (G H : SimpleDiGraph α) (capacity : G.Capacity W) :
    transport G H (Equiv.refl (α × α)) capacity = capacity := rfl

theorem transport_comp (G : SimpleDiGraph α) (H : SimpleDiGraph γ) (K : SimpleDiGraph ε)
    (f : (α × α) ≃ (γ × γ)) (g : (γ × γ) ≃ (ε × ε))
    (capacity : G.Capacity W) :
    transport H K g (transport G H f capacity) = transport G K (f.trans g) capacity :=
  SimpleDiGraph.EdgeWeight.transport_comp G H K f g capacity

theorem transport_inverse (G : SimpleDiGraph α) (H : SimpleDiGraph γ)
    (f : (α × α) ≃ (γ × γ)) (capacity : G.Capacity W) :
    transport H G f.symm (transport G H f capacity) = capacity :=
  SimpleDiGraph.EdgeWeight.transport_inverse G H f capacity

@[simp] theorem transportRelabelVertices_apply (G : SimpleDiGraph α) (f : α ≃ γ)
    (capacity : G.Capacity W) (a : α × α) :
    transportRelabelVertices G f capacity (f a.1, f a.2) = capacity a := by
  simp [transportRelabelVertices, transport, SimpleDiGraph.arcRelabelEquiv]

@[simp] theorem transportReverse_apply (G : SimpleDiGraph α) (capacity : G.Capacity W)
    (a : α × α) : transportReverse G capacity (a.2, a.1) = capacity a := by
  simp [transportReverse, transport, SimpleDiGraph.arcReverseEquiv]

end SimpleDiGraph.Capacity

end GraphLib
