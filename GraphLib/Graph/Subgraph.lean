/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Adjacency

/-!
# Subgraphs and same-carrier restrictions

This file gives all four GraphLib graph families their canonical same-ambient subgraph order.
The notation `H ≤ G` compares vertex sets and sets of actual edges or arcs. Stronger spanning
and induced relations use the scoped notations `≤s` and `≤i`.

Induced restriction and edge restriction retain the ambient vertex and edge/tag types. In
particular, `restrictEdges` on a general graph takes bundled `Edge` or `Arc` values, so parallel
actual edges remain distinguishable.
-/

namespace GraphLib
variable {α β : Type*}

open scoped GraphLib

/-! ## Subgraph orders -/

/-- `H.IsSubgraph G` means that every vertex and actual edge of `H` belongs to `G`.
The preferred spelling is `H ≤ G`. -/
structure Graph.IsSubgraph (H G : Graph α β) : Prop where
  /-- Every vertex of the subgraph belongs to the ambient graph. -/
  vertexSet_subset : V(H) ⊆ V(G)
  /-- Every bundled actual edge of the subgraph belongs to the ambient graph. -/
  edgeSet_subset : E(H) ⊆ E(G)

/-- `H.IsSubgraph G` means that every vertex and actual edge of `H` belongs to `G`.
The preferred spelling is `H ≤ G`. -/
structure SimpleGraph.IsSubgraph (H G : SimpleGraph α) : Prop where
  /-- Every vertex of the subgraph belongs to the ambient graph. -/
  vertexSet_subset : V(H) ⊆ V(G)
  /-- Every actual endpoint-pair edge of the subgraph belongs to the ambient graph. -/
  edgeSet_subset : E(H) ⊆ E(G)

/-- `H.IsSubgraph G` means that every vertex and actual arc of `H` belongs to `G`.
The preferred spelling is `H ≤ G`. -/
structure DiGraph.IsSubgraph (H G : DiGraph α β) : Prop where
  /-- Every vertex of the subgraph belongs to the ambient graph. -/
  vertexSet_subset : V(H) ⊆ V(G)
  /-- Every bundled actual arc of the subgraph belongs to the ambient graph. -/
  edgeSet_subset : E(H) ⊆ E(G)

/-- `H.IsSubgraph G` means that every vertex and actual arc of `H` belongs to `G`.
The preferred spelling is `H ≤ G`. -/
structure SimpleDiGraph.IsSubgraph (H G : SimpleDiGraph α) : Prop where
  /-- Every vertex of the subgraph belongs to the ambient graph. -/
  vertexSet_subset : V(H) ⊆ V(G)
  /-- Every actual ordered-pair arc of the subgraph belongs to the ambient graph. -/
  edgeSet_subset : E(H) ⊆ E(G)

namespace Graph

theorem IsSubgraph.trans {G H K : Graph α β} (hGH : G.IsSubgraph H)
    (hHK : H.IsSubgraph K) : G.IsSubgraph K :=
  ⟨hGH.vertexSet_subset.trans hHK.vertexSet_subset,
    hGH.edgeSet_subset.trans hHK.edgeSet_subset⟩

/-- The subgraph relation on general graphs is componentwise inclusion of vertex sets and
bundled actual-edge sets. -/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨fun _ h => h, fun _ h => h⟩
  le_trans _ _ _ := IsSubgraph.trans
  le_antisymm _ _ hGH hHG := Graph.ext
    (Set.Subset.antisymm hGH.vertexSet_subset hHG.vertexSet_subset)
    (Set.Subset.antisymm hGH.edgeSet_subset hHG.edgeSet_subset)

@[simp] theorem isSubgraph_iff_le (H G : Graph α β) : H.IsSubgraph G ↔ H ≤ G := Iff.rfl

attribute [grind →] IsSubgraph.vertexSet_subset IsSubgraph.edgeSet_subset

theorem IsSubgraph.isLink {H G : Graph α β} (hHG : H ≤ G) {e u v}
    (h : H.IsLink e u v) : G.IsLink e u v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.endpoints_eq⟩

theorem IsSubgraph.inc {H G : Graph α β} (hHG : H ≤ G) {e v}
    (h : H.Inc e v) : G.Inc e v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.2⟩

theorem IsSubgraph.adj {H G : Graph α β} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, hHG.isLink he⟩

@[grind →] theorem Adj.mono {H G : Graph α β} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := hHG.adj h

end Graph

namespace SimpleGraph

theorem IsSubgraph.trans {G H K : SimpleGraph α} (hGH : G.IsSubgraph H)
    (hHK : H.IsSubgraph K) : G.IsSubgraph K :=
  ⟨hGH.vertexSet_subset.trans hHK.vertexSet_subset,
    hGH.edgeSet_subset.trans hHK.edgeSet_subset⟩

/-- The subgraph relation on simple graphs is componentwise inclusion of vertex and actual-edge
sets. -/
instance : PartialOrder (SimpleGraph α) where
  le := IsSubgraph
  le_refl _ := ⟨fun _ h => h, fun _ h => h⟩
  le_trans _ _ _ := IsSubgraph.trans
  le_antisymm _ _ hGH hHG := SimpleGraph.ext
    (Set.Subset.antisymm hGH.vertexSet_subset hHG.vertexSet_subset)
    (Set.Subset.antisymm hGH.edgeSet_subset hHG.edgeSet_subset)

@[simp] theorem isSubgraph_iff_le (H G : SimpleGraph α) : H.IsSubgraph G ↔ H ≤ G := Iff.rfl

attribute [grind →] IsSubgraph.vertexSet_subset IsSubgraph.edgeSet_subset

theorem IsSubgraph.isLink {H G : SimpleGraph α} (hHG : H ≤ G) {e u v}
    (h : H.IsLink e u v) : G.IsLink e u v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.endpoints_eq⟩

theorem IsSubgraph.inc {H G : SimpleGraph α} (hHG : H ≤ G) {e v}
    (h : H.Inc e v) : G.Inc e v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.2⟩

theorem IsSubgraph.adj {H G : SimpleGraph α} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, hHG.isLink he⟩

@[grind →] theorem Adj.mono {H G : SimpleGraph α} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := hHG.adj h

end SimpleGraph

namespace DiGraph

theorem IsSubgraph.trans {G H K : DiGraph α β} (hGH : G.IsSubgraph H)
    (hHK : H.IsSubgraph K) : G.IsSubgraph K :=
  ⟨hGH.vertexSet_subset.trans hHK.vertexSet_subset,
    hGH.edgeSet_subset.trans hHK.edgeSet_subset⟩

/-- The subgraph relation on general directed graphs is componentwise inclusion of vertex sets
and bundled actual-arc sets. -/
instance : PartialOrder (DiGraph α β) where
  le := IsSubgraph
  le_refl _ := ⟨fun _ h => h, fun _ h => h⟩
  le_trans _ _ _ := IsSubgraph.trans
  le_antisymm _ _ hGH hHG := DiGraph.ext
    (Set.Subset.antisymm hGH.vertexSet_subset hHG.vertexSet_subset)
    (Set.Subset.antisymm hGH.edgeSet_subset hHG.edgeSet_subset)

@[simp] theorem isSubgraph_iff_le (H G : DiGraph α β) : H.IsSubgraph G ↔ H ≤ G := Iff.rfl

attribute [grind →] IsSubgraph.vertexSet_subset IsSubgraph.edgeSet_subset

theorem IsSubgraph.isArc {H G : DiGraph α β} (hHG : H ≤ G) {a u v}
    (h : H.IsArc a u v) : G.IsArc a u v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.source_eq, h.target_eq⟩

theorem IsSubgraph.inc {H G : DiGraph α β} (hHG : H ≤ G) {a v}
    (h : H.Inc a v) : G.Inc a v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.2⟩

theorem IsSubgraph.adj {H G : DiGraph α β} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, hHG.isArc ha⟩

@[grind →] theorem Adj.mono {H G : DiGraph α β} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := hHG.adj h

end DiGraph

namespace SimpleDiGraph

theorem IsSubgraph.trans {G H K : SimpleDiGraph α} (hGH : G.IsSubgraph H)
    (hHK : H.IsSubgraph K) : G.IsSubgraph K :=
  ⟨hGH.vertexSet_subset.trans hHK.vertexSet_subset,
    hGH.edgeSet_subset.trans hHK.edgeSet_subset⟩

/-- The subgraph relation on simple directed graphs is componentwise inclusion of vertex and
actual-arc sets. -/
instance : PartialOrder (SimpleDiGraph α) where
  le := IsSubgraph
  le_refl _ := ⟨fun _ h => h, fun _ h => h⟩
  le_trans _ _ _ := IsSubgraph.trans
  le_antisymm _ _ hGH hHG := SimpleDiGraph.ext
    (Set.Subset.antisymm hGH.vertexSet_subset hHG.vertexSet_subset)
    (Set.Subset.antisymm hGH.edgeSet_subset hHG.edgeSet_subset)

@[simp] theorem isSubgraph_iff_le (H G : SimpleDiGraph α) : H.IsSubgraph G ↔ H ≤ G := Iff.rfl

attribute [grind →] IsSubgraph.vertexSet_subset IsSubgraph.edgeSet_subset

theorem IsSubgraph.isArc {H G : SimpleDiGraph α} (hHG : H ≤ G) {a u v}
    (h : H.IsArc a u v) : G.IsArc a u v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.source_eq, h.target_eq⟩

theorem IsSubgraph.inc {H G : SimpleDiGraph α} (hHG : H ≤ G) {a v}
    (h : H.Inc a v) : G.Inc a v :=
  ⟨hHG.edgeSet_subset h.edge_mem, h.2⟩

theorem IsSubgraph.adj {H G : SimpleDiGraph α} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, hHG.isArc ha⟩

@[grind →] theorem Adj.mono {H G : SimpleDiGraph α} (hHG : H ≤ G) {u v}
    (h : H.Adj u v) : G.Adj u v := hHG.adj h

end SimpleDiGraph

/-! ## Lattice operations -/

private def Graph.bottomGraph : Graph α β where
  vertexSet := ∅
  edgeSet := ∅
  endpoints_mem := by simp

private def Graph.infGraph (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∩ V(H)
  edgeSet := E(G) ∩ E(H)
  endpoints_mem := by
    rintro e ⟨heG, heH⟩ v hv
    exact ⟨G.endpoints_mem e heG v hv, H.endpoints_mem e heH v hv⟩

private def Graph.supGraph (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  endpoints_mem := by
    rintro e (heG | heH) v hv
    · exact Or.inl (G.endpoints_mem e heG v hv)
    · exact Or.inr (H.endpoints_mem e heH v hv)

private def Graph.topGraph : Graph α β where
  vertexSet := Set.univ
  edgeSet := Set.univ
  endpoints_mem := by simp

instance : SemilatticeInf (Graph α β) where
  inf := Graph.infGraph
  inf_le_left _ _ := ⟨Set.inter_subset_left, Set.inter_subset_left⟩
  inf_le_right _ _ := ⟨Set.inter_subset_right, Set.inter_subset_right⟩
  le_inf _ _ _ hG hH := ⟨fun _ hv => ⟨hG.vertexSet_subset hv, hH.vertexSet_subset hv⟩,
    fun _ he => ⟨hG.edgeSet_subset he, hH.edgeSet_subset he⟩⟩

instance : SemilatticeSup (Graph α β) where
  sup := Graph.supGraph
  le_sup_left _ _ := ⟨Set.subset_union_left, Set.subset_union_left⟩
  le_sup_right _ _ := ⟨Set.subset_union_right, Set.subset_union_right⟩
  sup_le _ _ _ hG hH := ⟨fun _ hv => by
      rcases hv with hv | hv
      · exact hG.vertexSet_subset hv
      · exact hH.vertexSet_subset hv,
    fun _ he => by
      rcases he with he | he
      · exact hG.edgeSet_subset he
      · exact hH.edgeSet_subset he⟩

instance : Lattice (Graph α β) where

instance : OrderBot (Graph α β) where
  bot := Graph.bottomGraph
  bot_le _ := ⟨Set.empty_subset _, Set.empty_subset _⟩

instance : OrderTop (Graph α β) where
  top := Graph.topGraph
  le_top _ := ⟨Set.subset_univ _, Set.subset_univ _⟩

private def SimpleGraph.bottomGraph : SimpleGraph α where
  vertexSet := ∅
  edgeSet := ∅
  endpoints_mem := by simp
  loopless := by simp

private def SimpleGraph.infGraph (G H : SimpleGraph α) : SimpleGraph α where
  vertexSet := V(G) ∩ V(H)
  edgeSet := E(G) ∩ E(H)
  endpoints_mem := by
    rintro e ⟨heG, heH⟩ v hv
    exact ⟨G.endpoints_mem e heG v hv, H.endpoints_mem e heH v hv⟩
  loopless := by
    rintro e ⟨heG, _⟩
    exact G.loopless e heG

private def SimpleGraph.supGraph (G H : SimpleGraph α) : SimpleGraph α where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  endpoints_mem := by
    rintro e (heG | heH) v hv
    · exact Or.inl (G.endpoints_mem e heG v hv)
    · exact Or.inr (H.endpoints_mem e heH v hv)
  loopless := by
    rintro e (heG | heH)
    · exact G.loopless e heG
    · exact H.loopless e heH

private def SimpleGraph.topGraph : SimpleGraph α where
  vertexSet := Set.univ
  edgeSet := {e | ¬ e.IsDiag}
  endpoints_mem := by simp
  loopless := by simp

instance : SemilatticeInf (SimpleGraph α) where
  inf := SimpleGraph.infGraph
  inf_le_left _ _ := ⟨Set.inter_subset_left, Set.inter_subset_left⟩
  inf_le_right _ _ := ⟨Set.inter_subset_right, Set.inter_subset_right⟩
  le_inf _ _ _ hG hH := ⟨fun _ hv => ⟨hG.vertexSet_subset hv, hH.vertexSet_subset hv⟩,
    fun _ he => ⟨hG.edgeSet_subset he, hH.edgeSet_subset he⟩⟩

instance : SemilatticeSup (SimpleGraph α) where
  sup := SimpleGraph.supGraph
  le_sup_left _ _ := ⟨Set.subset_union_left, Set.subset_union_left⟩
  le_sup_right _ _ := ⟨Set.subset_union_right, Set.subset_union_right⟩
  sup_le _ _ _ hG hH := ⟨fun _ hv => by
      rcases hv with hv | hv
      · exact hG.vertexSet_subset hv
      · exact hH.vertexSet_subset hv,
    fun _ he => by
      rcases he with he | he
      · exact hG.edgeSet_subset he
      · exact hH.edgeSet_subset he⟩

instance : Lattice (SimpleGraph α) where

instance : OrderBot (SimpleGraph α) where
  bot := SimpleGraph.bottomGraph
  bot_le _ := ⟨Set.empty_subset _, Set.empty_subset _⟩

instance : OrderTop (SimpleGraph α) where
  top := SimpleGraph.topGraph
  le_top G := ⟨Set.subset_univ _, fun e he => G.loopless e he⟩

private def DiGraph.bottomGraph : DiGraph α β where
  vertexSet := ∅
  edgeSet := ∅
  source_mem := by simp
  target_mem := by simp

private def DiGraph.infGraph (G H : DiGraph α β) : DiGraph α β where
  vertexSet := V(G) ∩ V(H)
  edgeSet := E(G) ∩ E(H)
  source_mem := by
    rintro a ⟨haG, haH⟩
    exact ⟨G.source_mem a haG, H.source_mem a haH⟩
  target_mem := by
    rintro a ⟨haG, haH⟩
    exact ⟨G.target_mem a haG, H.target_mem a haH⟩

private def DiGraph.supGraph (G H : DiGraph α β) : DiGraph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  source_mem := by
    rintro a (haG | haH)
    · exact Or.inl (G.source_mem a haG)
    · exact Or.inr (H.source_mem a haH)
  target_mem := by
    rintro a (haG | haH)
    · exact Or.inl (G.target_mem a haG)
    · exact Or.inr (H.target_mem a haH)

private def DiGraph.topGraph : DiGraph α β where
  vertexSet := Set.univ
  edgeSet := Set.univ
  source_mem := by simp
  target_mem := by simp

instance : SemilatticeInf (DiGraph α β) where
  inf := DiGraph.infGraph
  inf_le_left _ _ := ⟨Set.inter_subset_left, Set.inter_subset_left⟩
  inf_le_right _ _ := ⟨Set.inter_subset_right, Set.inter_subset_right⟩
  le_inf _ _ _ hG hH := ⟨fun _ hv => ⟨hG.vertexSet_subset hv, hH.vertexSet_subset hv⟩,
    fun _ he => ⟨hG.edgeSet_subset he, hH.edgeSet_subset he⟩⟩

instance : SemilatticeSup (DiGraph α β) where
  sup := DiGraph.supGraph
  le_sup_left _ _ := ⟨Set.subset_union_left, Set.subset_union_left⟩
  le_sup_right _ _ := ⟨Set.subset_union_right, Set.subset_union_right⟩
  sup_le _ _ _ hG hH := ⟨fun _ hv => by
      rcases hv with hv | hv
      · exact hG.vertexSet_subset hv
      · exact hH.vertexSet_subset hv,
    fun _ he => by
      rcases he with he | he
      · exact hG.edgeSet_subset he
      · exact hH.edgeSet_subset he⟩

instance : Lattice (DiGraph α β) where

instance : OrderBot (DiGraph α β) where
  bot := DiGraph.bottomGraph
  bot_le _ := ⟨Set.empty_subset _, Set.empty_subset _⟩

instance : OrderTop (DiGraph α β) where
  top := DiGraph.topGraph
  le_top _ := ⟨Set.subset_univ _, Set.subset_univ _⟩

private def SimpleDiGraph.bottomGraph : SimpleDiGraph α where
  vertexSet := ∅
  edgeSet := ∅
  source_mem := by simp
  target_mem := by simp
  loopless := by simp

private def SimpleDiGraph.infGraph (G H : SimpleDiGraph α) : SimpleDiGraph α where
  vertexSet := V(G) ∩ V(H)
  edgeSet := E(G) ∩ E(H)
  source_mem := by
    rintro a ⟨haG, haH⟩
    exact ⟨G.source_mem a haG, H.source_mem a haH⟩
  target_mem := by
    rintro a ⟨haG, haH⟩
    exact ⟨G.target_mem a haG, H.target_mem a haH⟩
  loopless := by
    rintro a ⟨haG, _⟩
    exact G.loopless a haG

private def SimpleDiGraph.supGraph (G H : SimpleDiGraph α) : SimpleDiGraph α where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  source_mem := by
    rintro a (haG | haH)
    · exact Or.inl (G.source_mem a haG)
    · exact Or.inr (H.source_mem a haH)
  target_mem := by
    rintro a (haG | haH)
    · exact Or.inl (G.target_mem a haG)
    · exact Or.inr (H.target_mem a haH)
  loopless := by
    rintro a (haG | haH)
    · exact G.loopless a haG
    · exact H.loopless a haH

private def SimpleDiGraph.topGraph : SimpleDiGraph α where
  vertexSet := Set.univ
  edgeSet := {a | a.1 ≠ a.2}
  source_mem := by simp
  target_mem := by simp
  loopless := by simp

instance : SemilatticeInf (SimpleDiGraph α) where
  inf := SimpleDiGraph.infGraph
  inf_le_left _ _ := ⟨Set.inter_subset_left, Set.inter_subset_left⟩
  inf_le_right _ _ := ⟨Set.inter_subset_right, Set.inter_subset_right⟩
  le_inf _ _ _ hG hH := ⟨fun _ hv => ⟨hG.vertexSet_subset hv, hH.vertexSet_subset hv⟩,
    fun _ he => ⟨hG.edgeSet_subset he, hH.edgeSet_subset he⟩⟩

instance : SemilatticeSup (SimpleDiGraph α) where
  sup := SimpleDiGraph.supGraph
  le_sup_left _ _ := ⟨Set.subset_union_left, Set.subset_union_left⟩
  le_sup_right _ _ := ⟨Set.subset_union_right, Set.subset_union_right⟩
  sup_le _ _ _ hG hH := ⟨fun _ hv => by
      rcases hv with hv | hv
      · exact hG.vertexSet_subset hv
      · exact hH.vertexSet_subset hv,
    fun _ he => by
      rcases he with he | he
      · exact hG.edgeSet_subset he
      · exact hH.edgeSet_subset he⟩

instance : Lattice (SimpleDiGraph α) where

instance : OrderBot (SimpleDiGraph α) where
  bot := SimpleDiGraph.bottomGraph
  bot_le _ := ⟨Set.empty_subset _, Set.empty_subset _⟩

instance : OrderTop (SimpleDiGraph α) where
  top := SimpleDiGraph.topGraph
  le_top G := ⟨Set.subset_univ _, fun a ha => G.loopless a ha⟩

/-! ### Lattice carrier formulas -/

namespace Graph

@[simp] theorem vertexSet_bot : V((⊥ : Graph α β)) = ∅ := rfl
@[simp] theorem edgeSet_bot : E((⊥ : Graph α β)) = ∅ := rfl
@[simp] theorem vertexSet_top : V((⊤ : Graph α β)) = Set.univ := rfl
@[simp] theorem edgeSet_top : E((⊤ : Graph α β)) = Set.univ := rfl
@[simp] theorem vertexSet_inf (G H : Graph α β) : V(G ⊓ H) = V(G) ∩ V(H) := rfl
@[simp] theorem edgeSet_inf (G H : Graph α β) : E(G ⊓ H) = E(G) ∩ E(H) := rfl
@[simp] theorem vertexSet_sup (G H : Graph α β) : V(G ⊔ H) = V(G) ∪ V(H) := rfl
@[simp] theorem edgeSet_sup (G H : Graph α β) : E(G ⊔ H) = E(G) ∪ E(H) := rfl

end Graph

namespace SimpleGraph

@[simp] theorem vertexSet_bot : V((⊥ : SimpleGraph α)) = ∅ := rfl
@[simp] theorem edgeSet_bot : E((⊥ : SimpleGraph α)) = ∅ := rfl
@[simp] theorem vertexSet_top : V((⊤ : SimpleGraph α)) = Set.univ := rfl
@[simp] theorem edgeSet_top : E((⊤ : SimpleGraph α)) = {e | ¬ e.IsDiag} := rfl
@[simp] theorem vertexSet_inf (G H : SimpleGraph α) : V(G ⊓ H) = V(G) ∩ V(H) := rfl
@[simp] theorem edgeSet_inf (G H : SimpleGraph α) : E(G ⊓ H) = E(G) ∩ E(H) := rfl
@[simp] theorem vertexSet_sup (G H : SimpleGraph α) : V(G ⊔ H) = V(G) ∪ V(H) := rfl
@[simp] theorem edgeSet_sup (G H : SimpleGraph α) : E(G ⊔ H) = E(G) ∪ E(H) := rfl

end SimpleGraph

namespace DiGraph

@[simp] theorem vertexSet_bot : V((⊥ : DiGraph α β)) = ∅ := rfl
@[simp] theorem edgeSet_bot : E((⊥ : DiGraph α β)) = ∅ := rfl
@[simp] theorem vertexSet_top : V((⊤ : DiGraph α β)) = Set.univ := rfl
@[simp] theorem edgeSet_top : E((⊤ : DiGraph α β)) = Set.univ := rfl
@[simp] theorem vertexSet_inf (G H : DiGraph α β) : V(G ⊓ H) = V(G) ∩ V(H) := rfl
@[simp] theorem edgeSet_inf (G H : DiGraph α β) : E(G ⊓ H) = E(G) ∩ E(H) := rfl
@[simp] theorem vertexSet_sup (G H : DiGraph α β) : V(G ⊔ H) = V(G) ∪ V(H) := rfl
@[simp] theorem edgeSet_sup (G H : DiGraph α β) : E(G ⊔ H) = E(G) ∪ E(H) := rfl

end DiGraph

namespace SimpleDiGraph

@[simp] theorem vertexSet_bot : V((⊥ : SimpleDiGraph α)) = ∅ := rfl
@[simp] theorem edgeSet_bot : E((⊥ : SimpleDiGraph α)) = ∅ := rfl
@[simp] theorem vertexSet_top : V((⊤ : SimpleDiGraph α)) = Set.univ := rfl
@[simp] theorem edgeSet_top : E((⊤ : SimpleDiGraph α)) = {a | a.1 ≠ a.2} := rfl
@[simp] theorem vertexSet_inf (G H : SimpleDiGraph α) : V(G ⊓ H) = V(G) ∩ V(H) := rfl
@[simp] theorem edgeSet_inf (G H : SimpleDiGraph α) : E(G ⊓ H) = E(G) ∩ E(H) := rfl
@[simp] theorem vertexSet_sup (G H : SimpleDiGraph α) : V(G ⊔ H) = V(G) ∪ V(H) := rfl
@[simp] theorem edgeSet_sup (G H : SimpleDiGraph α) : E(G ⊔ H) = E(G) ∪ E(H) := rfl

end SimpleDiGraph

/-! ## Spanning and induced subgraphs -/

/-- `H ≤s G` means that `H` is a subgraph of `G` with the same vertex set. -/
structure Graph.IsSpanningSubgraph (H G : Graph α β) : Prop extends le : H ≤ G where
  /-- A spanning subgraph has exactly the ambient vertex set. -/
  vertexSet_eq : V(H) = V(G)

/-- `H ≤s G` means that `H` is a subgraph of `G` with the same vertex set. -/
structure SimpleGraph.IsSpanningSubgraph (H G : SimpleGraph α) : Prop extends le : H ≤ G where
  /-- A spanning subgraph has exactly the ambient vertex set. -/
  vertexSet_eq : V(H) = V(G)

/-- `H ≤s G` means that `H` is a subgraph of `G` with the same vertex set. -/
structure DiGraph.IsSpanningSubgraph (H G : DiGraph α β) : Prop extends le : H ≤ G where
  /-- A spanning subgraph has exactly the ambient vertex set. -/
  vertexSet_eq : V(H) = V(G)

/-- `H ≤s G` means that `H` is a subgraph of `G` with the same vertex set. -/
structure SimpleDiGraph.IsSpanningSubgraph (H G : SimpleDiGraph α) : Prop extends le : H ≤ G where
  /-- A spanning subgraph has exactly the ambient vertex set. -/
  vertexSet_eq : V(H) = V(G)

scoped infixl:50 " ≤s " => Graph.IsSpanningSubgraph
scoped infixl:50 " ≤s " => SimpleGraph.IsSpanningSubgraph
scoped infixl:50 " ≤s " => DiGraph.IsSpanningSubgraph
scoped infixl:50 " ≤s " => SimpleDiGraph.IsSpanningSubgraph

/-- `H ≤i G` means that `H` retains every actual edge of `G` whose endpoints are vertices of
`H`. -/
structure Graph.IsInducedSubgraph (H G : Graph α β) : Prop extends le : H ≤ G where
  /-- Every ambient bundled edge linking two retained vertices is retained. -/
  isLink_of_mem_mem : ∀ {e u v}, G.IsLink e u v → u ∈ V(H) → v ∈ V(H) → H.IsLink e u v

/-- `H ≤i G` means that `H` retains every actual edge of `G` whose endpoints are vertices of
`H`. -/
structure SimpleGraph.IsInducedSubgraph (H G : SimpleGraph α) : Prop extends le : H ≤ G where
  /-- Every ambient edge linking two retained vertices is retained. -/
  isLink_of_mem_mem : ∀ {e u v}, G.IsLink e u v → u ∈ V(H) → v ∈ V(H) → H.IsLink e u v

/-- `H ≤i G` means that `H` retains every actual arc of `G` whose source and target are
vertices of `H`. -/
structure DiGraph.IsInducedSubgraph (H G : DiGraph α β) : Prop extends le : H ≤ G where
  /-- Every ambient bundled arc between retained vertices is retained. -/
  isArc_of_mem_mem : ∀ {a u v}, G.IsArc a u v → u ∈ V(H) → v ∈ V(H) → H.IsArc a u v

/-- `H ≤i G` means that `H` retains every actual arc of `G` whose source and target are
vertices of `H`. -/
structure SimpleDiGraph.IsInducedSubgraph (H G : SimpleDiGraph α) : Prop extends le : H ≤ G where
  /-- Every ambient arc between retained vertices is retained. -/
  isArc_of_mem_mem : ∀ {a u v}, G.IsArc a u v → u ∈ V(H) → v ∈ V(H) → H.IsArc a u v

scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph
scoped infixl:50 " ≤i " => SimpleGraph.IsInducedSubgraph
scoped infixl:50 " ≤i " => DiGraph.IsInducedSubgraph
scoped infixl:50 " ≤i " => SimpleDiGraph.IsInducedSubgraph

namespace Graph.IsSpanningSubgraph

@[simp] protected theorem rfl (G : Graph α β) : G ≤s G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, rfl⟩

protected theorem trans {G H K : Graph α β} (hGH : G ≤s H) (hHK : H ≤s K) : G ≤s K :=
  ⟨hGH.le.trans hHK.le, hGH.vertexSet_eq.trans hHK.vertexSet_eq⟩

end Graph.IsSpanningSubgraph

namespace SimpleGraph.IsSpanningSubgraph

@[simp] protected theorem rfl (G : SimpleGraph α) : G ≤s G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, rfl⟩

protected theorem trans {G H K : SimpleGraph α} (hGH : G ≤s H)
    (hHK : H ≤s K) : G ≤s K :=
  ⟨hGH.le.trans hHK.le, hGH.vertexSet_eq.trans hHK.vertexSet_eq⟩

end SimpleGraph.IsSpanningSubgraph

namespace DiGraph.IsSpanningSubgraph

@[simp] protected theorem rfl (G : DiGraph α β) : G ≤s G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, rfl⟩

protected theorem trans {G H K : DiGraph α β} (hGH : G ≤s H) (hHK : H ≤s K) : G ≤s K :=
  ⟨hGH.le.trans hHK.le, hGH.vertexSet_eq.trans hHK.vertexSet_eq⟩

end DiGraph.IsSpanningSubgraph

namespace SimpleDiGraph.IsSpanningSubgraph

@[simp] protected theorem rfl (G : SimpleDiGraph α) : G ≤s G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, rfl⟩

protected theorem trans {G H K : SimpleDiGraph α} (hGH : G ≤s H)
    (hHK : H ≤s K) : G ≤s K :=
  ⟨hGH.le.trans hHK.le, hGH.vertexSet_eq.trans hHK.vertexSet_eq⟩

end SimpleDiGraph.IsSpanningSubgraph

namespace Graph.IsInducedSubgraph

@[simp] protected theorem rfl (G : Graph α β) : G ≤i G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, fun h _ _ => h⟩

protected theorem trans {G H K : Graph α β} (hGH : G ≤i H) (hHK : H ≤i K) : G ≤i K :=
  ⟨hGH.le.trans hHK.le, fun h hu hv => hGH.isLink_of_mem_mem
    (hHK.isLink_of_mem_mem h (hGH.le.vertexSet_subset hu) (hGH.le.vertexSet_subset hv)) hu hv⟩

theorem isLink_congr {H G : Graph α β} (hHG : H ≤i G) {e u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.IsLink e u v ↔ G.IsLink e u v :=
  ⟨hHG.le.isLink, fun h => hHG.isLink_of_mem_mem h hu hv⟩

theorem adj_congr {H G : Graph α β} (hHG : H ≤i G) {u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.Adj u v ↔ G.Adj u v := by
  constructor
  · exact hHG.le.adj
  · rintro ⟨e, he⟩
    exact ⟨e, hHG.isLink_of_mem_mem he hu hv⟩

end Graph.IsInducedSubgraph

namespace SimpleGraph.IsInducedSubgraph

@[simp] protected theorem rfl (G : SimpleGraph α) : G ≤i G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, fun h _ _ => h⟩

protected theorem trans {G H K : SimpleGraph α} (hGH : G ≤i H)
    (hHK : H ≤i K) : G ≤i K :=
  ⟨hGH.le.trans hHK.le, fun h hu hv => hGH.isLink_of_mem_mem
    (hHK.isLink_of_mem_mem h (hGH.le.vertexSet_subset hu) (hGH.le.vertexSet_subset hv)) hu hv⟩

theorem isLink_congr {H G : SimpleGraph α} (hHG : H ≤i G) {e u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.IsLink e u v ↔ G.IsLink e u v :=
  ⟨hHG.le.isLink, fun h => hHG.isLink_of_mem_mem h hu hv⟩

theorem adj_congr {H G : SimpleGraph α} (hHG : H ≤i G) {u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.Adj u v ↔ G.Adj u v := by
  constructor
  · exact hHG.le.adj
  · rintro ⟨e, he⟩
    exact ⟨e, hHG.isLink_of_mem_mem he hu hv⟩

end SimpleGraph.IsInducedSubgraph

namespace DiGraph.IsInducedSubgraph

@[simp] protected theorem rfl (G : DiGraph α β) : G ≤i G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, fun h _ _ => h⟩

protected theorem trans {G H K : DiGraph α β} (hGH : G ≤i H) (hHK : H ≤i K) : G ≤i K :=
  ⟨hGH.le.trans hHK.le, fun h hu hv => hGH.isArc_of_mem_mem
    (hHK.isArc_of_mem_mem h (hGH.le.vertexSet_subset hu) (hGH.le.vertexSet_subset hv)) hu hv⟩

theorem isArc_congr {H G : DiGraph α β} (hHG : H ≤i G) {a u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.IsArc a u v ↔ G.IsArc a u v :=
  ⟨hHG.le.isArc, fun h => hHG.isArc_of_mem_mem h hu hv⟩

theorem adj_congr {H G : DiGraph α β} (hHG : H ≤i G) {u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.Adj u v ↔ G.Adj u v := by
  constructor
  · exact hHG.le.adj
  · rintro ⟨a, ha⟩
    exact ⟨a, hHG.isArc_of_mem_mem ha hu hv⟩

end DiGraph.IsInducedSubgraph

namespace SimpleDiGraph.IsInducedSubgraph

@[simp] protected theorem rfl (G : SimpleDiGraph α) : G ≤i G :=
  ⟨⟨fun _ h => h, fun _ h => h⟩, fun h _ _ => h⟩

protected theorem trans {G H K : SimpleDiGraph α} (hGH : G ≤i H)
    (hHK : H ≤i K) : G ≤i K :=
  ⟨hGH.le.trans hHK.le, fun h hu hv => hGH.isArc_of_mem_mem
    (hHK.isArc_of_mem_mem h (hGH.le.vertexSet_subset hu) (hGH.le.vertexSet_subset hv)) hu hv⟩

theorem isArc_congr {H G : SimpleDiGraph α} (hHG : H ≤i G) {a u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.IsArc a u v ↔ G.IsArc a u v :=
  ⟨hHG.le.isArc, fun h => hHG.isArc_of_mem_mem h hu hv⟩

theorem adj_congr {H G : SimpleDiGraph α} (hHG : H ≤i G) {u v}
    (hu : u ∈ V(H)) (hv : v ∈ V(H)) : H.Adj u v ↔ G.Adj u v := by
  constructor
  · exact hHG.le.adj
  · rintro ⟨a, ha⟩
    exact ⟨a, hHG.isArc_of_mem_mem ha hu hv⟩

end SimpleDiGraph.IsInducedSubgraph

/-! ## Induced restrictions -/

/-- The subgraph induced by `S`, retaining the ambient vertex and tag types. -/
def Graph.induce (G : Graph α β) (S : Set α) : Graph α β where
  vertexSet := S ∩ V(G)
  edgeSet := {e ∈ E(G) | ∀ v ∈ e.endpoints, v ∈ S}
  endpoints_mem := by
    rintro e ⟨he, hS⟩ v hv
    exact ⟨hS v hv, G.endpoints_mem e he v hv⟩

/-- The simple subgraph induced by `S`, retaining the ambient vertex type. -/
def SimpleGraph.induce (G : SimpleGraph α) (S : Set α) : SimpleGraph α where
  vertexSet := S ∩ V(G)
  edgeSet := {e ∈ E(G) | ∀ v ∈ e, v ∈ S}
  endpoints_mem := by
    rintro e ⟨he, hS⟩ v hv
    exact ⟨hS v hv, G.endpoints_mem e he v hv⟩
  loopless := by
    rintro e ⟨he, _⟩
    exact G.loopless e he

/-- The directed subgraph induced by `S`, retaining the ambient vertex and tag types. -/
def DiGraph.induce (G : DiGraph α β) (S : Set α) : DiGraph α β where
  vertexSet := S ∩ V(G)
  edgeSet := {a ∈ E(G) | a.source ∈ S ∧ a.target ∈ S}
  source_mem := by rintro a ⟨ha, hs, _⟩; exact ⟨hs, G.source_mem a ha⟩
  target_mem := by rintro a ⟨ha, _, ht⟩; exact ⟨ht, G.target_mem a ha⟩

/-- The simple directed subgraph induced by `S`, retaining the ambient vertex type. -/
def SimpleDiGraph.induce (G : SimpleDiGraph α) (S : Set α) : SimpleDiGraph α where
  vertexSet := S ∩ V(G)
  edgeSet := {a ∈ E(G) | a.1 ∈ S ∧ a.2 ∈ S}
  source_mem := by rintro a ⟨ha, hs, _⟩; exact ⟨hs, G.source_mem a ha⟩
  target_mem := by rintro a ⟨ha, _, ht⟩; exact ⟨ht, G.target_mem a ha⟩
  loopless := by rintro a ⟨ha, _, _⟩; exact G.loopless a ha

namespace Graph

@[simp] theorem vertexSet_induce (G : Graph α β) (S : Set α) :
    V(G.induce S) = S ∩ V(G) := rfl

@[simp] theorem edgeSet_induce (G : Graph α β) (S : Set α) :
    E(G.induce S) = {e ∈ E(G) | ∀ v ∈ e.endpoints, v ∈ S} := rfl

@[simp] theorem mem_vertexSet_induce (G : Graph α β) (S : Set α) (v : α) :
    v ∈ V(G.induce S) ↔ v ∈ S ∧ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_induce (G : Graph α β) (S : Set α) (e : Edge α β) :
    e ∈ E(G.induce S) ↔ e ∈ E(G) ∧ ∀ v ∈ e.endpoints, v ∈ S := Iff.rfl

@[simp] theorem induce_isLink (G : Graph α β) (S : Set α) (e : Edge α β) (u v : α) :
    (G.induce S).IsLink e u v ↔ G.IsLink e u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [Graph.IsLink, mem_edgeSet_induce]
  constructor
  · rintro ⟨⟨he, hS⟩, huv⟩
    refine ⟨⟨he, huv⟩, hS u ?_, hS v ?_⟩ <;> rw [huv] <;> simp
  · rintro ⟨⟨he, huv⟩, hu, hv⟩
    refine ⟨⟨he, ?_⟩, huv⟩
    intro w hw
    rw [huv] at hw
    rcases (Sym2.mem_iff.mp hw) with rfl | rfl
    · exact hu
    · exact hv

@[simp] theorem induce_inc (G : Graph α β) (S : Set α) (e : Edge α β) (v : α) :
    (G.induce S).Inc e v ↔ G.Inc e v ∧ ∀ w ∈ e.endpoints, w ∈ S := by
  simp only [Graph.Inc, mem_edgeSet_induce]
  tauto

@[simp] theorem induce_adj (G : Graph α β) (S : Set α) (u v : α) :
    (G.induce S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [Graph.adj_iff_exists_isLink, induce_isLink]
  constructor
  · rintro ⟨e, he, hu, hv⟩
    exact ⟨⟨e, he⟩, hu, hv⟩
  · rintro ⟨⟨e, he⟩, hu, hv⟩
    exact ⟨e, he, hu, hv⟩

@[simp] theorem induce_le (G : Graph α β) (S : Set α) : G.induce S ≤ G :=
  ⟨fun _ h => h.2, fun _ h => h.1⟩

/-- An induced restriction retains every ambient actual edge whose endpoints survive. -/
theorem induce_isInducedSubgraph (G : Graph α β) (S : Set α) : G.induce S ≤i G :=
  ⟨G.induce_le S, fun h hu hv => (G.induce_isLink S _ _ _).2 ⟨h, hu.1, hv.1⟩⟩

/-- A graph lies below an induced restriction exactly when it lies below the source graph and
all its vertices belong to the inducing set. -/
theorem induce_le_iff (H G : Graph α β) (S : Set α) :
    H ≤ G.induce S ↔ H ≤ G ∧ V(H) ⊆ S := by
  constructor
  · intro h
    exact ⟨h.trans (G.induce_le S), fun _ hv => (h.vertexSet_subset hv).1⟩
  · rintro ⟨hHG, hS⟩
    refine ⟨fun v hv => ⟨hS hv, hHG.vertexSet_subset hv⟩, fun e he => ⟨hHG.edgeSet_subset he, ?_⟩⟩
    intro v hv
    exact hS (H.endpoints_mem e he v hv)

theorem induce_mono {G H : Graph α β} {S T : Set α} (hGH : G ≤ H) (hST : S ⊆ T) :
    G.induce S ≤ H.induce T :=
  ⟨fun _ h => ⟨hST h.1, hGH.vertexSet_subset h.2⟩,
    fun _ h => ⟨hGH.edgeSet_subset h.1, fun v hv => hST (h.2 v hv)⟩⟩

theorem induce_mono_left {G H : Graph α β} (hGH : G ≤ H) (S : Set α) :
    G.induce S ≤ H.induce S := induce_mono hGH (fun _ h => h)

theorem induce_mono_right (G : Graph α β) {S T : Set α} (hST : S ⊆ T) :
    G.induce S ≤ G.induce T := induce_mono le_rfl hST

@[simp] theorem induce_empty (G : Graph α β) : G.induce ∅ = ⊥ := by
  apply Graph.ext
  · simp
  · ext e
    simp only [mem_edgeSet_induce, Set.mem_empty_iff_false, edgeSet_bot, iff_false]
    rintro ⟨_, h⟩
    exact h e.endpoints.out.1 (Sym2.out_fst_mem e.endpoints)

@[simp] theorem induce_univ (G : Graph α β) : G.induce Set.univ = G := by
  apply Graph.ext
  · simp
  · ext e
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by simp⟩

@[simp] theorem induce_vertexSet (G : Graph α β) : G.induce V(G) = G := by
  apply Graph.ext
  · simp
  · ext e
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, G.endpoints_mem e h⟩

@[simp] theorem induce_induce (G : Graph α β) (S T : Set α) :
    (G.induce S).induce T = G.induce (S ∩ T) := by
  apply Graph.ext
  · ext v
    simp only [mem_vertexSet_induce, Set.mem_inter_iff]
    tauto
  · ext e
    simp only [mem_edgeSet_induce, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨he, hS⟩, hT⟩
      exact ⟨he, fun v hv => ⟨hS v hv, hT v hv⟩⟩
    · rintro ⟨he, hST⟩
      exact ⟨⟨he, fun v hv => (hST v hv).1⟩, fun v hv => (hST v hv).2⟩

@[simp] theorem induce_idem (G : Graph α β) (S : Set α) :
    (G.induce S).induce S = G.induce S := by simp

end Graph

namespace SimpleGraph

@[simp] theorem vertexSet_induce (G : SimpleGraph α) (S : Set α) :
    V(G.induce S) = S ∩ V(G) := rfl

@[simp] theorem edgeSet_induce (G : SimpleGraph α) (S : Set α) :
    E(G.induce S) = {e ∈ E(G) | ∀ v ∈ e, v ∈ S} := rfl

@[simp] theorem mem_vertexSet_induce (G : SimpleGraph α) (S : Set α) (v : α) :
    v ∈ V(G.induce S) ↔ v ∈ S ∧ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_induce (G : SimpleGraph α) (S : Set α) (e : Sym2 α) :
    e ∈ E(G.induce S) ↔ e ∈ E(G) ∧ ∀ v ∈ e, v ∈ S := Iff.rfl

@[simp] theorem induce_isLink (G : SimpleGraph α) (S : Set α) (e : Sym2 α) (u v : α) :
    (G.induce S).IsLink e u v ↔ G.IsLink e u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [SimpleGraph.IsLink, mem_edgeSet_induce]
  constructor
  · rintro ⟨⟨he, hS⟩, huv⟩
    refine ⟨⟨he, huv⟩, hS u ?_, hS v ?_⟩ <;> rw [huv] <;> simp
  · rintro ⟨⟨he, huv⟩, hu, hv⟩
    refine ⟨⟨he, ?_⟩, huv⟩
    intro w hw
    rw [huv] at hw
    rcases (Sym2.mem_iff.mp hw) with rfl | rfl
    · exact hu
    · exact hv

@[simp] theorem induce_inc (G : SimpleGraph α) (S : Set α) (e : Sym2 α) (v : α) :
    (G.induce S).Inc e v ↔ G.Inc e v ∧ ∀ w ∈ e, w ∈ S := by
  simp only [SimpleGraph.Inc, mem_edgeSet_induce]
  tauto

@[simp] theorem induce_adj (G : SimpleGraph α) (S : Set α) (u v : α) :
    (G.induce S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [SimpleGraph.adj_iff_exists_isLink, induce_isLink]
  constructor
  · rintro ⟨e, he, hu, hv⟩
    exact ⟨⟨e, he⟩, hu, hv⟩
  · rintro ⟨⟨e, he⟩, hu, hv⟩
    exact ⟨e, he, hu, hv⟩

@[simp] theorem induce_le (G : SimpleGraph α) (S : Set α) : G.induce S ≤ G :=
  ⟨fun _ h => h.2, fun _ h => h.1⟩

/-- An induced restriction retains every ambient actual edge whose endpoints survive. -/
theorem induce_isInducedSubgraph (G : SimpleGraph α) (S : Set α) : G.induce S ≤i G :=
  ⟨G.induce_le S, fun h hu hv => (G.induce_isLink S _ _ _).2 ⟨h, hu.1, hv.1⟩⟩

/-- A graph lies below an induced restriction exactly when it lies below the source graph and
all its vertices belong to the inducing set. -/
theorem induce_le_iff (H G : SimpleGraph α) (S : Set α) :
    H ≤ G.induce S ↔ H ≤ G ∧ V(H) ⊆ S := by
  constructor
  · intro h
    exact ⟨h.trans (G.induce_le S), fun _ hv => (h.vertexSet_subset hv).1⟩
  · rintro ⟨hHG, hS⟩
    refine ⟨fun v hv => ⟨hS hv, hHG.vertexSet_subset hv⟩, fun e he => ⟨hHG.edgeSet_subset he, ?_⟩⟩
    intro v hv
    exact hS (H.endpoints_mem e he v hv)

theorem induce_mono {G H : SimpleGraph α} {S T : Set α} (hGH : G ≤ H) (hST : S ⊆ T) :
    G.induce S ≤ H.induce T :=
  ⟨fun _ h => ⟨hST h.1, hGH.vertexSet_subset h.2⟩,
    fun _ h => ⟨hGH.edgeSet_subset h.1, fun v hv => hST (h.2 v hv)⟩⟩

theorem induce_mono_left {G H : SimpleGraph α} (hGH : G ≤ H) (S : Set α) :
    G.induce S ≤ H.induce S := induce_mono hGH (fun _ h => h)

theorem induce_mono_right (G : SimpleGraph α) {S T : Set α} (hST : S ⊆ T) :
    G.induce S ≤ G.induce T := induce_mono le_rfl hST

@[simp] theorem induce_empty (G : SimpleGraph α) : G.induce ∅ = ⊥ := by
  apply SimpleGraph.ext
  · simp
  · ext e
    simp only [mem_edgeSet_induce, Set.mem_empty_iff_false, edgeSet_bot, iff_false]
    rintro ⟨_, h⟩
    exact h e.out.1 (Sym2.out_fst_mem e)

@[simp] theorem induce_univ (G : SimpleGraph α) : G.induce Set.univ = G := by
  apply SimpleGraph.ext
  · simp
  · ext e
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by simp⟩

@[simp] theorem induce_vertexSet (G : SimpleGraph α) : G.induce V(G) = G := by
  apply SimpleGraph.ext
  · simp
  · ext e
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, G.endpoints_mem e h⟩

@[simp] theorem induce_induce (G : SimpleGraph α) (S T : Set α) :
    (G.induce S).induce T = G.induce (S ∩ T) := by
  apply SimpleGraph.ext
  · ext v
    simp only [mem_vertexSet_induce, Set.mem_inter_iff]
    tauto
  · ext e
    simp only [mem_edgeSet_induce, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨he, hS⟩, hT⟩
      exact ⟨he, fun v hv => ⟨hS v hv, hT v hv⟩⟩
    · rintro ⟨he, hST⟩
      exact ⟨⟨he, fun v hv => (hST v hv).1⟩, fun v hv => (hST v hv).2⟩

@[simp] theorem induce_idem (G : SimpleGraph α) (S : Set α) :
    (G.induce S).induce S = G.induce S := by simp

end SimpleGraph

namespace DiGraph

@[simp] theorem vertexSet_induce (G : DiGraph α β) (S : Set α) :
    V(G.induce S) = S ∩ V(G) := rfl

@[simp] theorem edgeSet_induce (G : DiGraph α β) (S : Set α) :
    E(G.induce S) = {a ∈ E(G) | a.source ∈ S ∧ a.target ∈ S} := rfl

@[simp] theorem mem_vertexSet_induce (G : DiGraph α β) (S : Set α) (v : α) :
    v ∈ V(G.induce S) ↔ v ∈ S ∧ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_induce (G : DiGraph α β) (S : Set α) (a : Arc α β) :
    a ∈ E(G.induce S) ↔ a ∈ E(G) ∧ a.source ∈ S ∧ a.target ∈ S := Iff.rfl

@[simp] theorem induce_isArc (G : DiGraph α β) (S : Set α) (a : Arc α β) (u v : α) :
    (G.induce S).IsArc a u v ↔ G.IsArc a u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [DiGraph.IsArc, mem_edgeSet_induce]
  constructor
  · rintro ⟨⟨ha, hs, ht⟩, hu, hv⟩
    exact ⟨⟨ha, hu, hv⟩, hu ▸ hs, hv ▸ ht⟩
  · rintro ⟨⟨ha, hu, hv⟩, hs, ht⟩
    exact ⟨⟨ha, hu ▸ hs, hv ▸ ht⟩, hu, hv⟩

@[simp] theorem induce_inc (G : DiGraph α β) (S : Set α) (a : Arc α β) (v : α) :
    (G.induce S).Inc a v ↔ G.Inc a v ∧ a.source ∈ S ∧ a.target ∈ S := by
  simp only [DiGraph.Inc, mem_edgeSet_induce]
  tauto

@[simp] theorem induce_adj (G : DiGraph α β) (S : Set α) (u v : α) :
    (G.induce S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [DiGraph.adj_iff_exists_isArc, induce_isArc]
  constructor
  · rintro ⟨a, ha, hu, hv⟩
    exact ⟨⟨a, ha⟩, hu, hv⟩
  · rintro ⟨⟨a, ha⟩, hu, hv⟩
    exact ⟨a, ha, hu, hv⟩

@[simp] theorem induce_le (G : DiGraph α β) (S : Set α) : G.induce S ≤ G :=
  ⟨fun _ h => h.2, fun _ h => h.1⟩

/-- An induced restriction retains every ambient actual arc whose source and target survive. -/
theorem induce_isInducedSubgraph (G : DiGraph α β) (S : Set α) : G.induce S ≤i G :=
  ⟨G.induce_le S, fun h hu hv => (G.induce_isArc S _ _ _).2 ⟨h, hu.1, hv.1⟩⟩

/-- A directed graph lies below an induced restriction exactly when it lies below the source
graph and all its vertices belong to the inducing set. -/
theorem induce_le_iff (H G : DiGraph α β) (S : Set α) :
    H ≤ G.induce S ↔ H ≤ G ∧ V(H) ⊆ S := by
  constructor
  · intro h
    exact ⟨h.trans (G.induce_le S), fun _ hv => (h.vertexSet_subset hv).1⟩
  · rintro ⟨hHG, hS⟩
    refine ⟨fun v hv => ⟨hS hv, hHG.vertexSet_subset hv⟩,
      fun a ha => ⟨hHG.edgeSet_subset ha, ?_, ?_⟩⟩
    · exact hS (H.source_mem a ha)
    · exact hS (H.target_mem a ha)

theorem induce_mono {G H : DiGraph α β} {S T : Set α} (hGH : G ≤ H) (hST : S ⊆ T) :
    G.induce S ≤ H.induce T :=
  ⟨fun _ h => ⟨hST h.1, hGH.vertexSet_subset h.2⟩,
    fun _ h => ⟨hGH.edgeSet_subset h.1, hST h.2.1, hST h.2.2⟩⟩

theorem induce_mono_left {G H : DiGraph α β} (hGH : G ≤ H) (S : Set α) :
    G.induce S ≤ H.induce S := induce_mono hGH (fun _ h => h)

theorem induce_mono_right (G : DiGraph α β) {S T : Set α} (hST : S ⊆ T) :
    G.induce S ≤ G.induce T := induce_mono le_rfl hST

@[simp] theorem induce_empty (G : DiGraph α β) : G.induce ∅ = ⊥ := by
  ext <;> simp

@[simp] theorem induce_univ (G : DiGraph α β) : G.induce Set.univ = G := by
  ext <;> simp

@[simp] theorem induce_vertexSet (G : DiGraph α β) : G.induce V(G) = G := by
  apply DiGraph.ext
  · simp
  · ext a
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, G.source_mem a h, G.target_mem a h⟩

@[simp] theorem induce_induce (G : DiGraph α β) (S T : Set α) :
    (G.induce S).induce T = G.induce (S ∩ T) := by
  ext <;> simp [and_assoc, and_left_comm, and_comm]

@[simp] theorem induce_idem (G : DiGraph α β) (S : Set α) :
    (G.induce S).induce S = G.induce S := by simp

end DiGraph

namespace SimpleDiGraph

@[simp] theorem vertexSet_induce (G : SimpleDiGraph α) (S : Set α) :
    V(G.induce S) = S ∩ V(G) := rfl

@[simp] theorem edgeSet_induce (G : SimpleDiGraph α) (S : Set α) :
    E(G.induce S) = {a ∈ E(G) | a.1 ∈ S ∧ a.2 ∈ S} := rfl

@[simp] theorem mem_vertexSet_induce (G : SimpleDiGraph α) (S : Set α) (v : α) :
    v ∈ V(G.induce S) ↔ v ∈ S ∧ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_induce (G : SimpleDiGraph α) (S : Set α) (a : α × α) :
    a ∈ E(G.induce S) ↔ a ∈ E(G) ∧ a.1 ∈ S ∧ a.2 ∈ S := Iff.rfl

@[simp] theorem induce_isArc (G : SimpleDiGraph α) (S : Set α) (a : α × α) (u v : α) :
    (G.induce S).IsArc a u v ↔ G.IsArc a u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [SimpleDiGraph.IsArc, mem_edgeSet_induce]
  constructor
  · rintro ⟨⟨ha, hs, ht⟩, hu, hv⟩
    exact ⟨⟨ha, hu, hv⟩, hu ▸ hs, hv ▸ ht⟩
  · rintro ⟨⟨ha, hu, hv⟩, hs, ht⟩
    exact ⟨⟨ha, hu ▸ hs, hv ▸ ht⟩, hu, hv⟩

@[simp] theorem induce_inc (G : SimpleDiGraph α) (S : Set α) (a : α × α) (v : α) :
    (G.induce S).Inc a v ↔ G.Inc a v ∧ a.1 ∈ S ∧ a.2 ∈ S := by
  simp only [SimpleDiGraph.Inc, mem_edgeSet_induce]
  tauto

@[simp] theorem induce_adj (G : SimpleDiGraph α) (S : Set α) (u v : α) :
    (G.induce S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [SimpleDiGraph.adj_iff_exists_isArc, induce_isArc]
  constructor
  · rintro ⟨a, ha, hu, hv⟩
    exact ⟨⟨a, ha⟩, hu, hv⟩
  · rintro ⟨⟨a, ha⟩, hu, hv⟩
    exact ⟨a, ha, hu, hv⟩

@[simp] theorem induce_le (G : SimpleDiGraph α) (S : Set α) : G.induce S ≤ G :=
  ⟨fun _ h => h.2, fun _ h => h.1⟩

/-- An induced restriction retains every ambient actual arc whose source and target survive. -/
theorem induce_isInducedSubgraph (G : SimpleDiGraph α) (S : Set α) : G.induce S ≤i G :=
  ⟨G.induce_le S, fun h hu hv => (G.induce_isArc S _ _ _).2 ⟨h, hu.1, hv.1⟩⟩

/-- A directed graph lies below an induced restriction exactly when it lies below the source
graph and all its vertices belong to the inducing set. -/
theorem induce_le_iff (H G : SimpleDiGraph α) (S : Set α) :
    H ≤ G.induce S ↔ H ≤ G ∧ V(H) ⊆ S := by
  constructor
  · intro h
    exact ⟨h.trans (G.induce_le S), fun _ hv => (h.vertexSet_subset hv).1⟩
  · rintro ⟨hHG, hS⟩
    refine ⟨fun v hv => ⟨hS hv, hHG.vertexSet_subset hv⟩,
      fun a ha => ⟨hHG.edgeSet_subset ha, ?_, ?_⟩⟩
    · exact hS (H.source_mem a ha)
    · exact hS (H.target_mem a ha)

theorem induce_mono {G H : SimpleDiGraph α} {S T : Set α} (hGH : G ≤ H) (hST : S ⊆ T) :
    G.induce S ≤ H.induce T :=
  ⟨fun _ h => ⟨hST h.1, hGH.vertexSet_subset h.2⟩,
    fun _ h => ⟨hGH.edgeSet_subset h.1, hST h.2.1, hST h.2.2⟩⟩

theorem induce_mono_left {G H : SimpleDiGraph α} (hGH : G ≤ H) (S : Set α) :
    G.induce S ≤ H.induce S := induce_mono hGH (fun _ h => h)

theorem induce_mono_right (G : SimpleDiGraph α) {S T : Set α} (hST : S ⊆ T) :
    G.induce S ≤ G.induce T := induce_mono le_rfl hST

@[simp] theorem induce_empty (G : SimpleDiGraph α) : G.induce ∅ = ⊥ := by
  ext <;> simp

@[simp] theorem induce_univ (G : SimpleDiGraph α) : G.induce Set.univ = G := by
  ext <;> simp

@[simp] theorem induce_vertexSet (G : SimpleDiGraph α) : G.induce V(G) = G := by
  apply SimpleDiGraph.ext
  · simp
  · ext a
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, G.source_mem a h, G.target_mem a h⟩

@[simp] theorem induce_induce (G : SimpleDiGraph α) (S T : Set α) :
    (G.induce S).induce T = G.induce (S ∩ T) := by
  ext <;> simp [and_assoc, and_left_comm, and_comm]

@[simp] theorem induce_idem (G : SimpleDiGraph α) (S : Set α) :
    (G.induce S).induce S = G.induce S := by simp

end SimpleDiGraph

/-! ## Spanning restrictions to actual edges -/

/-- Restrict a general graph to the actual bundled edges in `F`, keeping every vertex. -/
def Graph.restrictEdges (G : Graph α β) (F : Set (Edge α β)) : Graph α β where
  vertexSet := V(G)
  edgeSet := E(G) ∩ F
  endpoints_mem := by rintro e ⟨he, _⟩; exact G.endpoints_mem e he

/-- Restrict a simple graph to the actual endpoint-pair edges in `F`, keeping every vertex. -/
def SimpleGraph.restrictEdges (G : SimpleGraph α) (F : Set (Sym2 α)) : SimpleGraph α where
  vertexSet := V(G)
  edgeSet := E(G) ∩ F
  endpoints_mem := by rintro e ⟨he, _⟩; exact G.endpoints_mem e he
  loopless := by rintro e ⟨he, _⟩; exact G.loopless e he

/-- Restrict a general directed graph to the actual bundled arcs in `F`, keeping every vertex. -/
def DiGraph.restrictEdges (G : DiGraph α β) (F : Set (Arc α β)) : DiGraph α β where
  vertexSet := V(G)
  edgeSet := E(G) ∩ F
  source_mem := by rintro a ⟨ha, _⟩; exact G.source_mem a ha
  target_mem := by rintro a ⟨ha, _⟩; exact G.target_mem a ha

/-- Restrict a simple directed graph to the actual ordered-pair arcs in `F`, keeping every
vertex. -/
def SimpleDiGraph.restrictEdges (G : SimpleDiGraph α) (F : Set (α × α)) : SimpleDiGraph α where
  vertexSet := V(G)
  edgeSet := E(G) ∩ F
  source_mem := by rintro a ⟨ha, _⟩; exact G.source_mem a ha
  target_mem := by rintro a ⟨ha, _⟩; exact G.target_mem a ha
  loopless := by rintro a ⟨ha, _⟩; exact G.loopless a ha

namespace Graph

@[simp] theorem vertexSet_restrictEdges (G : Graph α β) (F : Set (Edge α β)) :
    V(G.restrictEdges F) = V(G) := rfl

@[simp] theorem edgeSet_restrictEdges (G : Graph α β) (F : Set (Edge α β)) :
    E(G.restrictEdges F) = E(G) ∩ F := rfl

@[simp] theorem mem_vertexSet_restrictEdges (G : Graph α β) (F : Set (Edge α β)) (v : α) :
    v ∈ V(G.restrictEdges F) ↔ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_restrictEdges (G : Graph α β) (F : Set (Edge α β))
    (e : Edge α β) : e ∈ E(G.restrictEdges F) ↔ e ∈ E(G) ∧ e ∈ F := Iff.rfl

@[simp] theorem restrictEdges_isLink (G : Graph α β) (F : Set (Edge α β))
    (e : Edge α β) (u v : α) :
    (G.restrictEdges F).IsLink e u v ↔ G.IsLink e u v ∧ e ∈ F := by
  simp only [Graph.IsLink, mem_edgeSet_restrictEdges]
  tauto

@[simp] theorem restrictEdges_inc (G : Graph α β) (F : Set (Edge α β))
    (e : Edge α β) (v : α) :
    (G.restrictEdges F).Inc e v ↔ G.Inc e v ∧ e ∈ F := by
  simp only [Graph.Inc, mem_edgeSet_restrictEdges]
  tauto

/-- Adjacency after edge restriction is witnessed by a retained actual bundled edge. -/
@[simp] theorem restrictEdges_adj (G : Graph α β) (F : Set (Edge α β)) (u v : α) :
    (G.restrictEdges F).Adj u v ↔ ∃ e ∈ F, G.IsLink e u v := by
  simp only [Graph.adj_iff_exists_isLink, restrictEdges_isLink]
  tauto

@[simp] theorem restrictEdges_le (G : Graph α β) (F : Set (Edge α β)) :
    G.restrictEdges F ≤ G := ⟨fun _ h => h, fun _ h => h.1⟩

theorem restrictEdges_isSpanningSubgraph (G : Graph α β) (F : Set (Edge α β)) :
    G.restrictEdges F ≤s G := ⟨G.restrictEdges_le F, rfl⟩

/-- A graph lies below an edge restriction exactly when it lies below the source graph and all
its actual edges belong to the restricting set. -/
theorem restrictEdges_le_iff (H G : Graph α β) (F : Set (Edge α β)) :
    H ≤ G.restrictEdges F ↔ H ≤ G ∧ E(H) ⊆ F := by
  constructor
  · intro h
    exact ⟨h.trans (G.restrictEdges_le F), fun _ he => (h.edgeSet_subset he).2⟩
  · rintro ⟨hHG, hF⟩
    exact ⟨hHG.vertexSet_subset, fun _ he => ⟨hHG.edgeSet_subset he, hF he⟩⟩

theorem restrictEdges_mono {G H : Graph α β} {F K : Set (Edge α β)}
    (hGH : G ≤ H) (hFK : F ⊆ K) : G.restrictEdges F ≤ H.restrictEdges K :=
  ⟨hGH.vertexSet_subset, fun _ he => ⟨hGH.edgeSet_subset he.1, hFK he.2⟩⟩

theorem restrictEdges_mono_left {G H : Graph α β} (hGH : G ≤ H)
    (F : Set (Edge α β)) : G.restrictEdges F ≤ H.restrictEdges F :=
  restrictEdges_mono hGH (fun _ h => h)

theorem restrictEdges_mono_right (G : Graph α β) {F K : Set (Edge α β)} (hFK : F ⊆ K) :
    G.restrictEdges F ≤ G.restrictEdges K := restrictEdges_mono le_rfl hFK

@[simp] theorem edgeSet_restrictEdges_empty (G : Graph α β) :
    E(G.restrictEdges ∅) = ∅ := by simp

@[simp] theorem restrictEdges_univ (G : Graph α β) : G.restrictEdges Set.univ = G := by
  ext <;> simp

@[simp] theorem restrictEdges_edgeSet (G : Graph α β) : G.restrictEdges E(G) = G := by
  ext <;> simp

@[simp] theorem restrictEdges_restrictEdges (G : Graph α β) (F K : Set (Edge α β)) :
    (G.restrictEdges F).restrictEdges K = G.restrictEdges (F ∩ K) := by
  ext <;> simp [Set.inter_assoc]

@[simp] theorem restrictEdges_idem (G : Graph α β) (F : Set (Edge α β)) :
    (G.restrictEdges F).restrictEdges F = G.restrictEdges F := by simp

end Graph

namespace SimpleGraph

@[simp] theorem vertexSet_restrictEdges (G : SimpleGraph α) (F : Set (Sym2 α)) :
    V(G.restrictEdges F) = V(G) := rfl

@[simp] theorem edgeSet_restrictEdges (G : SimpleGraph α) (F : Set (Sym2 α)) :
    E(G.restrictEdges F) = E(G) ∩ F := rfl

@[simp] theorem mem_vertexSet_restrictEdges (G : SimpleGraph α) (F : Set (Sym2 α)) (v : α) :
    v ∈ V(G.restrictEdges F) ↔ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_restrictEdges (G : SimpleGraph α) (F : Set (Sym2 α)) (e : Sym2 α) :
    e ∈ E(G.restrictEdges F) ↔ e ∈ E(G) ∧ e ∈ F := Iff.rfl

@[simp] theorem restrictEdges_isLink (G : SimpleGraph α) (F : Set (Sym2 α))
    (e : Sym2 α) (u v : α) :
    (G.restrictEdges F).IsLink e u v ↔ G.IsLink e u v ∧ e ∈ F := by
  simp only [SimpleGraph.IsLink, mem_edgeSet_restrictEdges]
  tauto

@[simp] theorem restrictEdges_inc (G : SimpleGraph α) (F : Set (Sym2 α))
    (e : Sym2 α) (v : α) :
    (G.restrictEdges F).Inc e v ↔ G.Inc e v ∧ e ∈ F := by
  simp only [SimpleGraph.Inc, mem_edgeSet_restrictEdges]
  tauto

/-- Adjacency after edge restriction is witnessed by a retained actual endpoint-pair edge. -/
@[simp] theorem restrictEdges_adj (G : SimpleGraph α) (F : Set (Sym2 α)) (u v : α) :
    (G.restrictEdges F).Adj u v ↔ ∃ e ∈ F, G.IsLink e u v := by
  simp only [SimpleGraph.adj_iff_exists_isLink, restrictEdges_isLink]
  tauto

@[simp] theorem restrictEdges_le (G : SimpleGraph α) (F : Set (Sym2 α)) :
    G.restrictEdges F ≤ G := ⟨fun _ h => h, fun _ h => h.1⟩

theorem restrictEdges_isSpanningSubgraph (G : SimpleGraph α) (F : Set (Sym2 α)) :
    G.restrictEdges F ≤s G := ⟨G.restrictEdges_le F, rfl⟩

/-- A graph lies below an edge restriction exactly when it lies below the source graph and all
its actual edges belong to the restricting set. -/
theorem restrictEdges_le_iff (H G : SimpleGraph α) (F : Set (Sym2 α)) :
    H ≤ G.restrictEdges F ↔ H ≤ G ∧ E(H) ⊆ F := by
  constructor
  · intro h
    exact ⟨h.trans (G.restrictEdges_le F), fun _ he => (h.edgeSet_subset he).2⟩
  · rintro ⟨hHG, hF⟩
    exact ⟨hHG.vertexSet_subset, fun _ he => ⟨hHG.edgeSet_subset he, hF he⟩⟩

theorem restrictEdges_mono {G H : SimpleGraph α} {F K : Set (Sym2 α)}
    (hGH : G ≤ H) (hFK : F ⊆ K) : G.restrictEdges F ≤ H.restrictEdges K :=
  ⟨hGH.vertexSet_subset, fun _ he => ⟨hGH.edgeSet_subset he.1, hFK he.2⟩⟩

theorem restrictEdges_mono_left {G H : SimpleGraph α} (hGH : G ≤ H) (F : Set (Sym2 α)) :
    G.restrictEdges F ≤ H.restrictEdges F := restrictEdges_mono hGH (fun _ h => h)

theorem restrictEdges_mono_right (G : SimpleGraph α) {F K : Set (Sym2 α)} (hFK : F ⊆ K) :
    G.restrictEdges F ≤ G.restrictEdges K := restrictEdges_mono le_rfl hFK

@[simp] theorem edgeSet_restrictEdges_empty (G : SimpleGraph α) :
    E(G.restrictEdges ∅) = ∅ := by simp

@[simp] theorem restrictEdges_univ (G : SimpleGraph α) : G.restrictEdges Set.univ = G := by
  ext <;> simp

@[simp] theorem restrictEdges_edgeSet (G : SimpleGraph α) : G.restrictEdges E(G) = G := by
  ext <;> simp

@[simp] theorem restrictEdges_restrictEdges (G : SimpleGraph α) (F K : Set (Sym2 α)) :
    (G.restrictEdges F).restrictEdges K = G.restrictEdges (F ∩ K) := by
  ext <;> simp [Set.inter_assoc]

@[simp] theorem restrictEdges_idem (G : SimpleGraph α) (F : Set (Sym2 α)) :
    (G.restrictEdges F).restrictEdges F = G.restrictEdges F := by simp

end SimpleGraph

namespace DiGraph

@[simp] theorem vertexSet_restrictEdges (G : DiGraph α β) (F : Set (Arc α β)) :
    V(G.restrictEdges F) = V(G) := rfl

@[simp] theorem edgeSet_restrictEdges (G : DiGraph α β) (F : Set (Arc α β)) :
    E(G.restrictEdges F) = E(G) ∩ F := rfl

@[simp] theorem mem_vertexSet_restrictEdges (G : DiGraph α β) (F : Set (Arc α β)) (v : α) :
    v ∈ V(G.restrictEdges F) ↔ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_restrictEdges (G : DiGraph α β) (F : Set (Arc α β)) (a : Arc α β) :
    a ∈ E(G.restrictEdges F) ↔ a ∈ E(G) ∧ a ∈ F := Iff.rfl

@[simp] theorem restrictEdges_isArc (G : DiGraph α β) (F : Set (Arc α β))
    (a : Arc α β) (u v : α) :
    (G.restrictEdges F).IsArc a u v ↔ G.IsArc a u v ∧ a ∈ F := by
  simp only [DiGraph.IsArc, mem_edgeSet_restrictEdges]
  tauto

@[simp] theorem restrictEdges_inc (G : DiGraph α β) (F : Set (Arc α β))
    (a : Arc α β) (v : α) :
    (G.restrictEdges F).Inc a v ↔ G.Inc a v ∧ a ∈ F := by
  simp only [DiGraph.Inc, mem_edgeSet_restrictEdges]
  tauto

/-- Directed adjacency after restriction is witnessed by a retained actual bundled arc. -/
@[simp] theorem restrictEdges_adj (G : DiGraph α β) (F : Set (Arc α β)) (u v : α) :
    (G.restrictEdges F).Adj u v ↔ ∃ a ∈ F, G.IsArc a u v := by
  simp only [DiGraph.adj_iff_exists_isArc, restrictEdges_isArc]
  tauto

@[simp] theorem restrictEdges_le (G : DiGraph α β) (F : Set (Arc α β)) :
    G.restrictEdges F ≤ G := ⟨fun _ h => h, fun _ h => h.1⟩

theorem restrictEdges_isSpanningSubgraph (G : DiGraph α β) (F : Set (Arc α β)) :
    G.restrictEdges F ≤s G := ⟨G.restrictEdges_le F, rfl⟩

/-- A directed graph lies below an edge restriction exactly when it lies below the source graph
and all its actual arcs belong to the restricting set. -/
theorem restrictEdges_le_iff (H G : DiGraph α β) (F : Set (Arc α β)) :
    H ≤ G.restrictEdges F ↔ H ≤ G ∧ E(H) ⊆ F := by
  constructor
  · intro h
    exact ⟨h.trans (G.restrictEdges_le F), fun _ he => (h.edgeSet_subset he).2⟩
  · rintro ⟨hHG, hF⟩
    exact ⟨hHG.vertexSet_subset, fun _ he => ⟨hHG.edgeSet_subset he, hF he⟩⟩

theorem restrictEdges_mono {G H : DiGraph α β} {F K : Set (Arc α β)}
    (hGH : G ≤ H) (hFK : F ⊆ K) : G.restrictEdges F ≤ H.restrictEdges K :=
  ⟨hGH.vertexSet_subset, fun _ he => ⟨hGH.edgeSet_subset he.1, hFK he.2⟩⟩

theorem restrictEdges_mono_left {G H : DiGraph α β} (hGH : G ≤ H) (F : Set (Arc α β)) :
    G.restrictEdges F ≤ H.restrictEdges F := restrictEdges_mono hGH (fun _ h => h)

theorem restrictEdges_mono_right (G : DiGraph α β) {F K : Set (Arc α β)} (hFK : F ⊆ K) :
    G.restrictEdges F ≤ G.restrictEdges K := restrictEdges_mono le_rfl hFK

@[simp] theorem edgeSet_restrictEdges_empty (G : DiGraph α β) :
    E(G.restrictEdges ∅) = ∅ := by simp

@[simp] theorem restrictEdges_univ (G : DiGraph α β) : G.restrictEdges Set.univ = G := by
  ext <;> simp

@[simp] theorem restrictEdges_edgeSet (G : DiGraph α β) : G.restrictEdges E(G) = G := by
  ext <;> simp

@[simp] theorem restrictEdges_restrictEdges (G : DiGraph α β) (F K : Set (Arc α β)) :
    (G.restrictEdges F).restrictEdges K = G.restrictEdges (F ∩ K) := by
  ext <;> simp [Set.inter_assoc]

@[simp] theorem restrictEdges_idem (G : DiGraph α β) (F : Set (Arc α β)) :
    (G.restrictEdges F).restrictEdges F = G.restrictEdges F := by simp

end DiGraph

namespace SimpleDiGraph

@[simp] theorem vertexSet_restrictEdges (G : SimpleDiGraph α) (F : Set (α × α)) :
    V(G.restrictEdges F) = V(G) := rfl

@[simp] theorem edgeSet_restrictEdges (G : SimpleDiGraph α) (F : Set (α × α)) :
    E(G.restrictEdges F) = E(G) ∩ F := rfl

@[simp] theorem mem_vertexSet_restrictEdges (G : SimpleDiGraph α) (F : Set (α × α)) (v : α) :
    v ∈ V(G.restrictEdges F) ↔ v ∈ V(G) := Iff.rfl

@[simp] theorem mem_edgeSet_restrictEdges (G : SimpleDiGraph α) (F : Set (α × α)) (a : α × α) :
    a ∈ E(G.restrictEdges F) ↔ a ∈ E(G) ∧ a ∈ F := Iff.rfl

@[simp] theorem restrictEdges_isArc (G : SimpleDiGraph α) (F : Set (α × α))
    (a : α × α) (u v : α) :
    (G.restrictEdges F).IsArc a u v ↔ G.IsArc a u v ∧ a ∈ F := by
  simp only [SimpleDiGraph.IsArc, mem_edgeSet_restrictEdges]
  tauto

@[simp] theorem restrictEdges_inc (G : SimpleDiGraph α) (F : Set (α × α))
    (a : α × α) (v : α) :
    (G.restrictEdges F).Inc a v ↔ G.Inc a v ∧ a ∈ F := by
  simp only [SimpleDiGraph.Inc, mem_edgeSet_restrictEdges]
  tauto

/-- Directed adjacency after restriction is witnessed by a retained actual ordered-pair arc. -/
@[simp] theorem restrictEdges_adj (G : SimpleDiGraph α) (F : Set (α × α)) (u v : α) :
    (G.restrictEdges F).Adj u v ↔ ∃ a ∈ F, G.IsArc a u v := by
  simp only [SimpleDiGraph.adj_iff_exists_isArc, restrictEdges_isArc]
  tauto

@[simp] theorem restrictEdges_le (G : SimpleDiGraph α) (F : Set (α × α)) :
    G.restrictEdges F ≤ G := ⟨fun _ h => h, fun _ h => h.1⟩

theorem restrictEdges_isSpanningSubgraph (G : SimpleDiGraph α) (F : Set (α × α)) :
    G.restrictEdges F ≤s G := ⟨G.restrictEdges_le F, rfl⟩

/-- A directed graph lies below an edge restriction exactly when it lies below the source graph
and all its actual arcs belong to the restricting set. -/
theorem restrictEdges_le_iff (H G : SimpleDiGraph α) (F : Set (α × α)) :
    H ≤ G.restrictEdges F ↔ H ≤ G ∧ E(H) ⊆ F := by
  constructor
  · intro h
    exact ⟨h.trans (G.restrictEdges_le F), fun _ he => (h.edgeSet_subset he).2⟩
  · rintro ⟨hHG, hF⟩
    exact ⟨hHG.vertexSet_subset, fun _ he => ⟨hHG.edgeSet_subset he, hF he⟩⟩

theorem restrictEdges_mono {G H : SimpleDiGraph α} {F K : Set (α × α)}
    (hGH : G ≤ H) (hFK : F ⊆ K) : G.restrictEdges F ≤ H.restrictEdges K :=
  ⟨hGH.vertexSet_subset, fun _ he => ⟨hGH.edgeSet_subset he.1, hFK he.2⟩⟩

theorem restrictEdges_mono_left {G H : SimpleDiGraph α} (hGH : G ≤ H) (F : Set (α × α)) :
    G.restrictEdges F ≤ H.restrictEdges F := restrictEdges_mono hGH (fun _ h => h)

theorem restrictEdges_mono_right (G : SimpleDiGraph α) {F K : Set (α × α)} (hFK : F ⊆ K) :
    G.restrictEdges F ≤ G.restrictEdges K := restrictEdges_mono le_rfl hFK

@[simp] theorem edgeSet_restrictEdges_empty (G : SimpleDiGraph α) :
    E(G.restrictEdges ∅) = ∅ := by simp

@[simp] theorem restrictEdges_univ (G : SimpleDiGraph α) : G.restrictEdges Set.univ = G := by
  ext <;> simp

@[simp] theorem restrictEdges_edgeSet (G : SimpleDiGraph α) : G.restrictEdges E(G) = G := by
  ext <;> simp

@[simp] theorem restrictEdges_restrictEdges (G : SimpleDiGraph α) (F K : Set (α × α)) :
    (G.restrictEdges F).restrictEdges K = G.restrictEdges (F ∩ K) := by
  ext <;> simp [Set.inter_assoc]

@[simp] theorem restrictEdges_idem (G : SimpleDiGraph α) (F : Set (α × α)) :
    (G.restrictEdges F).restrictEdges F = G.restrictEdges F := by simp

end SimpleDiGraph

/-! ## Mixed restriction normalization -/

namespace Graph

/-- Inducing vertices commutes with restricting actual edges. -/
@[simp] theorem restrictEdges_induce (G : Graph α β) (S : Set α)
    (F : Set (Edge α β)) :
    (G.induce S).restrictEdges F = (G.restrictEdges F).induce S := by
  apply Graph.ext <;> ext <;> simp only [mem_vertexSet_restrictEdges,
    mem_vertexSet_induce, mem_edgeSet_restrictEdges, mem_edgeSet_induce]
  tauto

end Graph

namespace SimpleGraph

/-- Inducing vertices commutes with restricting actual edges. -/
@[simp] theorem restrictEdges_induce (G : SimpleGraph α) (S : Set α)
    (F : Set (Sym2 α)) :
    (G.induce S).restrictEdges F = (G.restrictEdges F).induce S := by
  apply SimpleGraph.ext <;> ext <;> simp only [mem_vertexSet_restrictEdges,
    mem_vertexSet_induce, mem_edgeSet_restrictEdges, mem_edgeSet_induce]
  tauto

end SimpleGraph

namespace DiGraph

/-- Inducing vertices commutes with restricting actual arcs. -/
@[simp] theorem restrictEdges_induce (G : DiGraph α β) (S : Set α)
    (F : Set (Arc α β)) :
    (G.induce S).restrictEdges F = (G.restrictEdges F).induce S := by
  apply DiGraph.ext <;> ext <;> simp only [mem_vertexSet_restrictEdges,
    mem_vertexSet_induce, mem_edgeSet_restrictEdges, mem_edgeSet_induce]
  tauto

end DiGraph

namespace SimpleDiGraph

/-- Inducing vertices commutes with restricting actual arcs. -/
@[simp] theorem restrictEdges_induce (G : SimpleDiGraph α) (S : Set α)
    (F : Set (α × α)) :
    (G.induce S).restrictEdges F = (G.restrictEdges F).induce S := by
  apply SimpleDiGraph.ext <;> ext <;> simp only [mem_vertexSet_restrictEdges,
    mem_vertexSet_induce, mem_edgeSet_restrictEdges, mem_edgeSet_induce]
  tauto

end SimpleDiGraph

end GraphLib
