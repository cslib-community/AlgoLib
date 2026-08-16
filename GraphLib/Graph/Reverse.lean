/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Map

/-!
# Directed graph reversal

Reversal swaps the source and target of every actual arc. For a general directed graph this
changes each nonloop bundled arc value while preserving its tag. Reversal is an involution and
is distinct from residual-network construction.
-/

namespace GraphLib
variable {α β γ δ : Type*}

open scoped GraphLib

namespace Arc

/-- Reverse a directed arc by swapping its source and target while preserving its tag. -/
def reverse (a : Arc α β) : Arc α β := ⟨a.tag, (a.target, a.source)⟩

@[simp] theorem tag_reverse (a : Arc α β) : a.reverse.tag = a.tag := rfl

@[simp] theorem source_reverse (a : Arc α β) : a.reverse.source = a.target := rfl

@[simp] theorem target_reverse (a : Arc α β) : a.reverse.target = a.source := rfl

@[simp] theorem endpoints_reverse (a : Arc α β) :
    a.reverse.endpoints = (a.target, a.source) := rfl

@[simp] theorem reverse_reverse (a : Arc α β) : a.reverse.reverse = a := by
  apply Arc.ext <;> simp

/-- Arc reversal is injective. -/
theorem reverse_injective : Function.Injective (reverse : Arc α β → Arc α β) :=
  Function.Involutive.injective reverse_reverse

/-- Arc reversal as an explicit equivalence. -/
def reverseEquiv : Arc α β ≃ Arc α β where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

@[simp] theorem reverseEquiv_apply (a : Arc α β) : reverseEquiv a = a.reverse := rfl

@[simp] theorem reverse_relabelVertices (f : α ≃ γ) (a : Arc α β) :
    (Arc.relabelVertices f a).reverse = Arc.relabelVertices f a.reverse := by
  apply Arc.ext <;> simp

@[simp] theorem reverse_relabelTags (g : β ≃ δ) (a : Arc α β) :
    (Arc.relabelTags g a).reverse = Arc.relabelTags g a.reverse := by
  apply Arc.ext <;> simp

/-- Taking the image under arc reversal twice restores the original set. -/
@[simp] theorem image_reverse_image (F : Set (Arc α β)) :
    Arc.reverse '' (Arc.reverse '' F) = F := by
  ext a
  constructor
  · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
    simpa using hc
  · intro ha
    exact ⟨a.reverse, ⟨a, ha, rfl⟩, by simp⟩

end Arc

namespace SimpleDiGraph

/-- Taking the image under ordered-pair reversal twice restores the original set. -/
@[simp] theorem image_swap_image (F : Set (α × α)) :
    (fun a : α × α => (a.2, a.1)) ''
        ((fun a : α × α => (a.2, a.1)) '' F) = F := by
  ext a
  constructor
  · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
    simpa using hc
  · intro ha
    exact ⟨(a.2, a.1), ⟨a, ha, rfl⟩, by simp⟩

end SimpleDiGraph

/-! ## Graph definitions -/

/-- Reverse every actual arc of a general directed graph. -/
def DiGraph.reverse (G : DiGraph α β) : DiGraph α β where
  vertexSet := V(G)
  edgeSet := Arc.reverse '' E(G)
  source_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact G.target_mem a ha
  target_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact G.source_mem a ha

/-- Reverse every arc of a simple directed graph. -/
def SimpleDiGraph.reverse (G : SimpleDiGraph α) : SimpleDiGraph α where
  vertexSet := V(G)
  edgeSet := (fun a => (a.2, a.1)) '' E(G)
  source_mem := by rintro _ ⟨a, ha, rfl⟩; exact G.target_mem a ha
  target_mem := by rintro _ ⟨a, ha, rfl⟩; exact G.source_mem a ha
  loopless := by rintro _ ⟨a, ha, rfl⟩ h; exact G.loopless a ha h.symm

namespace DiGraph

@[simp] theorem vertexSet_reverse (G : DiGraph α β) : V(G.reverse) = V(G) := rfl

@[simp] theorem edgeSet_reverse (G : DiGraph α β) : E(G.reverse) = Arc.reverse '' E(G) := rfl

@[simp] theorem mem_edgeSet_reverse (G : DiGraph α β) (a : Arc α β) :
    a ∈ E(G.reverse) ↔ a.reverse ∈ E(G) := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have h : b = a.reverse := calc
      b = b.reverse.reverse := (Arc.reverse_reverse b).symm
      _ = a.reverse := congrArg Arc.reverse hba
    exact h ▸ hb
  · intro ha
    exact ⟨a.reverse, ha, by simp⟩

@[simp] theorem reverse_isArc (G : DiGraph α β) (a : Arc α β) (u v : α) :
    G.reverse.IsArc a u v ↔ G.IsArc a.reverse v u := by
  change (a ∈ E(G.reverse) ∧ a.source = u ∧ a.target = v) ↔ _
  rw [mem_edgeSet_reverse]
  simp only [DiGraph.IsArc, Arc.source_reverse, Arc.target_reverse]
  tauto

@[simp] theorem reverse_inc (G : DiGraph α β) (a : Arc α β) (v : α) :
    G.reverse.Inc a v ↔ G.Inc a.reverse v := by
  change (a ∈ E(G.reverse) ∧ (a.source = v ∨ a.target = v)) ↔ _
  rw [mem_edgeSet_reverse]
  simp only [DiGraph.Inc, Arc.source_reverse, Arc.target_reverse]
  tauto

@[simp] theorem reverse_adj (G : DiGraph α β) (u v : α) :
    G.reverse.Adj u v ↔ G.Adj v u := by
  constructor
  · rintro ⟨a, ha⟩
    exact (G.reverse_isArc a u v).1 ha |>.adj
  · rintro ⟨a, ha⟩
    exact ⟨a.reverse, (G.reverse_isArc a.reverse u v).2 (by simpa using ha)⟩

/-- Reversal sends incoming actual arcs to outgoing actual arcs. -/
@[simp] theorem outIncidenceSet_reverse (G : DiGraph α β) (v : α) :
    G.reverse.outIncidenceSet v = Arc.reverse '' G.inIncidenceSet v := by
  ext a
  constructor
  · intro ha
    have hmem := (G.reverse.mem_outIncidenceSet v a).mp ha
    refine ⟨a.reverse, ?_, by simp⟩
    exact (G.mem_inIncidenceSet v a.reverse).mpr
      ⟨(G.mem_edgeSet_reverse a).1 hmem.1, by simpa using hmem.2⟩
  · rintro ⟨b, hb, rfl⟩
    have hmem := (G.mem_inIncidenceSet v b).mp hb
    exact (G.reverse.mem_outIncidenceSet v b.reverse).mpr
      ⟨(G.mem_edgeSet_reverse b.reverse).2 (by simpa using hmem.1), by simpa using hmem.2⟩

/-- Reversal sends outgoing actual arcs to incoming actual arcs. -/
@[simp] theorem inIncidenceSet_reverse (G : DiGraph α β) (v : α) :
    G.reverse.inIncidenceSet v = Arc.reverse '' G.outIncidenceSet v := by
  ext a
  constructor
  · intro ha
    have hmem := (G.reverse.mem_inIncidenceSet v a).mp ha
    refine ⟨a.reverse, ?_, by simp⟩
    exact (G.mem_outIncidenceSet v a.reverse).mpr
      ⟨(G.mem_edgeSet_reverse a).1 hmem.1, by simpa using hmem.2⟩
  · rintro ⟨b, hb, rfl⟩
    have hmem := (G.mem_outIncidenceSet v b).mp hb
    exact (G.reverse.mem_inIncidenceSet v b.reverse).mpr
      ⟨(G.mem_edgeSet_reverse b.reverse).2 (by simpa using hmem.1), by simpa using hmem.2⟩

@[simp] theorem reverse_reverse (G : DiGraph α β) : G.reverse.reverse = G := by
  apply DiGraph.ext
  · rfl
  · ext a
    rw [mem_edgeSet_reverse, mem_edgeSet_reverse, Arc.reverse_reverse]

/-- Reversal preserves and reflects the subgraph order. -/
theorem reverse_le_reverse {G H : DiGraph α β} : G.reverse ≤ H.reverse ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨h.vertexSet_subset, fun a ha => ?_⟩
    have har : a.reverse ∈ E(G.reverse) := (G.mem_edgeSet_reverse a.reverse).2 (by simpa)
    have hHr := h.edgeSet_subset har
    simpa using (H.mem_edgeSet_reverse a.reverse).1 hHr
  · refine ⟨h.vertexSet_subset, fun a ha => ?_⟩
    rw [mem_edgeSet_reverse] at ha ⊢
    exact h.edgeSet_subset ha

theorem IsSubgraph.reverse {G H : DiGraph α β} (h : G ≤ H) : G.reverse ≤ H.reverse :=
  reverse_le_reverse.2 h

theorem reverse_le_reverse_spanning {G H : DiGraph α β} :
    G.reverse ≤s H.reverse ↔ G ≤s H := by
  constructor <;> intro h
  · exact ⟨reverse_le_reverse.1 h.le, h.vertexSet_eq⟩
  · exact ⟨reverse_le_reverse.2 h.le, h.vertexSet_eq⟩

theorem IsSpanningSubgraph.reverse {G H : DiGraph α β} (h : G ≤s H) :
    G.reverse ≤s H.reverse := reverse_le_reverse_spanning.2 h

theorem reverse_le_reverse_induced {G H : DiGraph α β} :
    G.reverse ≤i H.reverse ↔ G ≤i H := by
  constructor
  · intro h
    refine ⟨reverse_le_reverse.1 h.le, ?_⟩
    intro a u v ha hu hv
    have har : H.reverse.IsArc a.reverse v u :=
      (H.reverse_isArc a.reverse v u).2 (by simpa using ha)
    have hkeep := h.isArc_of_mem_mem har hv hu
    simpa using (G.reverse_isArc a.reverse v u).1 hkeep
  · intro h
    refine ⟨reverse_le_reverse.2 h.le, ?_⟩
    intro a u v ha hu hv
    have har : H.IsArc a.reverse v u := (H.reverse_isArc a u v).1 ha
    have hkeep := h.isArc_of_mem_mem har hv hu
    exact (G.reverse_isArc a u v).2 hkeep

theorem IsInducedSubgraph.reverse {G H : DiGraph α β} (h : G ≤i H) :
    G.reverse ≤i H.reverse := reverse_le_reverse_induced.2 h

/-! ## Commutation with same-carrier transformations -/

@[simp] theorem reverse_induce (G : DiGraph α β) (S : Set α) :
    (G.induce S).reverse = G.reverse.induce S := by
  apply DiGraph.ext
  · rfl
  · ext a
    rw [mem_edgeSet_reverse, mem_edgeSet_induce, mem_edgeSet_induce, mem_edgeSet_reverse]
    simp only [Arc.source_reverse, Arc.target_reverse]
    tauto

@[simp] theorem reverse_restrictEdges (G : DiGraph α β) (F : Set (Arc α β)) :
    (G.restrictEdges F).reverse = G.reverse.restrictEdges (Arc.reverse '' F) := by
  apply DiGraph.ext
  · rfl
  · ext a
    simp only [mem_edgeSet_reverse, mem_edgeSet_restrictEdges]
    constructor
    · rintro ⟨ha, hF⟩
      exact ⟨ha, ⟨a.reverse, hF, by simp⟩⟩
    · rintro ⟨ha, b, hb, hba⟩
      have h : b = a.reverse := calc
        b = b.reverse.reverse := (Arc.reverse_reverse b).symm
        _ = a.reverse := congrArg Arc.reverse hba
      exact ⟨ha, h ▸ hb⟩

@[simp] theorem reverse_deleteEdges (G : DiGraph α β) (F : Set (Arc α β)) :
    (G.deleteEdges F).reverse = G.reverse.deleteEdges (Arc.reverse '' F) := by
  apply DiGraph.ext
  · rfl
  · ext a
    simp only [mem_edgeSet_reverse, mem_edgeSet_deleteEdges]
    constructor
    · rintro ⟨ha, hnot⟩
      refine ⟨ha, ?_⟩
      rintro ⟨b, hb, hba⟩
      have h : b = a.reverse := calc
        b = b.reverse.reverse := (Arc.reverse_reverse b).symm
        _ = a.reverse := congrArg Arc.reverse hba
      exact hnot (h ▸ hb)
    · rintro ⟨ha, hnot⟩
      refine ⟨ha, fun hF => hnot ?_⟩
      exact ⟨a.reverse, hF, by simp⟩

@[simp] theorem reverse_deleteEdge (G : DiGraph α β) (a : Arc α β) :
    (G.deleteEdge a).reverse = G.reverse.deleteEdge a.reverse := by
  simp [deleteEdge]

@[simp] theorem reverse_deleteVerts (G : DiGraph α β) (S : Set α) :
    (G.deleteVerts S).reverse = G.reverse.deleteVerts S := by
  simp [deleteVerts]

@[simp] theorem reverse_deleteVert (G : DiGraph α β) (v : α) :
    (G.deleteVert v).reverse = G.reverse.deleteVert v := by simp [deleteVert]

@[simp] theorem reverse_deleteArcsFromTo (G : DiGraph α β) (u v : α) :
    (G.deleteArcsFromTo u v).reverse = G.reverse.deleteArcsFromTo v u := by
  apply DiGraph.ext
  · rfl
  · ext a
    rw [mem_edgeSet_reverse, mem_edgeSet_deleteArcsFromTo,
      mem_edgeSet_deleteArcsFromTo, mem_edgeSet_reverse]
    simp only [Arc.source_reverse, Arc.target_reverse]
    tauto

/-! ## Commutation with maps and relabeling -/

@[simp] theorem reverse_relabelVertices (G : DiGraph α β) (f : α ≃ γ) :
    (G.relabelVertices f).reverse = G.reverse.relabelVertices f := by
  apply DiGraph.ext
  · rfl
  · ext a
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c.reverse, ⟨c, hc, rfl⟩, by simp⟩
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨Arc.relabelVertices f c, ⟨c, hc, rfl⟩, by simp⟩

@[simp] theorem reverse_relabelTags (G : DiGraph α β) (g : β ≃ δ) :
    (G.relabelTags g).reverse = G.reverse.relabelTags g := by
  apply DiGraph.ext
  · rfl
  · ext a
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c.reverse, ⟨c, hc, rfl⟩, by simp⟩
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨Arc.relabelTags g c, ⟨c, hc, rfl⟩, by simp⟩

/-- Reversal commutes with provenance-bearing vertex maps after reversing the provenance tag
on the mapped reversed graph. -/
@[simp] theorem reverse_mapVertices (G : DiGraph α β) (f : α → γ) :
    (G.mapVertices f).reverse =
      (G.reverse.mapVertices f).relabelTags (Arc.reverseEquiv : Arc α β ≃ Arc α β) := by
  apply DiGraph.ext
  · rfl
  · ext a
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨Arc.mapVertices f c.reverse, ⟨c.reverse, ⟨c, hc, rfl⟩, rfl⟩, by
        apply Arc.ext <;> simp⟩
    · rintro ⟨b, ⟨c, ⟨d, hd, hdc⟩, rfl⟩, rfl⟩
      subst c
      exact ⟨Arc.mapVertices f d, ⟨d, hd, rfl⟩, by
        apply Arc.ext <;> simp⟩

end DiGraph

namespace SimpleDiGraph

@[simp] theorem vertexSet_reverse (G : SimpleDiGraph α) : V(G.reverse) = V(G) := rfl

@[simp] theorem edgeSet_reverse (G : SimpleDiGraph α) :
    E(G.reverse) = (fun a => (a.2, a.1)) '' E(G) := rfl

@[simp] theorem mem_edgeSet_reverse (G : SimpleDiGraph α) (a : α × α) :
    a ∈ E(G.reverse) ↔ (a.2, a.1) ∈ E(G) := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have h : b = (a.2, a.1) := by
      apply Prod.ext
      · exact congrArg Prod.snd hba
      · exact congrArg Prod.fst hba
    exact h ▸ hb
  · intro ha
    exact ⟨(a.2, a.1), ha, by simp⟩

@[simp] theorem reverse_isArc (G : SimpleDiGraph α) (a : α × α) (u v : α) :
    G.reverse.IsArc a u v ↔ G.IsArc (a.2, a.1) v u := by
  change (a ∈ E(G.reverse) ∧ a.1 = u ∧ a.2 = v) ↔ _
  rw [mem_edgeSet_reverse]
  simp only [SimpleDiGraph.IsArc]
  tauto

@[simp] theorem reverse_inc (G : SimpleDiGraph α) (a : α × α) (v : α) :
    G.reverse.Inc a v ↔ G.Inc (a.2, a.1) v := by
  change (a ∈ E(G.reverse) ∧ (a.1 = v ∨ a.2 = v)) ↔ _
  rw [mem_edgeSet_reverse]
  simp only [SimpleDiGraph.Inc]
  tauto

@[simp] theorem reverse_adj (G : SimpleDiGraph α) (u v : α) :
    G.reverse.Adj u v ↔ G.Adj v u := by
  simp [SimpleDiGraph.adj_iff]

/-- Reversal sends incoming actual arcs to outgoing actual arcs. -/
@[simp] theorem outIncidenceSet_reverse (G : SimpleDiGraph α) (v : α) :
    G.reverse.outIncidenceSet v =
      (fun a : α × α => (a.2, a.1)) '' G.inIncidenceSet v := by
  ext a
  constructor
  · intro ha
    have hmem := (G.reverse.mem_outIncidenceSet v a).mp ha
    refine ⟨(a.2, a.1), ?_, by simp⟩
    exact (G.mem_inIncidenceSet v (a.2, a.1)).mpr
      ⟨(G.mem_edgeSet_reverse a).1 hmem.1, by simpa using hmem.2⟩
  · rintro ⟨b, hb, rfl⟩
    have hmem := (G.mem_inIncidenceSet v b).mp hb
    exact (G.reverse.mem_outIncidenceSet v (b.2, b.1)).mpr
      ⟨(G.mem_edgeSet_reverse (b.2, b.1)).2 (by simpa using hmem.1), by simpa using hmem.2⟩

/-- Reversal sends outgoing actual arcs to incoming actual arcs. -/
@[simp] theorem inIncidenceSet_reverse (G : SimpleDiGraph α) (v : α) :
    G.reverse.inIncidenceSet v =
      (fun a : α × α => (a.2, a.1)) '' G.outIncidenceSet v := by
  ext a
  constructor
  · intro ha
    have hmem := (G.reverse.mem_inIncidenceSet v a).mp ha
    refine ⟨(a.2, a.1), ?_, by simp⟩
    exact (G.mem_outIncidenceSet v (a.2, a.1)).mpr
      ⟨(G.mem_edgeSet_reverse a).1 hmem.1, by simpa using hmem.2⟩
  · rintro ⟨b, hb, rfl⟩
    have hmem := (G.mem_outIncidenceSet v b).mp hb
    exact (G.reverse.mem_inIncidenceSet v (b.2, b.1)).mpr
      ⟨(G.mem_edgeSet_reverse (b.2, b.1)).2 (by simpa using hmem.1), by simpa using hmem.2⟩

@[simp] theorem reverse_reverse (G : SimpleDiGraph α) : G.reverse.reverse = G := by
  apply SimpleDiGraph.ext
  · rfl
  · ext a
    rw [mem_edgeSet_reverse, mem_edgeSet_reverse]

theorem reverse_le_reverse {G H : SimpleDiGraph α} : G.reverse ≤ H.reverse ↔ G ≤ H := by
  constructor <;> intro h
  · refine ⟨h.vertexSet_subset, fun a ha => ?_⟩
    have har : (a.2, a.1) ∈ E(G.reverse) :=
      (G.mem_edgeSet_reverse (a.2, a.1)).2 (by simpa)
    have hHr := h.edgeSet_subset har
    simpa using (H.mem_edgeSet_reverse (a.2, a.1)).1 hHr
  · exact ⟨h.vertexSet_subset, fun a ha => by
      rw [mem_edgeSet_reverse] at ha ⊢
      exact h.edgeSet_subset ha⟩

theorem IsSubgraph.reverse {G H : SimpleDiGraph α} (h : G ≤ H) : G.reverse ≤ H.reverse :=
  reverse_le_reverse.2 h

theorem reverse_le_reverse_spanning {G H : SimpleDiGraph α} :
    G.reverse ≤s H.reverse ↔ G ≤s H := by
  constructor <;> intro h
  · exact ⟨reverse_le_reverse.1 h.le, h.vertexSet_eq⟩
  · exact ⟨reverse_le_reverse.2 h.le, h.vertexSet_eq⟩

theorem IsSpanningSubgraph.reverse {G H : SimpleDiGraph α} (h : G ≤s H) :
    G.reverse ≤s H.reverse := reverse_le_reverse_spanning.2 h

theorem reverse_le_reverse_induced {G H : SimpleDiGraph α} :
    G.reverse ≤i H.reverse ↔ G ≤i H := by
  constructor
  · intro h
    refine ⟨reverse_le_reverse.1 h.le, ?_⟩
    intro a u v ha hu hv
    have har : H.reverse.IsArc (a.2, a.1) v u :=
      (H.reverse_isArc (a.2, a.1) v u).2 (by simpa using ha)
    have hkeep := h.isArc_of_mem_mem har hv hu
    simpa using (G.reverse_isArc (a.2, a.1) v u).1 hkeep
  · intro h
    refine ⟨reverse_le_reverse.2 h.le, ?_⟩
    intro a u v ha hu hv
    have har : H.IsArc (a.2, a.1) v u := (H.reverse_isArc a u v).1 ha
    have hkeep := h.isArc_of_mem_mem har hv hu
    exact (G.reverse_isArc a u v).2 hkeep

theorem IsInducedSubgraph.reverse {G H : SimpleDiGraph α} (h : G ≤i H) :
    G.reverse ≤i H.reverse := reverse_le_reverse_induced.2 h

@[simp] theorem reverse_induce (G : SimpleDiGraph α) (S : Set α) :
    (G.induce S).reverse = G.reverse.induce S := by
  apply SimpleDiGraph.ext
  · rfl
  · ext a
    rw [mem_edgeSet_reverse, mem_edgeSet_induce, mem_edgeSet_induce, mem_edgeSet_reverse]
    tauto

@[simp] theorem reverse_restrictEdges (G : SimpleDiGraph α) (F : Set (α × α)) :
    (G.restrictEdges F).reverse =
      G.reverse.restrictEdges ((fun a => (a.2, a.1)) '' F) := by
  apply SimpleDiGraph.ext
  · rfl
  · ext a
    simp only [mem_edgeSet_reverse, mem_edgeSet_restrictEdges]
    constructor
    · rintro ⟨ha, hF⟩
      exact ⟨ha, ⟨(a.2, a.1), hF, by simp⟩⟩
    · rintro ⟨ha, b, hb, hba⟩
      have h : b = (a.2, a.1) := by
        apply Prod.ext
        · exact congrArg Prod.snd hba
        · exact congrArg Prod.fst hba
      exact ⟨ha, h ▸ hb⟩

@[simp] theorem reverse_deleteEdges (G : SimpleDiGraph α) (F : Set (α × α)) :
    (G.deleteEdges F).reverse =
      G.reverse.deleteEdges ((fun a => (a.2, a.1)) '' F) := by
  apply SimpleDiGraph.ext
  · rfl
  · ext a
    simp only [mem_edgeSet_reverse, mem_edgeSet_deleteEdges]
    constructor
    · rintro ⟨ha, hnot⟩
      refine ⟨ha, ?_⟩
      rintro ⟨b, hb, hba⟩
      have h : b = (a.2, a.1) := by
        apply Prod.ext
        · exact congrArg Prod.snd hba
        · exact congrArg Prod.fst hba
      exact hnot (h ▸ hb)
    · rintro ⟨ha, hnot⟩
      exact ⟨ha, fun hF => hnot ⟨(a.2, a.1), hF, by simp⟩⟩

@[simp] theorem reverse_deleteEdge (G : SimpleDiGraph α) (a : α × α) :
    (G.deleteEdge a).reverse = G.reverse.deleteEdge (a.2, a.1) := by
  simp [deleteEdge]

@[simp] theorem reverse_deleteVerts (G : SimpleDiGraph α) (S : Set α) :
    (G.deleteVerts S).reverse = G.reverse.deleteVerts S := by simp [deleteVerts]

@[simp] theorem reverse_deleteVert (G : SimpleDiGraph α) (v : α) :
    (G.deleteVert v).reverse = G.reverse.deleteVert v := by simp [deleteVert]

@[simp] theorem reverse_deleteArcsFromTo (G : SimpleDiGraph α) (u v : α) :
    (G.deleteArcsFromTo u v).reverse = G.reverse.deleteArcsFromTo v u := by
  apply SimpleDiGraph.ext
  · rfl
  · ext a
    rw [mem_edgeSet_reverse, mem_edgeSet_deleteArcsFromTo,
      mem_edgeSet_deleteArcsFromTo, mem_edgeSet_reverse]
    tauto

@[simp] theorem reverse_relabelVertices (G : SimpleDiGraph α) (f : α ≃ γ) :
    (G.relabelVertices f).reverse = G.reverse.relabelVertices f := by
  apply SimpleDiGraph.ext
  · rfl
  · ext a
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨(c.2, c.1), ⟨c, hc, rfl⟩, by simp⟩
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨(f c.1, f c.2), ⟨c, hc, rfl⟩, by simp⟩

end SimpleDiGraph

end GraphLib
