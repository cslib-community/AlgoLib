/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Graph.Adjacency
import GraphLib.Graph.Finite
import Mathlib.Data.Set.Finite.Lattice

/-!
# Basic graph constructions

This file provides a deliberately small collection of graph constructors used for examples and
foundation tests. General graphs are constructed from sets of complete bundled actual edges or
arcs, so reused tags and parallel values retain their identity. The simple complete constructors
contain every nonloop edge or arc on the supplied vertex set.
-/

namespace GraphLib

open scoped GraphLib

variable {α β : Type*}

private theorem sym2MemSet_finite (e : Sym2 α) : {v | v ∈ e}.Finite := by
  induction e using Sym2.ind with
  | h u v =>
    rw [show {x | x ∈ s(u, v)} = {u, v} by ext x; simp [Sym2.mem_iff]]
    exact (Set.finite_singleton v).insert u

/-! ## Empty and edgeless graphs -/

namespace Graph

/-- The general graph with no vertices and no actual edges. -/
def empty : Graph α β where
  vertexSet := ∅
  edgeSet := ∅
  endpoints_mem := by simp

/-- The general graph on `S` with no actual edges. -/
def edgeless (S : Set α) : Graph α β where
  vertexSet := S
  edgeSet := ∅
  endpoints_mem := by simp

@[simp] theorem vertexSet_empty : (empty : Graph α β).vertexSet = ∅ := rfl

@[simp] theorem edgeSet_empty : (empty : Graph α β).edgeSet = ∅ := rfl

@[simp] theorem vertexSet_edgeless (S : Set α) : (edgeless S : Graph α β).vertexSet = S := rfl

@[simp] theorem edgeSet_edgeless (S : Set α) : (edgeless S : Graph α β).edgeSet = ∅ := rfl

@[simp] theorem empty_isLink (e : Edge α β) (u v : α) :
    ¬(empty : Graph α β).IsLink e u v := by simp [IsLink]

@[simp] theorem edgeless_isLink (S : Set α) (e : Edge α β) (u v : α) :
    ¬(edgeless S : Graph α β).IsLink e u v := by simp [IsLink]

@[simp] theorem empty_adj (u v : α) : ¬(empty : Graph α β).Adj u v := by
  simp [Adj]

@[simp] theorem edgeless_adj (S : Set α) (u v : α) : ¬(edgeless S : Graph α β).Adj u v := by
  simp [Adj]

@[simp] theorem empty_eq_edgeless : (empty : Graph α β) = edgeless ∅ := by
  ext <;> simp

instance instFiniteVertexSetEmpty : Finite V((empty : Graph α β)) := by
  change Finite (∅ : Set α)
  infer_instance

instance instFiniteEdgeSetEmpty : Finite E((empty : Graph α β)) := by
  change Finite (∅ : Set (Edge α β))
  infer_instance

instance instFiniteVertexSetEdgeless (S : Set α) [Finite S] :
    Finite V((edgeless S : Graph α β)) := by
  change Finite S
  infer_instance

instance instFiniteEdgeSetEdgeless (S : Set α) : Finite E((edgeless S : Graph α β)) := by
  change Finite (∅ : Set (Edge α β))
  infer_instance

end Graph

namespace SimpleGraph

/-- The simple graph with no vertices and no edges. -/
def empty : SimpleGraph α where
  vertexSet := ∅
  edgeSet := ∅
  endpoints_mem := by simp
  loopless := by simp

/-- The simple graph on `S` with no edges. -/
def edgeless (S : Set α) : SimpleGraph α where
  vertexSet := S
  edgeSet := ∅
  endpoints_mem := by simp
  loopless := by simp

@[simp] theorem vertexSet_empty : (empty : SimpleGraph α).vertexSet = ∅ := rfl

@[simp] theorem edgeSet_empty : (empty : SimpleGraph α).edgeSet = ∅ := rfl

@[simp] theorem vertexSet_edgeless (S : Set α) : (edgeless S).vertexSet = S := rfl

@[simp] theorem edgeSet_edgeless (S : Set α) : (edgeless S).edgeSet = ∅ := rfl

@[simp] theorem empty_isLink (e : Sym2 α) (u v : α) :
    ¬(empty : SimpleGraph α).IsLink e u v := by simp [IsLink]

@[simp] theorem edgeless_isLink (S : Set α) (e : Sym2 α) (u v : α) :
    ¬(edgeless S).IsLink e u v := by simp [IsLink]

@[simp] theorem empty_adj (u v : α) : ¬(empty : SimpleGraph α).Adj u v := by
  simp [Adj]

@[simp] theorem edgeless_adj (S : Set α) (u v : α) : ¬(edgeless S).Adj u v := by
  simp [Adj]

@[simp] theorem empty_eq_edgeless : (empty : SimpleGraph α) = edgeless ∅ := by
  ext <;> simp

instance instFiniteVertexSetEmpty : Finite V((empty : SimpleGraph α)) := by
  change Finite (∅ : Set α)
  infer_instance

instance instFiniteEdgeSetEmpty : Finite E((empty : SimpleGraph α)) := by
  change Finite (∅ : Set (Sym2 α))
  infer_instance

instance instFiniteVertexSetEdgeless (S : Set α) [Finite S] : Finite V(edgeless S) := by
  change Finite S
  infer_instance

instance instFiniteEdgeSetEdgeless (S : Set α) : Finite E(edgeless S) := by
  change Finite (∅ : Set (Sym2 α))
  infer_instance

end SimpleGraph

namespace DiGraph

/-- The general directed graph with no vertices and no actual arcs. -/
def empty : DiGraph α β where
  vertexSet := ∅
  edgeSet := ∅
  source_mem := by simp
  target_mem := by simp

/-- The general directed graph on `S` with no actual arcs. -/
def edgeless (S : Set α) : DiGraph α β where
  vertexSet := S
  edgeSet := ∅
  source_mem := by simp
  target_mem := by simp

@[simp] theorem vertexSet_empty : (empty : DiGraph α β).vertexSet = ∅ := rfl

@[simp] theorem edgeSet_empty : (empty : DiGraph α β).edgeSet = ∅ := rfl

@[simp] theorem vertexSet_edgeless (S : Set α) : (edgeless S : DiGraph α β).vertexSet = S := rfl

@[simp] theorem edgeSet_edgeless (S : Set α) : (edgeless S : DiGraph α β).edgeSet = ∅ := rfl

@[simp] theorem empty_isArc (a : Arc α β) (u v : α) :
    ¬(empty : DiGraph α β).IsArc a u v := by simp [IsArc]

@[simp] theorem edgeless_isArc (S : Set α) (a : Arc α β) (u v : α) :
    ¬(edgeless S : DiGraph α β).IsArc a u v := by simp [IsArc]

@[simp] theorem empty_adj (u v : α) : ¬(empty : DiGraph α β).Adj u v := by
  simp [Adj]

@[simp] theorem edgeless_adj (S : Set α) (u v : α) : ¬(edgeless S : DiGraph α β).Adj u v := by
  simp [Adj]

@[simp] theorem empty_eq_edgeless : (empty : DiGraph α β) = edgeless ∅ := by
  ext <;> simp

instance instFiniteVertexSetEmpty : Finite V((empty : DiGraph α β)) := by
  change Finite (∅ : Set α)
  infer_instance

instance instFiniteEdgeSetEmpty : Finite E((empty : DiGraph α β)) := by
  change Finite (∅ : Set (Arc α β))
  infer_instance

instance instFiniteVertexSetEdgeless (S : Set α) [Finite S] :
    Finite V((edgeless S : DiGraph α β)) := by
  change Finite S
  infer_instance

instance instFiniteEdgeSetEdgeless (S : Set α) : Finite E((edgeless S : DiGraph α β)) := by
  change Finite (∅ : Set (Arc α β))
  infer_instance

end DiGraph

namespace SimpleDiGraph

/-- The simple directed graph with no vertices and no arcs. -/
def empty : SimpleDiGraph α where
  vertexSet := ∅
  edgeSet := ∅
  source_mem := by simp
  target_mem := by simp
  loopless := by simp

/-- The simple directed graph on `S` with no arcs. -/
def edgeless (S : Set α) : SimpleDiGraph α where
  vertexSet := S
  edgeSet := ∅
  source_mem := by simp
  target_mem := by simp
  loopless := by simp

@[simp] theorem vertexSet_empty : (empty : SimpleDiGraph α).vertexSet = ∅ := rfl

@[simp] theorem edgeSet_empty : (empty : SimpleDiGraph α).edgeSet = ∅ := rfl

@[simp] theorem vertexSet_edgeless (S : Set α) : (edgeless S).vertexSet = S := rfl

@[simp] theorem edgeSet_edgeless (S : Set α) : (edgeless S).edgeSet = ∅ := rfl

@[simp] theorem empty_isArc (a : α × α) (u v : α) :
    ¬(empty : SimpleDiGraph α).IsArc a u v := by simp [IsArc]

@[simp] theorem edgeless_isArc (S : Set α) (a : α × α) (u v : α) :
    ¬(edgeless S).IsArc a u v := by simp [IsArc]

@[simp] theorem empty_adj (u v : α) : ¬(empty : SimpleDiGraph α).Adj u v := by
  simp [Adj]

@[simp] theorem edgeless_adj (S : Set α) (u v : α) : ¬(edgeless S).Adj u v := by
  simp [Adj]

@[simp] theorem empty_eq_edgeless : (empty : SimpleDiGraph α) = edgeless ∅ := by
  ext <;> simp

instance instFiniteVertexSetEmpty : Finite V((empty : SimpleDiGraph α)) := by
  change Finite (∅ : Set α)
  infer_instance

instance instFiniteEdgeSetEmpty : Finite E((empty : SimpleDiGraph α)) := by
  change Finite (∅ : Set (α × α))
  infer_instance

instance instFiniteVertexSetEdgeless (S : Set α) [Finite S] : Finite V(edgeless S) := by
  change Finite S
  infer_instance

instance instFiniteEdgeSetEdgeless (S : Set α) : Finite E(edgeless S) := by
  change Finite (∅ : Set (α × α))
  infer_instance

end SimpleDiGraph

/-! ## General graphs generated by actual edges or arcs -/

namespace Graph

/-- The general graph generated by the actual bundled edges in `F`. Its vertices are exactly the
endpoints of those edges. -/
def ofEdgeSet (F : Set (Edge α β)) : Graph α β where
  vertexSet := ⋃ e ∈ F, {v | v ∈ e.endpoints}
  edgeSet := F
  endpoints_mem := by
    intro e he v hv
    simp only [Set.mem_iUnion]
    exact ⟨e, ⟨he, hv⟩⟩

/-- The general graph generated by the single actual bundled edge `e`. -/
def ofEdge (e : Edge α β) : Graph α β := ofEdgeSet {e}

@[simp] theorem mem_vertexSet_ofEdgeSet (F : Set (Edge α β)) (v : α) :
    v ∈ (ofEdgeSet F).vertexSet ↔ ∃ e ∈ F, v ∈ e.endpoints := by
  simp [ofEdgeSet]

@[simp] theorem edgeSet_ofEdgeSet (F : Set (Edge α β)) : (ofEdgeSet F).edgeSet = F := rfl

@[simp] theorem ofEdgeSet_isLink (F : Set (Edge α β)) (e : Edge α β) (u v : α) :
    (ofEdgeSet F).IsLink e u v ↔ e ∈ F ∧ e.endpoints = s(u, v) := by
  rfl

@[simp] theorem ofEdgeSet_adj (F : Set (Edge α β)) (u v : α) :
    (ofEdgeSet F).Adj u v ↔ ∃ e ∈ F, e.endpoints = s(u, v) := by
  simp [Adj]

@[simp] theorem mem_vertexSet_ofEdge (e : Edge α β) (v : α) :
    v ∈ (ofEdge e).vertexSet ↔ v ∈ e.endpoints := by
  change v ∈ (ofEdgeSet {e}).vertexSet ↔ _
  rw [mem_vertexSet_ofEdgeSet]
  simp

@[simp] theorem mem_edgeSet_ofEdge (e f : Edge α β) : f ∈ E(ofEdge e) ↔ f = e := by
  simp [ofEdge]

@[simp] theorem edgeSet_ofEdge (e : Edge α β) : (ofEdge e).edgeSet = {e} := rfl

@[simp] theorem ofEdge_isLink (e f : Edge α β) (u v : α) :
    (ofEdge e).IsLink f u v ↔ f = e ∧ e.endpoints = s(u, v) := by
  change (ofEdgeSet {e}).IsLink f u v ↔ _
  rw [ofEdgeSet_isLink]
  constructor
  · rintro ⟨rfl, hends⟩
    exact ⟨rfl, hends⟩
  · rintro ⟨rfl, hends⟩
    exact ⟨by simp, hends⟩

@[simp] theorem ofEdge_adj (e : Edge α β) (u v : α) :
    (ofEdge e).Adj u v ↔ e.endpoints = s(u, v) := by
  change (ofEdgeSet {e}).Adj u v ↔ _
  rw [ofEdgeSet_adj]
  simp

@[simp] theorem ofEdgeSet_empty : ofEdgeSet (∅ : Set (Edge α β)) = empty := by
  apply Graph.ext
  · ext v
    simp [ofEdgeSet]
  · rfl

instance instFiniteVertexSetOfEdgeSet (F : Set (Edge α β)) [Finite F] :
    Finite V(ofEdgeSet F) := by
  refine ((Set.toFinite F).biUnion fun e _ => ?_).to_subtype
  exact sym2MemSet_finite e.endpoints

instance instFiniteEdgeSetOfEdgeSet (F : Set (Edge α β)) [Finite F] :
    Finite E(ofEdgeSet F) := by
  change Finite F
  infer_instance

instance instFiniteVertexSetOfEdge (e : Edge α β) : Finite V(ofEdge e) := by
  change Finite V(ofEdgeSet {e})
  infer_instance

instance instFiniteEdgeSetOfEdge (e : Edge α β) : Finite E(ofEdge e) := by
  change Finite E(ofEdgeSet {e})
  infer_instance

end Graph

namespace DiGraph

/-- The general directed graph generated by the actual bundled arcs in `A`. Its vertices are
exactly the sources and targets of those arcs. -/
def ofArcSet (A : Set (Arc α β)) : DiGraph α β where
  vertexSet := Arc.source '' A ∪ Arc.target '' A
  edgeSet := A
  source_mem := fun a ha => Or.inl ⟨a, ha, rfl⟩
  target_mem := fun a ha => Or.inr ⟨a, ha, rfl⟩

/-- The general directed graph generated by the single actual bundled arc `a`. -/
def ofArc (a : Arc α β) : DiGraph α β := ofArcSet {a}

@[simp] theorem mem_vertexSet_ofArcSet (A : Set (Arc α β)) (v : α) :
    v ∈ (ofArcSet A).vertexSet ↔ (∃ a ∈ A, a.source = v) ∨ ∃ a ∈ A, a.target = v := by
  simp [ofArcSet]

@[simp] theorem edgeSet_ofArcSet (A : Set (Arc α β)) : (ofArcSet A).edgeSet = A := rfl

@[simp] theorem ofArcSet_isArc (A : Set (Arc α β)) (a : Arc α β) (u v : α) :
    (ofArcSet A).IsArc a u v ↔ a ∈ A ∧ a.source = u ∧ a.target = v := by
  rfl

@[simp] theorem ofArcSet_adj (A : Set (Arc α β)) (u v : α) :
    (ofArcSet A).Adj u v ↔ ∃ a ∈ A, a.source = u ∧ a.target = v := by
  simp [Adj]

@[simp] theorem mem_vertexSet_ofArc (a : Arc α β) (v : α) :
    v ∈ (ofArc a).vertexSet ↔ a.source = v ∨ a.target = v := by
  change v ∈ (ofArcSet {a}).vertexSet ↔ _
  rw [mem_vertexSet_ofArcSet]
  simp

@[simp] theorem mem_edgeSet_ofArc (a b : Arc α β) : b ∈ E(ofArc a) ↔ b = a := by
  simp [ofArc]

@[simp] theorem edgeSet_ofArc (a : Arc α β) : (ofArc a).edgeSet = {a} := rfl

@[simp] theorem ofArc_isArc (a b : Arc α β) (u v : α) :
    (ofArc a).IsArc b u v ↔ b = a ∧ a.source = u ∧ a.target = v := by
  change (ofArcSet {a}).IsArc b u v ↔ _
  rw [ofArcSet_isArc]
  constructor
  · rintro ⟨rfl, hsource, htarget⟩
    exact ⟨rfl, hsource, htarget⟩
  · rintro ⟨rfl, hsource, htarget⟩
    exact ⟨by simp, hsource, htarget⟩

@[simp] theorem ofArc_adj (a : Arc α β) (u v : α) :
    (ofArc a).Adj u v ↔ a.source = u ∧ a.target = v := by
  change (ofArcSet {a}).Adj u v ↔ _
  rw [ofArcSet_adj]
  simp

@[simp] theorem ofArcSet_empty : ofArcSet (∅ : Set (Arc α β)) = empty := by
  apply DiGraph.ext
  · ext v
    simp [ofArcSet]
  · rfl

instance instFiniteVertexSetOfArcSet (A : Set (Arc α β)) [Finite A] :
    Finite V(ofArcSet A) := by
  exact (((Set.toFinite A).image Arc.source).union
    ((Set.toFinite A).image Arc.target)).to_subtype

instance instFiniteEdgeSetOfArcSet (A : Set (Arc α β)) [Finite A] :
    Finite E(ofArcSet A) := by
  change Finite A
  infer_instance

instance instFiniteVertexSetOfArc (a : Arc α β) : Finite V(ofArc a) := by
  change Finite V(ofArcSet {a})
  infer_instance

instance instFiniteEdgeSetOfArc (a : Arc α β) : Finite E(ofArc a) := by
  change Finite E(ofArcSet {a})
  infer_instance

end DiGraph

/-! ## Single-edge simple graphs -/

namespace SimpleGraph

/-- The simple graph consisting of the single edge between distinct vertices `u` and `v`. -/
def singleEdge (u v : α) (hne : u ≠ v) : SimpleGraph α where
  vertexSet := {u, v}
  edgeSet := {s(u, v)}
  endpoints_mem := by
    intro e he x hx
    rw [Set.mem_singleton_iff] at he
    subst e
    simpa [Sym2.mem_iff] using hx
  loopless := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst e
    simpa [Sym2.mk_isDiag_iff] using hne

@[simp] theorem mem_vertexSet_singleEdge (u v : α) (hne : u ≠ v) (x : α) :
    x ∈ (singleEdge u v hne).vertexSet ↔ x = u ∨ x = v := by
  simp [singleEdge]

@[simp] theorem edgeSet_singleEdge (u v : α) (hne : u ≠ v) :
    (singleEdge u v hne).edgeSet = {s(u, v)} := rfl

@[simp] theorem mem_edgeSet_singleEdge (u v : α) (hne : u ≠ v) (e : Sym2 α) :
    e ∈ E(singleEdge u v hne) ↔ e = s(u, v) := by
  simp [singleEdge]

@[simp] theorem singleEdge_isLink (u v : α) (hne : u ≠ v) (e : Sym2 α) (x y : α) :
    (singleEdge u v hne).IsLink e x y ↔ e = s(u, v) ∧ e = s(x, y) := by
  rw [isLink_iff, mem_edgeSet_singleEdge]

@[simp] theorem singleEdge_adj (u v : α) (hne : u ≠ v) (x y : α) :
    (singleEdge u v hne).Adj x y ↔ s(x, y) = s(u, v) := by
  rw [adj_iff, mem_edgeSet_singleEdge]

theorem singleEdge_comm (u v : α) (hne : u ≠ v) :
    singleEdge u v hne = singleEdge v u (Ne.symm hne) := by
  ext <;> simp [singleEdge, or_comm, Sym2.eq_swap]

instance instFiniteVertexSetSingleEdge (u v : α) (hne : u ≠ v) :
    Finite V(singleEdge u v hne) := by
  change Finite ({u, v} : Set α)
  infer_instance

instance instFiniteEdgeSetSingleEdge (u v : α) (hne : u ≠ v) :
    Finite E(singleEdge u v hne) :=
  SimpleGraph.instFiniteEdgeSet (singleEdge u v hne)

end SimpleGraph

namespace SimpleDiGraph

/-- The simple directed graph consisting of the single arc from `u` to distinct `v`. -/
def singleArc (u v : α) (hne : u ≠ v) : SimpleDiGraph α where
  vertexSet := {u, v}
  edgeSet := {(u, v)}
  source_mem := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    simp
  target_mem := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    simp
  loopless := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hne

@[simp] theorem mem_vertexSet_singleArc (u v : α) (hne : u ≠ v) (x : α) :
    x ∈ (singleArc u v hne).vertexSet ↔ x = u ∨ x = v := by
  simp [singleArc]

@[simp] theorem edgeSet_singleArc (u v : α) (hne : u ≠ v) :
    (singleArc u v hne).edgeSet = {(u, v)} := rfl

@[simp] theorem mem_edgeSet_singleArc (u v : α) (hne : u ≠ v) (a : α × α) :
    a ∈ E(singleArc u v hne) ↔ a = (u, v) := by
  simp [singleArc]

@[simp] theorem singleArc_isArc (u v : α) (hne : u ≠ v) (a : α × α) (x y : α) :
    (singleArc u v hne).IsArc a x y ↔ a = (u, v) ∧ a.1 = x ∧ a.2 = y := by
  rw [isArc_iff, mem_edgeSet_singleArc]

@[simp] theorem singleArc_adj (u v : α) (hne : u ≠ v) (x y : α) :
    (singleArc u v hne).Adj x y ↔ x = u ∧ y = v := by
  rw [adj_iff, mem_edgeSet_singleArc]
  simp

instance instFiniteVertexSetSingleArc (u v : α) (hne : u ≠ v) :
    Finite V(singleArc u v hne) := by
  change Finite ({u, v} : Set α)
  infer_instance

instance instFiniteEdgeSetSingleArc (u v : α) (hne : u ≠ v) :
    Finite E(singleArc u v hne) :=
  SimpleDiGraph.instFiniteEdgeSet (singleArc u v hne)

end SimpleDiGraph

/-! ## Complete simple graphs -/

namespace SimpleGraph

/-- The complete simple graph on `S`: every unordered pair of distinct vertices in `S` is an
edge. -/
def complete (S : Set α) : SimpleGraph α where
  vertexSet := S
  edgeSet := {e | (∀ v ∈ e, v ∈ S) ∧ ¬e.IsDiag}
  endpoints_mem := fun _ he => he.1
  loopless := fun _ he => he.2

@[simp] theorem vertexSet_complete (S : Set α) : (complete S).vertexSet = S := rfl

@[simp] theorem edgeSet_complete (S : Set α) :
    (complete S).edgeSet = {e | (∀ v ∈ e, v ∈ S) ∧ ¬e.IsDiag} := rfl

@[simp] theorem mem_edgeSet_complete (S : Set α) (e : Sym2 α) :
    e ∈ E(complete S) ↔ (∀ v ∈ e, v ∈ S) ∧ ¬e.IsDiag := Iff.rfl

@[simp] theorem complete_isLink (S : Set α) (e : Sym2 α) (u v : α) :
    (complete S).IsLink e u v ↔
      e = s(u, v) ∧ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  constructor
  · rintro ⟨he, rfl⟩
    refine ⟨rfl, he.1 u (by simp), he.1 v (by simp), ?_⟩
    simpa [Sym2.mk_isDiag_iff] using he.2
  · rintro ⟨rfl, hu, hv, hne⟩
    exact ⟨by simp [complete, hu, hv, Sym2.mk_isDiag_iff, hne], rfl⟩

@[simp] theorem complete_adj (S : Set α) (u v : α) :
    (complete S).Adj u v ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  constructor
  · rintro ⟨e, he⟩
    exact ((complete_isLink S e u v).mp he).2
  · rintro ⟨hu, hv, hne⟩
    exact ⟨s(u, v), (complete_isLink S s(u, v) u v).mpr ⟨rfl, hu, hv, hne⟩⟩

@[simp] theorem complete_empty : complete (∅ : Set α) = empty := by
  apply SimpleGraph.ext
  · rfl
  · ext e
    induction e using Sym2.ind with
    | h u v =>
      change ((∀ x ∈ s(u, v), x ∈ (∅ : Set α)) ∧ ¬s(u, v).IsDiag) ↔ False
      constructor
      · intro he
        exact he.1 u (Sym2.mem_iff.mpr (Or.inl rfl))
      · exact False.elim

instance instFiniteVertexSetComplete (S : Set α) [Finite S] : Finite V(complete S) := by
  change Finite S
  infer_instance

instance instFiniteEdgeSetComplete (S : Set α) [Finite S] : Finite E(complete S) :=
  SimpleGraph.instFiniteEdgeSet (complete S)

end SimpleGraph

namespace SimpleDiGraph

/-- The complete simple directed graph on `S`: every ordered pair of distinct vertices in `S` is
an arc. -/
def complete (S : Set α) : SimpleDiGraph α where
  vertexSet := S
  edgeSet := {a | a.1 ∈ S ∧ a.2 ∈ S ∧ a.1 ≠ a.2}
  source_mem := fun _ ha => ha.1
  target_mem := fun _ ha => ha.2.1
  loopless := fun _ ha => ha.2.2

@[simp] theorem vertexSet_complete (S : Set α) : (complete S).vertexSet = S := rfl

@[simp] theorem edgeSet_complete (S : Set α) :
    (complete S).edgeSet = {a | a.1 ∈ S ∧ a.2 ∈ S ∧ a.1 ≠ a.2} := rfl

@[simp] theorem mem_edgeSet_complete (S : Set α) (a : α × α) :
    a ∈ E(complete S) ↔ a.1 ∈ S ∧ a.2 ∈ S ∧ a.1 ≠ a.2 := Iff.rfl

@[simp] theorem complete_isArc (S : Set α) (a : α × α) (u v : α) :
    (complete S).IsArc a u v ↔
      a = (u, v) ∧ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  constructor
  · rintro ⟨ha, hsource, htarget⟩
    have hpair : a = (u, v) := Prod.ext hsource htarget
    subst a
    exact ⟨rfl, ha.1, ha.2.1, ha.2.2⟩
  · rintro ⟨rfl, hu, hv, hne⟩
    exact ⟨⟨hu, hv, hne⟩, rfl, rfl⟩

@[simp] theorem complete_adj (S : Set α) (u v : α) :
    (complete S).Adj u v ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  rw [adj_iff]
  rfl

@[simp] theorem complete_empty : complete (∅ : Set α) = empty := by
  ext <;> simp [complete]

instance instFiniteVertexSetComplete (S : Set α) [Finite S] : Finite V(complete S) := by
  change Finite S
  infer_instance

instance instFiniteEdgeSetComplete (S : Set α) [Finite S] : Finite E(complete S) :=
  SimpleDiGraph.instFiniteEdgeSet (complete S)

end SimpleDiGraph

end GraphLib
