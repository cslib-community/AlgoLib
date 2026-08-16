/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Weight.Basic
import GraphLib.Walk.InGraph
import GraphLib.Walk.InDiGraph
import GraphLib.Walk.InSimpleGraph.Path
import GraphLib.Walk.InSimpleDiGraph.Path

/-!
# Traversal weights

Traversal weights sum attached data over reconstructed actual edges or arcs. A realization proof
is not needed to compute a weight. It is needed only when replacing a weight by another function
that agrees on the active edge set of the ambient graph.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ δ W : Type*}

/-! ## General undirected graphs -/

namespace Graph

/-- The weight of a raw undirected walk, summed over its reconstructed bundled actual edges. -/
def walkWeight [AddMonoid W] (G : Graph α β) (weight : G.EdgeWeight W)
    (w : Walk α β) : W := (w.edges.map weight).sum

/-- The weight of a general path, summed over its reconstructed bundled actual edges. -/
def pathWeight [AddMonoid W] (G : Graph α β) (weight : G.EdgeWeight W)
    (p : Path α β) : W := G.walkWeight weight p.val

@[simp] theorem walkWeight_singleton [AddMonoid W] (G : Graph α β)
    (weight : G.EdgeWeight W) (v : α) : G.walkWeight weight (.singleton v) = 0 := rfl

@[simp] theorem pathWeight_singleton [AddMonoid W] (G : Graph α β)
    (weight : G.EdgeWeight W) (v : α) :
    G.pathWeight weight (Path.singleton v) = 0 := rfl

@[simp] theorem walkWeight_cons [AddMonoid W] (G : Graph α β) (weight : G.EdgeWeight W)
    (w : Walk α β) (v : α) (t : β) :
    G.walkWeight weight (w.cons v t) =
      G.walkWeight weight w + weight ⟨t, s(w.tail, v)⟩ := by
  simp [walkWeight, List.concat_eq_append]

theorem walkWeight_append [AddMonoid W] (G : Graph α β) (weight : G.EdgeWeight W)
    (p q : Walk α β) (t : β) :
    G.walkWeight weight (p.append q t) =
      G.walkWeight weight p + weight ⟨t, s(p.tail, q.head)⟩ + G.walkWeight weight q := by
  simp [walkWeight, Walk.edges_append, List.map_append, List.sum_append, add_assoc]

theorem walkWeight_glue [AddMonoid W] (G : Graph α β) (weight : G.EdgeWeight W)
    (p q : Walk α β) (h : p.tail = q.head) :
    G.walkWeight weight (p.glue q h) = G.walkWeight weight p + G.walkWeight weight q := by
  simp [walkWeight, Walk.edges_glue, List.map_append, List.sum_append]

@[simp] theorem pathWeight_eq_walkWeight [AddMonoid W] (G : Graph α β)
    (weight : G.EdgeWeight W) (p : Path α β) :
    G.pathWeight weight p = G.walkWeight weight p.val := rfl

theorem pathWeight_append [AddMonoid W] (G : Graph α β) (weight : G.EdgeWeight W)
    (p q : Path α β) (t : β) (hdisj : ∀ v ∈ p.vertices, v ∈ q.vertices → False) :
    G.pathWeight weight (p.append q t hdisj) =
      G.pathWeight weight p + weight ⟨t, s(p.tail, q.head)⟩ + G.pathWeight weight q := by
  exact G.walkWeight_append weight p.val q.val t

theorem pathWeight_glue [AddMonoid W] (G : Graph α β) (weight : G.EdgeWeight W)
    (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    G.pathWeight weight (p.glue q h hdisj) =
      G.pathWeight weight p + G.pathWeight weight q :=
  G.walkWeight_glue weight p.val q.val h

/-- Realized walks have equal sums for weights that agree on the active actual edges. -/
theorem walkWeight_congr [AddMonoid W] (G : Graph α β) {weight₁ weight₂ : G.EdgeWeight W}
    {w : Walk α β} (hweight : Graph.EdgeWeight.EqOn G weight₁ weight₂)
    (hw : G.IsWalkIn w) : G.walkWeight weight₁ w = G.walkWeight weight₂ w := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact hweight (hw.edge_mem he)

/-- Realized paths have equal sums for weights that agree on the active actual edges. -/
theorem pathWeight_congr [AddMonoid W] (G : Graph α β)
    {weight₁ weight₂ : G.EdgeWeight W} {p : Path α β}
    (hweight : Graph.EdgeWeight.EqOn G weight₁ weight₂) (hp : G.IsPathIn p) :
    G.pathWeight weight₁ p = G.pathWeight weight₂ p :=
  G.walkWeight_congr hweight hp.isWalkIn

/-- Undirected reversal preserves traversal weight. -/
@[simp] theorem walkWeight_reverse [AddCommMonoid W] (G : Graph α β)
    (weight : G.EdgeWeight W) (w : Walk α β) :
    G.walkWeight weight w.reverse = G.walkWeight weight w := by
  simp [walkWeight]

@[simp] theorem pathWeight_reverse [AddCommMonoid W] (G : Graph α β)
    (weight : G.EdgeWeight W) (p : Path α β) :
    G.pathWeight weight p.reverse = G.pathWeight weight p := by
  simp [pathWeight]

/-- Vertex relabeling preserves walk weight under the corresponding transported data. -/
theorem walkWeight_relabelVertices [AddMonoid W] (G : Graph α β) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (w : Walk α β) :
    (G.relabelVertices f).walkWeight (Graph.EdgeWeight.transportRelabelVertices G f weight)
      (w.mapVertices f) = G.walkWeight weight w := by
  induction w with
  | singleton v => rfl
  | cons w v t ih =>
      rw [Walk.mapVertices, walkWeight_cons, walkWeight_cons, ih]
      congr 1
      simp only [Walk.tail_mapVertices]
      have heq : Edge.mk t s(f w.tail, f v) =
          Edge.relabelVertices f ⟨t, s(w.tail, v)⟩ := by
        apply Edge.ext <;> simp
      rw [heq, Graph.EdgeWeight.transportRelabelVertices_apply]

/-- Tag relabeling preserves walk weight under the corresponding transported data. -/
theorem walkWeight_relabelTags [AddMonoid W] (G : Graph α β) (f : β ≃ δ)
    (weight : G.EdgeWeight W) (w : Walk α β) :
    (G.relabelTags f).walkWeight (Graph.EdgeWeight.transportRelabelTags G f weight)
      (w.mapTags f) = G.walkWeight weight w := by
  induction w with
  | singleton v => rfl
  | cons w v t ih =>
      rw [Walk.mapTags, walkWeight_cons, walkWeight_cons, ih]
      congr 1
      simp only [Walk.tail_mapTags]
      change Graph.EdgeWeight.transportRelabelTags G f weight
        (Edge.relabelTags f ⟨t, s(w.tail, v)⟩) = _
      rw [Graph.EdgeWeight.transportRelabelTags_apply]

theorem pathWeight_relabelVertices [AddMonoid W] (G : Graph α β) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (p : Path α β) :
    (G.relabelVertices f).pathWeight (Graph.EdgeWeight.transportRelabelVertices G f weight)
      (p.relabelVertices f) = G.pathWeight weight p :=
  G.walkWeight_relabelVertices f weight p.val

theorem pathWeight_relabelTags [AddMonoid W] (G : Graph α β) (f : β ≃ δ)
    (weight : G.EdgeWeight W) (p : Path α β) :
    (G.relabelTags f).pathWeight (Graph.EdgeWeight.transportRelabelTags G f weight)
      (p.relabelTags f) = G.pathWeight weight p :=
  G.walkWeight_relabelTags f weight p.val

end Graph

/-! ## General directed graphs -/

namespace DiGraph

/-- The weight of a raw directed walk, summed over its reconstructed bundled actual arcs. -/
def walkWeight [AddMonoid W] (G : DiGraph α β) (weight : G.EdgeWeight W)
    (w : Walk α β) : W := (w.arcs.map weight).sum

/-- The weight of a directed path, summed over its reconstructed bundled actual arcs. -/
def pathWeight [AddMonoid W] (G : DiGraph α β) (weight : G.EdgeWeight W)
    (p : Path α β) : W := G.walkWeight weight p.val

@[simp] theorem walkWeight_singleton [AddMonoid W] (G : DiGraph α β)
    (weight : G.EdgeWeight W) (v : α) : G.walkWeight weight (.singleton v) = 0 := rfl

@[simp] theorem pathWeight_singleton [AddMonoid W] (G : DiGraph α β)
    (weight : G.EdgeWeight W) (v : α) :
    G.pathWeight weight (Path.singleton v) = 0 := rfl

@[simp] theorem walkWeight_cons [AddMonoid W] (G : DiGraph α β) (weight : G.EdgeWeight W)
    (w : Walk α β) (v : α) (t : β) :
    G.walkWeight weight (w.cons v t) =
      G.walkWeight weight w + weight ⟨t, (w.tail, v)⟩ := by
  simp [walkWeight, List.concat_eq_append]

theorem walkWeight_append [AddMonoid W] (G : DiGraph α β) (weight : G.EdgeWeight W)
    (p q : Walk α β) (t : β) :
    G.walkWeight weight (p.append q t) =
      G.walkWeight weight p + weight ⟨t, (p.tail, q.head)⟩ + G.walkWeight weight q := by
  simp [walkWeight, Walk.arcs_append, List.map_append, List.sum_append, add_assoc]

theorem walkWeight_glue [AddMonoid W] (G : DiGraph α β) (weight : G.EdgeWeight W)
    (p q : Walk α β) (h : p.tail = q.head) :
    G.walkWeight weight (p.glue q h) = G.walkWeight weight p + G.walkWeight weight q := by
  simp [walkWeight, Walk.arcs_glue, List.map_append, List.sum_append]

@[simp] theorem pathWeight_eq_walkWeight [AddMonoid W] (G : DiGraph α β)
    (weight : G.EdgeWeight W) (p : Path α β) :
    G.pathWeight weight p = G.walkWeight weight p.val := rfl

theorem pathWeight_append [AddMonoid W] (G : DiGraph α β) (weight : G.EdgeWeight W)
    (p q : Path α β) (t : β) (hdisj : ∀ v ∈ p.vertices, v ∈ q.vertices → False) :
    G.pathWeight weight (p.append q t hdisj) =
      G.pathWeight weight p + weight ⟨t, (p.tail, q.head)⟩ + G.pathWeight weight q := by
  exact G.walkWeight_append weight p.val q.val t

theorem pathWeight_glue [AddMonoid W] (G : DiGraph α β) (weight : G.EdgeWeight W)
    (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    G.pathWeight weight (p.glue q h hdisj) =
      G.pathWeight weight p + G.pathWeight weight q :=
  G.walkWeight_glue weight p.val q.val h

/-- Realized directed walks have equal sums for weights agreeing on active actual arcs. -/
theorem walkWeight_congr [AddMonoid W] (G : DiGraph α β)
    {weight₁ weight₂ : G.EdgeWeight W} {w : Walk α β}
    (hweight : DiGraph.EdgeWeight.EqOn G weight₁ weight₂) (hw : G.IsWalkIn w) :
    G.walkWeight weight₁ w = G.walkWeight weight₂ w := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact hweight (hw.arc_mem ha)

/-- Realized directed paths have equal sums for weights agreeing on active actual arcs. -/
theorem pathWeight_congr [AddMonoid W] (G : DiGraph α β)
    {weight₁ weight₂ : G.EdgeWeight W} {p : Path α β}
    (hweight : DiGraph.EdgeWeight.EqOn G weight₁ weight₂) (hp : G.IsPathIn p) :
    G.pathWeight weight₁ p = G.pathWeight weight₂ p :=
  G.walkWeight_congr hweight hp.isWalkIn

/-- Reversing a directed walk preserves weight after transporting data through arc reversal. -/
@[simp] theorem walkWeight_reverse [AddCommMonoid W] (G : DiGraph α β)
    (weight : G.EdgeWeight W) (w : Walk α β) :
    G.reverse.walkWeight (DiGraph.EdgeWeight.transportReverse G weight) w.reverse =
      G.walkWeight weight w := by
  rw [walkWeight, Walk.arcs_reverse, List.map_map, List.map_reverse, List.sum_reverse]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact DiGraph.EdgeWeight.transportReverse_apply G weight a

@[simp] theorem pathWeight_reverse [AddCommMonoid W] (G : DiGraph α β)
    (weight : G.EdgeWeight W) (p : Path α β) :
    G.reverse.pathWeight (DiGraph.EdgeWeight.transportReverse G weight) p.reverse =
      G.pathWeight weight p := by
  exact G.walkWeight_reverse weight p.val

/-- Vertex relabeling preserves directed walk weight under transported data. -/
theorem walkWeight_relabelVertices [AddMonoid W] (G : DiGraph α β) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (w : Walk α β) :
    (G.relabelVertices f).walkWeight (DiGraph.EdgeWeight.transportRelabelVertices G f weight)
      (w.mapVertices f) = G.walkWeight weight w := by
  induction w with
  | singleton v => rfl
  | cons w v t ih =>
      rw [Walk.mapVertices, walkWeight_cons, walkWeight_cons, ih]
      congr 1
      simp only [Walk.tail_mapVertices]
      have heq : Arc.mk t (f w.tail, f v) =
          Arc.relabelVertices f ⟨t, (w.tail, v)⟩ := by
        apply Arc.ext <;> simp
      rw [heq, DiGraph.EdgeWeight.transportRelabelVertices_apply]

/-- Tag relabeling preserves directed walk weight under transported data. -/
theorem walkWeight_relabelTags [AddMonoid W] (G : DiGraph α β) (f : β ≃ δ)
    (weight : G.EdgeWeight W) (w : Walk α β) :
    (G.relabelTags f).walkWeight (DiGraph.EdgeWeight.transportRelabelTags G f weight)
      (w.mapTags f) = G.walkWeight weight w := by
  induction w with
  | singleton v => rfl
  | cons w v t ih =>
      rw [Walk.mapTags, walkWeight_cons, walkWeight_cons, ih]
      congr 1
      simp only [Walk.tail_mapTags]
      change DiGraph.EdgeWeight.transportRelabelTags G f weight
        (Arc.relabelTags f ⟨t, (w.tail, v)⟩) = _
      rw [DiGraph.EdgeWeight.transportRelabelTags_apply]

theorem pathWeight_relabelVertices [AddMonoid W] (G : DiGraph α β) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (p : Path α β) :
    (G.relabelVertices f).pathWeight (DiGraph.EdgeWeight.transportRelabelVertices G f weight)
      (p.relabelVertices f) = G.pathWeight weight p :=
  G.walkWeight_relabelVertices f weight p.val

theorem pathWeight_relabelTags [AddMonoid W] (G : DiGraph α β) (f : β ≃ δ)
    (weight : G.EdgeWeight W) (p : Path α β) :
    (G.relabelTags f).pathWeight (DiGraph.EdgeWeight.transportRelabelTags G f weight)
      (p.relabelTags f) = G.pathWeight weight p :=
  G.walkWeight_relabelTags f weight p.val

end DiGraph

/-! ## Simple undirected graphs -/

namespace SimpleGraph

/-- The weight of a simple walk, summed over its actual unordered edge pairs. -/
def walkWeight [AddMonoid W] (G : SimpleGraph α) (weight : G.EdgeWeight W)
    (w : SimpleWalk α) : W := (w.edges.map weight).sum

/-- The weight of a simple path, summed over its actual unordered edge pairs. -/
def pathWeight [AddMonoid W] (G : SimpleGraph α) (weight : G.EdgeWeight W)
    (p : SimplePath α) : W := G.walkWeight weight p.val

@[simp] theorem pathWeight_singleton [AddMonoid W] (G : SimpleGraph α)
    (weight : G.EdgeWeight W) (v : α) :
    G.pathWeight weight (SimplePath.singleton v) = 0 := rfl

@[simp] theorem pathWeight_extendTail [AddMonoid W] (G : SimpleGraph α)
    (weight : G.EdgeWeight W) (p : SimplePath α) (v : α)
    (hfresh : v ∉ p.vertices) :
    G.pathWeight weight (p.extendTail v hfresh) =
      G.pathWeight weight p + weight s(p.tail, v) := by
  simp [pathWeight, walkWeight, List.concat_eq_append]

theorem walkWeight_append [AddMonoid W] (G : SimpleGraph α) (weight : G.EdgeWeight W)
    (p q : SimpleWalk α) (h : p.tail ≠ q.head) :
    G.walkWeight weight (p.append q h) =
      G.walkWeight weight p + weight s(p.tail, q.head) + G.walkWeight weight q := by
  rw [walkWeight, SimpleWalk.edges_append]
  simp [walkWeight, List.map_append, List.sum_append, add_assoc]

theorem walkWeight_glue [AddMonoid W] (G : SimpleGraph α) (weight : G.EdgeWeight W)
    (p q : SimpleWalk α) (h : p.tail = q.head) :
    G.walkWeight weight (p.glue q h) = G.walkWeight weight p + G.walkWeight weight q := by
  rw [walkWeight, SimpleWalk.edges_glue]
  simp [walkWeight, List.map_append, List.sum_append]

@[simp] theorem pathWeight_eq_walkWeight [AddMonoid W] (G : SimpleGraph α)
    (weight : G.EdgeWeight W) (p : SimplePath α) :
    G.pathWeight weight p = G.walkWeight weight p.val := rfl

theorem pathWeight_append [AddMonoid W] (G : SimpleGraph α) (weight : G.EdgeWeight W)
    (p q : SimplePath α)
    (hdisj : ∀ v : α, v ∈ p.vertices → v ∈ q.vertices → False) :
    G.pathWeight weight (p.append q hdisj) =
      G.pathWeight weight p + weight s(p.tail, q.head) + G.pathWeight weight q := by
  have hne : p.val.tail ≠ q.val.head := by
    intro h
    apply hdisj p.tail (VertexSeq.tail_mem p.vertices)
    change p.val.tail ∈ q.val.val
    rw [h]
    exact VertexSeq.head_mem q.vertices
  simpa [pathWeight, SimplePath.append] using G.walkWeight_append weight p.val q.val hne

theorem pathWeight_glue [AddMonoid W] (G : SimpleGraph α) (weight : G.EdgeWeight W)
    (p q : SimplePath α) (h : p.tail = q.head)
    (hdisj : p.vertices.length ≠ 0 →
      ∀ v : α, v ∈ p.vertices.dropTail → v ∈ q.vertices → False) :
    G.pathWeight weight (p.glue q h hdisj) =
      G.pathWeight weight p + G.pathWeight weight q :=
  G.walkWeight_glue weight p.val q.val h

/-- Realized simple walks have equal sums for weights agreeing on active edges. -/
theorem walkWeight_congr [AddMonoid W] (G : SimpleGraph α)
    {weight₁ weight₂ : G.EdgeWeight W} {w : SimpleWalk α}
    (hweight : SimpleGraph.EdgeWeight.EqOn G weight₁ weight₂)
    (hw : G.IsSimpleWalkIn w) : G.walkWeight weight₁ w = G.walkWeight weight₂ w := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact hweight (hw.edge_mem G he)

/-- Realized simple paths have equal sums for weights agreeing on active edges. -/
theorem pathWeight_congr [AddMonoid W] (G : SimpleGraph α)
    {weight₁ weight₂ : G.EdgeWeight W} {p : SimplePath α}
    (hweight : SimpleGraph.EdgeWeight.EqOn G weight₁ weight₂)
    (hp : G.IsSimplePathIn p) : G.pathWeight weight₁ p = G.pathWeight weight₂ p :=
  G.walkWeight_congr hweight ((SimpleGraph.IsSimplePathIn.iff_isSimpleWalkIn G p).mp hp)

/-- Undirected simple-walk reversal preserves traversal weight. -/
@[simp] theorem walkWeight_reverse [AddCommMonoid W] (G : SimpleGraph α)
    (weight : G.EdgeWeight W) (w : SimpleWalk α) :
    G.walkWeight weight w.reverse = G.walkWeight weight w := by
  simp [walkWeight]

@[simp] theorem pathWeight_reverse [AddCommMonoid W] (G : SimpleGraph α)
    (weight : G.EdgeWeight W) (p : SimplePath α) :
    G.pathWeight weight p.reverse = G.pathWeight weight p := by
  exact G.walkWeight_reverse weight p.val

/-- Vertex relabeling preserves simple-walk weight under transported data. -/
theorem walkWeight_relabelVertices [AddMonoid W] (G : SimpleGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (w : SimpleWalk α) :
    (G.relabelVertices f).walkWeight
      (SimpleGraph.EdgeWeight.transportRelabelVertices G f weight)
      (w.map f f.injective) = G.walkWeight weight w := by
  rcases w with ⟨w, hw⟩
  change ((w.map f).edges.map (weight ∘ Sym2.map f.symm)).sum =
    (w.edges.map weight).sum
  induction w with
  | singleton v => rfl
  | cons q v ih =>
      simp only [VertexSeq.map, VertexSeq.edges_cons, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      rw [ih hw.1]
      simp

theorem pathWeight_relabelVertices [AddMonoid W] (G : SimpleGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (p : SimplePath α) :
    (G.relabelVertices f).pathWeight
      (SimpleGraph.EdgeWeight.transportRelabelVertices G f weight)
      (p.map f f.injective) = G.pathWeight weight p :=
  G.walkWeight_relabelVertices f weight p.val

end SimpleGraph

/-! ## Simple directed graphs -/

namespace SimpleDiGraph

/-- The weight of a simple directed walk, summed over its actual ordered arc pairs. -/
def walkWeight [AddMonoid W] (G : SimpleDiGraph α) (weight : G.EdgeWeight W)
    (w : SimpleWalk α) : W := (w.arcs.map weight).sum

/-- The weight of a simple directed path, summed over its actual ordered arc pairs. -/
def pathWeight [AddMonoid W] (G : SimpleDiGraph α) (weight : G.EdgeWeight W)
    (p : SimplePath α) : W := G.walkWeight weight p.val

@[simp] theorem pathWeight_singleton [AddMonoid W] (G : SimpleDiGraph α)
    (weight : G.EdgeWeight W) (v : α) :
    G.pathWeight weight (SimplePath.singleton v) = 0 := rfl

@[simp] theorem pathWeight_extendTail [AddMonoid W] (G : SimpleDiGraph α)
    (weight : G.EdgeWeight W) (p : SimplePath α) (v : α)
    (hfresh : v ∉ p.vertices) :
    G.pathWeight weight (p.extendTail v hfresh) =
      G.pathWeight weight p + weight (p.tail, v) := by
  simp [pathWeight, walkWeight, List.concat_eq_append]

theorem walkWeight_append [AddMonoid W] (G : SimpleDiGraph α) (weight : G.EdgeWeight W)
    (p q : SimpleWalk α) (h : p.tail ≠ q.head) :
    G.walkWeight weight (p.append q h) =
      G.walkWeight weight p + weight (p.tail, q.head) + G.walkWeight weight q := by
  rw [walkWeight, SimpleWalk.arcs_append]
  simp [walkWeight, List.map_append, List.sum_append, add_assoc]

theorem walkWeight_glue [AddMonoid W] (G : SimpleDiGraph α) (weight : G.EdgeWeight W)
    (p q : SimpleWalk α) (h : p.tail = q.head) :
    G.walkWeight weight (p.glue q h) = G.walkWeight weight p + G.walkWeight weight q := by
  rw [walkWeight, SimpleWalk.arcs_glue]
  simp [walkWeight, List.map_append, List.sum_append]

@[simp] theorem pathWeight_eq_walkWeight [AddMonoid W] (G : SimpleDiGraph α)
    (weight : G.EdgeWeight W) (p : SimplePath α) :
    G.pathWeight weight p = G.walkWeight weight p.val := rfl

theorem pathWeight_append [AddMonoid W] (G : SimpleDiGraph α) (weight : G.EdgeWeight W)
    (p q : SimplePath α)
    (hdisj : ∀ v : α, v ∈ p.vertices → v ∈ q.vertices → False) :
    G.pathWeight weight (p.append q hdisj) =
      G.pathWeight weight p + weight (p.tail, q.head) + G.pathWeight weight q := by
  have hne : p.val.tail ≠ q.val.head := by
    intro h
    apply hdisj p.tail (VertexSeq.tail_mem p.vertices)
    change p.val.tail ∈ q.val.val
    rw [h]
    exact VertexSeq.head_mem q.vertices
  simpa [pathWeight, SimplePath.append] using G.walkWeight_append weight p.val q.val hne

theorem pathWeight_glue [AddMonoid W] (G : SimpleDiGraph α) (weight : G.EdgeWeight W)
    (p q : SimplePath α) (h : p.tail = q.head)
    (hdisj : p.vertices.length ≠ 0 →
      ∀ v : α, v ∈ p.vertices.dropTail → v ∈ q.vertices → False) :
    G.pathWeight weight (p.glue q h hdisj) =
      G.pathWeight weight p + G.pathWeight weight q :=
  G.walkWeight_glue weight p.val q.val h

/-- Realized simple directed walks have equal sums for weights agreeing on active arcs. -/
theorem walkWeight_congr [AddMonoid W] (G : SimpleDiGraph α)
    {weight₁ weight₂ : G.EdgeWeight W} {w : SimpleWalk α}
    (hweight : SimpleDiGraph.EdgeWeight.EqOn G weight₁ weight₂)
    (hw : G.IsSimpleWalkIn w) : G.walkWeight weight₁ w = G.walkWeight weight₂ w := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact hweight (hw.arc_mem G ha)

/-- Realized simple directed paths have equal sums for weights agreeing on active arcs. -/
theorem pathWeight_congr [AddMonoid W] (G : SimpleDiGraph α)
    {weight₁ weight₂ : G.EdgeWeight W} {p : SimplePath α}
    (hweight : SimpleDiGraph.EdgeWeight.EqOn G weight₁ weight₂)
    (hp : G.IsSimplePathIn p) : G.pathWeight weight₁ p = G.pathWeight weight₂ p :=
  G.walkWeight_congr hweight hp.isSimpleWalkIn

/-- Directed simple-walk reversal preserves weight under pair-swap transport. -/
@[simp] theorem walkWeight_reverse [AddCommMonoid W] (G : SimpleDiGraph α)
    (weight : G.EdgeWeight W) (w : SimpleWalk α) :
    G.reverse.walkWeight (SimpleDiGraph.EdgeWeight.transportReverse G weight) w.reverse =
      G.walkWeight weight w := by
  simp [walkWeight, SimpleDiGraph.EdgeWeight.transportReverse,
    SimpleDiGraph.EdgeWeight.transport, SimpleDiGraph.arcReverseEquiv,
    List.map_map, Function.comp_def]

@[simp] theorem pathWeight_reverse [AddCommMonoid W] (G : SimpleDiGraph α)
    (weight : G.EdgeWeight W) (p : SimplePath α) :
    G.reverse.pathWeight (SimpleDiGraph.EdgeWeight.transportReverse G weight) p.reverse =
      G.pathWeight weight p := by
  exact G.walkWeight_reverse weight p.val

/-- Vertex relabeling preserves simple directed walk weight under transported data. -/
theorem walkWeight_relabelVertices [AddMonoid W] (G : SimpleDiGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (w : SimpleWalk α) :
    (G.relabelVertices f).walkWeight
      (SimpleDiGraph.EdgeWeight.transportRelabelVertices G f weight)
      (w.map f f.injective) = G.walkWeight weight w := by
  rcases w with ⟨w, hw⟩
  change ((w.map f).arcs.map (weight ∘ Prod.map f.symm f.symm)).sum =
    (w.arcs.map weight).sum
  induction w with
  | singleton v => rfl
  | cons q v ih =>
      simp only [VertexSeq.map, VertexSeq.arcs_cons, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      rw [ih hw.1]
      simp

theorem pathWeight_relabelVertices [AddMonoid W] (G : SimpleDiGraph α) (f : α ≃ γ)
    (weight : G.EdgeWeight W) (p : SimplePath α) :
    (G.relabelVertices f).pathWeight
      (SimpleDiGraph.EdgeWeight.transportRelabelVertices G f weight)
      (p.map f f.injective) = G.pathWeight weight p :=
  G.walkWeight_relabelVertices f weight p.val

end SimpleDiGraph

end GraphLib
