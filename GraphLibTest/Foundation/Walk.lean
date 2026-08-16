/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Theory.MooreBound
import GraphLib.Walk.Coverage

/-!
# Validated simple-spine regression checks

These checks freeze the declarations used by the relocated
`VertexSeq → SimpleWalk → SimplePath → SimpleCycle → Girth → MooreBound` chain.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ : Type*}

#check GraphLib.List.commonPrefix
#check GraphLib.List.commonPrefix_split
#check GraphLib.List.commonPrefix_ne_nil

#check GraphLib.Set.ncard_biUnion_finset_eq_sum
#check GraphLib.Set.mul_ncard_le_ncard_of_children

#check VertexSeq.singleton
#check VertexSeq.cons
#check VertexSeq.suffixFrom
#check VertexSeq.eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one

#check SimplePath.singleton
#check SimplePath.append
#check SimplePath.extendTail
#check SimplePath.vertices
#check SimplePath.head
#check SimplePath.tail
#check SimplePath.length
#check Path.glue
#check Path.relabelVertices
#check Path.relabelTags

#check SimpleGraph.IsVertexSeqIn.iff_edges
#check SimpleGraph.IsSimpleWalkIn.append
#check SimpleGraph.IsSimpleWalkIn.toSimpleGraph_le
#check SimpleGraph.IsSimpleWalkIn.of_toSimpleGraph_le
#check SimpleGraph.IsSimpleWalkIn.iff_toSimpleGraph_le
#check SimpleGraph.IsSimplePathIn.singleton
#check SimpleGraph.IsSimplePathIn.extendTail
#check SimpleGraph.IsSimplePathIn.exists_longer_of_adj_not_mem
#check SimpleGraph.IsSimplePathIn.glue
#check SimpleDiGraph.IsSimplePathIn.glue

#check SimpleCycle.ofPathClosing
#check SimpleCycle.ofInternallyDisjointPaths
#check SimpleCycle.ofTwoPaths
#check SimpleCycle.length_ofTwoPaths
#check SimpleCycle.head_ofTwoPaths_mem_left
#check SimpleCycle.edges_ofTwoPaths_subset
#check SimpleCycle.relabelVertices
#check SimpleDiCycle.relabelVertices
#check Cycle.relabelVertices
#check Cycle.relabelTags
#check DiCycle.relabelVertices
#check DiCycle.relabelTags

#check SimpleGraph.IsSimpleCycleIn.ofPathClosing
#check SimpleGraph.IsSimpleCycleIn.ofTwoPaths
#check SimpleGraph.IsSimpleCycleIn.exists_length_le_succ_of_adj_mem
#check SimpleGraph.IsSimpleCycleIn.exists_length_le_add_of_two_paths
#check Graph.IsPathIn.glue
#check Graph.IsPathIn.relabelVertices
#check Graph.IsCycleIn.relabelTags
#check DiGraph.IsPathIn.relabelTags
#check DiGraph.IsCycleIn.relabelVertices
#check SimpleGraph.IsSimplePathIn.induce_iff
#check SimpleGraph.IsSimpleCycleIn.deleteEdges_iff
#check SimpleDiGraph.IsSimplePathIn.relabelVertices
#check SimpleDiGraph.IsSimpleDiCycleIn.restrictEdges_iff

#check SimpleGraph.girth
#check SimpleGraph.mooreBound_odd
#check SimpleGraph.mooreBound_even

example (v : α) : (SimplePath.singleton v).vertices = VertexSeq.singleton v := rfl
example (v : α) : (SimplePath.singleton v).head = v := rfl
example (v : α) : (SimplePath.singleton v).tail = v := rfl
example (v : α) : (SimplePath.singleton v).length = 0 := rfl

example (p : SimplePath α) (v : α) (h : v ∉ p.vertices) :
    (p.extendTail v h).vertices = p.vertices.cons v := rfl
example (p : SimplePath α) (v : α) (h : v ∉ p.vertices) :
    (p.extendTail v h).tail = v := rfl

example (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).edges = p.edges ++ q.edges := by simp

example (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).tail = f p.tail := by simp

example (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).relabelVertices f.symm = p := by simp

example (c : Cycle α β) (g : β ≃ γ) :
    (c.relabelTags g).tags = c.tags.map g := by simp

example (c : DiCycle α β) (g : β ≃ γ) :
    (c.relabelTags g).relabelTags g.symm = c := by simp

example (c : SimpleCycle α) (f : α ≃ γ) :
    (c.relabelVertices f).relabelVertices f.symm = c := by simp

example (c : SimpleDiCycle α) (f : α ≃ γ) :
    (c.relabelVertices f).relabelVertices f.symm = c := by simp

/-! Phase 5: general walk identity and convention checks. -/

private def tagReuseWalk : Walk ℕ Bool :=
  ((Walk.singleton 0).cons 1 true).cons 2 true

example : tagReuseWalk.tags = [true, true] := by decide
example : tagReuseWalk.edges =
    [Edge.mk true s(0, 1), Edge.mk true s(1, 2)] := by decide
example : tagReuseWalk.edges[0] ≠ tagReuseWalk.edges[1] := by decide

private def tagReuseTrail : Trail ℕ Bool := ⟨tagReuseWalk, by decide⟩

/-- Eulerian coverage distinguishes the two same-tag actual bundled edges. -/
example : tagReuseWalk.toGraph.IsEulerianTrailIn tagReuseTrail := by
  constructor
  · exact (Graph.IsWalkIn.iff_toGraph_le tagReuseWalk.toGraph tagReuseWalk).2 le_rfl
  · intro e
    rfl

private def antiparallelWalk : Walk ℕ Bool :=
  ((Walk.singleton 0).cons 1 true).cons 0 true

/-- Same-tag antiparallel steps repeat an undirected actual edge. -/
example : ¬ antiparallelWalk.edges.Nodup := by
  simp [antiparallelWalk, Walk.edges]

/-- The same raw steps are distinct directed actual arcs. -/
example : antiparallelWalk.arcs.Nodup := by decide

private def loopWalk : Walk ℕ Unit := (Walk.singleton 0).cons 0 ()
private def loopCycle : Cycle ℕ Unit := ⟨loopWalk, by
  simp [loopWalk, Walk.closed, Walk.dropTail, Walk.vertices, Walk.edges]⟩

example : loopCycle.length = 1 := rfl

private def parallelTwoWalk : Walk ℕ Bool :=
  ((Walk.singleton 0).cons 1 false).cons 0 true
private def parallelTwoCycle : Cycle ℕ Bool := ⟨parallelTwoWalk, by
  simp [parallelTwoWalk, Walk.closed, Walk.dropTail, Walk.vertices, Walk.edges]⟩

example : parallelTwoCycle.length = 2 := rfl
example : parallelTwoCycle.edges.Nodup := parallelTwoCycle.edges_nodup

private def directedTwoWalk : SimpleWalk ℕ :=
  ⟨(VertexSeq.singleton 0).cons 1 |>.cons 0, by
    simp [VertexSeq.nonstalling, VertexSeq.tail]⟩
private def directedTwoCycle : SimpleDiCycle ℕ := ⟨directedTwoWalk, by
  simp [directedTwoWalk, SimpleWalk.IsDiCycle, SimpleWalk.closed, SimpleWalk.dropTail,
    VertexSeq.length, VertexSeq.dropTail, VertexSeq.closed, VertexSeq.nodup,
    VertexSeq.mem_def, VertexSeq.toList]⟩

example : directedTwoCycle.length = 2 := rfl
example : directedTwoCycle.arcs.Nodup := directedTwoCycle.arcs_nodup

/-- Undirected simple cycles retain the conventional lower bound of three. -/
example (c : SimpleCycle α) : 3 ≤ c.length := c.property.1

/-- Coverage data without realization is rejected. -/
example : ¬ (⊥ : Graph ℕ Unit).IsEulerianTrailIn
    (Trail.singleton 0 : Trail ℕ Unit) := by
  intro h
  have : 0 ∈ V((⊥ : Graph ℕ Unit)) := h.isTrailIn.head_mem
  simpa using this

example (w : Walk α Bool) : w.toGraph.IsWalkIn w :=
  (Graph.IsWalkIn.iff_toGraph_le w.toGraph w).2 le_rfl

example (w : Walk α Bool) : w.toDiGraph.IsWalkIn w :=
  (DiGraph.IsWalkIn.iff_toDiGraph_le w.toDiGraph w).2 le_rfl

example {G : Graph α Bool} {p : Path α Bool} (f : α ≃ α) (h : G.IsPathIn p) :
    (G.relabelVertices f).IsPathIn (p.relabelVertices f) := h.relabelVertices f

example {G : DiGraph α Bool} {c : DiCycle α Bool} (f : Bool ≃ Bool)
    (h : G.IsCycleIn c) :
    (G.relabelTags f).IsCycleIn (c.relabelTags f) := h.relabelTags f

example {G : DiGraph α Bool} {w : Walk α Bool} (h : G.IsWalkIn w) :
    G.reverse.IsWalkIn w.reverse := h.reverse

example {G : Graph α Bool} {t : Trail α Bool} (h : G.IsEulerianTrailIn t) :
    G.IsTrailIn t := h.isTrailIn

example {G : DiGraph α Bool} {p : Path α Bool} (h : G.IsHamiltonianPathIn p) :
    G.IsPathIn p := h.isPathIn

end GraphLib
