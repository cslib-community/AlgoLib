/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Walk.InSimpleGraph.Path
import GraphLib.Walk.SimpleCycle
import Mathlib.Data.Set.Card

/-!
# Simple cycles realized in a simple graph

`SimpleGraph.IsSimpleCycleIn G c` says a `SimpleCycle` is realized in `G`, together with the
cycle-construction lemmas that build a realized cycle out of realized paths. Cycle-existence and
acyclicity predicates live in `GraphLib.Connectivity.Acyclic`.

Part of the `InSimpleGraph` folder; see the umbrella module
`GraphLib.Walk.InSimpleGraph`.

## Main definitions

* `SimpleGraph.IsSimpleCycleIn` — a simple cycle realized in a graph.

## Main results

* `SimpleGraph.IsSimpleCycleIn.ofPathClosing` — close a realized path into a cycle.
* `SimpleGraph.IsSimpleCycleIn.ofTwoPaths` — obtain a realized cycle from two paths.
-/

variable {α γ : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Simple cycles realized in a graph -/

/-- A simple cycle is realized in `G` when its underlying simple walk is
realized in `G`. -/
@[grind] def IsSimpleCycleIn (G : SimpleGraph α) (c : SimpleCycle α) : Prop :=
  G.IsSimpleWalkIn c.val

namespace IsSimpleCycleIn

/-- Realization of a simple cycle is realization of its underlying simple walk. -/
@[simp, grind =] lemma iff_isSimpleWalkIn
    (G : SimpleGraph α) (c : SimpleCycle α) :
    G.IsSimpleCycleIn c ↔ G.IsSimpleWalkIn c.val := Iff.rfl

/-- Reversing a realized cycle preserves realization. -/
@[grind →] lemma reverse (G : SimpleGraph α) {c : SimpleCycle α}
    (hc : G.IsSimpleCycleIn c) : G.IsSimpleCycleIn c.reverse :=
  IsSimpleWalkIn.reverse G hc

/-- Every edge traversed by a realized cycle is an edge of the graph. -/
@[grind →] lemma edge_mem (G : SimpleGraph α) {c : SimpleCycle α}
    (hc : G.IsSimpleCycleIn c) {e : Sym2 α} (he : e ∈ c.edges) : e ∈ E(G) :=
  IsSimpleWalkIn.edge_mem G hc he

/-- The generated graph of a realized cycle is a subgraph of `G`. -/
lemma toSimpleGraph_le (G : SimpleGraph α) {c : SimpleCycle α}
    (hc : G.IsSimpleCycleIn c) : c.val.toSimpleGraph ≤ G :=
  IsSimpleWalkIn.toSimpleGraph_le G hc

/-- Realization is monotone under passing to a supergraph. -/
@[grind →] lemma mono (G H : SimpleGraph α) {c : SimpleCycle α}
    (hc : H.IsSimpleCycleIn c) (hsub : H ≤ G) :
    G.IsSimpleCycleIn c :=
  IsSimpleWalkIn.mono G H hc hsub

theorem induce_iff (G : SimpleGraph α) (S : Set α) (c : SimpleCycle α) :
    (G.induce S).IsSimpleCycleIn c ↔
      G.IsSimpleCycleIn c ∧ ∀ v ∈ c.support, v ∈ S :=
  IsSimpleWalkIn.induce_iff G S c.val

theorem restrictEdges_iff (G : SimpleGraph α) (F : Set (Sym2 α)) (c : SimpleCycle α) :
    (G.restrictEdges F).IsSimpleCycleIn c ↔
      G.IsSimpleCycleIn c ∧ ∀ e ∈ c.edges, e ∈ F :=
  IsSimpleWalkIn.restrictEdges_iff G F c.val

theorem deleteEdges_iff (G : SimpleGraph α) (F : Set (Sym2 α)) (c : SimpleCycle α) :
    (G.deleteEdges F).IsSimpleCycleIn c ↔
      G.IsSimpleCycleIn c ∧ ∀ e ∈ c.edges, e ∉ F :=
  IsSimpleWalkIn.deleteEdges_iff G F c.val

theorem relabelVertices {G : SimpleGraph α} {c : SimpleCycle α} (f : α ≃ γ)
    (h : G.IsSimpleCycleIn c) :
    (G.relabelVertices f).IsSimpleCycleIn (c.relabelVertices f) :=
  IsSimpleWalkIn.relabelVertices f h

/-- Closing a realized simple path by an edge from its tail to its head gives a
realized simple cycle. -/
lemma ofPathClosing (G : SimpleGraph α) {p : SimplePath α}
    (hp : G.IsSimplePathIn p) (hclose : G.Adj p.tail p.head)
    (hlen : 2 ≤ p.length) :
    G.IsSimpleCycleIn (SimpleCycle.ofPathClosing p hlen) := by
  change G.IsSimpleWalkIn (SimpleCycle.ofPathClosing p hlen).val
  change G.IsVertexSeqIn (VertexSeq.cons (SimplePath.vertices p) (SimplePath.head p))
  exact IsVertexSeqIn.cons (SimplePath.vertices p) (SimplePath.head p) hp hclose

/-- Two realized internally disjoint paths with the same endpoints form a
realized simple cycle. -/
lemma ofInternallyDisjointPaths (G : SimpleGraph α) {P Q : SimplePath α}
    (hP : G.IsSimplePathIn P) (hQ : G.IsSimplePathIn Q)
    (hhead : P.head = Q.head) (htail : P.tail = Q.tail)
    (hab : P.head ≠ P.tail)
    (hint : ∀ z, z ∈ P.vertices → z ∈ Q.vertices →
      z = P.head ∨ z = P.tail)
    (hlen : 3 ≤ P.length + Q.length) :
    G.IsSimpleCycleIn
      (SimpleCycle.ofInternallyDisjointPaths P Q hhead htail hab hint hlen) := by
  change G.IsSimpleWalkIn
    (SimpleCycle.ofInternallyDisjointPaths P Q hhead htail hab hint hlen).val
  unfold SimpleCycle.ofInternallyDisjointPaths
  apply IsSimpleWalkIn.glue G hP (IsSimpleWalkIn.reverse G hQ)
  change P.vertices.tail = Q.vertices.reverse.head
  simpa only [VertexSeq.head_reverse] using htail

/-- Two distinct realized simple paths with the same endpoints determine a
realized simple cycle. -/
lemma ofTwoPaths [DecidableEq α] (G : SimpleGraph α) {p q : SimplePath α}
    (hp : G.IsSimplePathIn p) (hq : G.IsSimplePathIn q)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    G.IsSimpleCycleIn (SimpleCycle.ofTwoPaths p q hhead htail hne) := by
  rw [iff_isSimpleWalkIn, IsSimpleWalkIn.iff_edges]
  refine ⟨IsSimpleWalkIn.mem_vertexSet G hp
    (SimpleCycle.head_ofTwoPaths_mem_left p q hhead htail hne), ?_⟩
  intro e he
  rcases SimpleCycle.edges_ofTwoPaths_subset p q hhead htail hne he with hep | heq
  · exact IsSimpleWalkIn.edge_mem G hp hep
  · exact IsSimpleWalkIn.edge_mem G hq heq

/-- The length of a realized simple cycle is bounded by the number of vertices
of the ambient graph. -/
lemma length_le_ncard_vertexSet (G : SimpleGraph α) (hV : V(G).Finite)
    {c : SimpleCycle α} (hc : G.IsSimpleCycleIn c) :
    c.length ≤ V(G).ncard := by
  have hinterior : G.IsSimplePathIn (SimpleCycle.interior c) :=
    IsSimpleWalkIn.dropTail G hc
  have hpath := IsSimplePathIn.length_succ_le_ncard_vertexSet G hV hinterior
  have hthree : 3 ≤ (SimpleCycle.vertices c).length := c.2.1
  have hpos : (SimpleCycle.vertices c).length ≠ 0 := by omega
  have hlen_cycle : (SimpleCycle.interior c).length + 1 = c.length := by
    simpa [SimpleCycle.interior, SimplePath.length, SimpleWalk.dropTail,
      SimpleCycle.length, SimpleCycle.vertices] using
      VertexSeq.length_dropTail_succ (SimpleCycle.vertices c) hpos
  omega

/-! ## Existence of a short cycle from realized paths

Where `ofPathClosing` / `ofInternallyDisjointPaths` / `ofTwoPaths` above are the
constructor bridges — they say *this particular* cycle is realized — the two
lemmas here are the existence corollaries a caller actually wants: some realized
cycle exists, and it is no longer than the paths it was built from. The length
bound is what the Moore argument consumes.

They depend on neither girth nor the Moore development, so they live here in the
`InSimpleGraph` layer rather than in the Moore-bound file that first needed
them. -/

/-- If a vertex on a realized simple path is adjacent to the tail and the
suffix starting at that vertex has length at least two, then closing that suffix
gives a simple cycle. -/
lemma exists_length_le_succ_of_adj_mem (G : SimpleGraph α) [DecidableEq α]
    {p : SimplePath α} (hp : G.IsSimplePathIn p) {y : α}
    (hy_mem : y ∈ p.vertices) (hadj : G.Adj p.tail y)
    (hlen : 2 ≤ (p.vertices.suffixFrom y hy_mem).length) :
    ∃ c : SimpleCycle α, G.IsSimpleCycleIn c ∧ c.length ≤ p.length + 1 := by
  let q : SimplePath α := p.suffixFrom y hy_mem
  have hq : G.IsSimplePathIn q :=
    SimpleGraph.IsSimpleWalkIn.suffixFrom G hp y hy_mem
  have hclose : G.Adj q.tail q.head := by
    change G.Adj (p.vertices.suffixFrom y hy_mem).tail
      (p.vertices.suffixFrom y hy_mem).head
    simpa only [VertexSeq.tail_suffixFrom, VertexSeq.head_suffixFrom] using hadj
  refine ⟨SimpleCycle.ofPathClosing q hlen,
    IsSimpleCycleIn.ofPathClosing G hq hclose hlen, ?_⟩
  have hq_le : (p.vertices.suffixFrom y hy_mem).length ≤ p.vertices.length :=
    VertexSeq.length_suffixFrom_le p.vertices y hy_mem
  change (VertexSeq.cons (p.vertices.suffixFrom y hy_mem)
    (p.vertices.suffixFrom y hy_mem).head).length ≤ p.vertices.length + 1
  simpa only [VertexSeq.length, Nat.add_comm] using Nat.add_le_add_right hq_le 1

/-- Two distinct realized simple paths with common endpoints determine a
realized simple cycle whose length is at most the sum of their lengths. -/
lemma exists_length_le_add_of_two_paths (G : SimpleGraph α)
    {p q : SimplePath α} (hp : G.IsSimplePathIn p) (hq : G.IsSimplePathIn q)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    ∃ c : SimpleCycle α, G.IsSimpleCycleIn c ∧ c.length ≤ p.length + q.length := by
  classical
  exact ⟨SimpleCycle.ofTwoPaths p q hhead htail hne,
    ofTwoPaths G hp hq hhead htail hne,
    SimpleCycle.length_ofTwoPaths p q hhead htail hne⟩

end IsSimpleCycleIn

end SimpleGraph

end GraphLib
