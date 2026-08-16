/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Walk.InSimpleGraph.Walk
import GraphLib.Walk.SimplePath
import Mathlib.Data.Set.Card

/-!
# Simple paths realized in a simple graph

`SimpleGraph.IsSimplePathIn G p` says a `SimplePath` is realized in `G` through
its underlying simple walk, with the path-specific API (extension by a fresh
adjacent vertex, the vertex-count bound).

Part of the `InSimpleGraph` folder; see the umbrella module
`GraphLib.Walk.InSimpleGraph`.
-/

variable {α γ : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Simple paths realized in a graph -/

/-- A simple path is realized in `G` when its underlying simple walk is
realized in `G`. -/
@[grind] def IsSimplePathIn (G : SimpleGraph α) (p : SimplePath α) : Prop :=
  G.IsSimpleWalkIn p.val

namespace IsSimplePathIn

theorem isSimpleWalkIn {G : SimpleGraph α} {p : SimplePath α}
    (h : G.IsSimplePathIn p) : G.IsSimpleWalkIn p.val := h

theorem reverse {G : SimpleGraph α} {p : SimplePath α} (h : G.IsSimplePathIn p) :
    G.IsSimplePathIn p.reverse := IsSimpleWalkIn.reverse G h

theorem mono (G H : SimpleGraph α) {p : SimplePath α} (hp : H.IsSimplePathIn p)
    (hHG : H ≤ G) : G.IsSimplePathIn p := IsSimpleWalkIn.mono G H hp hHG

/-- Realization of a simple path is realization of its underlying simple walk. -/
@[simp, grind =] lemma iff_isSimpleWalkIn (G : SimpleGraph α) (p : SimplePath α) :
    G.IsSimplePathIn p ↔ G.IsSimpleWalkIn p.val := Iff.rfl

/-- A singleton path is realized exactly when its vertex is in the graph. -/
lemma singleton (G : SimpleGraph α) {v : α} (hv : v ∈ V(G)) :
    G.IsSimplePathIn (SimplePath.singleton v) :=
  IsVertexSeqIn.singleton v hv

theorem induce_iff (G : SimpleGraph α) (S : Set α) (p : SimplePath α) :
    (G.induce S).IsSimplePathIn p ↔
      G.IsSimplePathIn p ∧ ∀ v ∈ p.support, v ∈ S :=
  IsSimpleWalkIn.induce_iff G S p.val

theorem restrictEdges_iff (G : SimpleGraph α) (F : Set (Sym2 α)) (p : SimplePath α) :
    (G.restrictEdges F).IsSimplePathIn p ↔
      G.IsSimplePathIn p ∧ ∀ e ∈ p.edges, e ∈ F :=
  IsSimpleWalkIn.restrictEdges_iff G F p.val

theorem deleteEdges_iff (G : SimpleGraph α) (F : Set (Sym2 α)) (p : SimplePath α) :
    (G.deleteEdges F).IsSimplePathIn p ↔
      G.IsSimplePathIn p ∧ ∀ e ∈ p.edges, e ∉ F :=
  IsSimpleWalkIn.deleteEdges_iff G F p.val

theorem relabelVertices {G : SimpleGraph α} {p : SimplePath α} (f : α ≃ γ)
    (h : G.IsSimplePathIn p) :
    (G.relabelVertices f).IsSimplePathIn (SimplePath.map f f.injective p) :=
  IsSimpleWalkIn.relabelVertices f h

/-- Gluing realized paths at a shared endpoint preserves realization. -/
theorem glue (G : SimpleGraph α) {p q : SimplePath α}
    (hp : G.IsSimplePathIn p) (hq : G.IsSimplePathIn q)
    (h : p.tail = q.head)
    (hdisj : p.vertices.length ≠ 0 →
      ∀ v : α, v ∈ p.vertices.dropTail → v ∈ q.vertices → False) :
    G.IsSimplePathIn (p.glue q h hdisj) :=
  IsSimpleWalkIn.glue G hp hq h

/-- Extending a realized path by a fresh adjacent tail vertex preserves realization. -/
lemma extendTail (G : SimpleGraph α) {p : SimplePath α} {v : α}
    (hp : G.IsSimplePathIn p) (hadj : G.Adj p.tail v) (hnot : v ∉ p.vertices) :
    G.IsSimplePathIn (p.extendTail v hnot) := by
  change G.IsVertexSeqIn (p.vertices.cons v)
  exact IsVertexSeqIn.cons p.vertices v hp hadj

/-- Extending a realized simple path by a fresh adjacent vertex gives a realized
simple path whose length is one larger. -/
lemma exists_longer_of_adj_not_mem (G : SimpleGraph α) {p : SimplePath α} {v : α}
    (hp : G.IsSimplePathIn p) (hadj : G.Adj p.tail v) (hnot : v ∉ p.vertices) :
    ∃ q : SimplePath α, G.IsSimplePathIn q ∧ q.length = p.length + 1 :=
  ⟨p.extendTail v hnot, extendTail G hp hadj hnot, SimplePath.length_extendTail p v hnot⟩

/-- The number of vertices of a realized simple path is bounded by the number
of vertices of the ambient graph. -/
lemma length_succ_le_ncard_vertexSet (G : SimpleGraph α) (hV : V(G).Finite)
    {p : SimplePath α} (hp : G.IsSimplePathIn p) :
    p.length + 1 ≤ V(G).ncard := by
  classical
  let S : Set α := {v | v ∈ p.support}
  have hS : S ⊆ V(G) := fun v hv => IsSimpleWalkIn.mem_vertexSet G hp hv
  have hnodup : p.support.Nodup := by
    simpa [SimplePath.support] using
      (VertexSeq.nodup_iff_toList_nodup (SimplePath.vertices p)).1 (SimplePath.nodup p)
  have hS_card : S.ncard = p.support.length := by
    rw [show S = (p.support.toFinset : Set α) by ext v; simp [S], Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnodup]
  have hlen : p.support.length = p.length + 1 := by
    simpa [SimplePath.support, SimplePath.length] using
      VertexSeq.length_toList (SimplePath.vertices p)
  have hcard : S.ncard ≤ V(G).ncard := Set.ncard_le_ncard hS hV
  omega

end IsSimplePathIn

end SimpleGraph

end GraphLib
