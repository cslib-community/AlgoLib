/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Theory.Connectivity.Cuts
import Mathlib.Data.ENat.Lattice

/-!
# Vertex and edge connectivity

The connectivity numbers `κ(G)` and `κ'(G)` measure how many vertices, respectively
edges, must be removed to destroy the connectivity of `G`.

## Main definitions

* `SimpleGraph.IsVertexSeparating G S` — deleting `S` disconnects `G` *or* leaves at most
  one vertex.
* `SimpleGraph.IsEdgeSeparating G F` — deleting `F` disconnects `G`, or `G` is trivial.
* `SimpleGraph.vertexConnectivity G` — the least size of such an `S`, written `κ(G)`.
* `SimpleGraph.edgeConnectivity G` — the least size of such an `F`, written `κ'(G)`.

## Main results

* `SimpleGraph.vertexConnectivity_ge_iff` / `SimpleGraph.edgeConnectivity_ge_iff` — the
  lower-bound characterizations; nearly everything else is a corollary.
* `SimpleGraph.vertexConnectivity_le_encard` / `SimpleGraph.edgeConnectivity_le_encard` —
  every separating set bounds the connectivity number from above.

## Design choices

* **The Diestel convention.** `κ` is the least size of a vertex set whose deletion
  disconnects `G` *or leaves at most one vertex*. Without the second disjunct the
  complete graph `Kₙ` would have `κ(Kₙ) = ⊤`, since no vertex set disconnects it; with
  it, `κ(Kₙ) = n - 1`, and Whitney's inequality `κ ≤ κ' ≤ δ` holds without a case split.
  The same patch on the edge side gives the usual convention `κ'(G) = 0` for a graph with
  at most one vertex. The unpatched "least vertex cut" quantity is kept as
  `vertexCutNumber` / `edgeCutNumber` for comparison, with the degeneracy documented.
* **`Set.encard`, not `Set.ncard`.** `encard` is already `ℕ∞`-valued, so it needs no
  coercion inside the `⨅`, and it returns `⊤` rather than the junk value `0` on infinite
  sets. A `κ` built on `ncard` would report `0` — perfect disconnection — for a graph
  whose only cuts are infinite.
* **Nested `⨅`, mirroring `girth`.** The shape `⨅ (x) (_ : P x), f x` is the one used by
  `SimpleGraph.girth` in `GraphLib.Theory.Structures.SimpleGraph_only.Girth`, so the
  same infimum API (`le_iInf₂_iff`, `iInf₂_le`, `iInf_eq_top`) applies verbatim. The
  empty-index convention makes the connectivity of a graph with no separating set `⊤`
  automatically.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Separating sets -/

/-- `S` is *vertex-separating* in `G` when deleting it either disconnects `G` or leaves
at most one vertex.

The second disjunct is the Diestel convention. It is what makes `κ(Kₙ) = n - 1` rather
than `⊤`: no set of vertices disconnects a complete graph, but deleting all but one of
them leaves a single vertex. -/
def IsVertexSeparating (G : SimpleGraph α) (S : Set α) : Prop :=
  S ⊆ V(G) ∧ (¬ (G.deleteVertices S).IsPreconnected ∨ (V(G) \ S).Subsingleton)

/-- `F` is *edge-separating* in `G` when deleting it disconnects `G`, or `G` has at most
one vertex. The second disjunct gives the usual convention `κ'(G) = 0` on the trivial
graph, where no set of edges can disconnect anything. -/
def IsEdgeSeparating (G : SimpleGraph α) (F : Set (Sym2 α)) : Prop :=
  F ⊆ E(G) ∧ (¬ (G.deleteEdges F).IsPreconnected ∨ V(G).Subsingleton)

/-- Every vertex cut is vertex-separating. -/
lemma IsVertexCut.isVertexSeparating {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexCut S) : G.IsVertexSeparating S := ⟨h.1, Or.inl h.2⟩

/-- Every edge cut is edge-separating. -/
lemma IsEdgeCut.isEdgeSeparating {G : SimpleGraph α} {F : Set (Sym2 α)}
    (h : G.IsEdgeCut F) : G.IsEdgeSeparating F := ⟨h.1, Or.inl h.2⟩

/-! ## The connectivity numbers -/

/-- The *vertex connectivity* `κ(G)`: the least number of vertices whose deletion either
disconnects `G` or leaves at most one vertex.

It is `⊤` exactly when no set of vertices does either — for instance in an infinite
complete graph. See `IsVertexSeparating` for the convention on complete graphs. -/
noncomputable def vertexConnectivity (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (S : Set α) (_ : G.IsVertexSeparating S), S.encard

/-- The *edge connectivity* `κ'(G)`: the least number of edges whose deletion
disconnects `G`, with the convention `κ'(G) = 0` when `G` has at most one vertex. -/
noncomputable def edgeConnectivity (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (F : Set (Sym2 α)) (_ : G.IsEdgeSeparating F), F.encard

end SimpleGraph

/-- `κ(G)` is the vertex connectivity of `G`.

Declared directly inside `namespace GraphLib` rather than inside `namespace SimpleGraph`,
so that `scoped` attaches it to `GraphLib` and a plain `open scoped GraphLib` brings it
into scope alongside `V(G)` and `E(G)`. -/
scoped notation "κ(" G ")" => GraphLib.SimpleGraph.vertexConnectivity G

/-- `κ'(G)` is the edge connectivity of `G`. -/
scoped notation "κ'(" G ")" => GraphLib.SimpleGraph.edgeConnectivity G

namespace SimpleGraph

/-! ## The infimum API -/

/-- Every vertex-separating set bounds `κ(G)` from above. -/
lemma vertexConnectivity_le_encard {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexSeparating S) : κ(G) ≤ S.encard :=
  iInf₂_le S h

/-- Every edge-separating set bounds `κ'(G)` from above. -/
lemma edgeConnectivity_le_encard {G : SimpleGraph α} {F : Set (Sym2 α)}
    (h : G.IsEdgeSeparating F) : κ'(G) ≤ F.encard :=
  iInf₂_le F h

/-- Every vertex cut bounds `κ(G)` from above. -/
lemma vertexConnectivity_le_encard_of_isVertexCut {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexCut S) : κ(G) ≤ S.encard :=
  vertexConnectivity_le_encard h.isVertexSeparating

/-- Every edge cut bounds `κ'(G)` from above. -/
lemma edgeConnectivity_le_encard_of_isEdgeCut {G : SimpleGraph α} {F : Set (Sym2 α)}
    (h : G.IsEdgeCut F) : κ'(G) ≤ F.encard :=
  edgeConnectivity_le_encard h.isEdgeSeparating

/-- The lower-bound characterization of `κ(G)`: the workhorse lemma. -/
theorem vertexConnectivity_ge_iff {G : SimpleGraph α} {n : ℕ∞} :
    n ≤ κ(G) ↔ ∀ S : Set α, G.IsVertexSeparating S → n ≤ S.encard := by
  simp [vertexConnectivity, le_iInf_iff]

/-- The lower-bound characterization of `κ'(G)`. -/
theorem edgeConnectivity_ge_iff {G : SimpleGraph α} {n : ℕ∞} :
    n ≤ κ'(G) ↔ ∀ F : Set (Sym2 α), G.IsEdgeSeparating F → n ≤ F.encard := by
  simp [edgeConnectivity, le_iInf_iff]

/-- `κ(G) = ⊤` exactly when every vertex-separating set is infinite — in particular when
there is no separating set at all. -/
theorem vertexConnectivity_eq_top_iff {G : SimpleGraph α} :
    κ(G) = ⊤ ↔ ∀ S : Set α, G.IsVertexSeparating S → S.Infinite := by
  simp [vertexConnectivity, iInf_eq_top]

/-- `κ'(G) = ⊤` exactly when every edge-separating set is infinite. -/
theorem edgeConnectivity_eq_top_iff {G : SimpleGraph α} :
    κ'(G) = ⊤ ↔ ∀ F : Set (Sym2 α), G.IsEdgeSeparating F → F.Infinite := by
  simp [edgeConnectivity, iInf_eq_top]

/-! ## Degenerate cases -/

/-- A disconnected graph has vertex connectivity zero: the empty set already separates
it. -/
lemma vertexConnectivity_eq_zero_of_not_isPreconnected {G : SimpleGraph α}
    (h : ¬ G.IsPreconnected) : κ(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using vertexConnectivity_le_encard (S := ∅) ⟨Set.empty_subset _, Or.inl (by simpa)⟩

/-- A disconnected graph has edge connectivity zero. -/
lemma edgeConnectivity_eq_zero_of_not_isPreconnected {G : SimpleGraph α}
    (h : ¬ G.IsPreconnected) : κ'(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using edgeConnectivity_le_encard (F := ∅) ⟨Set.empty_subset _, Or.inl (by simpa)⟩

/-- A graph with at most one vertex has vertex connectivity zero. -/
lemma vertexConnectivity_eq_zero_of_subsingleton {G : SimpleGraph α}
    (h : V(G).Subsingleton) : κ(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using vertexConnectivity_le_encard (S := ∅)
    ⟨Set.empty_subset _, Or.inr (by simpa using h)⟩

/-- A graph with at most one vertex has edge connectivity zero. -/
lemma edgeConnectivity_eq_zero_of_subsingleton {G : SimpleGraph α}
    (h : V(G).Subsingleton) : κ'(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using edgeConnectivity_le_encard (F := ∅) ⟨Set.empty_subset _, Or.inr h⟩

/-- A graph of positive vertex connectivity is connected. -/
lemma isConnected_of_zero_lt_vertexConnectivity {G : SimpleGraph α}
    (h : 0 < κ(G)) : G.IsConnected := by
  refine ⟨?_, ?_⟩
  · rw [Set.nonempty_iff_ne_empty]
    intro hempty
    exact absurd (vertexConnectivity_eq_zero_of_subsingleton
      (by rw [hempty]; exact Set.subsingleton_empty)) h.ne'
  · by_contra hpre
    exact absurd (vertexConnectivity_eq_zero_of_not_isPreconnected hpre) h.ne'

/-! ## The unpatched cut numbers

These are the literal readings of "the least size of a cut". They are recorded for
comparison and are *degenerate on complete graphs*: `Kₙ` has no vertex cut at all, so
`vertexCutNumber Kₙ = ⊤`. Prefer `vertexConnectivity` / `edgeConnectivity`. -/

/-- The least size of a vertex cut of `G`, the literal reading of Definition 3.1.(i).

Degenerate on complete graphs, which have no vertex cut: `vertexCutNumber Kₙ = ⊤`,
whereas `κ(Kₙ) = n - 1`. -/
noncomputable def vertexCutNumber (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (S : Set α) (_ : G.IsVertexCut S), S.encard

/-- The least size of an edge cut of `G`. Degenerate on graphs with at most one vertex,
which have no edge cut. -/
noncomputable def edgeCutNumber (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (F : Set (Sym2 α)) (_ : G.IsEdgeCut F), F.encard

/-- The patched connectivity is at most the literal cut number: every cut is separating,
so the infimum ranges over a larger family. Equality holds whenever `G` has a cut at all
that is no bigger than the best subsingleton-leaving set — in particular for every
non-complete graph. -/
lemma vertexConnectivity_le_vertexCutNumber (G : SimpleGraph α) :
    κ(G) ≤ G.vertexCutNumber :=
  le_iInf₂ fun _ hS => vertexConnectivity_le_encard_of_isVertexCut hS

/-- The patched edge connectivity is at most the literal edge cut number. -/
lemma edgeConnectivity_le_edgeCutNumber (G : SimpleGraph α) :
    κ'(G) ≤ G.edgeCutNumber :=
  le_iInf₂ fun _ hF => edgeConnectivity_le_encard_of_isEdgeCut hF

end SimpleGraph

end GraphLib
