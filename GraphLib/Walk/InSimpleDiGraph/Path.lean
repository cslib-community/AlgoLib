/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.InSimpleDiGraph.Walk
import GraphLib.Walk.SimplePath

/-!
# Simple paths realized in simple directed graphs
-/

namespace GraphLib

variable {α γ : Type*}

open scoped GraphLib

namespace SimpleDiGraph

/-! ## Directed simple paths -/

/-- A directed simple path realized in a simple digraph. -/
def IsSimplePathIn (G : SimpleDiGraph α) (p : SimplePath α) : Prop :=
  G.IsSimpleWalkIn p.val

namespace IsSimplePathIn

theorem isSimpleWalkIn {G : SimpleDiGraph α} {p : SimplePath α}
    (h : G.IsSimplePathIn p) : G.IsSimpleWalkIn p.val := h

theorem reverse {G : SimpleDiGraph α} {p : SimplePath α} (h : G.IsSimplePathIn p) :
    G.reverse.IsSimplePathIn p.reverse :=
  IsSimpleWalkIn.reverse G h

theorem mono (G H : SimpleDiGraph α) {p : SimplePath α} (hp : H.IsSimplePathIn p)
    (hHG : H ≤ G) : G.IsSimplePathIn p :=
  IsSimpleWalkIn.mono G H hp hHG

theorem induce_iff (G : SimpleDiGraph α) (S : Set α) (p : SimplePath α) :
    (G.induce S).IsSimplePathIn p ↔
      G.IsSimplePathIn p ∧ ∀ v ∈ p.support, v ∈ S :=
  IsSimpleWalkIn.induce_iff G S p.val

theorem restrictEdges_iff (G : SimpleDiGraph α) (F : Set (α × α)) (p : SimplePath α) :
    (G.restrictEdges F).IsSimplePathIn p ↔
      G.IsSimplePathIn p ∧ ∀ a ∈ p.arcs, a ∈ F :=
  IsSimpleWalkIn.restrictEdges_iff G F p.val

theorem deleteEdges_iff (G : SimpleDiGraph α) (F : Set (α × α)) (p : SimplePath α) :
    (G.deleteEdges F).IsSimplePathIn p ↔
      G.IsSimplePathIn p ∧ ∀ a ∈ p.arcs, a ∉ F :=
  IsSimpleWalkIn.deleteEdges_iff G F p.val

theorem relabelVertices {G : SimpleDiGraph α} {p : SimplePath α} (f : α ≃ γ)
    (h : G.IsSimplePathIn p) :
    (G.relabelVertices f).IsSimplePathIn (SimplePath.map f f.injective p) :=
  IsSimpleWalkIn.relabelVertices f h

/-- Gluing realized directed paths at a shared endpoint preserves realization. -/
theorem glue (G : SimpleDiGraph α) {p q : SimplePath α}
    (hp : G.IsSimplePathIn p) (hq : G.IsSimplePathIn q)
    (h : p.tail = q.head)
    (hdisj : p.vertices.length ≠ 0 →
      ∀ v : α, v ∈ p.vertices.dropTail → v ∈ q.vertices → False) :
    G.IsSimplePathIn (p.glue q h hdisj) :=
  IsSimpleWalkIn.glue G hp hq h

end IsSimplePathIn

end SimpleDiGraph

end GraphLib
