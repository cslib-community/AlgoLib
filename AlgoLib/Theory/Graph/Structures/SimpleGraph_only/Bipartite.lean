/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import AlgoLib.Theory.Graph.Structures.InSimpleGraph
import Mathlib.Algebra.Group.Nat.Even

/-!
# Bipartite simple graphs

A simple graph is *bipartite* when it admits a proper two-colouring: a colouring
of the vertices by `Bool` under which every edge joins vertices of opposite
colour. Along a realized vertex sequence the colour therefore flips across each
edge, so the two endpoints agree in colour exactly when the sequence has even
length. Specialising this to closed walks — in particular simple cycles — shows
that every cycle in a bipartite graph is even.

The girth consequence (`SimpleGraph.girth.even_of_isBipartite`) lives in
`AlgoLib.Theory.Structures.SimpleGraph_only.Girth`, so that the basic colouring
definitions here do not depend on the girth development.

## Main definitions

* `SimpleGraph.IsProperTwoColoring G color` — `color` is a proper two-colouring.
* `SimpleGraph.IsBipartite G` — `G` admits a proper two-colouring.

## Main results

* `SimpleGraph.IsBipartite.even_length_of_closed` — a realized closed walk in a
  bipartite graph has even length.
* `SimpleGraph.IsBipartite.even_length_of_isSimpleCycleIn` — every realized simple
  cycle in a bipartite graph has even length.

## Implementation notes

The colouring formulation is chosen because the parity argument reduces to a
single `Bool` flip along each edge, avoiding any set-partition bookkeeping. The
workhorse is `IsProperTwoColoring.same_color_iff_even`, an `iff` proved by
induction on `IsVertexSeqIn`; the closed-walk and cycle statements are short
corollaries of it, and live in the `IsBipartite` namespace because that is the
predicate they assume.
-/

variable {α : Type*}

namespace AlgoLib

open scoped AlgoLib

namespace SimpleGraph

/-! ## Bipartite graphs -/

/-- A *proper two-colouring* of `G` is a colouring `color : α → Bool` under which
every edge joins vertices of opposite colour. -/
@[grind] def IsProperTwoColoring (G : SimpleGraph α) (color : α → Bool) : Prop :=
  ∀ ⦃u v : α⦄, G.Adj u v → color u ≠ color v

/-- `G` is *bipartite* when it admits a proper two-colouring. -/
@[grind] def IsBipartite (G : SimpleGraph α) : Prop :=
  ∃ color : α → Bool, G.IsProperTwoColoring color

namespace IsProperTwoColoring

/-! ## Colour parity along a realized sequence -/

/-- Under a proper two-colouring the endpoints of a realized vertex sequence have
equal colour exactly when the sequence has even length: the colour flips across
every edge. This is the workhorse behind the cycle and girth statements. -/
lemma same_color_iff_even (G : SimpleGraph α) {color : α → Bool}
    (hcol : G.IsProperTwoColoring color) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : color w.head = color w.tail ↔ Even w.length := by
  induction hw with
  | singleton v hv => simp [VertexSeq.length]
  | cons w u hw he ih =>
      have hne : color w.tail ≠ color u := hcol he
      simp only [VertexSeq.head_cons, VertexSeq.tail_cons, VertexSeq.length]
      rw [Nat.add_comm 1 w.length, Nat.even_add_one, ← ih]
      revert hne
      cases color w.head <;> cases color w.tail <;> cases color u <;> decide

end IsProperTwoColoring

namespace IsBipartite

/-! ## Closed walks and cycles are even -/

/-- A realized closed walk in a bipartite graph has even length. -/
lemma even_length_of_closed (G : SimpleGraph α) (hG : G.IsBipartite)
    {w : SimpleWalk α} (hw : G.IsSimpleWalkIn w) (hcl : w.closed) :
    Even w.length := by
  obtain ⟨color, hcol⟩ := hG
  have hw' : G.IsVertexSeqIn w.val := hw
  have hcl' : w.val.head = w.val.tail := hcl
  exact (IsProperTwoColoring.same_color_iff_even G hcol hw').1 (congrArg color hcl')

/-- Every realized simple cycle in a bipartite graph has even length. -/
lemma even_length_of_isSimpleCycleIn (G : SimpleGraph α) (hG : G.IsBipartite)
    {c : SimpleCycle α} (hc : G.IsSimpleCycleIn c) : Even c.length :=
  even_length_of_closed G hG hc c.closed

end IsBipartite

end SimpleGraph

end AlgoLib
