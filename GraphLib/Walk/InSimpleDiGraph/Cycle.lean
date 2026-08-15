/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.InSimpleDiGraph.Path
import GraphLib.Walk.SimpleDiCycle

/-!
# Simple directed cycles realized in simple directed graphs
-/

namespace GraphLib

variable {α : Type*}

open scoped GraphLib

namespace SimpleDiGraph

/-! ## Directed simple cycles -/

/-- A directed simple cycle realized in a simple digraph. -/
def IsSimpleDiCycleIn (G : SimpleDiGraph α) (c : SimpleDiCycle α) : Prop :=
  G.IsSimpleWalkIn c.val

namespace IsSimpleDiCycleIn

theorem isSimpleWalkIn {G : SimpleDiGraph α} {c : SimpleDiCycle α}
    (h : G.IsSimpleDiCycleIn c) : G.IsSimpleWalkIn c.val := h

theorem reverse {G : SimpleDiGraph α} {c : SimpleDiCycle α}
    (h : G.IsSimpleDiCycleIn c) : G.reverse.IsSimpleDiCycleIn c.reverse :=
  IsSimpleWalkIn.reverse G h

theorem mono (G H : SimpleDiGraph α) {c : SimpleDiCycle α}
    (hc : H.IsSimpleDiCycleIn c) (hHG : H ≤ G) : G.IsSimpleDiCycleIn c :=
  IsSimpleWalkIn.mono G H hc hHG

/-- Closing a realized path along a directed adjacency produces a realized directed cycle. -/
theorem ofPathClosing (G : SimpleDiGraph α) (p : SimplePath α) (hp : G.IsSimplePathIn p)
    (hlen : 1 ≤ p.length) (hclose : G.Adj p.tail p.head) :
    G.IsSimpleDiCycleIn (SimpleDiCycle.ofPathClosing p hlen) := by
  change G.IsVertexSeqIn (p.vertices.cons p.head)
  exact .cons p.vertices p.head hp hclose

end IsSimpleDiCycleIn

end SimpleDiGraph

end GraphLib
