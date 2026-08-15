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

variable {α : Type*}

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

end IsSimplePathIn

end SimpleDiGraph

end GraphLib
