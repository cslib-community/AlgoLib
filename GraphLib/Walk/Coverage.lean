/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.InDiGraph
import GraphLib.Walk.InGraph
import GraphLib.Walk.InSimpleDiGraph
import GraphLib.Walk.InSimpleGraph

/-!
# Eulerian and Hamiltonian specifications

Every coverage predicate includes realization. General Eulerian coverage compares full bundled
actual edges or arcs, never raw tags.
-/

namespace GraphLib

variable {α β : Type*}

open scoped GraphLib

namespace Graph

/-- A realized trail that traverses exactly the actual edges of a general graph. -/
def IsEulerianTrailIn (G : Graph α β) (t : Trail α β) : Prop :=
  G.IsTrailIn t ∧ ∀ e, e ∈ t.edges ↔ e ∈ E(G)

/-- A realized circuit that traverses exactly the actual edges of a general graph. -/
def IsEulerianCircuitIn (G : Graph α β) (c : Circuit α β) : Prop :=
  G.IsCircuitIn c ∧ ∀ e, e ∈ c.edges ↔ e ∈ E(G)

/-- A realized path whose vertices are exactly the graph's vertices. -/
def IsHamiltonianPathIn (G : Graph α β) (p : Path α β) : Prop :=
  G.IsPathIn p ∧ ∀ v, v ∈ p.vertices ↔ v ∈ V(G)

/-- A realized cycle whose vertex-simple interior contains exactly the graph's vertices. -/
def IsHamiltonianCycleIn (G : Graph α β) (c : Cycle α β) : Prop :=
  G.IsCycleIn c ∧ ∀ v, v ∈ c.interior.vertices ↔ v ∈ V(G)

namespace IsEulerianTrailIn
theorem isTrailIn {G : Graph α β} {t : Trail α β} (h : G.IsEulerianTrailIn t) :
    G.IsTrailIn t := h.1
theorem edge_mem {G : Graph α β} {t : Trail α β} (h : G.IsEulerianTrailIn t)
    {e : Edge α β} : e ∈ t.edges ↔ e ∈ E(G) := h.2 e
theorem congr {G H : Graph α β} {t : Trail α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) :
    G.IsEulerianTrailIn t ↔ H.IsEulerianTrailIn t := by
  simp only [Graph.IsEulerianTrailIn, Graph.IsTrailIn]
  rw [Graph.IsWalkIn.congr hV hE, hE]
end IsEulerianTrailIn

namespace IsEulerianCircuitIn
theorem isCircuitIn {G : Graph α β} {c : Circuit α β} (h : G.IsEulerianCircuitIn c) :
    G.IsCircuitIn c := h.1
theorem edge_mem {G : Graph α β} {c : Circuit α β} (h : G.IsEulerianCircuitIn c)
    {e : Edge α β} : e ∈ c.edges ↔ e ∈ E(G) := h.2 e
theorem congr {G H : Graph α β} {c : Circuit α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) :
    G.IsEulerianCircuitIn c ↔ H.IsEulerianCircuitIn c := by
  simp only [Graph.IsEulerianCircuitIn, Graph.IsCircuitIn, Graph.IsTrailIn]
  rw [Graph.IsWalkIn.congr hV hE, hE]
end IsEulerianCircuitIn

namespace IsHamiltonianPathIn
theorem isPathIn {G : Graph α β} {p : Path α β} (h : G.IsHamiltonianPathIn p) :
    G.IsPathIn p := h.1
theorem vertex_mem {G : Graph α β} {p : Path α β} (h : G.IsHamiltonianPathIn p)
    {v : α} : v ∈ p.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : Graph α β} {p : Path α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) :
    G.IsHamiltonianPathIn p ↔ H.IsHamiltonianPathIn p := by
  simp only [Graph.IsHamiltonianPathIn, Graph.IsPathIn]
  rw [Graph.IsWalkIn.congr hV hE, hV]
end IsHamiltonianPathIn

namespace IsHamiltonianCycleIn
theorem isCycleIn {G : Graph α β} {c : Cycle α β} (h : G.IsHamiltonianCycleIn c) :
    G.IsCycleIn c := h.1
theorem vertex_mem {G : Graph α β} {c : Cycle α β} (h : G.IsHamiltonianCycleIn c)
    {v : α} : v ∈ c.interior.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : Graph α β} {c : Cycle α β} (hV : V(G) = V(H)) (hE : E(G) = E(H)) :
    G.IsHamiltonianCycleIn c ↔ H.IsHamiltonianCycleIn c := by
  simp only [Graph.IsHamiltonianCycleIn, Graph.IsCycleIn]
  rw [Graph.IsWalkIn.congr hV hE, hV]
end IsHamiltonianCycleIn

end Graph

namespace DiGraph

def IsEulerianTrailIn (G : DiGraph α β) (t : DiTrail α β) : Prop :=
  G.IsTrailIn t ∧ ∀ a, a ∈ t.arcs ↔ a ∈ E(G)

def IsEulerianCircuitIn (G : DiGraph α β) (c : DiCircuit α β) : Prop :=
  G.IsCircuitIn c ∧ ∀ a, a ∈ c.arcs ↔ a ∈ E(G)

def IsHamiltonianPathIn (G : DiGraph α β) (p : Path α β) : Prop :=
  G.IsPathIn p ∧ ∀ v, v ∈ p.vertices ↔ v ∈ V(G)

def IsHamiltonianCycleIn (G : DiGraph α β) (c : DiCycle α β) : Prop :=
  G.IsCycleIn c ∧ ∀ v, v ∈ c.interior.vertices ↔ v ∈ V(G)

namespace IsEulerianTrailIn
theorem isTrailIn {G : DiGraph α β} {t : DiTrail α β} (h : G.IsEulerianTrailIn t) :
    G.IsTrailIn t := h.1
theorem arc_mem {G : DiGraph α β} {t : DiTrail α β} (h : G.IsEulerianTrailIn t)
    {a : Arc α β} : a ∈ t.arcs ↔ a ∈ E(G) := h.2 a
theorem congr {G H : DiGraph α β} {t : DiTrail α β} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsEulerianTrailIn t ↔ H.IsEulerianTrailIn t := by
  simp only [DiGraph.IsEulerianTrailIn, DiGraph.IsTrailIn]
  rw [DiGraph.IsWalkIn.congr hV hE, hE]
end IsEulerianTrailIn

namespace IsEulerianCircuitIn
theorem isCircuitIn {G : DiGraph α β} {c : DiCircuit α β} (h : G.IsEulerianCircuitIn c) :
    G.IsCircuitIn c := h.1
theorem arc_mem {G : DiGraph α β} {c : DiCircuit α β} (h : G.IsEulerianCircuitIn c)
    {a : Arc α β} : a ∈ c.arcs ↔ a ∈ E(G) := h.2 a
theorem congr {G H : DiGraph α β} {c : DiCircuit α β} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsEulerianCircuitIn c ↔ H.IsEulerianCircuitIn c := by
  simp only [DiGraph.IsEulerianCircuitIn, DiGraph.IsCircuitIn, DiGraph.IsTrailIn]
  rw [DiGraph.IsWalkIn.congr hV hE, hE]
end IsEulerianCircuitIn

namespace IsHamiltonianPathIn
theorem isPathIn {G : DiGraph α β} {p : Path α β} (h : G.IsHamiltonianPathIn p) :
    G.IsPathIn p := h.1
theorem vertex_mem {G : DiGraph α β} {p : Path α β} (h : G.IsHamiltonianPathIn p)
    {v : α} : v ∈ p.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : DiGraph α β} {p : Path α β} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsHamiltonianPathIn p ↔ H.IsHamiltonianPathIn p := by
  simp only [DiGraph.IsHamiltonianPathIn, DiGraph.IsPathIn]
  rw [DiGraph.IsWalkIn.congr hV hE, hV]
end IsHamiltonianPathIn

namespace IsHamiltonianCycleIn
theorem isCycleIn {G : DiGraph α β} {c : DiCycle α β} (h : G.IsHamiltonianCycleIn c) :
    G.IsCycleIn c := h.1
theorem vertex_mem {G : DiGraph α β} {c : DiCycle α β} (h : G.IsHamiltonianCycleIn c)
    {v : α} : v ∈ c.interior.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : DiGraph α β} {c : DiCycle α β} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsHamiltonianCycleIn c ↔ H.IsHamiltonianCycleIn c := by
  simp only [DiGraph.IsHamiltonianCycleIn, DiGraph.IsCycleIn]
  rw [DiGraph.IsWalkIn.congr hV hE, hV]
end IsHamiltonianCycleIn

end DiGraph

namespace SimpleGraph

/-- A realized simple walk with no repeated edge that covers every edge. -/
def IsEulerianTrailIn (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  G.IsSimpleWalkIn w ∧ w.edges.Nodup ∧ ∀ e, e ∈ w.edges ↔ e ∈ E(G)

/-- A nonempty closed realized edge-simple walk that covers every edge. -/
def IsEulerianCircuitIn (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  G.IsSimpleWalkIn w ∧ 0 < w.length ∧ w.closed ∧ w.edges.Nodup ∧
    ∀ e, e ∈ w.edges ↔ e ∈ E(G)

def IsHamiltonianPathIn (G : SimpleGraph α) (p : SimplePath α) : Prop :=
  G.IsSimplePathIn p ∧ ∀ v, v ∈ p.vertices ↔ v ∈ V(G)

def IsHamiltonianCycleIn (G : SimpleGraph α) (c : SimpleCycle α) : Prop :=
  G.IsSimpleCycleIn c ∧ ∀ v, v ∈ c.interior.vertices ↔ v ∈ V(G)

namespace IsEulerianTrailIn
theorem isSimpleWalkIn {G : SimpleGraph α} {w : SimpleWalk α} (h : G.IsEulerianTrailIn w) :
    G.IsSimpleWalkIn w := h.1
theorem edge_mem {G : SimpleGraph α} {w : SimpleWalk α} (h : G.IsEulerianTrailIn w)
    {e : Sym2 α} : e ∈ w.edges ↔ e ∈ E(G) := h.2.2 e
theorem congr {G H : SimpleGraph α} {w : SimpleWalk α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsEulerianTrailIn w ↔ H.IsEulerianTrailIn w := by
  simp only [SimpleGraph.IsEulerianTrailIn]
  rw [SimpleGraph.IsSimpleWalkIn.congr hV hE, hE]
end IsEulerianTrailIn

namespace IsEulerianCircuitIn
theorem isSimpleWalkIn {G : SimpleGraph α} {w : SimpleWalk α} (h : G.IsEulerianCircuitIn w) :
    G.IsSimpleWalkIn w := h.1
theorem edge_mem {G : SimpleGraph α} {w : SimpleWalk α} (h : G.IsEulerianCircuitIn w)
    {e : Sym2 α} : e ∈ w.edges ↔ e ∈ E(G) := h.2.2.2.2 e
theorem congr {G H : SimpleGraph α} {w : SimpleWalk α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsEulerianCircuitIn w ↔ H.IsEulerianCircuitIn w := by
  simp only [SimpleGraph.IsEulerianCircuitIn]
  rw [SimpleGraph.IsSimpleWalkIn.congr hV hE, hE]
end IsEulerianCircuitIn

namespace IsHamiltonianPathIn
theorem isSimplePathIn {G : SimpleGraph α} {p : SimplePath α} (h : G.IsHamiltonianPathIn p) :
    G.IsSimplePathIn p := h.1
theorem vertex_mem {G : SimpleGraph α} {p : SimplePath α} (h : G.IsHamiltonianPathIn p)
    {v : α} : v ∈ p.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : SimpleGraph α} {p : SimplePath α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsHamiltonianPathIn p ↔ H.IsHamiltonianPathIn p := by
  simp only [SimpleGraph.IsHamiltonianPathIn, SimpleGraph.IsSimplePathIn]
  rw [SimpleGraph.IsSimpleWalkIn.congr hV hE, hV]
end IsHamiltonianPathIn

namespace IsHamiltonianCycleIn
theorem isSimpleCycleIn {G : SimpleGraph α} {c : SimpleCycle α}
    (h : G.IsHamiltonianCycleIn c) : G.IsSimpleCycleIn c := h.1
theorem vertex_mem {G : SimpleGraph α} {c : SimpleCycle α} (h : G.IsHamiltonianCycleIn c)
    {v : α} : v ∈ c.interior.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : SimpleGraph α} {c : SimpleCycle α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsHamiltonianCycleIn c ↔ H.IsHamiltonianCycleIn c := by
  simp only [SimpleGraph.IsHamiltonianCycleIn, SimpleGraph.IsSimpleCycleIn]
  rw [SimpleGraph.IsSimpleWalkIn.congr hV hE, hV]
end IsHamiltonianCycleIn

end SimpleGraph

namespace SimpleDiGraph

def IsEulerianTrailIn (G : SimpleDiGraph α) (w : SimpleWalk α) : Prop :=
  G.IsSimpleWalkIn w ∧ w.arcs.Nodup ∧ ∀ a, a ∈ w.arcs ↔ a ∈ E(G)

def IsEulerianCircuitIn (G : SimpleDiGraph α) (w : SimpleWalk α) : Prop :=
  G.IsSimpleWalkIn w ∧ 0 < w.length ∧ w.closed ∧ w.arcs.Nodup ∧
    ∀ a, a ∈ w.arcs ↔ a ∈ E(G)

def IsHamiltonianPathIn (G : SimpleDiGraph α) (p : SimplePath α) : Prop :=
  G.IsSimplePathIn p ∧ ∀ v, v ∈ p.vertices ↔ v ∈ V(G)

def IsHamiltonianCycleIn (G : SimpleDiGraph α) (c : SimpleDiCycle α) : Prop :=
  G.IsSimpleDiCycleIn c ∧ ∀ v, v ∈ c.interior.vertices ↔ v ∈ V(G)

namespace IsEulerianTrailIn
theorem isSimpleWalkIn {G : SimpleDiGraph α} {w : SimpleWalk α} (h : G.IsEulerianTrailIn w) :
    G.IsSimpleWalkIn w := h.1
theorem arc_mem {G : SimpleDiGraph α} {w : SimpleWalk α} (h : G.IsEulerianTrailIn w)
    {a : α × α} : a ∈ w.arcs ↔ a ∈ E(G) := h.2.2 a
theorem congr {G H : SimpleDiGraph α} {w : SimpleWalk α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsEulerianTrailIn w ↔ H.IsEulerianTrailIn w := by
  simp only [SimpleDiGraph.IsEulerianTrailIn]
  rw [SimpleDiGraph.IsSimpleWalkIn.congr hV hE, hE]
end IsEulerianTrailIn

namespace IsEulerianCircuitIn
theorem isSimpleWalkIn {G : SimpleDiGraph α} {w : SimpleWalk α}
    (h : G.IsEulerianCircuitIn w) : G.IsSimpleWalkIn w := h.1
theorem arc_mem {G : SimpleDiGraph α} {w : SimpleWalk α} (h : G.IsEulerianCircuitIn w)
    {a : α × α} : a ∈ w.arcs ↔ a ∈ E(G) := h.2.2.2.2 a
theorem congr {G H : SimpleDiGraph α} {w : SimpleWalk α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsEulerianCircuitIn w ↔ H.IsEulerianCircuitIn w := by
  simp only [SimpleDiGraph.IsEulerianCircuitIn]
  rw [SimpleDiGraph.IsSimpleWalkIn.congr hV hE, hE]
end IsEulerianCircuitIn

namespace IsHamiltonianPathIn
theorem isSimplePathIn {G : SimpleDiGraph α} {p : SimplePath α}
    (h : G.IsHamiltonianPathIn p) : G.IsSimplePathIn p := h.1
theorem vertex_mem {G : SimpleDiGraph α} {p : SimplePath α} (h : G.IsHamiltonianPathIn p)
    {v : α} : v ∈ p.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : SimpleDiGraph α} {p : SimplePath α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsHamiltonianPathIn p ↔ H.IsHamiltonianPathIn p := by
  simp only [SimpleDiGraph.IsHamiltonianPathIn, SimpleDiGraph.IsSimplePathIn]
  rw [SimpleDiGraph.IsSimpleWalkIn.congr hV hE, hV]
end IsHamiltonianPathIn

namespace IsHamiltonianCycleIn
theorem isSimpleDiCycleIn {G : SimpleDiGraph α} {c : SimpleDiCycle α}
    (h : G.IsHamiltonianCycleIn c) : G.IsSimpleDiCycleIn c := h.1
theorem vertex_mem {G : SimpleDiGraph α} {c : SimpleDiCycle α}
    (h : G.IsHamiltonianCycleIn c) {v : α} : v ∈ c.interior.vertices ↔ v ∈ V(G) := h.2 v
theorem congr {G H : SimpleDiGraph α} {c : SimpleDiCycle α} (hV : V(G) = V(H))
    (hE : E(G) = E(H)) : G.IsHamiltonianCycleIn c ↔ H.IsHamiltonianCycleIn c := by
  simp only [SimpleDiGraph.IsHamiltonianCycleIn, SimpleDiGraph.IsSimpleDiCycleIn]
  rw [SimpleDiGraph.IsSimpleWalkIn.congr hV hE, hV]
end IsHamiltonianCycleIn

end SimpleDiGraph

end GraphLib
