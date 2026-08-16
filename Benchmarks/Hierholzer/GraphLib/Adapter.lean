import Benchmarks.Hierholzer.Common
import GraphLib.Graph.DegreeSum

/-!
# GraphLib semantic adapter for the Hierholzer benchmark

This module spells the frozen graph-neutral meanings using full bundled GraphLib edges.  In
particular, `ActualEdge G` is a subtype of `E(G)` and never the edge tag or endpoint image.
-/

set_option autoImplicit false

namespace Benchmarks.Hierholzer.GraphLib

open scoped _root_.GraphLib
open scoped BigOperators

universe u v

variable {α : Type u} {β : Type v}

/-- The actual mathematical vertices of `G`. -/
abbrev Vertex (G : _root_.GraphLib.Graph α β) := {v // v ∈ V(G)}

/-- The actual bundled mathematical edges of `G`. -/
abbrev ActualEdge (G : _root_.GraphLib.Graph α β) := {e // e ∈ E(G)}

/-- The frozen actual-edge link relation. -/
def Link (G : _root_.GraphLib.Graph α β) (e : ActualEdge G) (x y : Vertex G) : Prop :=
  G.IsLink e.1 x.1 y.1

/-- The frozen incidence relation. -/
def Inc (G : _root_.GraphLib.Graph α β) (e : ActualEdge G) (x : Vertex G) : Prop :=
  ∃ y : Vertex G, Link G e x y

/-- The frozen loop relation. -/
def Loop (G : _root_.GraphLib.Graph α β) (e : ActualEdge G) (x : Vertex G) : Prop :=
  Link G e x x

/-- The frozen loop-counting degree. -/
noncomputable def degree (G : _root_.GraphLib.Graph α β) (x : Vertex G) : Nat :=
  Set.ncard {e : ActualEdge G | Inc G e x} + Set.ncard {e : ActualEdge G | Loop G e x}

/-- The frozen edge-forgetting one-step relation. -/
def Step (G : _root_.GraphLib.Graph α β) (x y : Vertex G) : Prop :=
  ∃ e : ActualEdge G, Link G e x y

/-- The frozen reflexive-transitive reachability relation. -/
def Reachable (G : _root_.GraphLib.Graph α β) : Vertex G → Vertex G → Prop :=
  Relation.ReflTransGen (Step G)

/-- The official number of mathematical vertices. -/
noncomputable def vertexCount (G : _root_.GraphLib.Graph α β) : Nat :=
  Set.ncard V(G)

/-- The official number of actual bundled mathematical edges. -/
noncomputable def edgeCount (G : _root_.GraphLib.Graph α β) : Nat :=
  Set.ncard E(G)

theorem inc_iff_graphInc (G : _root_.GraphLib.Graph α β) (e : ActualEdge G) (x : Vertex G) :
    Inc G e x ↔ G.Inc e.1 x.1 := by
  constructor
  · rintro ⟨y, hy⟩
    exact hy.inc_left
  · intro hx
    obtain ⟨y, hy⟩ := (G.inc_iff_exists_isLink e.1 x.1).mp hx
    exact ⟨⟨y, hy.right_mem⟩, hy⟩

theorem loop_iff_graphIsLink (G : _root_.GraphLib.Graph α β) (e : ActualEdge G)
    (x : Vertex G) : Loop G e x ↔ G.IsLink e.1 x.1 x.1 := Iff.rfl

/-- The frozen degree is definitionally faithful to GraphLib's loop-corrected native degree. -/
theorem degree_eq_graphDegree (G : _root_.GraphLib.Graph α β) [Finite E(G)] (x : Vertex G) :
    degree G x = G.degree x.1 := by
  rw [degree]
  have hinc : Set.ncard {e : ActualEdge G | Inc G e x} =
      Set.ncard (G.incidenceSet x.1) := by
    rw [show {e : ActualEdge G | Inc G e x} =
        {e : ActualEdge G | G.Inc e.1 x.1} by ext e; simp [inc_iff_graphInc]]
    change Set.ncard {e : ActualEdge G | e.1 ∈ G.incidenceSet x.1} = _
    rw [Set.ncard_subtype]
    congr 1
    ext e
    simp [_root_.GraphLib.Graph.Inc] <;> aesop
  have hloop : Set.ncard {e : ActualEdge G | Loop G e x} =
      Set.ncard (G.loopSet x.1) := by
    change Set.ncard {e : ActualEdge G | G.IsLink e.1 x.1 x.1} = _
    change Set.ncard {e : ActualEdge G | e.1 ∈ G.loopSet x.1} = _
    rw [Set.ncard_subtype]
    congr 1
    ext e
    simp [_root_.GraphLib.Graph.IsLink] <;> aesop
  rw [hinc, hloop, G.ncard_incidenceSet_add_ncard_loopSet_eq_degree]

theorem natCard_vertex (G : _root_.GraphLib.Graph α β) :
    Nat.card (Vertex G) = vertexCount G := by
  rw [← Set.ncard_univ]
  simpa [vertexCount] using
    (Set.ncard_subtype (fun x : α => x ∈ V(G)) (Set.univ : Set α))

theorem natCard_actualEdge (G : _root_.GraphLib.Graph α β) :
    Nat.card (ActualEdge G) = edgeCount G := by
  rw [← Set.ncard_univ]
  simpa [edgeCount] using
    (Set.ncard_subtype (fun e : _root_.GraphLib.Edge α β => e ∈ E(G))
      (Set.univ : Set (_root_.GraphLib.Edge α β)))

/-- The sum of frozen adapter degrees, with a proof-local finite enumeration. -/
noncomputable def degreeSum (G : _root_.GraphLib.Graph α β) [Finite V(G)] : Nat :=
  letI : Fintype (Vertex G) := Fintype.ofFinite (Vertex G)
  ∑ x : Vertex G, degree G x

/-- The native handshaking theorem, transported to the frozen subtype-indexed adapter degree. -/
theorem degreeSum_eq_twice_edgeCount (G : _root_.GraphLib.Graph α β)
    [Finite V(G)] [Finite E(G)] : degreeSum G = 2 * edgeCount G := by
  classical
  unfold degreeSum
  letI : Fintype (Vertex G) := Fintype.ofFinite (Vertex G)
  calc
    (∑ x : Vertex G, degree G x) = ∑ x : Vertex G, G.degree x.1 := by
      apply Finset.sum_congr rfl
      intro x _
      exact degree_eq_graphDegree G x
    _ = ∑ x ∈ G.vertexFinset, G.degree x := by
      symm
      exact Finset.sum_subtype G.vertexFinset (fun x => G.mem_vertexFinset)
        (fun x => G.degree x)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    _ = 2 * edgeCount G := by rw [edgeCount, G.ncard_edgeSet]

end Benchmarks.Hierholzer.GraphLib
