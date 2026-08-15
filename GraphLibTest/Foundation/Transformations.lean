/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Reverse
import GraphLibTest.Foundation.Basic

/-!
# Same-carrier transformation tests

Compile-time and semantic fixtures for the Phase 2 subgraph/restriction API and the Phase 3
deletion, mapping, relabeling, reversal, and conversion API.
-/

namespace GraphLibTest.Foundation.Transformations

open GraphLib
open scoped GraphLib
open GraphLibTest.Foundation.Basic

variable {α β γ δ : Type*}

section TypeChecks

variable
  (Gu Hu : Graph α β) (Gs Hs : SimpleGraph α)
  (Gd Hd : DiGraph α β) (Gsd Hsd : SimpleDiGraph α)
  (S : Set α) (Fu : Set (Edge α β)) (Fs : Set (Sym2 α))
  (Fd : Set (Arc α β)) (Fsd : Set (α × α))

#check (Gu.induce S : Graph α β)
#check (Gs.induce S : SimpleGraph α)
#check (Gd.induce S : DiGraph α β)
#check (Gsd.induce S : SimpleDiGraph α)

#check (Gu.restrictEdges Fu : Graph α β)
#check (Gs.restrictEdges Fs : SimpleGraph α)
#check (Gd.restrictEdges Fd : DiGraph α β)
#check (Gsd.restrictEdges Fsd : SimpleDiGraph α)

example : Gu ≤ Gu := le_rfl
example : Gs ≤ Gs := le_rfl
example : Gd ≤ Gd := le_rfl
example : Gsd ≤ Gsd := le_rfl

example : Gu ≤s Gu := Graph.IsSpanningSubgraph.rfl Gu
example : Gs ≤s Gs := SimpleGraph.IsSpanningSubgraph.rfl Gs
example : Gd ≤s Gd := DiGraph.IsSpanningSubgraph.rfl Gd
example : Gsd ≤s Gsd := SimpleDiGraph.IsSpanningSubgraph.rfl Gsd

example : Gu ≤i Gu := Graph.IsInducedSubgraph.rfl Gu
example : Gs ≤i Gs := SimpleGraph.IsInducedSubgraph.rfl Gs
example : Gd ≤i Gd := DiGraph.IsInducedSubgraph.rfl Gd
example : Gsd ≤i Gsd := SimpleDiGraph.IsInducedSubgraph.rfl Gsd

example : V(Gu ⊓ Hu) = V(Gu) ∩ V(Hu) := by simp
example : E(Gs ⊔ Hs) = E(Gs) ∪ E(Hs) := by simp
example : V((⊥ : DiGraph α β)) = ∅ := by simp
example : E((⊤ : DiGraph α β)) = Set.univ := by simp
example : V(Gsd ⊔ Hsd) = V(Gsd) ∪ V(Hsd) := by simp
example : E(Gsd ⊓ Hsd) = E(Gsd) ∩ E(Hsd) := by simp

/-- The removed graph-indexing surface does not leave graph `GetElem` instances behind. -/
example : True := by
  fail_if_success
    have _h : GetElem (Graph α β) (Set α) (Graph α β) (fun _ _ => True) := inferInstance
  fail_if_success
    have _h : GetElem (SimpleGraph α) (Set α) (SimpleGraph α) (fun _ _ => True) :=
      inferInstance
  fail_if_success
    have _h : GetElem (DiGraph α β) (Set α) (DiGraph α β) (fun _ _ => True) := inferInstance
  fail_if_success
    have _h : GetElem (SimpleDiGraph α) (Set α) (SimpleDiGraph α) (fun _ _ => True) :=
      inferInstance
  trivial

end TypeChecks

section Laws

example (G : Graph α β) (S T : Set α) :
    (G.induce S).induce T = G.induce (S ∩ T) := by simp

example (G : SimpleGraph α) (S : Set α) :
    (G.induce S).induce S = G.induce S := by simp

example (G : DiGraph α β) (F K : Set (Arc α β)) :
    (G.restrictEdges F).restrictEdges K = G.restrictEdges (F ∩ K) := by simp

example (G : SimpleDiGraph α) (F : Set (α × α)) :
    (G.restrictEdges F).restrictEdges F = G.restrictEdges F := by simp

example (G : Graph α β) (S : Set α) : G.induce S ≤i G := G.induce_isInducedSubgraph S

example (G : DiGraph α β) (F : Set (Arc α β)) : G.restrictEdges F ≤s G :=
  G.restrictEdges_isSpanningSubgraph F

example : s(0, 0) ∉ E((⊤ : SimpleGraph Nat)) := by simp
example : (0, 0) ∉ E((⊤ : SimpleDiGraph Nat)) := by simp

end Laws

section ParallelEdges

/-- Restrict the parallel-edge fixture to exactly one bundled edge. -/
def oneParallelEdge : Graph Nat Bool := parallelGraph.restrictEdges {parallelEdgeFalse}

example : oneParallelEdge ≤ parallelGraph := by
  exact parallelGraph.restrictEdges_le {parallelEdgeFalse}

example : oneParallelEdge ≤s parallelGraph := by
  exact parallelGraph.restrictEdges_isSpanningSubgraph {parallelEdgeFalse}

example : parallelEdgeFalse ∈ E(oneParallelEdge) := by
  simp [oneParallelEdge, parallelGraph]

example : parallelEdgeTrue ∉ E(oneParallelEdge) := by
  simp [oneParallelEdge, parallelGraph, parallelEdgeFalse, parallelEdgeTrue]

example : oneParallelEdge.Adj 0 1 := by
  change (parallelGraph.restrictEdges {parallelEdgeFalse}).Adj 0 1
  rw [Graph.restrictEdges_adj]
  exact ⟨parallelEdgeFalse, by simp, by simp [parallelGraph, parallelEdgeFalse]⟩

/-- Restrict the parallel-arc fixture to exactly one bundled arc. -/
def oneParallelArc : DiGraph Nat Bool := parallelDiGraph.restrictEdges {parallelArcTrue}

example : parallelArcTrue ∈ E(oneParallelArc) := by
  simp [oneParallelArc, parallelDiGraph]

example : parallelArcFalse ∉ E(oneParallelArc) := by
  simp [oneParallelArc, parallelDiGraph, parallelArcFalse, parallelArcTrue]

example : oneParallelArc.Adj 0 1 := by
  change (parallelDiGraph.restrictEdges {parallelArcTrue}).Adj 0 1
  rw [DiGraph.restrictEdges_adj]
  exact ⟨parallelArcTrue, by simp, by simp [parallelDiGraph, parallelArcTrue]⟩

end ParallelEdges

section PhaseThreeTypeChecks

variable
  (Gu : Graph α β) (Gs : SimpleGraph α)
  (Gd : DiGraph α β) (Gsd : SimpleDiGraph α)
  (S : Set α) (Fu : Set (Edge α β)) (Fs : Set (Sym2 α))
  (Fd : Set (Arc α β)) (Fsd : Set (α × α))
  (eu : Edge α β) (es : Sym2 α) (ad : Arc α β) (asd : α × α)
  (f : α → Nat) (σ : α ≃ Nat) (τ : β ≃ Bool)

#check (Gu.deleteEdges Fu : Graph α β)
#check (Gu.deleteEdge eu : Graph α β)
#check (Gu.deleteVerts S : Graph α β)
#check (Gu.deleteVert eu.endpoints.out.1 : Graph α β)
#check (Gu.deleteEdgesBetween eu.endpoints.out.1 eu.endpoints.out.2 : Graph α β)

#check (Gs.deleteEdges Fs : SimpleGraph α)
#check (Gs.deleteEdge es : SimpleGraph α)
#check (Gd.deleteArcsFromTo ad.source ad.target : DiGraph α β)
#check (Gsd.deleteArcsFromTo asd.1 asd.2 : SimpleDiGraph α)

#check (Gu.mapVertices f : Graph Nat (Edge α β))
#check (Gd.mapVertices f : DiGraph Nat (Arc α β))
#check (Gs.mapVertices f : SimpleGraph Nat)
#check (Gsd.mapVertices f : SimpleDiGraph Nat)

#check (Gu.relabelVertices σ : Graph Nat β)
#check (Gd.relabelVertices σ : DiGraph Nat β)
#check (Gs.relabelVertices σ : SimpleGraph Nat)
#check (Gsd.relabelVertices σ : SimpleDiGraph Nat)
#check (Gu.relabelTags τ : Graph α Bool)
#check (Gd.relabelTags τ : DiGraph α Bool)

#check (Gu.underlyingSimple : SimpleGraph α)
#check (Gd.underlyingSimple : SimpleDiGraph α)
#check (Gd.forgetDirection : Graph α (Arc α β))
#check (Gsd.forgetDirection : SimpleGraph α)
#check (Gd.reverse : DiGraph α β)
#check (Gsd.reverse : SimpleDiGraph α)

end PhaseThreeTypeChecks

section Deletion

example : parallelEdgeFalse ∉ E(parallelGraph.deleteEdge parallelEdgeFalse) := by
  exact parallelGraph.not_mem_edgeSet_deleteEdge parallelEdgeFalse

example : parallelEdgeTrue ∈ E(parallelGraph.deleteEdge parallelEdgeFalse) := by
  rw [Graph.mem_edgeSet_deleteEdge]
  simp [parallelGraph, parallelEdgeFalse, parallelEdgeTrue]

example : parallelEdgeFalse ∉ E(parallelGraph.deleteEdgesBetween 0 1) := by
  rw [Graph.mem_edgeSet_deleteEdgesBetween]
  simp [parallelGraph, parallelEdgeFalse]

example : parallelEdgeTrue ∉ E(parallelGraph.deleteEdgesBetween 0 1) := by
  rw [Graph.mem_edgeSet_deleteEdgesBetween]
  simp [parallelGraph, parallelEdgeTrue]

example : parallelArcFalse ∉ E(parallelDiGraph.deleteEdge parallelArcFalse) := by
  exact parallelDiGraph.not_mem_edgeSet_deleteEdge parallelArcFalse

example : parallelArcTrue ∈ E(parallelDiGraph.deleteEdge parallelArcFalse) := by
  rw [DiGraph.mem_edgeSet_deleteEdge]
  simp [parallelDiGraph, parallelArcFalse, parallelArcTrue]

example : parallelArcFalse ∉ E(parallelDiGraph.deleteArcsFromTo 0 1) := by
  rw [DiGraph.mem_edgeSet_deleteArcsFromTo]
  simp [parallelDiGraph, parallelArcFalse]

example : parallelArcTrue ∉ E(parallelDiGraph.deleteArcsFromTo 0 1) := by
  rw [DiGraph.mem_edgeSet_deleteArcsFromTo]
  simp [parallelDiGraph, parallelArcTrue]

example : (parallelGraph.deleteVerts {0} : Graph Nat Bool) = parallelGraph.induce ({0}ᶜ) := rfl

end Deletion

section MappingAndRelabeling

def constantVertexMap : Nat → Unit := fun _ => ()

def mappedReusedEdgeOne : Edge Unit (Edge Nat Unit) :=
  Edge.mapVertices constantVertexMap reusedTagEdgeOne

def mappedReusedEdgeTwo : Edge Unit (Edge Nat Unit) :=
  Edge.mapVertices constantVertexMap reusedTagEdgeTwo

example : mappedReusedEdgeOne ≠ mappedReusedEdgeTwo := by
  intro h
  exact (by decide : reusedTagEdgeOne ≠ reusedTagEdgeTwo)
    (Edge.mapVertices_injective constantVertexMap h)

example : mappedReusedEdgeOne ∈ E(tagReuseGraph.mapVertices constantVertexMap) := by
  simp [mappedReusedEdgeOne, tagReuseGraph]

example : mappedReusedEdgeTwo ∈ E(tagReuseGraph.mapVertices constantVertexMap) := by
  simp [mappedReusedEdgeTwo, tagReuseGraph]

example : mappedReusedEdgeOne.tag = reusedTagEdgeOne := rfl
example : mappedReusedEdgeTwo.tag = reusedTagEdgeTwo := rfl

/-- A one-edge simple graph used to expose loop dropping under a constant map. -/
def simpleOneEdge : SimpleGraph Nat where
  vertexSet := Set.univ
  edgeSet := {s(0, 1)}
  endpoints_mem := by simp
  loopless := by simp

example : E(simpleOneEdge.mapVertices constantVertexMap) = ∅ := by
  ext e
  induction e with
  | h u v => simp [simpleOneEdge, constantVertexMap]

example (G : Graph α β) : G.relabelVertices (Equiv.refl α) = G := by simp
example (G : DiGraph α β) : G.relabelTags (Equiv.refl β) = G := by simp

example (G : Graph α β) (f : α ≃ γ) (g : γ ≃ δ) :
    (G.relabelVertices f).relabelVertices g = G.relabelVertices (f.trans g) := by simp

example (G : SimpleGraph α) (f : α ≃ Nat) :
    (G.relabelVertices f).relabelVertices f.symm = G := by simp

end MappingAndRelabeling

section ReversalAndConversions

example : testArc.reverse.source = 5 := rfl
example : testArc.reverse.target = 4 := rfl
example : testArc.reverse.reverse = testArc := by simp

example : testArc.reverse ∈ E(oneArcDiGraph.reverse) := by
  simp [oneArcDiGraph, testArc]

example : oneArcDiGraph.reverse.Adj 5 4 := by
  rw [DiGraph.reverse_adj]
  exact (by simp [oneArcDiGraph, testArc] : oneArcDiGraph.IsArc testArc 4 5).adj

example : oneArcDiGraph.reverse.reverse = oneArcDiGraph := by simp

example : E(parallelGraph.underlyingSimple) = {s(0, 1)} := by
  ext e
  rw [Graph.mem_edgeSet_underlyingSimple]
  constructor
  · rintro ⟨he, -⟩
    simpa [Graph.edgeEndpointPairSet, parallelGraph, parallelEdgeFalse, parallelEdgeTrue,
      eq_comm] using he
  · intro he
    have heq : e = s(0, 1) := by simpa using he
    subst e
    constructor
    · exact ⟨parallelEdgeFalse, by simp [parallelGraph], rfl⟩
    · simp [Sym2.mk_isDiag_iff]

/-- A general loop is dropped by `underlyingSimple`. -/
def oneLoopGraph : Graph Nat Unit where
  vertexSet := {0}
  edgeSet := {⟨(), s(0, 0)⟩}
  endpoints_mem := by simp

example : E(oneLoopGraph.underlyingSimple) = ∅ := by
  ext e
  constructor
  · rintro ⟨⟨a, ha, hends⟩, hnon⟩
    have haeq : a = ⟨(), s(0, 0)⟩ := by simpa [oneLoopGraph] using ha
    subst a
    apply hnon
    rw [← hends]
    simp
  · simp

/-- Antiparallel simple arcs merge after direction is forgotten. -/
def antiparallelSimpleDiGraph : SimpleDiGraph Nat where
  vertexSet := Set.univ
  edgeSet := {(0, 1), (1, 0)}
  source_mem := by simp
  target_mem := by simp
  loopless := by simp

example : E(antiparallelSimpleDiGraph.forgetDirection) = {s(0, 1)} := by
  have hswap : s(1, 0) = s(0, 1) := Sym2.eq_swap
  ext e
  simp [antiparallelSimpleDiGraph, SimpleDiGraph.forgetDirection, hswap, eq_comm]

example : oneArcDiGraph.forgetDirection.Adj 4 5 := by
  rw [DiGraph.forgetDirection_adj]
  left
  exact (by simp [oneArcDiGraph, testArc] : oneArcDiGraph.IsArc testArc 4 5).adj

example : oneArcDiGraph.forgetDirection.Adj 5 4 := by
  rw [DiGraph.forgetDirection_adj]
  right
  exact (by simp [oneArcDiGraph, testArc] : oneArcDiGraph.IsArc testArc 4 5).adj

end ReversalAndConversions

end GraphLibTest.Foundation.Transformations
