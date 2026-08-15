/-
Throwaway experiments for `prompts/0814_design.md`.

This file is deliberately outside `GraphLib/`: it compares representations without changing
the public library.  It is compiled directly with

  lake env lean Prototypes/RepresentationStress.lean

The namespaces correspond to the three candidates in the prompt:

* `Bundled`: today's `GraphLib.Edge` / `GraphLib.Arc` representation;
* `Separate`: an abstract edge identity, using pinned Mathlib's `Graph` for undirected tests
  and a small function-backed `IsArc` model for directed tests;
* `OriginTagged`: a minimal transformation-side change which keeps bundled arcs but uses the
entire source arc as the output label during a noninjective vertex map.
-/

import GraphLib.Graph.Subgraph
import GraphLib.Theory.Structures.Walk
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.Graph.Maps

namespace RepresentationStress

open Set

/-! ## Shared residual-edge identity -/

/-- Residual direction is part of identity; `reverse e` cannot collide with either
`forward e` or with a pre-existing antiparallel edge. -/
inductive ResidualId (ε : Type*) where
  | forward : ε → ResidualId ε
  | reverse : ε → ResidualId ε
deriving DecidableEq, Repr

/-! ## Candidate 1: current bundled edge / arc values -/

namespace Bundled

open GraphLib
open scoped GraphLib

def parallel₀ : Edge Nat Bool := ⟨false, s(0, 1)⟩
def parallel₁ : Edge Nat Bool := ⟨true, s(0, 1)⟩

/-- Parallel edges are distinguishable when their labels differ. -/
example : parallel₀ ≠ parallel₁ := by decide

/-- Deleting one particular parallel edge from the actual bundled edge set keeps the other. -/
example : parallel₁ ∈ (({parallel₀, parallel₁} : Finset (Edge Nat Bool)).erase parallel₀) := by
  native_decide

example : parallel₀ ∉ (({parallel₀, parallel₁} : Finset (Edge Nat Bool)).erase parallel₀) := by
  simp

def twoParallelGraph : GraphLib.Graph Nat Bool where
  vertexSet := Set.univ
  edgeSet := {parallel₀, parallel₁}
  incidence' := by simp

def deleteEdge [DecidableEq β] (G : GraphLib.Graph α β) (e₀ : Edge α β) :
    GraphLib.Graph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet \ {e₀}
  incidence' := by
    intro e he
    exact G.incidence' e he.1

example : parallel₀ ∉ (deleteEdge twoParallelGraph parallel₀).edgeSet := by
  simp [deleteEdge]

example : parallel₁ ∈ (deleteEdge twoParallelGraph parallel₀).edgeSet := by
  simp [deleteEdge, twoParallelGraph, parallel₀, parallel₁]

/-- The public `E(G)` endpoint image cannot say which parallel edge survived: after deleting
`parallel₀`, its endpoint pair is still present because `parallel₁` has the same endpoints. -/
example : parallel₀.endpoints ∈ E(deleteEdge twoParallelGraph parallel₀) := by
  refine ⟨parallel₁, ?_, ?_⟩
  · simp [deleteEdge, twoParallelGraph, parallel₀, parallel₁]
  · decide

def mapEdge (f : α → γ) (e : Edge α β) : Edge γ β :=
  ⟨e.endpointsLabel, e.endpoints.map f⟩

/-- Same label, different original endpoints: legal under the current structure. -/
def collision₀ : Edge Nat Bool := ⟨false, s(0, 1)⟩
def collision₁ : Edge Nat Bool := ⟨false, s(2, 3)⟩

example : collision₀ ≠ collision₁ := by decide

/-- The raw bundled endpoint-map really does collapse legal, distinct edges. -/
example : mapEdge (fun _ : Nat => ()) collision₀ = mapEdge (fun _ : Nat => ()) collision₁ := by
  decide

def mapArc (f : α → γ) (e : Arc α β) : Arc γ β :=
  ⟨e.endpointsLabel, (f e.endpoints.1, f e.endpoints.2)⟩

def arc01 : Arc Nat Bool := ⟨false, (0, 1)⟩
def arc23 : Arc Nat Bool := ⟨false, (2, 3)⟩

example : arc01 ≠ arc23 := by decide
example : mapArc (fun _ : Nat => ()) arc01 = mapArc (fun _ : Nat => ()) arc23 := by decide

/-- Weights transport definitionally if they are really functions of the label.  Treating
arbitrary labels as identities is an extra semantic convention, not a current invariant. -/
def labelWeight (e : Edge α Bool) : Nat := if e.endpointsLabel then 11 else 7

example (f : α → γ) (e : Edge α Bool) : labelWeight (mapEdge f e) = labelWeight e := rfl

/-- A bijective vertex relabeling induces an explicit equivalence-style transport on arbitrary
arc weights.  Unlike a label-only weight, this is not definitionally unchanged, but its
round-trip theorem is discharged by the equivalence laws rather than by an equality cast. -/
def relabelArcWeight (f : α ≃ γ) (w : Arc α β → κ) (e : Arc γ β) : κ :=
  w (mapArc f.symm e)

example (f : α ≃ γ) (w : Arc α β → κ) (e : Arc α β) :
    relabelArcWeight f w (mapArc f e) = w e := by
  cases e with
  | mk label endpoints =>
    rcases endpoints with ⟨u, v⟩
    simp [relabelArcWeight, mapArc]

def reverseArc (e : Arc α β) : Arc α β :=
  ⟨e.endpointsLabel, (e.endpoints.2, e.endpoints.1)⟩

@[simp] theorem reverseArc_reverseArc (e : Arc α β) : reverseArc (reverseArc e) = e := by
  cases e
  rfl

def oneArcGraph : DiGraph Nat Bool where
  vertexSet := Set.univ
  edgeSet := {arc01}
  incidence' := by
    intro e he
    simp only [Set.mem_singleton_iff] at he
    subst e
    simp [arc01]

def reverse (G : DiGraph α β) : DiGraph α β where
  vertexSet := G.vertexSet
  edgeSet := reverseArc '' G.edgeSet
  incidence' := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hs, ht⟩ := G.incidence' e he
    exact ⟨ht, hs⟩

/-- Realization checks the exact bundled arc at each step. -/
def Realized (G : DiGraph α β) : Walk α (Arc α β) → Prop
  | .singleton v => v ∈ G.vertexSet
  | .cons w v e =>
      Realized G w ∧ e ∈ G.edgeSet ∧ e.endpoints = (w.tail, v)

def directedWalk : Walk Nat (Arc Nat Bool) :=
  (Walk.singleton 0).cons 1 arc01

example : Realized oneArcGraph directedWalk := by
  simp [Realized, oneArcGraph, directedWalk, arc01]

/-- Reversal changes both the order of the walk and every bundled arc value. -/
def reversedDirectedWalk : Walk Nat (Arc Nat Bool) :=
  (directedWalk.mapE reverseArc).reverse

example : Realized (reverse oneArcGraph) reversedDirectedWalk := by
  change Realized (reverse oneArcGraph)
    ((Walk.singleton 1).cons 0 (reverseArc arc01))
  simp [Realized, reverse, oneArcGraph, arc01, reverseArc]

/-- The edge-aware walk retains the exact bundled arc, not just `(0,1)`. -/
example : directedWalk.toEdgeList = [arc01] := rfl

/-- Inducing a graph keeps the ambient vertex and bundled-edge types, hence no subtype casts. -/
example : arc01 ∈ (oneArcGraph.induce ({0, 1} : Set Nat)).edgeSet := by
  simp [oneArcGraph, arc01, DiGraph.induce]

/-- A reverse residual copy and a genuinely antiparallel original coexist by tagging labels. -/
def residualForward : Arc Nat (ResidualId Bool) :=
  ⟨.forward false, (0, 1)⟩

def residualReverse : Arc Nat (ResidualId Bool) :=
  ⟨.reverse false, (1, 0)⟩

def originalAntiparallel : Arc Nat (ResidualId Bool) :=
  ⟨.forward true, (1, 0)⟩

example : residualForward ≠ residualReverse := by decide
example : residualReverse ≠ originalAntiparallel := by decide
example : residualForward ≠ originalAntiparallel := by decide

end Bundled

/-! ## Candidate 2: separate edge identities and IsLink / IsArc -/

namespace Separate

/-! The undirected deletion test uses the actual stable `Graph` API in pinned Mathlib. -/

def twoParallel : Graph Nat Bool := Graph.banana 0 1 Set.univ

example : twoParallel.IsLink false 0 1 := by simp [twoParallel]
example : twoParallel.IsLink true 0 1 := by simp [twoParallel]
example : false ∉ Graph.edgeSet (twoParallel.deleteEdges {false}) := by simp
example : true ∈ Graph.edgeSet (twoParallel.deleteEdges {false}) := by simp [twoParallel]

/-- Pinned Mathlib vertex maps leave `E(G) : Set ε` definitionally unchanged, even for a
noninjective map. -/
example (G : Graph α ε) (f : α → γ) : Graph.edgeSet (G.map f) = Graph.edgeSet G := rfl

/-- Function-backed directed incidence.  `IsArc` is graph-relative and the edge identity `ε`
does not contain endpoints.  This represents the separate-identity family without reproducing
all of Mathlib's relational structure axioms in this throwaway file. -/
structure DiGraph (α ε : Type*) where
  vertexSet : Set α
  edgeSet : Set ε
  source : ε → α
  target : ε → α
  incidence' : ∀ e ∈ edgeSet, source e ∈ vertexSet ∧ target e ∈ vertexSet

def DiGraph.IsArc (G : DiGraph α ε) (e : ε) (u v : α) : Prop :=
  e ∈ G.edgeSet ∧ G.source e = u ∧ G.target e = v

def DiGraph.mapV (G : DiGraph α ε) (f : α → γ) : DiGraph γ ε where
  vertexSet := f '' G.vertexSet
  edgeSet := G.edgeSet
  source := f ∘ G.source
  target := f ∘ G.target
  incidence' := by
    intro e he
    obtain ⟨hs, ht⟩ := G.incidence' e he
    exact ⟨⟨G.source e, hs, rfl⟩, ⟨G.target e, ht, rfl⟩⟩

def distinctEndpointArcs : DiGraph Nat Bool where
  vertexSet := Set.univ
  edgeSet := Set.univ
  source b := if b then 2 else 0
  target b := if b then 3 else 1
  incidence' := by simp

/-- Endpoint collision does not imply identity collision: the carrier is still `Bool`. -/
example : (distinctEndpointArcs.mapV (fun _ => ())).source false =
    (distinctEndpointArcs.mapV (fun _ => ())).source true := rfl

example : (distinctEndpointArcs.mapV (fun _ => ())).target false =
    (distinctEndpointArcs.mapV (fun _ => ())).target true := rfl

example : (false : Bool) ≠ true := by decide

/-- Edge weights need no transport at all under a vertex map because `ε` is unchanged. -/
def capacity : Bool → Nat
  | false => 5
  | true => 13

example (f : Nat → γ) (e : Bool)
    (_he : e ∈ (distinctEndpointArcs.mapV f).edgeSet) : capacity e = capacity e := rfl

def DiGraph.reverse (G : DiGraph α ε) : DiGraph α ε where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  source := G.target
  target := G.source
  incidence' := by
    intro e he
    obtain ⟨hs, ht⟩ := G.incidence' e he
    exact ⟨ht, hs⟩

def directedGraph : DiGraph Nat Bool where
  vertexSet := Set.univ
  edgeSet := {false}
  source _ := 0
  target _ := 1
  incidence' := by simp

def Realized (G : DiGraph α ε) : Walk α ε → Prop
  | .singleton v => v ∈ G.vertexSet
  | .cons w v e => Realized G w ∧ G.IsArc e w.tail v

def directedWalk : Walk Nat Bool := (Walk.singleton 0).cons 1 false

example : Realized directedGraph directedWalk := by
  simp [Realized, directedGraph, directedWalk, DiGraph.IsArc]

/-- Reversing the graph changes incidence but not the walk's edge identities. -/
example : Realized directedGraph.reverse directedWalk.reverse := by
  change Realized directedGraph.reverse ((Walk.singleton 1).cons 0 false)
  simp [Realized, DiGraph.reverse, directedGraph, DiGraph.IsArc]

example : directedWalk.toEdgeList = [false] := rfl

def DiGraph.deleteEdge [DecidableEq ε] (G : DiGraph α ε) (e₀ : ε) : DiGraph α ε where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet \ {e₀}
  source := G.source
  target := G.target
  incidence' := by
    intro e he
    exact G.incidence' e he.1

example : true ∈ (distinctEndpointArcs.deleteEdge false).edgeSet := by
  simp [DiGraph.deleteEdge, distinctEndpointArcs]

example : false ∉ (distinctEndpointArcs.deleteEdge false).edgeSet := by
  simp [DiGraph.deleteEdge]

def DiGraph.induce (G : DiGraph α ε) (S : Set α) : DiGraph α ε where
  vertexSet := S ∩ G.vertexSet
  edgeSet := {e ∈ G.edgeSet | G.source e ∈ S ∧ G.target e ∈ S}
  source := G.source
  target := G.target
  incidence' := by
    rintro e ⟨he, hs, ht⟩
    obtain ⟨hGs, hGt⟩ := G.incidence' e he
    exact ⟨⟨hs, hGs⟩, ⟨ht, hGt⟩⟩

/-- The edge has exactly the same type and value in an induced graph; no `Subtype` casts. -/
example : false ∈ (directedGraph.induce ({0, 1} : Set Nat)).edgeSet := by
  simp [DiGraph.induce, directedGraph]

def residual (G : DiGraph α ε) : DiGraph α (ResidualId ε) where
  vertexSet := G.vertexSet
  edgeSet := {r | match r with
    | .forward e => e ∈ G.edgeSet
    | .reverse e => e ∈ G.edgeSet}
  source r := match r with
    | .forward e => G.source e
    | .reverse e => G.target e
  target r := match r with
    | .forward e => G.target e
    | .reverse e => G.source e
  incidence' := by
    intro r hr
    cases r with
    | forward e => exact G.incidence' e hr
    | reverse e =>
      obtain ⟨hs, ht⟩ := G.incidence' e hr
      exact ⟨ht, hs⟩

example : ResidualId.forward false ≠ ResidualId.reverse false := by decide
example : ResidualId.reverse false ≠ ResidualId.forward true := by decide

end Separate

/-! ## Candidate 3: keep bundles, localize collision handling to the transformation -/

namespace OriginTagged

open GraphLib

/-- The output remains a bundled `Arc`, but its label is the entire source arc.  This is the
smallest construction-side repair for a noninjective vertex map: no new public graph type and
no global label-uniqueness invariant. -/
def mapArcKeepOrigin (f : α → γ) (e : Arc α β) : Arc γ (Arc α β) :=
  ⟨e, (f e.endpoints.1, f e.endpoints.2)⟩

theorem mapArcKeepOrigin_injective (f : α → γ) :
    Function.Injective (mapArcKeepOrigin (β := β) f) := by
  intro e₁ e₂ h
  exact congrArg Arc.endpointsLabel h

def collision₀ : Arc Nat Bool := ⟨false, (0, 1)⟩
def collision₁ : Arc Nat Bool := ⟨false, (2, 3)⟩

example : collision₀ ≠ collision₁ := by decide

/-- Endpoints coincide after contraction-like mapping ... -/
example : (mapArcKeepOrigin (fun _ : Nat => ()) collision₀).endpoints =
    (mapArcKeepOrigin (fun _ : Nat => ()) collision₁).endpoints := rfl

/-- ... but the output arcs remain distinct because their source arcs are their identities. -/
example : mapArcKeepOrigin (fun _ : Nat => ()) collision₀ ≠
    mapArcKeepOrigin (fun _ : Nat => ()) collision₁ := by decide

/-- Arbitrary edge weights/capacities transport by projection, with no inverse or choice. -/
def transportWeight (w : Arc α β → κ) (e : Arc γ (Arc α β)) : κ :=
  w e.endpointsLabel

example (w : Arc α β → κ) (f : α → γ) (e : Arc α β) :
    transportWeight w (mapArcKeepOrigin f e) = w e := rfl

def mapVKeepOrigin (G : DiGraph α β) (f : α → γ) : DiGraph γ (Arc α β) where
  vertexSet := f '' G.vertexSet
  edgeSet := mapArcKeepOrigin f '' G.edgeSet
  incidence' := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hs, ht⟩ := G.incidence' e he
    exact ⟨⟨e.endpoints.1, hs, rfl⟩, ⟨e.endpoints.2, ht, rfl⟩⟩

def sourceGraph : DiGraph Nat Bool := Bundled.oneArcGraph

example : mapArcKeepOrigin (fun _ : Nat => ()) Bundled.arc01 ∈
    (mapVKeepOrigin sourceGraph (fun _ : Nat => ())).edgeSet := by
  exact ⟨Bundled.arc01, by simp [sourceGraph, Bundled.oneArcGraph], rfl⟩

/-- Origin tagging composes awkwardly if applied naively: applying it twice nests the old
bundled arc in the new label.  This typechecks, documenting the real API friction. -/
def twiceMappedType (G : DiGraph α β) (f : α → γ) (g : γ → δ) :
    DiGraph δ (Arc γ (Arc α β)) :=
  mapVKeepOrigin (mapVKeepOrigin G f) g

end OriginTagged

end RepresentationStress
