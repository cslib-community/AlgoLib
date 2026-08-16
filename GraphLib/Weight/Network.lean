/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Finite
import GraphLib.Weight.Basic

/-!
# Networks, flows, and cuts

A network is specification data attached to a general directed graph. Capacities and flows are
indexed by complete bundled actual arcs, so parallel arcs, antiparallel arcs, loops, and reused
tags remain distinct. Algebraic, order, and finiteness assumptions are introduced only by the
operations that need them.
-/

namespace GraphLib

open scoped BigOperators GraphLib

variable {α β γ δ R : Type*}

namespace DiGraph

/-- A source, sink, and actual-arc capacity function attached to a directed graph. -/
structure Network (G : DiGraph α β) (R : Type*) where
  /-- The distinguished source vertex. -/
  source : α
  /-- The distinguished sink vertex. -/
  sink : α
  /-- The source belongs to the graph. -/
  source_mem : source ∈ V(G)
  /-- The sink belongs to the graph. -/
  sink_mem : sink ∈ V(G)
  /-- Source and sink are distinct. -/
  source_ne_sink : source ≠ sink
  /-- Capacity of each complete bundled ambient arc; only values on `E(G)` matter. -/
  capacity : Arc α β → R

/-- A flow on a network assigns a value to each complete bundled ambient arc. -/
abbrev Flow {G : DiGraph α β} (_N : Network G R) := Arc α β → R

/-! ## Cuts -/

/-- The active actual arcs whose source lies in `S` and whose target lies outside `S`. -/
def cutArcSet (G : DiGraph α β) (S : Set α) : Set (Arc α β) :=
  {a | a ∈ E(G) ∧ a.source ∈ S ∧ a.target ∉ S}

@[simp] theorem mem_cutArcSet (G : DiGraph α β) (S : Set α) (a : Arc α β) :
    a ∈ G.cutArcSet S ↔ a ∈ E(G) ∧ a.source ∈ S ∧ a.target ∉ S := Iff.rfl

/-- Every cut arc is an active arc of the graph. -/
theorem cutArcSet_subset_edgeSet (G : DiGraph α β) (S : Set α) :
    G.cutArcSet S ⊆ E(G) := fun _ ha => ha.1

/-- A finite actual-arc set has finite cut-arc sets. -/
theorem cutArcSet_finite (G : DiGraph α β) (S : Set α) [Finite E(G)] :
    (G.cutArcSet S).Finite := G.edgeSet_finite.subset (G.cutArcSet_subset_edgeSet S)

instance instFiniteCutArcSet (G : DiGraph α β) (S : Set α) [Finite E(G)] :
    Finite (G.cutArcSet S) := (G.cutArcSet_finite S).to_subtype

/-- The finite actual arcs leaving `S`, with membership equal to `cutArcSet`. -/
noncomputable def cutArcFinset (G : DiGraph α β) (S : Set α) [Finite E(G)] :
    Finset (Arc α β) := by
  classical
  exact G.edgeFinset.filter (fun a => a.source ∈ S ∧ a.target ∉ S)

@[simp] theorem mem_cutArcFinset (G : DiGraph α β) (S : Set α) [Finite E(G)]
    (a : Arc α β) : a ∈ G.cutArcFinset S ↔ a ∈ G.cutArcSet S := by
  simp [cutArcFinset]

namespace Network

/-- Relabel a network's vertices, transporting capacity along the induced arc equivalence. -/
def relabelVertices {G : DiGraph α β} (N : Network G R) (f : α ≃ γ) :
    Network (G.relabelVertices f) R where
  source := f N.source
  sink := f N.sink
  source_mem := ⟨N.source, N.source_mem, rfl⟩
  sink_mem := ⟨N.sink, N.sink_mem, rfl⟩
  source_ne_sink := fun h => N.source_ne_sink (f.injective h)
  capacity := DiGraph.Capacity.transportRelabelVertices G f N.capacity

/-- Relabel a network's arc tags, transporting capacity along the induced arc equivalence. -/
def relabelTags {G : DiGraph α β} (N : Network G R) (f : β ≃ δ) :
    Network (G.relabelTags f) R where
  source := N.source
  sink := N.sink
  source_mem := N.source_mem
  sink_mem := N.sink_mem
  source_ne_sink := N.source_ne_sink
  capacity := DiGraph.Capacity.transportRelabelTags G f N.capacity

/-- Reverse a network, swapping source and sink and transporting capacity to reversed arcs. -/
def reverse {G : DiGraph α β} (N : Network G R) : Network G.reverse R where
  source := N.sink
  sink := N.source
  source_mem := N.sink_mem
  sink_mem := N.source_mem
  source_ne_sink := N.source_ne_sink.symm
  capacity := DiGraph.Capacity.transportReverse G N.capacity

@[simp] theorem source_relabelVertices {G : DiGraph α β} (N : Network G R)
    (f : α ≃ γ) : (N.relabelVertices f).source = f N.source := rfl

@[simp] theorem sink_relabelVertices {G : DiGraph α β} (N : Network G R)
    (f : α ≃ γ) : (N.relabelVertices f).sink = f N.sink := rfl

@[simp] theorem capacity_relabelVertices {G : DiGraph α β} (N : Network G R)
    (f : α ≃ γ) (a : Arc α β) :
    (N.relabelVertices f).capacity (Arc.relabelVertices f a) = N.capacity a := by
  simp [relabelVertices]

@[simp] theorem source_relabelTags {G : DiGraph α β} (N : Network G R)
    (f : β ≃ δ) : (N.relabelTags f).source = N.source := rfl

@[simp] theorem sink_relabelTags {G : DiGraph α β} (N : Network G R)
    (f : β ≃ δ) : (N.relabelTags f).sink = N.sink := rfl

@[simp] theorem capacity_relabelTags {G : DiGraph α β} (N : Network G R)
    (f : β ≃ δ) (a : Arc α β) :
    (N.relabelTags f).capacity (Arc.relabelTags f a) = N.capacity a := by
  simp [relabelTags]

@[simp] theorem source_reverse {G : DiGraph α β} (N : Network G R) :
    N.reverse.source = N.sink := rfl

@[simp] theorem sink_reverse {G : DiGraph α β} (N : Network G R) :
    N.reverse.sink = N.source := rfl

@[simp] theorem capacity_reverse {G : DiGraph α β} (N : Network G R)
    (a : Arc α β) : N.reverse.capacity a.reverse = N.capacity a := by
  simp [reverse]

/-- A cut contains the source, excludes the sink, and contains only graph vertices. -/
def IsCut {G : DiGraph α β} (N : Network G R) (S : Set α) : Prop :=
  S ⊆ V(G) ∧ N.source ∈ S ∧ N.sink ∉ S

/-- The capacity of arcs leaving a vertex set. -/
noncomputable def cutCapacity {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) (S : Set α) : R := (G.cutArcFinset S).sum N.capacity

theorem cutCapacity_eq_sum_cutArcFinset {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) (S : Set α) :
    N.cutCapacity S = (G.cutArcFinset S).sum N.capacity := rfl

/-- Cut capacity depends only on capacity values of active arcs. -/
theorem cutCapacity_congr {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    {N₁ N₂ : Network G R}
    (hcapacity : DiGraph.Capacity.EqOn G N₁.capacity N₂.capacity)
    (S : Set α) : N₁.cutCapacity S = N₂.cutCapacity S := by
  classical
  rw [cutCapacity_eq_sum_cutArcFinset, cutCapacity_eq_sum_cutArcFinset]
  apply Finset.sum_congr rfl
  intro a ha
  exact hcapacity (G.mem_cutArcFinset S a |>.mp ha).1

end Network

/-! ## Flows and incidence sums -/

namespace Flow

/-- Equality of flows on the active actual arcs of a network's graph. -/
abbrev EqOn {G : DiGraph α β} (N : Network G R) (flow₁ flow₂ : Flow N) : Prop :=
  Set.EqOn flow₁ flow₂ E(G)

/-- Sum a flow over the actual arcs leaving a vertex. -/
noncomputable def outflow {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) (flow : Flow N) (v : α) : R :=
  (G.outIncidenceFinset v).sum flow

/-- Sum a flow over the actual arcs entering a vertex. -/
noncomputable def inflow {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) (flow : Flow N) (v : α) : R :=
  (G.inIncidenceFinset v).sum flow

/-- Net flow leaving the source. -/
noncomputable def flowValue {G : DiGraph α β} [AddCommGroup R] [Finite E(G)]
    (N : Network G R) (flow : Flow N) : R :=
  outflow N flow N.source - inflow N flow N.source

/-- A feasible flow is nonnegative, respects capacity on active arcs, and is conserved at every
internal vertex. -/
def IsFeasible {G : DiGraph α β} [AddCommMonoid R] [PartialOrder R] [Finite E(G)]
    (N : Network G R) (flow : Flow N) : Prop :=
  (∀ a ∈ E(G), 0 ≤ flow a ∧ flow a ≤ N.capacity a) ∧
    ∀ v ∈ V(G), v ≠ N.source → v ≠ N.sink → inflow N flow v = outflow N flow v

/-- Outflow depends only on flow values of active arcs. -/
theorem outflow_congr {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) {flow₁ flow₂ : Flow N} (h : EqOn N flow₁ flow₂) (v : α) :
    outflow N flow₁ v = outflow N flow₂ v := by
  classical
  simp only [outflow]
  apply Finset.sum_congr rfl
  intro a ha
  exact h ((G.mem_outIncidenceFinset v).mp ha).1

/-- Inflow depends only on flow values of active arcs. -/
theorem inflow_congr {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) {flow₁ flow₂ : Flow N} (h : EqOn N flow₁ flow₂) (v : α) :
    inflow N flow₁ v = inflow N flow₂ v := by
  classical
  simp only [inflow]
  apply Finset.sum_congr rfl
  intro a ha
  exact h ((G.mem_inIncidenceFinset v).mp ha).1

/-- Flow value depends only on flow values of active arcs. -/
theorem flowValue_congr {G : DiGraph α β} [AddCommGroup R] [Finite E(G)]
    (N : Network G R) {flow₁ flow₂ : Flow N} (h : EqOn N flow₁ flow₂) :
    flowValue N flow₁ = flowValue N flow₂ := by
  rw [flowValue, flowValue, outflow_congr N h N.source, inflow_congr N h N.source]

@[simp] theorem outflow_zero {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) (v : α) : outflow N (0 : Flow N) v = 0 := by
  simp [outflow]

@[simp] theorem inflow_zero {G : DiGraph α β} [AddCommMonoid R] [Finite E(G)]
    (N : Network G R) (v : α) : inflow N (0 : Flow N) v = 0 := by
  simp [inflow]

@[simp] theorem flowValue_zero {G : DiGraph α β} [AddCommGroup R] [Finite E(G)]
    (N : Network G R) : flowValue N (0 : Flow N) = 0 := by
  simp [flowValue]

/-- The zero flow is feasible when active capacities are nonnegative. -/
theorem zero_isFeasible {G : DiGraph α β} [AddCommMonoid R] [PartialOrder R]
    [Finite E(G)] (N : Network G R) (hcapacity : ∀ a ∈ E(G), 0 ≤ N.capacity a) :
    IsFeasible N (0 : Flow N) := by
  constructor
  · intro a ha
    exact ⟨le_rfl, hcapacity a ha⟩
  · intro v hv hsource hsink
    simp

/-- Feasibility depends only on the values of a flow on active arcs. -/
theorem isFeasible_congr {G : DiGraph α β} [AddCommMonoid R] [PartialOrder R]
    [Finite E(G)] (N : Network G R) {flow₁ flow₂ : Flow N} (h : EqOn N flow₁ flow₂) :
    IsFeasible N flow₁ ↔ IsFeasible N flow₂ := by
  constructor <;> intro hf
  · refine ⟨fun a ha => by simpa [h ha] using hf.1 a ha, ?_⟩
    intro v hv hsource hsink
    rw [← inflow_congr N h v, ← outflow_congr N h v]
    exact hf.2 v hv hsource hsink
  · refine ⟨fun a ha => by simpa [h ha] using hf.1 a ha, ?_⟩
    intro v hv hsource hsink
    rw [inflow_congr N h v, outflow_congr N h v]
    exact hf.2 v hv hsource hsink

/-- Feasibility depends only on active capacity values when source and sink agree. -/
theorem isFeasible_congr_capacity {G : DiGraph α β} [AddCommMonoid R] [PartialOrder R]
    [Finite E(G)] (N₁ N₂ : Network G R) (hsource : N₁.source = N₂.source)
    (hsink : N₁.sink = N₂.sink)
    (hcapacity : DiGraph.Capacity.EqOn G N₁.capacity N₂.capacity)
    (flow : Arc α β → R) : IsFeasible N₁ flow ↔ IsFeasible N₂ flow := by
  constructor <;> intro hf
  · refine ⟨fun a ha => ⟨(hf.1 a ha).1, (hf.1 a ha).2.trans_eq (hcapacity ha)⟩, ?_⟩
    intro v hv hvsource hvsink
    change inflow N₁ flow v = outflow N₁ flow v
    exact hf.2 v hv (fun h => hvsource (h.trans hsource))
      (fun h => hvsink (h.trans hsink))
  · refine ⟨fun a ha => ⟨(hf.1 a ha).1, (hf.1 a ha).2.trans_eq (hcapacity ha).symm⟩, ?_⟩
    intro v hv hvsource hvsink
    change inflow N₂ flow v = outflow N₂ flow v
    exact hf.2 v hv (fun h => hvsource (h.trans hsource.symm))
      (fun h => hvsink (h.trans hsink.symm))

/-- The conservation equation supplied by feasibility at an internal vertex. -/
theorem IsFeasible.conservation {G : DiGraph α β} [AddCommMonoid R] [PartialOrder R]
    [Finite E(G)] {N : Network G R} {flow : Flow N} (h : IsFeasible N flow)
    {v : α} (hv : v ∈ V(G)) (hsource : v ≠ N.source) (hsink : v ≠ N.sink) :
    inflow N flow v = outflow N flow v := h.2 v hv hsource hsink

/-- Transport a flow to a vertex-relabelled network. -/
def transportRelabelVertices {G : DiGraph α β} (N : Network G R) (f : α ≃ γ)
    (flow : Flow N) : Flow (N.relabelVertices f) :=
  DiGraph.EdgeWeight.transportRelabelVertices G f flow

/-- Transport a flow to a tag-relabelled network. -/
def transportRelabelTags {G : DiGraph α β} (N : Network G R) (f : β ≃ δ)
    (flow : Flow N) : Flow (N.relabelTags f) :=
  DiGraph.EdgeWeight.transportRelabelTags G f flow

/-- Transport a flow to the reversed network. -/
def transportReverse {G : DiGraph α β} (N : Network G R) (flow : Flow N) :
    Flow N.reverse := DiGraph.EdgeWeight.transportReverse G flow

@[simp] theorem transportRelabelVertices_apply {G : DiGraph α β} (N : Network G R)
    (f : α ≃ γ) (flow : Flow N) (a : Arc α β) :
    transportRelabelVertices N f flow (Arc.relabelVertices f a) = flow a := by
  simp [transportRelabelVertices]

@[simp] theorem transportRelabelTags_apply {G : DiGraph α β} (N : Network G R)
    (f : β ≃ δ) (flow : Flow N) (a : Arc α β) :
    transportRelabelTags N f flow (Arc.relabelTags f a) = flow a := by
  simp [transportRelabelTags]

@[simp] theorem transportReverse_apply {G : DiGraph α β} (N : Network G R)
    (flow : Flow N) (a : Arc α β) : transportReverse N flow a.reverse = flow a := by
  simp [transportReverse]

@[simp] theorem outflow_transportRelabelVertices {G : DiGraph α β} [AddCommMonoid R]
    [Finite E(G)] (N : Network G R) (f : α ≃ γ) (flow : Flow N) (v : α) :
    outflow (N.relabelVertices f) (transportRelabelVertices N f flow) (f v) =
      outflow N flow v := by
  classical
  symm
  apply Finset.sum_equiv (Arc.relabelVertices f)
  · intro a
    simp [DiGraph.mem_outIncidenceFinset]
  · intro a ha
    simp

@[simp] theorem inflow_transportRelabelVertices {G : DiGraph α β} [AddCommMonoid R]
    [Finite E(G)] (N : Network G R) (f : α ≃ γ) (flow : Flow N) (v : α) :
    inflow (N.relabelVertices f) (transportRelabelVertices N f flow) (f v) =
      inflow N flow v := by
  classical
  symm
  apply Finset.sum_equiv (Arc.relabelVertices f)
  · intro a
    simp [DiGraph.mem_inIncidenceFinset]
  · intro a ha
    simp

@[simp] theorem outflow_transportRelabelTags {G : DiGraph α β} [AddCommMonoid R]
    [Finite E(G)] (N : Network G R) (f : β ≃ δ) (flow : Flow N) (v : α) :
    outflow (N.relabelTags f) (transportRelabelTags N f flow) v = outflow N flow v := by
  classical
  symm
  apply Finset.sum_equiv (Arc.relabelTags f)
  · intro a
    simp [DiGraph.mem_outIncidenceFinset]
  · intro a ha
    simp

@[simp] theorem inflow_transportRelabelTags {G : DiGraph α β} [AddCommMonoid R]
    [Finite E(G)] (N : Network G R) (f : β ≃ δ) (flow : Flow N) (v : α) :
    inflow (N.relabelTags f) (transportRelabelTags N f flow) v = inflow N flow v := by
  classical
  symm
  apply Finset.sum_equiv (Arc.relabelTags f)
  · intro a
    simp [DiGraph.mem_inIncidenceFinset]
  · intro a ha
    simp

@[simp] theorem outflow_transportReverse {G : DiGraph α β} [AddCommMonoid R]
    [Finite E(G)] (N : Network G R) (flow : Flow N) (v : α) :
    outflow N.reverse (transportReverse N flow) v = inflow N flow v := by
  classical
  symm
  apply Finset.sum_equiv Arc.reverseEquiv
  · intro a
    simp only [DiGraph.mem_inIncidenceFinset, DiGraph.mem_outIncidenceFinset,
      Arc.reverseEquiv_apply, DiGraph.mem_edgeSet_reverse, Arc.reverse_reverse,
      Arc.source_reverse]
  · intro a ha
    simp

@[simp] theorem inflow_transportReverse {G : DiGraph α β} [AddCommMonoid R]
    [Finite E(G)] (N : Network G R) (flow : Flow N) (v : α) :
    inflow N.reverse (transportReverse N flow) v = outflow N flow v := by
  classical
  symm
  apply Finset.sum_equiv Arc.reverseEquiv
  · intro a
    simp only [DiGraph.mem_outIncidenceFinset, DiGraph.mem_inIncidenceFinset,
      Arc.reverseEquiv_apply, DiGraph.mem_edgeSet_reverse, Arc.reverse_reverse,
      Arc.target_reverse]
  · intro a ha
    simp

@[simp] theorem flowValue_transportRelabelVertices {G : DiGraph α β} [AddCommGroup R]
    [Finite E(G)] (N : Network G R) (f : α ≃ γ) (flow : Flow N) :
    flowValue (N.relabelVertices f) (transportRelabelVertices N f flow) =
      flowValue N flow := by
  simp [flowValue]

@[simp] theorem flowValue_transportRelabelTags {G : DiGraph α β} [AddCommGroup R]
    [Finite E(G)] (N : Network G R) (f : β ≃ δ) (flow : Flow N) :
    flowValue (N.relabelTags f) (transportRelabelTags N f flow) = flowValue N flow := by
  simp [flowValue]

theorem isFeasible_transportRelabelVertices {G : DiGraph α β} [AddCommMonoid R]
    [PartialOrder R] [Finite E(G)] (N : Network G R) (f : α ≃ γ) (flow : Flow N) :
    IsFeasible (N.relabelVertices f) (transportRelabelVertices N f flow) ↔
      IsFeasible N flow := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a ha
      simpa using hf.1 (Arc.relabelVertices f a)
        ((G.mem_edgeSet_relabelVertices f a).2 ha)
    · intro v hv hsource hsink
      have hsource' : f v ≠ (N.relabelVertices f).source := by simpa using hsource
      have hsink' : f v ≠ (N.relabelVertices f).sink := by simpa using hsink
      simpa using hf.2 (f v) ⟨v, hv, rfl⟩ hsource' hsink'
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a ha
      change a ∈ Arc.relabelVertices f '' E(G) at ha
      obtain ⟨b, hb, rfl⟩ := ha
      simpa using hf.1 b hb
    · intro v hv hsource hsink
      obtain ⟨u, hu, rfl⟩ := hv
      have hsource' : u ≠ N.source := by simpa using hsource
      have hsink' : u ≠ N.sink := by simpa using hsink
      simpa using hf.2 u hu hsource' hsink'

theorem isFeasible_transportRelabelTags {G : DiGraph α β} [AddCommMonoid R]
    [PartialOrder R] [Finite E(G)] (N : Network G R) (f : β ≃ δ) (flow : Flow N) :
    IsFeasible (N.relabelTags f) (transportRelabelTags N f flow) ↔
      IsFeasible N flow := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a ha
      simpa using hf.1 (Arc.relabelTags f a) ((G.mem_edgeSet_relabelTags f a).2 ha)
    · intro v hv hsource hsink
      simpa using hf.2 v (by simpa using hv) (by simpa using hsource) (by simpa using hsink)
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a ha
      change a ∈ Arc.relabelTags f '' E(G) at ha
      obtain ⟨b, hb, rfl⟩ := ha
      simpa using hf.1 b hb
    · intro v hv hsource hsink
      simpa using hf.2 v hv (by simpa using hsource) (by simpa using hsink)

theorem isFeasible_transportReverse {G : DiGraph α β} [AddCommMonoid R]
    [PartialOrder R] [Finite E(G)] (N : Network G R) (flow : Flow N) :
    IsFeasible N.reverse (transportReverse N flow) ↔ IsFeasible N flow := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a ha
      simpa using hf.1 a.reverse
        ((G.mem_edgeSet_reverse a.reverse).2 (by simpa using ha))
    · intro v hv hsource hsink
      have htarget := hf.2 v (by simpa using hv) (by simpa using hsink)
        (by simpa using hsource)
      simpa using htarget.symm
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a ha
      have ha' : a.reverse ∈ E(G) := (G.mem_edgeSet_reverse a).1 ha
      simpa using hf.1 a.reverse ha'
    · intro v hv hsource hsink
      have hsource' : v ≠ N.source := by simpa using hsink
      have hsink' : v ≠ N.sink := by simpa using hsource
      simpa using (hf.2 v (by simpa using hv) hsource' hsink').symm

end Flow

end DiGraph

end GraphLib
