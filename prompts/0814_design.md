We are revisiting one major architectural decision from the existing GraphLib architecture report: the representation of general undirected and directed graphs.

## Context

GraphLib currently uses bundled edge objects roughly of the following form:

```lean
structure Edge (α β : Type*) where
  endpointsLabel : β
  endpoints : Sym2 α

structure Arc (α β : Type*) where
  endpointsLabel : β
  endpoints : α × α

structure Graph (α β : Type*) where
  vertexSet : Set α
  edgeSet : Set (Edge α β)
  incidence' : ...

structure DiGraph (α β : Type*) where
  vertexSet : Set α
  edgeSet : Set (Arc α β)
  incidence' : ...
```

The previous architecture report Reports/2026-08-14_GRAPHLIB_ARCHITECTURE_PROPOSAL.md proposed replacing this with a Mathlib-like representation in which the edge type itself is an abstract edge identity `ε`, and incidence/endpoints are stored relationally through `IsLink` / `IsArc`.

I am **not yet convinced that this breaking change is desirable**.

My current preference is to preserve the existing GraphLib representation if possible. In particular, bundled edges/arcs have the ergonomic advantage that an edge object directly carries its endpoints.

However, the previous report raised a legitimate concern: under noninjective vertex transformations such as future contraction, two distinct bundled edge values may map to the same edge value. More generally, we need to understand whether bundled endpoints create unnecessary transport or identity problems for weights, capacities, relabeling, reverse graphs, residual graphs, walks, etc.

## Scope

Your task is to investigate this representation question deeply and produce a decision memo. Output it as a new markdown file in Reports folder.

**Do not implement contraction in GraphLib in this task.**
Contraction is explicitly out of scope for the current construction project.

However, future contraction should be used as a **stress test** of the representation. Prefer solving future contraction-specific problems on the contraction side if that yields a clean design; do not redesign the entire general graph representation merely to make a currently out-of-scope contraction API elegant unless there is a strong reason.

Do not modify the public GraphLib architecture yet. Small throwaway Lean prototypes/tests are encouraged if they help compare alternatives.

## Questions to answer

Compare at least:

1. The current bundled `Edge α β` / `Arc α β` representation.
2. A Mathlib-like design with a separate edge identity type `ε` and `IsLink` / `IsArc`.
3. Any minimal modification of the current bundled representation that resolves genuine problems without replacing it wholesale.
4. If useful, other representations found in relevant formal libraries or graph libraries.

Pay special attention to:

* parallel edges and loops;
* what exactly counts as edge identity;
* whether labels need any uniqueness invariant;
* `E(G)` and whether it denotes actual edges or endpoint pairs;
* deletion of one particular parallel edge;
* edge weights, costs, and capacities;
* vertex relabeling;
* edge relabeling;
* directed graph reversal;
* graph-independent general walks carrying edge information;
* induced subgraphs and edge restrictions;
* MST-style clients;
* flow and residual-network clients, especially coexistence of original, reverse residual, and antiparallel arcs;
* dynamic graph updates;
* future contraction / noninjective vertex maps, including possible edge collisions.

A likely issue in the current code is that the public notation `E(G)` may expose endpoint images rather than actual bundled edge objects. Treat this separately from the question of whether the underlying bundled representation itself is wrong.

## Required empirical tests

For the serious candidate designs, write small Lean prototypes or usage sketches exercising representative operations. We care about proof ergonomics, not only mathematical equivalence.

At minimum test:

* two parallel edges can be distinguished and one deleted;
* two edges with different original endpoints remain distinguishable under a hypothetical noninjective endpoint map, or explain how the transformation layer should preserve them;
* attaching a weight/capacity to an edge and transporting it through vertex relabeling;
* reversing a directed graph and a realized directed walk;
* representing residual arcs without identity collisions;
* taking an induced subgraph without introducing pervasive casts;
* constructing or realizing an edge-aware walk.

Report concrete friction: casts, transports, extra proof obligations, awkward extensionality, hidden invariants, or definitional-equality wins.

## Survey requirements

Inspect:

* the current GraphLib source and its real downstream clients;
* the Mathlib version pinned by this project;
* current Mathlib where relevant;
* relevant experimental Mathlib graph designs if they illuminate the tradeoff;
* other formal graph representations only when they provide genuinely useful evidence.

Distinguish clearly between stable upstream APIs and experimental proposals.

Do not argue “Mathlib does X, therefore we should do X.” Explain why each design property helps or hurts GraphLib's TCS-oriented clients.

## Four-subagent split

Use four subagents:

1. **Local architecture auditor**: inspect current GraphLib and downstream usage; identify proven ergonomic wins and actual pain points of the bundled representation.
2. **External surveyor**: inspect Mathlib and other relevant formal representations; extract design motivations and stable precedents.
3. **Prototype/stress-test engineer**: implement isolated Lean experiments comparing candidate representations on the scenarios above.
4. **Adversarial TCS reviewer**: attack each proposal from MST, flow/residual-network, multigraph walk, deletion, dynamic-update, and future-contraction use cases.

The parent agent must synthesize the evidence itself. Do not simply defer to one subagent's recommendation.

## Decision criteria

Evaluate each candidate on:

* mathematical correctness of edge identity semantics;
* Lean proof ergonomics;
* API simplicity;
* amount of transport/casting;
* compatibility with graph-independent walk data;
* suitability for TCS algorithms;
* future extensibility;
* migration cost;
* Mathlib interoperability;
* risk of premature abstraction.

## Output

Produce a self-contained representation decision memo containing:

1. current-state diagnosis;
2. survey findings;
3. prototype/test results;
4. comparison table of candidate designs;
5. concrete failure modes of each design;
6. recommended representation;
7. the **minimal changes** required from current GraphLib if the recommendation differs from it;
8. decisions marked as:

   * `LOCKED`
   * `PROVISIONAL`
   * `DEFERRED`
9. a short list of consequences that the later naming/API plan must respect.

Prefer preserving the existing GraphLib design when two designs are comparably good. Recommend a breaking representation change only if the evidence shows a meaningful long-term advantage that cannot reasonably be localized to later transformation APIs.

Do not produce the full GraphLib construction plan yet.
