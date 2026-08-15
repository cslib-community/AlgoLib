# Representation stress-test results

This is the empirical log for the prototype-engineer portion of
`prompts/0814_design.md`. The code is isolated in
`Prototypes/RepresentationStress.lean`; nothing under `GraphLib/` was changed.

## Build record

The pinned Mathlib graph modules were present as sources but were not initially built as
`.olean` files. I therefore ran:

```text
$ lake build Mathlib.Combinatorics.Graph.Delete Mathlib.Combinatorics.Graph.Maps
✔ [687/690] Built Mathlib.Combinatorics.Graph.Basic (3.8s)
✔ [688/690] Built Mathlib.Combinatorics.Graph.Subgraph (1.4s)
✔ [689/690] Built Mathlib.Combinatorics.Graph.Maps (1.2s)
✔ [690/690] Built Mathlib.Combinatorics.Graph.Delete (1.3s)
Build completed successfully (690 jobs).
```

Final prototype check:

```text
$ lake env lean Prototypes/RepresentationStress.lean
# exit code 0; no warnings or errors
```

## What was tested

| Test | Current bundles | Separate identity | Minimal bundle-preserving repair |
|---|---|---|---|
| Distinguish/delete parallel edges | `Edge Nat Bool` values differ by label; deleting `parallel₀` keeps `parallel₁` | Pinned Mathlib `Graph Nat Bool` keeps `false` and `true` as parallel edge identities and deletes just `false` | Uses the current behavior |
| Noninjective vertex map | Two legal same-label edges/arcs with different endpoints become equal under a constant endpoint map | `ε = Bool` is definitionally unchanged while both endpoint pairs collapse | Output label is the entire source arc; proved the map injective for arbitrary vertex functions |
| Weight/capacity | Definitional only when weight is a function of the preserved label; an arbitrary arc weight transports through a vertex equivalence by composing with the inverse arc relabeling | `capacity : ε → Nat` is literally unchanged under `mapV` | Arbitrary `Arc α β → κ` transports by projecting the origin label, definitionally |
| Reverse digraph/walk | Reverse maps every arc value and the walk needs `mapE reverseArc` followed by `reverse` | Reverse only swaps graph-relative source/target; the edge-aware walk only needs `reverse` | Ordinary reversal can retain current bundle API; origin tagging is only needed for noninjective transformations |
| Residual/original/antiparallel coexistence | `ResidualId.forward`/`.reverse` in the label makes all three bundled arcs unequal | The same sum/tag is the abstract residual edge carrier | Uses the same tagged-label technique; no graph representation change needed |
| Induced graph | Existing `DiGraph.induce` retains the ambient vertex type and exact bundled arcs; no casts | Prototype retains ambient vertex/edge types and exact `ε`; no casts | Inherits current induced-graph win |
| Edge-aware walk | Existing `Walk α (Arc α β)` stores the exact arc and realizes it by bundled endpoints | `Walk α ε` stores identity; realization additionally consults `G.IsArc` | Inherits current walk shape; mapped walks store origin-tagged bundled arcs |

## Concrete friction observed

### Current bundled representation

* The collision is real, but narrower than “bundles cannot support contraction”: it requires a
  noninjective endpoint map plus equal labels. `Edge`/`Arc` permit equal labels on distinct
  endpoint pairs because there is no uniqueness invariant. Consequently, a generic raw
  `mapEdge` or `mapArc` is not injective.
* `E(G)` is a separate public API defect. The compiled test deletes one actual parallel edge
  from `G.edgeSet`, yet the deleted edge's endpoint pair remains a member of `E(G)` because
  another parallel edge realizes the same pair. Thus `E(G)` cannot express deletion of one
  parallel edge even though `G.edgeSet` can.
* Endpoint access and induced subgraphs were very direct. The only obligations for `induce`
  were ordinary set-membership goals; there were no subtype equality transports or casts.
* A bijective vertex relabeling transported an arbitrary `Arc α β → κ` weight by applying the
  inverse equivalence to both endpoints. The round-trip proof simplified using the equivalence
  laws; it needed no `Eq.rec`/cast, but the transported function was not literally the old one.
* Directed reversal makes the bundled edge value change. A realized reversed walk required
  both edge mapping and walk reversal. In the concrete proof, simplification did not unfold the
  one-step `Walk.reverse` far enough, so an explicit `change` to its normal form was needed.
* Residual collision is solved cleanly by putting direction/provenance in the label type.
  This solution is necessary even with abstract edge identities: reverse residual copies must
  still receive identities distinct from originals.

### Separate `ε` plus graph-relative incidence

* In pinned Mathlib's stable undirected `Graph`, `Graph.map` keeps `edgeSet : Set ε`
  definitionally equal. This is the strongest result for noninjective maps and arbitrary
  edge-keyed weights: there is no transport at all.
* Directed tests used a deliberately small function-backed `IsArc` model (`source` and `target`
  stored graph-side, with `IsArc` derived). It demonstrates identity and client ergonomics, but
  is not evidence that a full relational `IsArc` structure is obligation-free. The pinned
  Mathlib `Graph` structure itself requires symmetry, endpoint-pair uniqueness, edge-existence,
  and incidence fields; those are extra constructor/extensionality obligations avoided by the
  function-backed sketch.
* Edge-aware walk data becomes maximally graph-independent (`Walk α ε`), but realization must
  consult graph-relative incidence at every step. Reversal was cleaner than with bundles:
  reverse the relation/source-target fields and reverse the walk, leaving every `ε` untouched.
* Inducing on a `Set α` while keeping ambient `α` and `ε` had the same no-cast win as GraphLib's
  current representation. Separate identities do not uniquely cause that win; embedded sets do.

### Origin-tagged noninjective transformation

* `mapArcKeepOrigin f : Arc α β → Arc γ (Arc α β)` is injective for every `f`, with a one-line
  proof by applying the `endpointsLabel` projection. It preserves different original edges even
  when all endpoints collapse.
* Any old weight/capacity `w : Arc α β → κ` transports by `w e.endpointsLabel`, and the expected
  computation theorem is `rfl`. This directly addresses the future-contraction stress test on
  the transformation side without changing `GraphLib.Arc`.
* The cost is visible in the type. Naively applying the construction twice gives
  `Arc δ (Arc γ (Arc α β))`: origin labels nest. A production transformation API would want a
  named provenance wrapper, an explicit origin projection, or a composition law that keeps the
  original identity flat.
* This prototype therefore supports a narrow conclusion: the noninjective-map collision does
  not by itself force a global representation migration. It can be localized, but the local API
  must expose provenance intentionally.

## Prototype-engineer conclusion

The tests do not reveal a correctness failure in bundled edges for current construction work.
They do reveal two concrete issues: `E(G)` currently erases real edge identity, and a naive
same-label endpoint map is unsafe for noninjective transformations. The first should be fixed
independently of representation. The second can be handled by a provenance-preserving
transformation result (origin-tagged labels) until repeated transformation composition or broad
Mathlib interoperability provides evidence that a separate global `ε` is worth the migration.

The separate-identity design is technically cleanest for arbitrary vertex maps, weights, and
directed reversal. Its advantage is meaningful, but in these experiments the current embedded
set design matched it on deletion, induced subgraphs, residual tags, and edge-aware walks, while
retaining direct endpoint projection.
