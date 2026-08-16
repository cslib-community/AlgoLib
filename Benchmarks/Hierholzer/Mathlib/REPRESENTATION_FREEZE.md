# Mathlib-side representation freeze

Freeze date: 2026-08-16. This record predates the timed Hierholzer core.

## Frozen schema

`CertifiedIncidenceRepresentation G` stores:

- `n`, `m`: dense vertex and actual-edge cardinalities;
- `decodeVertex : Fin n ≃ Vertex G` and `decodeEdge : Fin m ≃ Edge G` (erased semantic
  equivalences, not executable hot state);
- `ends : Vector (Fin n × Fin n) m`, an array-backed two-word endpoint record per edge;
- `buckets : Vector (Array (Dart m)) n`, an array-backed vertex table whose entries point to
  incidence arrays;
- endpoint soundness, bucket `Nodup`, and exact canonical bucket-membership laws (erased proofs).

`Dart m` has exactly two logical words: an actual dense edge ID and a Boolean endpoint role.
Role `false` belongs to endpoint 0 and role `true` to endpoint 1. If both endpoint IDs are equal,
the two distinct dart roles occur in the same bucket. There is one used flag per edge ID, never per
dart.

The laws constrain bucket contents but not their order. No start vertex, parity/reachability
certificate, used-edge order, successor schedule, splice schedule, or tour advice is stored.

## Storage-to-counter mapping

- Accessing an outer bucket slot/pointer: one `incidenceRead`.
- Reading a selected bucket's stored length: one `incidenceRead`.
- Reading a dart's edge ID and role: two `incidenceRead` events.
- Reading an edge's two endpoint IDs: two `endpointRead` events.
- Reading `n`/`m`, record projections, and proof fields: zero administrative cost under the frozen
  table.
- Mathematical decode equivalences are proof/decoding data and are not used by the timed core.
- Algorithm-owned used flags, cursors, stack frames, and output are not representation fields and
  use the corresponding frozen Common counters.

The primary implementation assumes constant-time dense `Vector`/`Array` get and linearly threaded
`Vector.set` under the frozen abstract RAM model. The report will state that persistent physical
copying is not verified by this abstraction.

## Footprint accounting

With `I` the sum of all inner incidence-array lengths, the logical representation footprint is

```text
repWords R = 5 + 2*n + 2*m + 2*I
```

The five constant words cover the representation header, the two stored sizes, and the two outer
array headers. The `2*n` term covers one outer bucket slot and one inner-array header per vertex.
Every endpoint pair contributes two words, and every dart contributes two words. Decode
equivalences and proofs are erased. Thus the frozen constants are
`r0 = 5`, `rV = 2`, `rE = 2`, `rI = 2`.

## Construction status at freeze

`representation_exists` is already compiled. Its `RepresentationConstruction.build` chooses
dense equivalences and endpoints noncomputably, then materializes exact filtered incidence
buckets. This construction is outside the primary clock and is not claimed to be executable
preprocessing.

## Content hashes

```text
799a74de2530156dfc47d3e8531a69494182caedaa872aa47a51a9c00f23843a  Benchmarks/Hierholzer/Mathlib/Representation.lean
67f137cd2e691dbe36b3f0b38fab0009f3eaf1e41fd5a3da2350010e2b58bee7  Benchmarks/Hierholzer/Mathlib/Adapter.lean
```

Validation command:

```sh
shasum -a 256 -c Benchmarks/Hierholzer/Mathlib/REPRESENTATION_MANIFEST.sha256
```

No executable representation field or primitive-operation category may be added after this point.
