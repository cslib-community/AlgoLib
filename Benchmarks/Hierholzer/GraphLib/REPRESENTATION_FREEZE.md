# GraphLib Hierholzer representation freeze

Status: executable schema frozen before the timed algorithm core. The independent review later
corrected only the logical footprint constant described below; no executable field, law, access,
or storage-to-counter mapping changed.

## Executable schema

- `Dart m = Fin m × Bool`: a dense full-edge ID and a distinct endpoint role.
- `IncidenceEnumeration n m.endpoints`: an array-backed `Vector` of length `m`; every entry
  stores two dense vertex IDs.
- `IncidenceEnumeration n m.buckets`: an array-backed `Vector` of length `n`; every entry stores
  an incidence `Array (Dart m)`.
- `CertifiedIncidenceRepresentation G.n` and `.m`: the two supplied dense sizes.
- Dense decoding equivalences and every `Represents` field are logical certification data and are
  excluded from executable word accounting under the protocol.

There is no cached tour, successor schedule, reachability/parity certificate, start-dependent
field, used flag, cursor, or algorithm state in the representation. Bucket order is unconstrained.

## Frozen laws

1. Every stored endpoint pair links the corresponding decoded full bundled GraphLib edge.
2. Every bucket is duplicate-free.
3. A dart occurs in a vertex bucket exactly when its Boolean role selects that vertex from the
   stored endpoint pair.
4. `n = Set.ncard V(G)` and `m = Set.ncard E(G)`.

These laws give exactly two globally distinct darts `(e,false)` and `(e,true)` for every edge.
For a loop they occur in the same bucket. Every vertex bucket exists, including isolated empty
buckets. Full `ActualEdge G` values—not tags—are in bijection with `Fin m`.

## Primitive storage-to-counter map

| Executable access | Frozen event charge |
| --- | --- |
| Outer bucket-vector pointer read | one `incidenceRead` |
| Inner bucket length/header read (cached for one scan call) | one `incidenceRead` |
| Dart edge-ID read | one `incidenceRead` |
| Dart role read | one `incidenceRead` |
| Stored first endpoint-ID read | one `endpointRead` |
| Stored second endpoint-ID read | one `endpointRead` |

All used-edge flags, cursors, stack frames, output buffers, and their charges are algorithm-owned,
not representation fields. Their categories are already fixed by Common and cannot change this
schema.

## Logical representation footprint

The two dense sizes cost two words. Each of the two top-level array-valued structure fields costs
one structure pointer plus one container header, for four further words. Endpoint entries cost
`2m`. Each vertex costs one outer pointer plus one inner-array header (`2n`). Every dart costs two
words (`2I`). Thus:

```text
repWords R = 6 + 2*n + 2*m + 2*I
r0 = 6, rV = 2, rE = 2, rI = 2
```

The pre-core record originally counted the two top-level container headers but omitted their two
structure-field pointers, despite counting the analogous outer pointers for inner bucket arrays.
Reviewer A classified that inconsistency as a representation-accounting defect. The one allowed
repair round changed `4` to `6` and updated this record/manifest. The schema and timed interface
remain exactly the pre-core ones.

Persistent-array reads are modeled constant-time under the frozen abstract RAM. The later core may
use linearly threaded persistent-array writes only under the separately reported unit-write RAM
assumption.

## Pre-core compilation

Before any timed algorithm source was created:

```text
lake env lean Benchmarks/Hierholzer/GraphLib/Adapter.lean       PASS
lake env lean Benchmarks/Hierholzer/GraphLib/Representation.lean PASS
```

No representation attempt was abandoned before this freeze.
