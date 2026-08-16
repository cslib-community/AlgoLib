# Hierholzer Common freeze report

## 1. Protocol and scope

The single source of truth was:

```text
HIERHOLZER_BENCHMARK_PROTOCOL.md
SHA-256: 32633e8f9e39c9c197a7ad1a1b7964d3cb75ba386df5b1a3262b39965fd1a79b
```

This freeze contains only graph-foundation-neutral infrastructure. It does not contain a
Hierholzer implementation, a graph representation, incidence construction, endpoint extraction,
degree/connectivity theory, or any GraphLib/Mathlib graph adapter.

## 2. Repository state

- Repository `HEAD`: `3a842eeb02c32af5ba6e45ba1a5ced7e9778bcfa`
- Parent: `d4dbdf45b2420750e55eb7caf529265a2bfff11f`, the repository commit recorded by the protocol
- Commit subject: `Strengthen GraphLib foundation and freeze Hierholzer benchmark`
- Commit date: `2026-08-16T16:36:41+02:00`
- Tracked working-tree diff before and after this task: empty
- Initial untracked path: `prompts/0816_common`
- Task output: the new untracked `Benchmarks/Hierholzer/Common.lean` and
  `Benchmarks/Hierholzer/Common/` tree

The newer `HEAD` is the protocol's documented committed-snapshot case: it is the immediate child of
the recorded commit. This Common task did not inspect the forbidden GraphLib source tree and
therefore did not recompute its separately frozen source manifest.

## 3. Toolchain and pinned dependencies

- Lean: `4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- Platform reported by Lean: `arm64-apple-darwin24.6.0`
- Lake: `5.0.0-src+3dc1a08`
- CSLib commit: `608cbe1b629a276abd3f2081f9b42dc766d8fd78` (clean)
- Mathlib commit: `d802ffd29db1f5dc5a29206b1a8af62bfcc234a3` (clean)
- `TimeM.lean` SHA-256:
  `b58d42bb8ba3345c5ab52701f8f4d77dae557b096b79d326ccda4fa4ffd3dcf6`
- CSLib MergeSort SHA-256:
  `3cfa73d2da202625935d3a15391cf548d1466b8b2b231443dcbee38f60e9a72a`

Both dependency hashes exactly match the frozen protocol.

## 4. Final Common tree

```text
Benchmarks/Hierholzer/Common.lean
Benchmarks/Hierholzer/Common/
  COMMON_FREEZE_REPORT.md
  COMMON_MANIFEST.sha256
  Cost.lean
  Tests.lean
  Tour.lean
```

The four Lean files total 827 physical lines. The Markdown report and SHA-256 manifest are not Lean
source and are not executable/helper code copied into a timed call graph.

## 5. Design decisions

- `Cost` is the exact fourteen-field record in protocol order. Zero and addition are componentwise,
  and `Cost.total` gives every component unit weight.
- Primitive wrappers preserve an arbitrary returned value. Index operations are restricted to
  `Nat` bounded-word values, preventing this API from advertising ambient mathematical equality as
  a unit-cost operation.
- Stack helpers take an explicit logical payload-word count and recursively compose unit read/write
  events. Canonical output helpers have fixed two-word prices. No composite injects a hand-built
  aggregate cost.
- `IndexedTour.decode` accepts only vertex/edge equivalences and is exactly pointwise relabeling.
  It is a semantic view; executable materialization of its lists is not free.
- `ValidEulerTour` is graph-neutral. Its positional clause uses `List.Forall₂` against
  `vertices.zip vertices.tail`; with the length clause this is exactly one consecutive vertex pair
  per edge position.
- No speculative dense-ID record, Array/List algorithms layer, or representation/state helper was
  added. Existing `Equiv` is the dense-ID interface.

## 6. Frozen storage-to-counter codebook

| Operation or logical storage class | Counter |
| --- | --- |
| Initialize one algorithm-owned word | `initWrite` |
| Read one incidence or offset word | `incidenceRead` |
| Read one endpoint-ID word | `endpointRead` |
| Read/write one used-edge flag | `usedRead` / `usedWrite` |
| Read/write one cursor | `cursorRead` / `cursorWrite` |
| Compare, increment, or add bounded-word indices | `indexOp` |
| Request stack empty/top check, push, peek, or pop | `stackControl` |
| Read/write one stack payload word | `stackRead` / `stackWrite` |
| Emit or visit one output step | `outputControl` |
| Read/write one output payload word | `outputRead` / `outputWrite` |

A separately stored incidence edge ID and role use two incidence reads; an endpoint pair uses two
endpoint reads. Each distinct stack action receives a control event. A canonical output emission is
one control plus two writes; visit/copy is one control, two reads, and two writes; storing the result
start ID is one output write. Administrative operations and proof-only decoding cost zero.

## 7. Public declaration inventory

All product declarations are under `Benchmarks.Hierholzer.Common`; event declarations are under
`.Event`, and decoder declarations are under `.IndexedTour`. Generated constructor, recursor,
projection, extensionality, and derived-instance declarations are grouped with their carrier.

### Frozen protocol objects

- `Cost`, its constructor, fourteen field projections, extensionality theorem, and derived
  `DecidableEq`/`Repr`
- `Cost.total`
- `TourData`, its constructor/projections, and derived `DecidableEq`/`Repr`
- `IndexedTour`, its constructor/projections, and derived `DecidableEq`/`Repr`
- `IndexedTour.decode`
- `ValidEulerTour`, its constructor/recursor and the six projections `length_eq`, `head_eq`,
  `last_eq`, `links`, `edges_nodup`, and `edges_complete`

### Cost algebra and primitive support

- Instances `costZero`, `costAdd`, and the componentwise `AddCommMonoid Cost`
- For every frozen field
  `initWrite`, `incidenceRead`, `endpointRead`, `usedRead`, `usedWrite`, `cursorRead`,
  `cursorWrite`, `indexOp`, `stackControl`, `stackRead`, `stackWrite`, `outputControl`,
  `outputRead`, `outputWrite`: the projection lemmas `zero_<field>` and `add_<field>`
- `Cost.total_zero`, `Cost.total_add`

### Cost primitives and accounting lemmas

For each name below, the public API contains the wrapper itself plus `ret_<name>`, `time_<name>`,
and `total_time_<name>`:

- Unit fields: `initWrite`, `incidenceRead`, `endpointRead`, `usedRead`, `usedWrite`, `cursorRead`,
  `cursorWrite`, `stackControl`, `stackRead`, `stackWrite`, `outputControl`, `outputRead`,
  `outputWrite`
- The only index specializations: `indexEq`, `indexLt`, `indexSucc`, `indexAdd`
- Frozen composites: `stackCheck`, `stackPush`, `stackPeek`, `stackPop`, `outputStoreStart`,
  `outputEmitStep`, `outputCopyStep`

There is no public `indexOp` wrapper, `charge`, `tickN`, cost basis constant, or arbitrary-cost
function.

### Generic tour semantics

- `IndexedTour.decode_vertices`, `decode_edges`, `decode_vertices_length`,
  `decode_edges_length`, `decode_vertices_head?`
- The `ValidEulerTour` carrier and its six semantic projections listed above

### Generic dense-ID helpers

- `IndexedTour.decode_edges_nodup_iff`
- `IndexedTour.decode_edges_complete_iff`

### Generic data-structure helpers

None. The implementation uses existing generic List and Equiv declarations instead of freezing a
new helper library.

`Tests.lean` contains only anonymous graph-free `example` checks and introduces no named benchmark
API.

## 8. Build commands and results

The pinned dependency was built with:

```sh
lake build Cslib.Algorithms.Lean.TimeM
```

Result: success, 458 jobs complete.

Every source also passed direct elaboration:

```sh
lake env lean Benchmarks/Hierholzer/Common/Cost.lean
lake env lean Benchmarks/Hierholzer/Common/Tour.lean
lake env lean Benchmarks/Hierholzer/Common/Tests.lean
lake env lean Benchmarks/Hierholzer/Common.lean
```

Final clean-artifact compilation used a temporary Common object root first on `LEAN_PATH` and
removed the repository object root from the dependency path:

```sh
set -eu
COMMON_BUILD_DIR=$(mktemp -d /private/tmp/hierholzer-common-final.XXXXXX)
COMMON_BASE_PATH=$(lake env printenv LEAN_PATH)
COMMON_ROOT_BUILD="$(pwd)/.lake/build/lib/lean"
COMMON_DEP_PATH=${COMMON_BASE_PATH//$COMMON_ROOT_BUILD:/}
COMMON_ISOLATED_PATH="$COMMON_BUILD_DIR:$COMMON_DEP_PATH"
COMMON_LEAN_BIN=$(lake env which lean)
mkdir -p "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common"
LEAN_PATH="$COMMON_ISOLATED_PATH" "$COMMON_LEAN_BIN" \
  -o "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common/Cost.olean" \
  -i "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common/Cost.ilean" \
  Benchmarks/Hierholzer/Common/Cost.lean
LEAN_PATH="$COMMON_ISOLATED_PATH" "$COMMON_LEAN_BIN" \
  -o "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common/Tour.olean" \
  -i "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common/Tour.ilean" \
  Benchmarks/Hierholzer/Common/Tour.lean
LEAN_PATH="$COMMON_ISOLATED_PATH" "$COMMON_LEAN_BIN" \
  -o "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common.olean" \
  -i "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common.ilean" \
  Benchmarks/Hierholzer/Common.lean
LEAN_PATH="$COMMON_ISOLATED_PATH" "$COMMON_LEAN_BIN" \
  -o "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common/Tests.olean" \
  -i "$COMMON_BUILD_DIR/Benchmarks/Hierholzer/Common/Tests.ilean" \
  Benchmarks/Hierholzer/Common/Tests.lean
```

Result: all four artifacts compiled successfully in protocol order. The final isolated build root
was `/private/tmp/hierholzer-common-final.bNHYDa`.

The root `lakefile.toml` has no `Benchmarks` Lean library, so `lake build` does not recognize these
modules as Lake targets. The explicit `lake env lean` compilation above is the build evidence; the
project configuration was deliberately not modified outside Common.

## 9. Tests

`Tests.lean` checks:

- zero cost, all fourteen primitive basis components, `Cost.total`, and bind addition;
- all four index results and their exact `indexOp` vectors;
- exact check/push/peek/pop and start/emit/copy component vectors and scalar totals;
- decoded start/destination order, edge order, lengths, and absence of reversal;
- zero-edge and one-edge abstract valid tours;
- an order-sensitive two-step link relation and a reordered-edge rejection;
- duplicate-edge rejection and missing-edge rejection.

All checks elaborate without graph imports.

## 10. Neutrality and dependency audit

Direct imports are exactly:

```text
Cslib.Algorithms.Lean.TimeM
Mathlib.Data.List.Forall2
Mathlib.Data.List.Nodup
Mathlib.Logic.Equiv.Defs
```

The umbrella imports only `Common.Cost` and `Common.Tour`, not tests. `lean --src-deps` reports the
only local umbrella dependencies as `Cost.lean` and `Tour.lean`. Searches found no GraphLib import,
Mathlib graph/SimpleGraph import, graph-specific public reference, graph representation, endpoint,
degree/connectivity, or algorithm declaration. The only capitalized word `Graph` found by a broad
text scan is in the test-module comment “Graph-free”.

No existing GraphLib, Mathlib, CSLib, foundation, project-configuration, or other tracked source
file was modified.

## 11. Raw-tick and arbitrary-cost audit

- Exactly 17 executable `TimeM.tick` calls occur, all in `Cost.lean`: thirteen non-index unit-field
  wrappers and the four frozen index specializations.
- No raw tick occurs in Tour, Tests, the umbrella, or any stack/output composite.
- No `✓`, `TimeM.mk`, explicit `{ ret := ..., time := ... }`, public generic charge, public
  `indexOp`, or aggregate-cost tick exists.
- Stack/output composites call unit wrappers recursively or in a fixed literal sequence.

Because `TimeM` is publicly imported and the public return type is literally `TimeM Cost α`, Lean's
module system cannot make `TimeM.tick` inaccessible to later code. Raw-tick containment is a closed
benchmark convention enforced by the mandatory source audit, not a capability guarantee.

## 12. `sorry`, unsafe code, and axioms audit

Searches found no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, or `noncomputable` declaration
in Common. There is no unexpected classical choice dependency.

Selected `#print axioms` results were identical:

```text
Cost.total_add                              [propext, Quot.sound]
Event.time_stackPush                       [propext, Quot.sound]
IndexedTour.decode_edges_nodup_iff          [propext, Quot.sound]
IndexedTour.decode_edges_complete_iff       [propext, Quot.sound]
```

These are standard imported/kernel axioms; no Common-specific axiom was introduced.

## 13. Hygiene and review audit

- `git diff --check`: pass
- Explicit trailing-whitespace scan over every delivered source/manifest: pass
- Cost field shape was independently checked with `#print Cost`: exactly fourteen `Nat` fields in
  protocol order
- Manifest path completeness and lexical ordering: pass
- Two mandated review rounds were completed by all four reviewers

Round 1 found no blocking defect. Accepted should-fixes added the full storage codebook, exact index
and composite vector tests, semantic-decoder runtime wording, and an order-sensitive link test.
Round 2 reported no blocking or should-fix finding from any reviewer. The independent build/freeze
reviewer classified the final source as freeze-ready.

## 14. Manifest generation and validation

Canonical regeneration command:

```sh
{ find Benchmarks/Hierholzer/Common -type f -name '*.lean' -print
  find Benchmarks/Hierholzer -maxdepth 1 -type f -name 'Common.lean' -print
} | LC_ALL=C sort | xargs shasum -a 256 \
  > Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256
```

Validation commands:

```sh
shasum -a 256 -c Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256
awk '{print $2}' Benchmarks/Hierholzer/Common/COMMON_MANIFEST.sha256 | LC_ALL=C sort -c
```

Both passed. A two-way path-set comparison between the discovered Lean files and manifest entries
was empty.

Manifest contents:

```text
e42aade197c6f943008e3f5b472852bc8785bd1bce1acd8fa916a35b41145b62  Benchmarks/Hierholzer/Common.lean
1b47b6f6fef0838f6861eb8eaf63f98af118a21312572fe7c28c8e59a6a5a412  Benchmarks/Hierholzer/Common/Cost.lean
3439ac544ec1d0d79f3f2da57035366c81197a84d9766fdf77575d05c330786a  Benchmarks/Hierholzer/Common/Tests.lean
ad0e365cbe32885a5a62eb0c1d04df05527ef55f57f6531ee24a3a5c4623dc6c  Benchmarks/Hierholzer/Common/Tour.lean
```

Manifest file SHA-256:

```text
624489ddf4f8b69e31c434fdef1bab44a6447ace777670f9b62fae54020f1910
```

The manifest does not include itself or this report. There are no additional non-Lean executable or
helper files to freeze.

## 15. Known limitations

- `TimeM` remains a manually trusted event ledger; ticks are not derived from Lean evaluator steps.
- Raw `TimeM.tick` remains technically accessible through the imported module and must be prohibited
  by later source audits.
- The root Lake configuration has no Benchmark target, so the explicit isolated Lean build is used.
- `IndexedTour.decode` is a logical pointwise view. Any later executable materialization must be
  charged according to the frozen output rules.
- The current repository `HEAD` is the immediate committed-snapshot child of the protocol's recorded
  commit, as documented above.

## 16. Confirmation and final status

The Common tree can be copied unchanged into both blind implementation worktrees. Neither
Hierholzer nor graph-specific infrastructure was implemented, and no graph foundation was inspected
or modified during this task.

COMMON_FREEZE_READY
