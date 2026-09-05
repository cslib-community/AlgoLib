# BFS with explicit inputs, outputs, and paper syntax

The declaration in [`Paper.lean`](Paper.lean) is actual Lean syntax:

```lean
def bfs : Program := graph_program (V, adjacency, s) returns visited {
  for v in V { visited[v] := false; }
  visited[s] := true;
  Q := [s];
  while Q is not empty {
    u := dequeue(Q);
    for v in adjacency[u] {
      if not visited[v] {
        visited[v] := true;
        enqueue(Q, v);
      }
    }
  }
  return visited;
}
```

Inputs and output are explicit:

| Name | Meaning |
| --- | --- |
| `V` | Vertices `0, …, n-1`, obtained from the adjacency input's size |
| `adjacency` | The adjacency lists, with a proved graph representation |
| `s` | Source vertex, required to belong to `V` |
| `visited` | Returned bitmap: `visited.contains v` tells whether `v` was reached |

The public API in [`Interface.lean`](Interface.lean) accepts `Arguments G` and
returns a `Result` with named `visited` and `steps` fields. No caller needs
register names, memory addresses, fuel, or a raw RAM state:

```lean
import AlgoLib.Experimental.RAM.BFS
open AlgoLib.Experimental.RAM.BFS Demo

def args : Arguments path.graph := path.arguments (source := 0) (by decide)
def answer : Result := run args

#eval answer.visited.toList
-- [0, 1, 2, 3]
#eval answer.steps
-- 142
```

`Arguments` has explicit `adjacency`, `representation`, and `source` fields.
The bounds and representation proofs are erased during execution. `G` is the
mathematical specification, not a second runtime graph.

The underlying reusable RAM abstraction is
`Checked.Procedure InputType OutputType`, in [`../Interface.lean`](../Interface.lean).
It declares an input encoder, a fixed code body, a restricted output descriptor,
and a termination certificate. Output descriptors expose registers, bitmap
views, or pairs of these. They cannot run an arbitrary Lean transformation to
compute the answer after the measured program has finished.

`return visited` exposes the final bitmap as a view without copying it.
`visited.toList` is a host-side formatting operation, outside the reported RAM
count, as is input encoding. BFS initialization is counted. The existing
`report path 0 (by decide)` convenience function now uses this public interface.

## Lowering and verification

The frontend constructs a structured `Plan`, then lowers it compositionally to
the existing imperative source language. Vertex and adjacency iterators insert
their cursor instructions; FIFO operations expand into memory reads and writes.
Adjacent instructions are grouped into blocks. The source compiler then lowers
these blocks and loops into RAM code.

`Paper.bfs_compiles` proves that the displayed program compiles **exactly** to
the existing `bfsCode`. `Paper.Program.compile_correct` relates the lowered
source execution to RAM execution, preserving the final state and exact cost.
The established correctness, connectivity, termination, and linear-time proofs
therefore carry through unchanged.

The public theorems are:

- `result_correct`: `visited.contains v = true ↔ Reachable G s v`.
- `result_list_correct`: the same contract for `visited.toList`.
- `result_connected`: visiting every vertex is equivalent to connectedness.
- `result_linear`: `steps ≤ 32(n + m)`.
- `result_length`: the returned bitmap has exactly `n` entries.

This is a focused traversal frontend with one FIFO and one bitmap. It supports
the constructs above, bound-variable renaming, and sequential traversal bodies.
Seeding and mark-before-enqueue are recognized as paired operations so their
lowering can reuse an address calculation. All names and both statements are
checked. Unsupported bodies, incorrect references, missing returns, and
conflicting interface names are rejected. It is not a general variable allocator
or arbitrary-array language. Editing the algorithm changes its compiled code;
the edited program needs its own verification certificate.

## The theorem to state

BFS returns exactly the reachable vertices **for every input graph**, including
a disconnected graph. With a valid source `s`, it visits **every vertex if and
only if the graph is connected**.

The definitions in [`Specification.lean`](Specification.lean) refer directly to
AlgoLib's `Graph Nat β`. Vertices are numbered `0, …, n-1`; labelled parallel
edges and loops are allowed. `Reachable` describes a finite edge walk,
with reflexivity restricted to actual vertices. The public contract is:

```lean
ReturnsReachable G source marked :=
  ∀ v, marked v ↔ Reachable G source v
```

`Input.correct` proves actual execution of `bfsCode`, this contract, and the
bound

```
steps ≤ 13n + 32m + 9.
```

`Input.linear` strengthens the presentation to

```
steps ≤ 32(n + m),
```

because a valid source implies `n ≥ 1`. Here `m` counts the **labelled** edges
in `G.edgeSet`. The repository's `E(G)` projects away labels and can collapse
parallel edges, so using its cardinality would be wrong for this representation.

`Demo.report_correct` states exact reachability directly for the returned
vertex list, and `Demo.report_connected` gives its connectivity equivalence.
The underlying `Input.connected_iff` proves:

```lean
(∀ v < a.n, input.run.2.memory (5 * v + 1) = 1) ↔ Connected G
```

[`GraphBridge.lean`](GraphBridge.lean) proves that `Reachable` and `Connected`
specialize exactly to the existing walk-based `SimpleGraph.Reachable` and
`SimpleGraph.IsConnected`. The specification does not replace those definitions.

## Program and proof as on paper

The mathematical reading of the program is ordinary FIFO BFS:

```text
for v in V: visited[v] := false
visited[s] := true
Q := [s]
while Q is not empty:
    u := dequeue(Q)
    for v in adjacency[u]:
        if not visited[v]:
            visited[v] := true
            enqueue(Q, v)
```

Below the paper frontend, [`bfsSource`](Program.lean) remains the intermediate
imperative form, with short helper procedures for memory operations:

```lean
def bfsSource : Stmt := imperative {
  head := 0;
  while head < size {
    call clearBody;
  }
  call seed;
  while head < tail {
    call popBody;
    while ptr > 0 {
      call scanBody;
    }
  }
}
```

`call` inlines source syntax. Each helper is written using assignments,
loads, stores, comparisons, and constant-size arithmetic. For example,
`popBody` loads one FIFO slot, increments `head`, and loads that vertex's
adjacency-list head. `scanBody` reads one neighbor, tests its visited flag,
marks and enqueues it if necessary, then advances one link.

`bfsSource_compiles` identifies this source's compilation with `bfsCode`.
The generic compiler theorems `Eval.compile` and `Eval.of_compile` preserve
both state and exact cost in both directions. `Input.source_correct` connects
the actual fuel-free run to the independent source semantics.

The correctness argument has four steps:

1. **Initialization.** Let `D` be the processed vertices and `Q` the FIFO.
   Initially `D = ∅`, `Q = [s]`, and only `s` is marked.
2. **Invariant.** The discovered set is `D ∪ Q`. The FIFO has no duplicates
   and is disjoint from `D`. Every discovered vertex is reachable from `s`.
   Every neighbor of every vertex in `D` has been discovered.
3. **Maintenance.** Dequeue `u`. Scanning its row appends precisely the
   previously unseen neighbors, marking them before enqueueing. Add `u` to
   `D`. Reachability follows by extending a walk with the edge `uv`;
   closure and uniqueness are preserved. This is `Invariant.process`.
4. **Exit.** When `Q = []`, the discovered set contains `s` and is closed
   under edges. Induction on any walk from `s` shows its endpoint belongs
   to `D`. Soundness is already in the invariant. This is `Invariant.exit`.

The ghost lists and finite sets express the proof. Runtime membership is a
single visited-cell read, and enqueue writes a single FIFO slot. The RAM does
not evaluate `Finset` membership, list append, or graph reachability.

## Verification conditions for correctness and time

The existing inline `invariant`/`decreases` syntax remains supported. BFS uses
**external modular loop VCs**, which let invariants refer to ghost sets, queues,
and remaining adjacency lists without recovering those objects from registers.
The new plain `while` syntax is for this route. It supplies no termination
certificate by itself; the zero-rank placeholder cannot pass the inline
`Source.VC` for a true iteration.

[`LoopVC.lean`](../LoopVC.lean) gives the reusable verification-condition rule.
For a loop, a ghost-to-memory relation `rep`, and a natural potential `Φ`, the
obligations are:

- **Initialization:** `rep g initialState`.
- **Exit:** the invariant and a false guard imply the postcondition.
- **Maintenance and time:** a true guard yields an actual body execution in
  `k` operations, a new state satisfying `rep g'`, and
  `1 + k + Φ(g') ≤ Φ(g)`.

`LoopVC.sound` proves that discharging these conditions gives a terminating
execution, the postcondition, and at most `Φ(g) + 1` operations. The extra one
pays for the final false guard. Strict decrease follows from paying for the
true guard, so a separate fuel or termination-bound argument is unnecessary.
These are modular VCs with reusable body contracts; this is not automatic
invariant discovery or a complete Dafny verifier.

All three loop certificates are discharged:

| Loop | Invariant/view | Potential | Certificate |
| --- | --- | --- | --- |
| Clear flags | Flags below `j` are zero; graph memory is preserved | `5(n-j)` | `clear_vc` |
| Scan a row | Remaining linked list and the discovery/FIFO view | `16 · length(remaining)` | `scan_vc` |
| BFS | Reachability, edge closure, FIFO uniqueness, memory view | Sum of vertex credits over `V \ D` | `bfs_vc` |

The `vcgen` tactic opens the exit and maintenance/time goals for these loop
contracts. For the existing inline `Source.VC`, it continues to expand the
source weakest-precondition obligations. The generated body conditions reduce
to ordinary instruction evaluation and
mathematical lemmas. Pointer/frame arithmetic stays in `Memory.lean` and the
local helper contracts. The central BFS proof in `Algorithm.lean` uses those
contracts, `Invariant.process`, and one potential identity.

## The linear-time proof

One adjacency entry uses six read/address instructions, one conditional test,
at most five mark/enqueue instructions, and three advance instructions.
Including its true loop guard, this costs at most **16** operations. Scanning
a row adds one final false guard.

One vertex therefore costs at most `8 + 16 degree(u)`: one outer guard, six
FIFO/head instructions, its adjacency scan, and the scan's final false guard.
Give each unprocessed vertex those credits:

```
Φ(D) = Σ[u ∈ V \ D] (8 + 16 degree(u)).
```

Uniqueness ensures that a dequeued `u` is absent from `D`. The entire time
maintenance proof is the identity

```
Φ(D ∪ {u}) + 8 + 16 degree(u) = Φ(D).
```

This is `potential_process`. Initially,

```
Φ(∅) = 8n + 16 Σ degree(u) = 8n + 32m.
```

Initialization costs at most `5n + 8`; the final outer guard costs one.
Together these give `13n + 32m + 9`. The theorem is an **upper bound** for the
unit-cost natural-number RAM, not a bit-complexity or host-runtime claim.
Unreachable rows need not be scanned, so a disconnected instance can cost less.

## Representation and client ergonomics

A client can start with a short labelled edge list:

```lean
def path : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2), (2, 2, 3)]
  distinct := by decide
  valid := by decide

def search := path.fromSource 0 (by decide)
```

`EdgeInput.represents` proves that row membership is exactly undirected
adjacency in the constructed repository `Graph`. `count_incidences` proves
that the total row length is twice the number of labelled edges. A loop
contributes two entries; parallel labels remain distinct. Callers do not
supply an assumed algorithmic time bound.

`Adjacency.encode_heap` proves that the pointer encoding decodes to those
exact rows. The memory layout has disjoint address classes for graph heads,
visited flags, FIFO slots, destinations, and next pointers. `GraphFrame` and
`View` supply reusable read/write, enqueue, and dequeue contracts. The input
encoder starts mutable cells with junk; BFS really initializes them.

The cost contract begins with **encoded adjacency lists as input**, as in the
standard RAM analysis of BFS. `EdgeInput` is a convenience specification/input
builder, not a separately verified linear-time edge-list-to-adjacency compiler;
it constructs each row from the edge list. Its preprocessing and display
formatting are not charged to `bfsCode`. Supplying an already represented
adjacency input through `Input` uses the same theorem.

## Files and validation

| File | Responsibility |
| --- | --- |
| `Specification.lean` | Repository `Graph` specification and exit argument |
| `GraphBridge.lean` | Agreement with existing `SimpleGraph` connectivity |
| `GraphInput.lean`, `Encoding.lean` | Edge/adjacency/pointer refinement and incidence count |
| `Memory.lean` | Layout, frame rules, queue view, source helpers |
| `Scan.lean` | Row-scanning VCs and RAM contract |
| `Algorithm.lean` | Paper-style invariant maintenance, potential, outer VCs |
| `Program.lean` | Initialization, fixed source/code, public executable and theorems |
| `Paper.lean` | Paper syntax, binding checks, and structured lowering |
| `Interface.lean` | Explicit input arguments, named output, and public contracts |
| `Demo.lean` | Client examples and theorem statements |
| `Tests.lean` | All 256 graph/source combinations on four vertices and boundary cases |

```sh
lake build AlgoLib.Experimental.RAM.BFS.Tests
lake build
```

Tests compare the actual RAM runner against an independent finite-closure
reference, check both the raw runner and the public input/output interface,
check FIFO uniqueness and the time bound, and cover a singleton,
an isolated source, a diamond, reverse discovery order, loops, and parallel
edges. Logical regressions reject an empty-graph source and zero credits at a
true guard. All mathematical guarantees are kernel-checked proofs.

Syntax regressions also check bound-variable renaming, reject incorrect output
names and duplicate interface names, and confirm that removing discovery changes
the compiled code.
