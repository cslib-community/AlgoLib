# BFS: graph specification, adjacency lists, and linear RAM time

Start with [`Demo.lean`](Demo.lean). It executes the same fixed RAM program on
any valid, finite undirected input, with no fuel argument:

```lean
import AlgoLib.Experimental.RAM.BFS
open AlgoLib.Experimental.RAM.BFS Demo

#eval report path 0 (by decide)
-- ([0, 1, 2, 3], 142)
#eval report splitGraph 0 (by decide)
-- ([0, 1, 2], 107)
#eval report splitGraph 3 (by decide)
-- ([3], 37)
```

`report` formats the visited bitmap. Its second component is the exact RAM
instruction count of BFS, including initialization. The convenience encoder
and output formatting are outside this count. The host Lean evaluator's speed
is not the modeled RAM time.

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

The executable [`bfsSource`](Program.lean) uses the existing imperative syntax,
with short helper procedures for the memory operations:

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
| `Demo.lean` | Client examples and theorem statements |
| `Tests.lean` | All 256 graph/source combinations on four vertices and boundary cases |

```sh
lake build AlgoLib.Experimental.RAM.BFS.Tests
lake build
```

Tests compare the actual RAM runner against an independent finite-closure
reference, check FIFO uniqueness and the time bound, and cover a singleton,
an isolated source, a diamond, reverse discovery order, loops, and parallel
edges. Logical regressions reject an empty-graph source and zero credits at a
true guard. All mathematical guarantees are kernel-checked proofs.
