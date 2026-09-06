# Graph algorithms with verified procedure composition

Start with [BFS.lean](BFS.lean) for the algorithm and theorem, and
[Graph.lean](Graph.lean) for its two reusable procedures. These are new prototype
programs using the Loom-connected frontend; they do not invoke the old production
BFS executable or reuse its whole-algorithm correctness theorem.

## 1. Run a graph algorithm on ordinary data

```lean
import AlgoLib.Experimental.RAM.Prototype.BFS

open AlgoLib.Experimental.RAM.BFS
open AlgoLib.Experimental.RAM.Prototype

def path : EdgeInput where
  n := 4
  edges := [(0, 0, 1), (1, 1, 2), (2, 2, 3)]
  distinct := by decide
  valid := by decide

#eval (BFS.search path ⟨0, by decide⟩).value.toList
-- [0, 1, 2, 3]
```

Each edge is `(label, endpoint, endpoint)`. Labels preserve parallel edges. A
`Fin graph.n` source supplies the vertex-bounds proof. A graph with no vertices
has no valid source for this API. Disconnected graphs are valid inputs: BFS
returns only the source component. See [GraphTests.lean](GraphTests.lean) for
connected, disconnected, isolated-source, singleton, loop, and parallel-edge runs.

The output is a Lean vertex-set view. `.contains v` queries membership and `.toList`
materializes it as a Lean list. `.steps` counts actual compiled RAM instructions;
no execution fuel is supplied by the caller.

## 2. State what the algorithm must establish

`BFS.main input` proves all three properties for the same `BFS.run input`:

- `out.contains v = true ↔ Reachable G source v`, for every natural number `v`;
- `Connected G ↔ BFS.vertices out = G.vertexSet`;
- `steps ≤ 370 * (a.n + input.representation.edges.card)`.

The specification uses the repository's `AlgoLib.Graph`, its vertex set, and its
labelled edges. The adjacency representation proves the connection to graph
reachability, including the bound of two stored incidences per labelled edge.

Connectivity here is characterized by the returned set. The API does not claim
a separately compiled Boolean postprocessing pass that compares all bitmap entries.
Graph encoding and displaying the result as a list are host-side operations outside
the RAM cost convention. Clearing the visited bitmap and initializing the FIFO
are compiled operations and **are** included in the time theorem.

## 3. Use a typed graph interface

The interface provides these logical views and certified operations:

| View/operation | Meaning | What the implementation guarantees |
|---|---|---|
| `s.seen` | Visited vertex set | Bitmap membership agrees with the mathematical set |
| `s.queue` | FIFO frontier | Enqueue and dequeue use certified queue storage |
| `s.row` | Remaining neighbors of the current vertex | An adjacency cursor follows the stored list |
| `s.current`, `s.processed` | Current vertex and completed vertices | Proof bookkeeping; completed vertices are never reprocessed |
| `dequeue a` | Remove the FIFO head and open its adjacency row | Preserves the graph and visited set |
| `discoverNext a` | Examine one neighbor, conditionally mark/enqueue, then advance | Preserves adjacency memory; marks before enqueueing |
| `finishVertex a` | Record a fully scanned vertex as processed | Ghost operation; emits no instructions |

The constant-work `discoverNext` primitive implements:

```text
v := next neighbor
if v is not visited:
    mark v visited
    enqueue v
advance the adjacency cursor
```

This conditional is a reusable graph primitive with a checked RAM implementation.
The adjacency **loop** is explicit in the next step. Neither an entire BFS nor an
entire neighbor scan can be inserted as an unproved unit-cost operation.

## 4. Write and verify the neighbor procedure once

The actual definition in `Graph.lean` is:

```lean
def scanCode (a : Adjacency) : Annotated (Search.model a) :=
  ram_do (entry, s, remaining) do
    while (neighborsRemain a)
      invariant ∀ v ∈ s.row, v < a.n
      invariant scanEffect s = scanEffect entry
      invariant 2 * s.row.length + 1 ≤ remaining
      decreasing s.row.length
      do
        perform discoverNext a
```

`entry` is the state on procedure entry; `s` is the current logical state.
They are ordinary mathematical views, not RAM registers or heap addresses.
`remaining` is a proof-only credit count. None of these annotation binders can
supply an executable operation: operations must have certified interface types.

`scanEffect` describes finishing the remaining row. The invariant says that
processing one neighbor preserves that final result. The row becomes shorter,
and each iteration pays for its test and primitive operation.

`scanVerification` solves the generated conditions. `Annotated.verify` packages
the body, precondition, postcondition, work bound, and checked proof into a
`Routine`. The result is `Graph.scanNeighbors`. Its contract requires valid row
vertices, returns the functional scan result, and allows `2 * row.length + 1`
credits. Callers need none of its loop proof.

## 5. Compose procedures

Vertex processing calls that independently verified procedure:

```lean
def processCode (a : Adjacency) : Annotated (Search.model a) :=
  ram_do (_entry, s, remaining) do
    perform dequeue a
    call scanNeighbors a
    perform finishVertex a
```

`processVerification` establishes the scan's precondition from the graph's
adjacency-validity contract. It uses only the scan's specified result and work
bound. Its public result, `processVertex`, is another reusable `Routine`.

A `call` compiles the callee's actual body by inlining it. Verification substitutes
its relational postcondition and upper cost bound. The rule accounts for **any**
actual execution cost below that bound; it does not pretend that the upper bound
is the exact execution cost. Calls cannot certify a different program or omit
payment. There is currently no recursive call stack or dynamic dispatch.

## 6. Supply the BFS argument alongside the outer loop

```lean
def code {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) (source : Nat) :
    Annotated (Search.model a) :=
  ram_do (_entry, s, remaining) do
    while (Graph.queueNotEmpty a)
      invariant frontierInvariant a G source s
      invariant potential a s + 1 ≤ remaining
      do
        call Graph.processVertex a
```

The frontier invariant states that:

1. discovered vertices are exactly processed vertices plus queued vertices;
2. queued vertices are distinct and have not been processed;
3. every discovered vertex is reachable from the source;
4. every neighbor of a processed vertex has been discovered.

`process_preserves` applies the existing mathematical graph-invariant lemma.
The potential reserves a charge for each unprocessed vertex and its adjacency
entries. Processing a vertex removes exactly that charge, so the procedure call
is paid for and the outer loop terminates. An additional decreasing annotation
is unnecessary here: the sound credit rule already proves termination.

At exit the queue is empty. The visited set contains the source and is closed
under graph edges, so every reachable vertex is visited. Soundness gives the
reverse inclusion. Undirected reachability then yields the connectivity theorem.

## 7. Obtain both Loom reasoning and RAM execution

```text
Velvet annotated-loop syntax + certified graph operations
                         │
                 Annotated: body + Plan
                         │
       scanNeighbors → processVertex → BFS
                         │
            generated modular verification conditions
                         │
             kernel-checked procedure contracts
                    ┌────┴─────┐
          actual Loom WP       verified RAM compilation
          BFS.loom_correct     BFS.main / BFS.search
```

`body_independent` proves that changing the source does not change the program.
`compiled_code_independent` also proves that changing the graph data does not
specialize the RAM code. The input graph is read from RAM.

The adapter still has a custom, kernel-justified VC generator connected to Loom's
actual algebra. This is not a claim that arbitrary upstream Velvet methods now
compile to RAM. `ram_do` adds generic typed primitives, modular procedure calls,
branches, assertions, and annotated loops over certified models. Mutable-array
`ram method` retains its documented scalar/array subset. Arbitrary host Lean calls,
unverified allocations, and freely aliased user-defined heaps remain unsupported.

## Where to extend the library

- Add a graph algorithm by composing existing operations in `ram_do` and supplying
  its mathematical invariants and procedure contracts.
- Add a new data-structure operation by certifying its functional effect, frame,
  and implementation cost in a library adapter; algorithm authors then use it
  through `perform`.
- Add a procedure by proving its generated VCs once with `Annotated.verify`.
- Use `procedure_vc [...]` to unfold logical contracts while keeping compiler
  certificates opaque. Remaining goals are ordinary Lean propositions.

The executable regression suite covers 256 graph/source combinations and special
graph shapes. Axiom guards cover the generic procedure rule, graph contracts,
Loom theorem, and final correctness/complexity theorem, alongside the existing
sorting and production checks.
