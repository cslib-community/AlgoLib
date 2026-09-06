# One BFS proof, two FIFO implementations

Start with [BreadthFirst.lean](BreadthFirst.lean). It contains the only BFS program
and the only algorithm verification proof used by the two runners. Array writes,
scalar locals, both loops, and queue calls are visible in that source. Queue
representations, memory addresses, and compiler certificates are absent.

## Run it

```lean
import AlgoLib.Experimental.RAM.Prototype.Composition.BFSExecution
import AlgoLib.Experimental.RAM.Legacy.Examples

open AlgoLib.Experimental.RAM
open Prototype.Composition

#eval (BreadthFirst.search .circular Legacy.Examples.diamond ⟨0, by decide⟩).value
#eval (BreadthFirst.search .twoStacks Legacy.Examples.diamond ⟨0, by decide⟩).value
```

Both return the vertex set `{0, 1, 2, 3}`. On this diamond input, the circular
backend takes 520 RAM steps and the two-stack backend takes 589. `search` takes an ordinary `EdgeInput`
and a valid source `Fin input.n`, returns a Lean `Finset Nat`, and reports actual
RAM instruction steps. It asks for no fuel. Termination follows from the checked
loop obligations.

The public theorems are:

- `search_correct`: membership in the result is equivalent to graph reachability
  from the source, using the repository's `Graph` definition.
- `connected`: the graph is connected iff the result equals `Finset.range input.n`.
- `linear`: the actual runner takes at most `2448 * (input.n + input.edges.length)`
  RAM steps.
- `same_result`: changing the FIFO backend preserves the result for every valid
  graph and source, not just the test examples.

A valid source rules out the empty graph. Isolated vertices, self-loops, and
parallel labelled edges are supported.

## Read the algorithm and its argument together

The source follows this pseudocode; the Lean file adds the invariants beside the
corresponding loops:

```text
BFS(graph, source) returns visited vertices
    for each vertex i: visited[i] := 0
    queue.clear()
    visited[source] := 1
    queue.enqueue(source)
    while queue.nonempty:
        u := queue.dequeue()
        row := graph.neighbors(u)
        while row.nonempty:
            v := row.next()
            if visited[v] = 0:
                visited[v] := 1
                queue.enqueue(v)
```

The mathematical vocabulary in [BFSFacts.lean](BFSFacts.lean) is small:

| Fact | Paper meaning | Where it is used |
|---|---|---|
| `marked visited` | Vertices with nonzero visited flags | Input/output assertions |
| `Frontier` | Discovered vertices split into processed vertices and a duplicate-free queue; all are reachable; processed neighbors are discovered | Outer invariant |
| `QueueOK` | Every queued vertex is marked, and no vertex is queued twice | Inner invariant and queue capacity |
| `scan` | Mathematical effect of scanning the remaining neighbors | Inner invariant |
| `work` | One unit per unprocessed vertex, plus one per adjacency entry of that vertex | Outer counting argument |

The inner invariant says that scanning the remaining row from the current state
has the same final effect as scanning the whole row from its entry state:

```lean
invariant "neighbor scan" scan row (marked visited) queue =
  at_loop_entry(scan row (marked visited) queue)
```

Marking a fresh vertex and enqueuing it preserves this fact. An already marked
vertex leaves the discovered set unchanged. Since vertices are marked before
enqueuing, a fresh vertex cannot already be in the queue; therefore a queue of
capacity at least `|V|` is sufficient.

[BFSFacts.lean](BFSFacts.lean) reuses the existing graph invariant and scan lemmas
from [Specification/Traversal.lean](../../Specification/Traversal.lean). The
algorithm proof supplies mathematical lemmas to the generated obligations; it
contains no queue address calculation or compiler simulation.

## Why the nested loops remain linear

Bounding every neighbor scan by the maximum degree would lose the desired
counting argument. The source instead writes:

```lean
amortized_work work a (marked visited) queue initially_at_most a.n + a.entries
```

The inner loop writes `iterations_at_most row.length`. The frontend infers the
charges for the guard, array reads/writes, assignments, and procedure calls. A
completed outer iteration decreases `work` by exactly `1 + degree(u)`. Its
allowance therefore pays for that particular row, not a worst-case row repeated
`|V|` times. Vertices not reached may leave unused allowance.

`initially_at_most` is checked, not trusted. The generated obligations require the
initial work to fit the supplied total and every iteration to preserve the
invariant, decrease the measure, and leave sufficient allowance. The negative
[WorkAccounting tests](../../Tests/WorkAccounting.lean) reject insufficient
initial allowances and stationary measures.

`at_loop_entry` is a logical snapshot. Neither the snapshot nor the work measure
is computed by RAM instructions.

## What changes when the queue changes?

Nothing in `BreadthFirst.bfs`, its invariants, or `bfsVerification` changes.

| Backend | Concrete implementation | Private accounting |
|---|---|---|
| `.circular` | A fixed-capacity circular buffer; head/length registers and wraparound by comparison/subtraction | No saved potential; operations have bounded worst-case cost |
| `.twoStacks` | Two fixed-capacity array stacks; reverse the back stack into the front only when necessary | Potential proportional to the number of back-stack elements pays for later transfers |

[Queue.lean](Queue.lean) exposes the same FIFO list model, capacity preconditions,
functional effects, and logical charges in both cases. Public calls use a
conservative charge of ten logical credits. The two-stack potential is owned and
hidden by [DataRefinement.lean](DataRefinement.lean); it is neither a BFS invariant
nor an extra argument to the client proof.

The two-stack backend itself uses a verified source program over stack operations.
Its RAM implementation is reconstructed through the existing linker. It is not a
host callback or a second unverified queue evaluator.

Both runners currently obtain the same conservative upper bound. Their actual
step counts differ. The smaller [OwnedQueues tests](../../Tests/OwnedQueues.lean)
also cover initially nonempty queues, where initial saved potential is explicitly
included in the runner's bound. BFS starts with an empty queue and zero saved
potential.

## Follow the checked connections

```text
BreadthFirst.bfs + inline invariants/counting annotations
                    |
          generated correctness/cost VCs
                    |
          bfsVerification / bfsProcedure
              /                       \
       loom_correct              BFSExecution linking
      actual Loom WP             /                  \
                            QueueRing         QueueStacksImplementation
                                 \                  /
                              existing verified RAM compiler
                                         |
                           search_correct + connected + linear
```

| File | Responsibility |
|---|---|
| [BreadthFirst.lean](BreadthFirst.lean) | Student-facing program, invariants, source proof, Loom theorem |
| [BFSFacts.lean](BFSFacts.lean) | Pure graph/bitmap/scan reasoning |
| [Queue.lean](Queue.lean), [GraphCursor.lean](GraphCursor.lean) | Abstract procedure contracts |
| [QueueRing.lean](QueueRing.lean) | Circular FIFO RAM implementation |
| [QueueStacks.lean](QueueStacks.lean) | Concrete two-stack source program and amortized refinement |
| [StackImplementation.lean](StackImplementation.lean), [QueueStacksImplementation.lean](QueueStacksImplementation.lean) | Reusable stack RAM operations and queue linking |
| [GraphCursorImplementation.lean](GraphCursorImplementation.lean) | Owned read-only adjacency-list cells and actual RAM loads |
| [BFSStorage.lean](BFSStorage.lean) | Disjoint resident storage for graph, bitmap, queue, and source |
| [BFSExecution.lean](BFSExecution.lean) | Local storage, certificate reconstruction, executable and final theorems |
| [DataRefinement.lean](DataRefinement.lean) | Generic abstraction map with hidden representation invariant and potential |

The dependency checker enforces that source programs and logical contracts do not
import their RAM implementations. Existing compiler proofs and axiom guards are
retained. Backend code comparison uses `ram_code_eq`, which reconstructs ordinary
equality proofs after erasing certificate fields; it adds no trusted equality test. Loom supplies the reasoning interpretation; the ownership/refinement
boundary follows the direction of Sepref-style data-structure refinement. This
extension is not an implementation of the entire Sepref system; see the existing
[composition design and credits](README.md).

## Cost and execution boundary

The input adjacency lists are resident before the RAM body starts. Host-side
encoding, allocating the arena, and observing the output bitmap as a `Finset` are
outside the reported instruction count. Clearing the visited array, initializing
the FIFO, scanning adjacency entries, and queue operations are inside it.

`runIn` makes arena base and capacity explicit. `code_independent` proves that,
for a fixed arena and FIFO choice, changing the graph or its correctness proof
does not change the compiled instructions. `search` is the convenient wrapper
that chooses a sufficient arena from input size/layout. This is a configured
RAM-code family; it does not claim a new dynamic allocator or a single
capacity-independent circular-buffer executable.

The polynomial coefficients come from normalizing the inferred allowance with
the selected backend's conversion rate. They are conservative instruction bounds,
not a claim of optimal BFS constants. The proof counts adjacency multiplicities;
`EdgeInput.represents` establishes at most two entries per labelled edge.

## Checks

```sh
lake build AlgoLib.Experimental.RAM.Tests.OwnedBFS
lake build AlgoLib.Experimental.RAM.Tests.OwnedBFSAxioms
python3 AlgoLib/Experimental/RAM/Tests/check_layers.py
```

The executable tests cover all 64 simple undirected graphs on four vertices,
every source, both FIFO implementations, and additional multigraph cases. A
separate independent reachability computation serves as their oracle. These tests
supplement the universal correctness and cost theorems.

With dependencies already built, the checked run in this workspace reported about
20 seconds for the BFS source proof, 5.1 seconds for backend assembly including
code independence, and 3.7 seconds for the executable BFS tests. These are local
incremental measurements, not clean-build or cross-machine performance promises.
Code comparison reconstructs constructor equalities instead of repeatedly trying
to equate the discarded ownership representations.
