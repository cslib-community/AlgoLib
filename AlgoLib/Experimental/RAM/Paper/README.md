# Writing a paper proof

You need mathematical invariants, sets/lists, and basic Lean proof syntax. You do not need to know the compiler, register allocation, queue addresses, or memory encoding.

Read [Examples.lean](Examples.lean) first. It runs both compiled algorithms and applies their correctness and time theorems to ordinary inputs. Execution takes no fuel: proving the credit obligations already establishes termination.

## 1. Choose certified operations

A `Program` uses a mathematical state. For graph traversal the state has:

- `seen`: discovered vertices;
- `queue`: the FIFO frontier;
- `row`: remaining adjacency entries of the current vertex;
- `current`: the dequeued vertex;
- `processed`: vertices whose entire row has been scanned.

The graph-traversal library offers `dequeue`, `visit`, and `finish`. Each exposes a precondition, mathematical effect, and work budget. The implementation and its memory proof are library responsibilities.

`visit` checks whether the current neighbor is already seen. If necessary it marks and enqueues the neighbor, then advances the row iterator. Appending to the specification's ghost list does not execute a Lean list append inside the RAM program: its certified implementation writes a queue slot.

## 2. Compose procedures and control flow

The syntax supports arbitrary combinations of `call`, `while`, and `if`:

```lean
def scanRow (a : Adjacency) : Program (model a) := paper {
  while (rowNonempty a) { call visit a; }
}
```

This is the actual library procedure body, not illustrative pseudocode. Its summary says that scanning a row has the mathematical effect `scan` and uses at most `2 * row.length + 1` work units. Each unit has a certified RAM implementation bound.

The caller writes `call (scanNeighbors a).call;`. Symbolic execution uses the procedure summary and never expands the traversal proof. The compiler still emits the real procedure body. Calls currently inline finite bodies; recursive procedures are not supported.

The BFS program and proof are in [BFS.lean](BFS.lean). The array example in [InsertionSort.lean](InsertionSort.lean) repeatedly calls a linear-time insertion operation while the unprocessed prefix is nonempty. It visits the prefix from right to left and grows a sorted suffix.

## 3. State an invariant and potential

For BFS the invariant says:

1. `seen = processed ∪ queue` and there is no partially scanned row at the outer loop header.
2. The queue has no duplicates and is disjoint from processed vertices.
3. All seen vertices are reachable from the source.
4. Every neighbor of a processed vertex has been seen.

`Invariant` packages the graph facts. Its `process` theorem expresses the mathematical maintenance argument, independently of memory. At exit its `exit` theorem establishes that the seen set is exactly the reachable set.

The BFS potential allocates `3 + 2 * degree(v)` credits to each unprocessed vertex. `Credits.remove` automatically computes the potential drop when a fresh vertex is processed. The user supplies the important fact that this vertex has not been processed before.

For insertion sort the invariant is simply that the suffix is sorted and the unprocessed values together with the suffix permute the input. The potential is:

```lean
def potential (s : State) : Nat :=
  s.todo.length * (s.todo.length + s.sorted.length + 2)
```

The total number of values stays constant. Each iteration spends at most one scan of the suffix plus loop overhead.

## 4. Prove the named obligations

`LoopProof` gives Lean three named fields:

| Field | What to show |
|---|---|
| `preservation` | The body preserves the invariant and leaves enough credits for the new potential |
| `payment` | A true loop guard has at least one available credit |
| `exit` | The invariant and false guard imply the desired result |

Inside `preservation`, use `paper_steps [bodyDefinitions]`. This expands program sequencing and registered **logical** contracts. Its goals concern sets, lists, bounds, and remaining credits. It does not expand implementations.

Supply algorithmic lemmas such as permutation preservation or “this vertex is fresh.” Then use `paper_credits` for arithmetic. It expands polynomial products and handles natural-number subtraction without requiring users to transport a cost theorem through a compiler.

If a tactic cannot close the goal, Lean retains the ordinary mathematical obligation. Change the invariant or add a mathematical lemma and rerun the tactic. There is no automatic invariant discovery and no fallback axiom.

After these fields check, `loopProof.correct` provides termination, correctness, and a work bound. Initialization is a separate mathematical obligation: show that the library's prepared input satisfies the invariant. See `initially` in each executable binding.

## 5. Obtain the executable and theorem

`Interface.run` combines certified input preparation, your proof, compilation, and output decoding. The library's existing BFS and array interfaces handle their layouts. You provide input and its mathematical validity proof, never source/machine correspondence.

For existing algorithms use:

- `Insertion.run xs`, `Insertion.run_correct xs`, `Insertion.quadratic xs h`;
- `BFS.run input`, `BFS.run_correct input v`, `BFS.connected_iff input`, `BFS.linear input`.

Both return `Result` with `value` and `steps`. BFS's value is a bitmap with `.contains` and `.toList`; insertion sort returns a list view of its RAM array.

## What automation does, and what remains yours

| Automatic | Supplied by the algorithm author |
|---|---|
| Contract substitution and sequencing | Algorithm invariant |
| Physical frames of certified operations | Logical connection to the problem specification |
| Procedure implementation reuse | Mathematical maintenance and exit lemmas |
| Primitive payments and budget arithmetic | Potential or charging scheme |
| Source/RAM correspondence and termination from credits | Input validity and invariant initialization |

The invariant can contain arbitrary mathematics, but ghost information cannot control execution unless a certified guard connects it to an actual machine test. Arbitrary mathematical functions cannot be smuggled into a one-step executable operation: constructing a new `Action` requires a checked implementation theorem.

## Extending the library

Algorithm clients compose existing contracts. A **library implementer** defining a new data structure must supply its representation, physical operations, and functional/cost proofs once. `Library/Framing.lean` provides reusable read/write-footprint rules for that work; graph and array representations already use them.

The current authoring libraries are deliberately small: graph traversal and adjacent-suffix insertion. Existing typed arrays, stacks, queues, procedures, and expressions remain available in `Language`/`Library`. Adapting a new combination of data structures to an abstract state still requires a library contract. We do not claim arbitrary heap ownership inference, automatic alias analysis, or a complete separation-logic solver.
