# Certified operations: the algorithm-facing library

This directory is the boundary between algorithm proofs and data-structure implementations. Its files expose logical state transitions, preconditions, work bounds, and stable input/output equations. They import the implementation certificates on your behalf.

| File | Use it for | Contract you use |
|---|---|---|
| [Insertion.lean](Insertion.lean) | An array with an unprocessed prefix and sorted suffix | `insertNext`: nonempty todo; ordered insertion; at most `sorted.length + 1` credits |
| [Search.lean](Search.lean) | Visited flags, FIFO frontier, and adjacency cursor | `dequeue`, `visit`, `scanNeighbors`, `finish`; reusable row-scan cost |

`scanNeighbors` is a library procedure: its implementation loops through the row, while callers reason from its functional/cost summary. It belongs here rather than in a second BFS algorithm file. A call does not erase its code: the compiler emits the certified procedure body.

The generic physical array, queue, stack, and graph contracts live in [Backend/Memory](../Backend/Memory). They are implementation APIs over memory, not additional student-level algorithms. A new public operation should expose an `Action` or `Procedure` here, with its representation proof in `Backend/Adapters` and stable logical equations for `paper_steps`.

Framing has two levels. Backend footprint proofs preserve unrelated memory. At this level, symbolic execution preserves untouched logical record fields. An algorithm author proves neither adjacency-pointer preservation nor queue-address arithmetic.
