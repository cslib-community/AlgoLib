# Small composition exercises

These examples isolate mechanisms used together by sorting and BFS. The compact
examples keep program declarations, verification and/or execution in the same file;
they do not require separate empty obligation/proof modules.

| Example | Program, obligations, proofs | Execution / theorem |
| --- | --- | --- |
| Buffer clients | [BufferClient](BufferClient.lean), [BufferAlgorithms](BufferAlgorithms.lean) | [Demo](Demo.lean): linked implementations and result theorems |
| FIFO clients | [QueueAlgorithms](QueueAlgorithms.lean) | Concrete executions and substitution are exercised in [queue tests](../../Tests/OwnedQueues.lean) |
| Mixed arrays and scalars | [MixedAlgorithms](MixedAlgorithms.lean) | Executable checks in [mixed frontend tests](../../Tests/MixedFrontend.lean) |

For a complete algorithm story use [insertion sort](../InsertionSort/README.md) or
[BFS](../BFS/README.md). Implementation contracts are in Library and Implementations,
not in this examples directory.
