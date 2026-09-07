# Library: abstract models and contracts

**Preferred public import:** `AlgoLib.Experimental.RAM.Library`.
See [public names and stability](../docs/PUBLIC-API.md); narrower module links below explain internals.

These modules describe what operations do and which logical resources they require.
They do not select concrete queue or array addresses.

- [Queue](Queue.lean): FIFO mathematical interface.
- [Stack](Stack.lean): stack interface.
- [Buffer](Buffer.lean): reusable buffer interface.
- [GraphCursor](GraphCursor.lean): adjacency scanning model and contracts.
- [QueueStacks](QueueStacks.lean): mathematical two-stack queue model and amortized argument.
- [SortingFacts](SortingFacts.lean): reusable list/array sorting mathematics.
- [Graph](Graph/): graph specifications, traversal, and the repository graph bridge.

Algorithms use these models in invariants. Implementations realize the operations
using owned memory and private potential. [BFS](../Examples/BFS/README.md) shows
one algorithm proof instantiated with two queues. Library extension belongs here
when it changes the public mathematical contract; representation changes belong
under Implementations.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

**Preferred import:** `AlgoLib.Experimental.RAM.Library`.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Library](../Library.lean) | public | Library: supported public entry point |
| [Buffer.lean](Buffer.lean) | internal | Abstract bounded buffers: one client, two private clearing strategies |
| [Graph/Graph.lean](Graph/Graph.lean) | internal | Graph-level algorithm specification |
| [Graph/GraphBridge.lean](Graph/GraphBridge.lean) | internal | Connect graph specification APIs |
| [Graph/Traversal.lean](Graph/Traversal.lean) | internal | Mathematical BFS discovery and frontier preservation |
| [GraphCursor.lean](GraphCursor.lean) | internal | Read-only adjacency cursors |
| [Queue.lean](Queue.lean) | internal | FIFO contracts shared by owned graph algorithms |
| [QueueStacks.lean](QueueStacks.lean) | internal | Private two-stack FIFO implementation |
| [SortingFacts.lean](SortingFacts.lean) | internal | The mathematical argument for adjacent-swap insertion sort |
| [Stack.lean](Stack.lean) | internal | Bounded stack contracts |

<!-- END GENERATED MODULE INDEX -->
