# Examples: one entry page per algorithm family

**Preferred public import:** `AlgoLib.Experimental.RAM.Examples`.
See [public names and stability](../docs/PUBLIC-API.md); narrower module links below explain internals.

| Example | What to learn |
| --- | --- |
| [Insertion sort](InsertionSort/README.md) | Nested loops, generated obligations, quadratic RAM bound, execution, and procedure calling |
| [BFS connectivity](BFS/README.md) | Graph operations, linear-time argument, ownership, unchanged proof with two queues |
| [Composition exercises](Composition/README.md) | Small buffer, queue, and mixed-variable clients testing individual mechanisms |

Each page links the source program, obligations, proofs, implementation assembly,
and executable theorem. Begin with the source and mathematical proof. Backend and
storage files are intended for implementation authors.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

**Preferred import:** `AlgoLib.Experimental.RAM.Examples`.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Examples](../Examples.lean) | public | Examples: supported public entry point |
| [BFS/Execution.lean](BFS/Execution.lean) | internal | Execute one verified BFS with either FIFO backend |
| [BFS/Facts.lean](BFS/Facts.lean) | internal | The paper argument for owned BFS |
| [BFS/Inputs.lean](BFS/Inputs.lean) | internal | Small adjacency-list inputs for BFS examples |
| [BFS/Obligations.lean](BFS/Obligations.lean) | internal | Generated BreadthFirst obligation API |
| [BFS/Program.lean](BFS/Program.lean) | internal | One paper-style BFS over owned queue, graph cursor, and visited array |
| [BFS/Proofs.lean](BFS/Proofs.lean) | internal | BFS proof declarations against the generated source API |
| [BFS/QueueBackend.lean](BFS/QueueBackend.lean) | internal | FIFO implementation adapter with stable assembly contracts |
| [BFS/Storage.lean](BFS/Storage.lean) | internal | Resident storage for the unchanged BFS client |
| [Composition/BufferAlgorithms.lean](Composition/BufferAlgorithms.lean) | internal | Paper-style owned buffer algorithms |
| [Composition/BufferClient.lean](Composition/BufferClient.lean) | internal | Client proofs using only abstract buffer contracts |
| [Composition/Demo.lean](Composition/Demo.lean) | internal | Execute the same client proof with independently selected buffer implementations |
| [Composition/MixedAlgorithms.lean](Composition/MixedAlgorithms.lean) | internal | Arrays, local variables, and procedure contracts in one method |
| [Composition/QueueAlgorithms.lean](Composition/QueueAlgorithms.lean) | internal | Small FIFO clients used before linking graph traversal |
| [InsertionSort/Backend.lean](InsertionSort/Backend.lean) | internal | Cached insertion-sort RAM certificates |
| [InsertionSort/Execution.lean](InsertionSort/Execution.lean) | internal | Ordinary lists through the unified frontend and verified RAM compiler |
| [InsertionSort/MinimumCaller.lean](InsertionSort/MinimumCaller.lean) | internal | Verified sorting and a modular caller |
| [InsertionSort/Obligations.lean](InsertionSort/Obligations.lean) | internal | Generated Sorting obligation API |
| [InsertionSort/Program.lean](InsertionSort/Program.lean) | internal | Insertion sort with mutable arrays and inline loop invariants |
| [InsertionSort/Proofs.lean](InsertionSort/Proofs.lean) | internal | Insertion-sort proofs against the generated obligation API |

<!-- END GENERATED MODULE INDEX -->
