# Implementations: private representations and resource refinement

**Preferred public import:** `AlgoLib.Experimental.RAM.Implementations`.
See [public names and stability](../docs/PUBLIC-API.md); narrower module links below explain internals.

This layer connects a library's mathematical model to owned machine memory.
An operation implementation supplies functional simulation, preservation of
unrelated memory, and a cost/potential inequality. These certificates compose.

| Directory | Responsibility |
| --- | --- |
| [Contracts](Contracts/) | Shared ownership, resource-aware refinement, focus/framing, local hiding, resident input/encoder laws |
| [Native](Native/) | One-cell signed values, scalar/array layouts, expression implementations, native encoders |
| [DataStructures](DataStructures/) | Ring and two-stack queues, buffers, stacks, adjacency cursor implementations |
| [Natural](Natural/) | Maintained natural-valued source views and their storage/memory contracts |

`Natural` is an internal compatibility implementation interface. Its runners and
linking use the native integer compiler. It is not Nat-RAM execution and it is not
a second algorithm frontend. Paired signed encodings retained here are historical
implementation evidence; standard signed assembly uses Native single-cell storage.

Start with [implementation contracts](IMPLEMENTATION-CONTRACTS.md).
A representation hides addresses; a private potential hides payment strategy.
The generic linking theorem in Compiler combines both without changing the client
proof. BFS assembly relies on public layout/encoder envelopes rather than private
queue fields. [The BFS guide](../Examples/BFS/README.md) identifies both implementations.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

**Preferred import:** `AlgoLib.Experimental.RAM.Implementations`.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Implementations](../Implementations.lean) | public | Implementations: supported public entry point |
| [Contracts/Focus.lean](Contracts/Focus.lean) | internal | Shared ownership-directed path focusing |
| [Contracts/LocalRefinement.lean](Contracts/LocalRefinement.lean) | internal | Shared private-local initialization and framing |
| [Contracts/Ownership.lean](Contracts/Ownership.lean) | internal | Store-independent ownership and private potential |
| [Contracts/ResidentInputs.lean](Contracts/ResidentInputs.lean) | internal | Shared resident-input encoders |
| [Contracts/ResourceRefinement.lean](Contracts/ResourceRefinement.lean) | internal | Compositional refinement independent of the implementation store |
| [DataStructures/BufferImplementation.lean](DataStructures/BufferImplementation.lean) | internal | Two bounded-buffer implementations with different private payment strategies |
| [DataStructures/GraphCursorImplementation.lean](DataStructures/GraphCursorImplementation.lean) | internal | Owned immutable adjacency lists |
| [DataStructures/QueueRing.lean](DataStructures/QueueRing.lean) | internal | Circular-buffer FIFO representation |
| [DataStructures/QueueStacksImplementation.lean](DataStructures/QueueStacksImplementation.lean) | internal | Link the two-stack FIFO to actual RAM |
| [DataStructures/StackImplementation.lean](DataStructures/StackImplementation.lean) | internal | Array-backed stack removal |
| [Native/ArrayExpressions.lean](Native/ArrayExpressions.lean) | internal | Native array operations with source-level contracts |
| [Native/ArrayStorage.lean](Native/ArrayStorage.lean) | internal | Relocatable single-cell native arrays |
| [Native/Encoding.lean](Native/Encoding.lean) | internal | Native resident inputs and ordinary output observations |
| [Native/Expressions.lean](Native/Expressions.lean) | internal | Native lowering of the unchanged Nat/Int source expressions |
| [Native/Locals.lean](Native/Locals.lean) | internal | Private native local storage |
| [Native/ScalarStorage.lean](Native/ScalarStorage.lean) | internal | Single-cell native scalar representations |
| [Natural/DataRefinement.lean](Natural/DataRefinement.lean) | compatibility | Implement abstract operations using already verified owned programs |
| [Natural/EncoderLayout.lean](Natural/EncoderLayout.lean) | compatibility | Public allocation and initialization contracts |
| [Natural/Encoding.lean](Natural/Encoding.lean) | compatibility | Compositional resident input interfaces |
| [Natural/ExpressionImplementation.lean](Natural/ExpressionImplementation.lean) | compatibility | Ownership-directed compilation of scalar and array expressions |
| [Natural/Language/Basic.lean](Natural/Language/Basic.lean) | compatibility | Typed implementation semantics |
| [Natural/Language/IntegerExecution.lean](Natural/Language/IntegerExecution.lean) | compatibility | Default execution of natural-valued compiler IR on Int-RAM |
| [Natural/Language/Interface.lean](Natural/Language/Interface.lean) | compatibility | Lower implementation interfaces |
| [Natural/Language/Normalization.lean](Natural/Language/Normalization.lean) | compatibility | Internal command normalization |
| [Natural/Language/Syntax.lean](Natural/Language/Syntax.lean) | compatibility | Lower typed DSL |
| [Natural/Language/VC.lean](Natural/Language/VC.lean) | compatibility | Typed verification conditions |
| [Natural/Language/Verification.lean](Natural/Language/Verification.lean) | compatibility | Typed total contracts and runner binding |
| [Natural/LocalImplementation.lean](Natural/LocalImplementation.lean) | compatibility | Private method-local storage |
| [Natural/Memory/Array.lean](Natural/Memory/Array.lean) | compatibility | Physical array contracts |
| [Natural/Memory/Framing.lean](Natural/Memory/Framing.lean) | compatibility | Reusable physical framing |
| [Natural/Memory/Graph.lean](Natural/Memory/Graph.lean) | compatibility | Typed graph data-structure contracts |
| [Natural/Memory/GraphInput.lean](Natural/Memory/GraphInput.lean) | compatibility | Construct certified graph inputs |
| [Natural/Memory/GraphMemory.lean](Natural/Memory/GraphMemory.lean) | compatibility | Adjacency layout and graph inputs |
| [Natural/Memory/Sequences.lean](Natural/Memory/Sequences.lean) | compatibility | Physical stack and FIFO contracts |
| [Natural/Ownership.lean](Natural/Ownership.lean) | compatibility | Local ownership of registers, heap cells, and private potential |
| [Natural/SignedArithmetic.lean](Natural/SignedArithmetic.lean) | compatibility | Exact signed arithmetic through the temporary natural-valued compiler IR |
| [Natural/SignedArrays.lean](Natural/SignedArrays.lean) | compatibility | Owned interleaved signed arrays |
| [Natural/SignedImplementation.lean](Natural/SignedImplementation.lean) | compatibility | Certified signed expression and storage interfaces |
| [Natural/SignedStorage.lean](Natural/SignedStorage.lean) | compatibility | Private canonical signed scalar representation |
| [Natural/Storage.lean](Natural/Storage.lean) | compatibility | Default separately owned scalar and array storage |

<!-- END GENERATED MODULE INDEX -->
