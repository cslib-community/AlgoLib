# Migration to abstraction layers

The canonical algorithm files are now `Programs/Sorting.lean` and `Programs/Connectivity.lean`. Each merges the earlier paper program, proof, and executable binding, and adds an explicit input/output `ram_method` contract with generated VCs.

This is a module-path and public-namespace migration. Old path shims are deliberately not left scattered through the tree. Use `import AlgoLib.Experimental.RAM` for the current public methods. The old `Paper` framework namespace is now `Authoring`; complete algorithms live in `Programs`.

| Previous public use | Current use |
|---|---|
| `Paper.Insertion.run`, `run_correct`, `quadratic` | `Programs.Sorting.run`, `run_correct`, `quadratic` |
| `Paper.Insertion.invariant`, `loopProof` | `Programs.Sorting.invariant`, `loopProof` |
| `Paper.BFS.run`, `linear`, `connected_iff` | `Programs.Connectivity.run`, `linear`, `connected_iff` |
| All-visited predicate only | Also `Programs.Connectivity.connected_iff_set` and `main` |
| `Paper.Program`, `LoopProof`, `paper_steps` | Open `Authoring`; logical proof tactics retain their names |
| `Paper.Insertion.insertNext`, `Paper.Search.scanNeighbors` | `Authoring.Insertion.insertNext`, `Authoring.Search.scanNeighbors`, exposed by `Library` |
| `Algorithms.*` older alternative executables | Explicit `Legacy.*` imports and namespace |
| Manual public executable binding | `ram_method` + `Method.VCs` + `VerifiedMethod` |

## Moved and consolidated modules

| Former path under RAM | Current path under RAM |
|---|---|
| `Paper/Basic.lean` | [Authoring/Semantics.lean](../Authoring/Semantics.lean) |
| `Paper/Syntax.lean` | [Authoring/Syntax.lean](../Authoring/Syntax.lean) |
| `Paper/Interface.lean` | [Authoring/Interface.lean](../Authoring/Interface.lean) |
| `Paper/Array.lean` | [Library/Insertion.lean](../Library/Insertion.lean) |
| `Paper/Search.lean` | [Library/Search.lean](../Library/Search.lean) |
| `Paper/Examples.lean` | [Programs/Examples.lean](../Programs/Examples.lean) |
| `Paper/InsertionSort.lean` | [Programs/Sorting.lean](../Programs/Sorting.lean) |
| `Paper/InsertionExecutable.lean` | [Programs/Sorting.lean](../Programs/Sorting.lean) |
| `Paper/BFS.lean` | [Programs/Connectivity.lean](../Programs/Connectivity.lean) |
| `Paper/BFSExecutable.lean` | [Programs/Connectivity.lean](../Programs/Connectivity.lean) |
| `Core/Runner.lean` | [Machine/Runner.lean](../Machine/Runner.lean) |
| `Core/Machine.lean` | [Machine/Machine.lean](../Machine/Machine.lean) |
| `Core/Output.lean` | [Machine/Output.lean](../Machine/Output.lean) |
| `Language/Compiler.lean` | [Backend/Language/Compiler.lean](../Backend/Language/Compiler.lean) |
| `Language/VC.lean` | [Backend/Language/VC.lean](../Backend/Language/VC.lean) |
| `Language/Normalization.lean` | [Backend/Language/Normalization.lean](../Backend/Language/Normalization.lean) |
| `Language/Interface.lean` | [Backend/Language/Interface.lean](../Backend/Language/Interface.lean) |
| `Language/Verification.lean` | [Backend/Language/Verification.lean](../Backend/Language/Verification.lean) |
| `Language/Syntax.lean` | [Backend/Language/Syntax.lean](../Backend/Language/Syntax.lean) |
| `Language/Refinement.lean` | [Backend/Language/Refinement.lean](../Backend/Language/Refinement.lean) |
| `Language/Basic.lean` | [Backend/Language/Basic.lean](../Backend/Language/Basic.lean) |
| `Proofs/BFS.lean` | [Backend/Certificates/BFS.lean](../Backend/Certificates/BFS.lean) |
| `Proofs/InsertionSort.lean` | [Backend/Certificates/InsertionSort.lean](../Backend/Certificates/InsertionSort.lean) |
| `Proofs/SortingSpec.lean` | [Backend/Certificates/SortingSpec.lean](../Backend/Certificates/SortingSpec.lean) |
| `Proofs/LoopVC.lean` | [Backend/Certificates/LoopVC.lean](../Backend/Certificates/LoopVC.lean) |
| `Internal/Insertion.lean` | [Backend/Adapters/Insertion.lean](../Backend/Adapters/Insertion.lean) |
| `Internal/InsertionInput.lean` | [Backend/Adapters/InsertionInput.lean](../Backend/Adapters/InsertionInput.lean) |
| `Internal/Search.lean` | [Backend/Adapters/Search.lean](../Backend/Adapters/Search.lean) |
| `Internal/SearchInput.lean` | [Backend/Adapters/SearchInput.lean](../Backend/Adapters/SearchInput.lean) |
| `Library/Framing.lean` | [Backend/Memory/Framing.lean](../Backend/Memory/Framing.lean) |
| `Library/Graph.lean` | [Backend/Memory/Graph.lean](../Backend/Memory/Graph.lean) |
| `Library/GraphMemory.lean` | [Backend/Memory/GraphMemory.lean](../Backend/Memory/GraphMemory.lean) |
| `Library/Array.lean` | [Backend/Memory/Array.lean](../Backend/Memory/Array.lean) |
| `Library/Sequences.lean` | [Backend/Memory/Sequences.lean](../Backend/Memory/Sequences.lean) |
| `Library/GraphInput.lean` | [Backend/Memory/GraphInput.lean](../Backend/Memory/GraphInput.lean) |
| `Algorithms/BFS.lean` | [Legacy/BFS.lean](../Legacy/BFS.lean) |
| `Algorithms/InsertionSort.lean` | [Legacy/InsertionSort.lean](../Legacy/InsertionSort.lean) |
| `Algorithms/Examples.lean` | [Legacy/Examples.lean](../Legacy/Examples.lean) |
| `Algorithms/LanguageExamples.lean` | [Legacy/LanguageExamples.lean](../Legacy/LanguageExamples.lean) |

## Earlier tutorial artifacts

The PDF tutorial and slide deck remain pinned historical artifacts for the earlier layout (`2c78e53` and preceding revisions). Their immutable GitHub source links still describe that version. The Lean companion has been migrated to current imports and names; use this map when comparing old screenshots or snippets with the current source.

Current source guides are [the layer overview](../README.md), [authoring](../Authoring/README.md), and [architecture](ARCHITECTURE.md). Algorithm proof and compiler semantics have not been weakened to perform this migration. The new method theorem derives its guarantees from the same checked execution chain.

## Unbundled logical credits

The current method syntax has no `time` field. Remove explicit `time` clauses and
the second RAM-payment branch of old verification proofs. `Action State` and
`Program State` are pure contracts; separate `ActionImplementation` and `Compilation`
certificates implement them. `method.certify proof` reconstructs those certificates.
See [Credits and backends](CREDITS-AND-BACKENDS.md) for the complete migration and
runnable proof-reuse example. The previously exported PDF and slides predate this
API change; use this guide and the checked Lean demos for current syntax.

## Pure frontend declarations

`ram method` now declares a `Specification`, not a backend-indexed `Method`. Import `Prototype.LogicalFrontend` and use `prove_algorithm` for a proof-only file. Attach a backend with `interface.realize name nameCorrect`. Existing `prove_ram` syntax still selects the default array backend. Pure mutable definitions moved to the `Authoring.Mutable` and `Authoring.MultipleArrays` namespaces; their backend modules retain their import paths. See [Generality and substitution](GENERALITY-AND-SUBSTITUTION.md).

## Owned, resource-aware composition

Use `Prototype.Composition.Language` for typed abstract clients and `Composition.Loom` for
reasoning. `Composition.Linking` and `Execution` are implementation-layer imports. Source
operations require separately registered `Primitive` and `TestImplementation` contracts;
`Linked` reconstructs structured composition. `Composition.Compatibility.ofProgram_vc`
transports existing Authoring proofs. Existing APIs remain available. See the
[owned composition guide](../Prototype/Composition/README.md) before migrating a backend:
locality and initial-potential accounting are additional required implementation evidence.
