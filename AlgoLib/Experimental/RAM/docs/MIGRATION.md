# Module-path reorganization

The source tree now follows Language, Verification, Library, Implementations,
Compiler, Machine, and Examples. Historical adapters and research fixtures have
explicit homes. [The root guide](../README.md) explains the connections.

This is a module-path migration, not a theorem renaming. Existing declaration
namespaces (including `Prototype.Composition` and `Checked.Language`) remain stable.
Update `import` lines; existing fully qualified theorem names remain valid.
There are no forwarding modules at retired paths, so there is one canonical file
for each implementation. [The complete mapping](module-migration.json) records old
and new source paths; [the document mapping](document-migration.json) records guides.

| Previous entry | New entry |
| --- | --- |
| `Prototype.LogicalFrontend` | `Language.Frontend` |
| `Prototype.Composition.Language` | `Language.Program` |
| `Prototype.GeneratedObligations` | `Verification.GeneratedObligations` |
| `Prototype.Composition.Assembly` | `Compiler.Assembly` |
| `Backend.Native.*` | `Compiler.Native.*` |
| `Prototype.Composition.SortingProgram` | `Examples.InsertionSort.Program` |
| `Prototype.Composition.SortingSpec` | `Examples.InsertionSort.Obligations` |
| `Prototype.Composition.SortingProofs` | `Examples.InsertionSort.Proofs` |
| `Prototype.Composition.Sorting` | `Examples.InsertionSort.MinimumCaller` |
| `Prototype.Composition.SortingExecution` | `Examples.InsertionSort.Execution` |
| `Prototype.Composition.BreadthFirstProgram` | `Examples.BFS.Program` |
| `Prototype.Composition.BreadthFirstSpec` | `Examples.BFS.Obligations` |
| `Prototype.Composition.BFSExecution` | `Examples.BFS.Execution` |

Prefixes in this table are relative to `AlgoLib.Experimental.RAM`.
Proof proposition identities, source syntax, credit contracts, and runtime semantics
are unchanged. Performance configurations, conformance generators, build imports,
and cache-reuse checks follow the new paths. Archived tutorials are marked historical;
new authoring starts at Examples rather than the old Programs directory.

The umbrella `import AlgoLib.Experimental.RAM` now imports the modern sorting and
BFS execution interfaces. Code using the earlier `Programs.Sorting` or
`Programs.Connectivity` declarations must explicitly import
`AlgoLib.Experimental.RAM.Historical.Programs.Sorting` or
`AlgoLib.Experimental.RAM.Historical.Programs.Connectivity`. Their declarations
remain available; they are no longer the public starting point.

## Contracts and verification responsibilities

`Language.Contracts` now contains only public mathematical contracts, uniform
allowances, and borrowing queries. Internal users of source metadata import
`Verification.SourceMetadata`; users of `Plan`/`Plan.sound` import `Verification.Plan`;
users of `Algorithm`/`Algorithm.certify` import `Verification.Algorithm`.
Declaration names and proof bodies are unchanged. The convenient public
`Language.Frontend` and `Language.Owned` imports continue to provide the author API.

The empty `Examples.BFS.Theorems` forwarding module was removed. Import
`Examples.BFS.Proofs` for the completed abstract procedure, or
`Examples.BFS.Execution` for the executable and final RAM theorems. The example
README remains the single reading-order entry point.

## Shared definitions and preferred public names

Register identifiers moved to Machine.Registers. Bitmap/Execution observations
were extracted to Machine.Output. Stateless natural arithmetic moved to
Language.Model.NatArithmetic. The NatEmbedding theorem moved to
Historical.Adapters.NatEmbedding; old instruction proofs remain in Historical.
Supported implementations no longer obtain natural compilation through an implicit
Historical import. Historical clients import their old compiler explicitly.

Each layer now has a preferred `AlgoLib.Experimental.RAM.<Layer>` import and
layer-aligned public aliases. This is a staged alias migration: original declaration
names remain valid. See [the public API policy](PUBLIC-API.md) and
[the generated name mapping](PUBLIC-NAMES.md).
