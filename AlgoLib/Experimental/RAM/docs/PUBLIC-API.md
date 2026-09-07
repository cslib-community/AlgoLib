# Public imports, names, and evolution policy

## Choose one entry point for your task

| Task | Preferred import | Preferred namespace |
| --- | --- | --- |
| Write a source method | `AlgoLib.Experimental.RAM.Language` | `Language` |
| Extend or inspect verification | `AlgoLib.Experimental.RAM.Verification` | `Verification` |
| Use data-structure contracts | `AlgoLib.Experimental.RAM.Library` | `Library.Queue`, `Library.Buffer`, `Library.GraphCursor` |
| Implement owned native storage | `AlgoLib.Experimental.RAM.Implementations` | `Implementations` |
| Assemble a native executable | `AlgoLib.Experimental.RAM.Compiler` | `Compiler` |
| Inspect or execute instructions | `AlgoLib.Experimental.RAM.Machine` | `Machine` |
| Run the complete algorithms | `AlgoLib.Experimental.RAM.Examples` | `Examples.InsertionSort`, `Examples.BFS` |

Namespaces in this table are below `AlgoLib.Experimental.RAM`. Method commands and
named proof commands are unchanged. For example:

```lean
import AlgoLib.Experimental.RAM.Examples
open AlgoLib.Experimental.RAM
#eval (Examples.InsertionSort.run [3, 1, 2]).value
#check Examples.InsertionSort.main
#check Examples.BFS.connected
#check Examples.BFS.linear
```

## Staged namespace migration

This release introduces **preferred public aliases**, not a blanket renaming of
implementation declarations. `Language.Program`, `Verification.Plan`, and the
other [public names](PUBLIC-NAMES.md) resolve to the existing checked definitions.
`Prototype.Composition` and `Integer` spellings remain compatible. Do not rewrite
working proofs just to follow a directory move. New documentation and clients should
use the layer-aligned names where provided; advanced internal names are not all
promoted to the public API.

The public aliases are exported by the layer entry modules. Narrow implementation
imports do not promise to install those aliases. Original narrow imports that were
previously documented remain supported during migration. Compatibility import paths
are explicit in the module inventory. No removal date is imposed in this release.

A future rename/removal requires: a canonical replacement, migration documentation,
updated maintained examples, preservation of semantic/axiom coverage, and a release
notice before compatibility spellings are removed. Aliases must continue to denote
the same definition; they must not silently acquire different credit or runtime semantics.

`Tests/PublicAPI.lean` executes a signed method and both algorithms using public
imports without historical namespaces. `Tests/PublicCompatibility.lean` checks
that old and new spellings are definitionally equal.

## Module status

`docs/modules.json` assigns every module one status and a layer. There is exactly
one preferred entry point per supported layer.

- **public:** supported author/library interface; entrypoint marks the preferred import.
- **internal:** implementation detail; direct imports may change with a documented refactor.
- **compatibility:** maintained natural-valued implementation view, with explicit imports.
- **historical:** old adapters and regression evidence, not a new-algorithm frontend.
- **research:** separately scoped semantic experiments.
- **test:** validation fixtures.

A public import can depend on internal modules; the status describes the promise to
clients, not access control. Metadata never serves as proof evidence.

## Keep navigation current

Run `python3 AlgoLib/Experimental/RAM/Tests/generate_navigation.py` after changing
module ownership, status, exports, imports, or module documentation. Generated
README inventories and [dependency diagrams](DEPENDENCIES.md) come from that data.
The conceptual explanations outside generated markers remain handwritten. CI runs
`--check`, rejecting missing metadata and stale generated sections. The layer check
also enforces that supported modules do not import Historical or Research.
