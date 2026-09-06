# Regression checks

Run `lake build` for the repository and explicitly build these RAM regression modules when changing the stack:

```sh
lake build AlgoLib.Experimental.RAM.Tests.Paper \
  AlgoLib.Experimental.RAM.Tests.PaperAxioms \
  AlgoLib.Experimental.RAM.Tests.Methods \
  AlgoLib.Experimental.RAM.Tests.Language
```

`Paper` exercises canonical compiled sorting/BFS, logical framing, and rejected budgets. `PaperAxioms` rejects unexpected theorem axioms. `Methods` checks explicit input/output contracts, main-theorem use, and rejection of unpayable methods. `Algorithms` and `Language` retain the older low-level/compiler regressions as well; they are not additional canonical program locations.

The CI style job runs `python3 AlgoLib/Experimental/RAM/Tests/check_layers.py`. It checks local import cycles, missing modules, module documentation, and the public/backend dependency boundary.

The isolated [Loom-style prototype](../Prototype/README.md) adds `Prototype.Tests` and
`Prototype.Axioms`, both included in the repository build. They check compiled insertion-sort
execution, rejected contracts/annotations, and exact axiom lists for the observation, compiler
connection, VCG, reconstruction, and sorting theorems. Existing axiom expectations are unchanged.

Executable checks cover short lists with duplicates, all simple four-vertex graphs and sources, singleton and disconnected graphs, loops, and parallel edges. They compare against independent host reference implementations. Kernel-checked theorem statements, rather than these finite tests, establish the general correctness and cost claims.

## Credit/backend separation

`CreditLogic.lean` imports only the logical semantics. `BackendReuse.lean` reuses its
four-credit procedure proof with two verified implementations and checks 16/24 actual
RAM steps. `CreditAxioms.lean` guards concrete certificates as well as generic composition.
The layer checker prevents the logical core and this proof fixture from importing a backend.
Method tests check that preparation remains charged, while frontend tests reject a `time`
override and missing realizations cannot be turned into executables.

## Supported compilation and implementation substitution

`ArraySubstitution.lean` checks the same insertion-sort and array-zeroing proof with
contiguous storage and a pointer-table representation. It compares executable results
against reference outputs and checks the inferred RAM bounds. It also checks structural
support for nested constructs, rejection of an unsupported action in an unreachable
branch, and the direct Loom-WP-to-RAM theorem. `GeneralityAxioms.lean` guards the
generic compiler, that theorem, the indirect representation proofs, and both concrete
algorithm certificates. Both modules are included in `lake build`.

The layer checker also follows transitive imports from the logical frontend, Loom
reasoning, and the two algorithm proofs: none may depend on a RAM backend. See the
[construction and scope guide](../docs/GENERALITY-AND-SUBSTITUTION.md).

## Ownership and private-resource composition

`Composition.lean` tests the typed owned client linker, all four combinations of lazy/eager
buffer implementations, exact RAM counts, framed payload preservation, argument/result
transfer, nested loops, unsupported-operation rejection, overlapping ownership rejection,
and unchanged insertion-sort proof transport. `CompositionAxioms.lean` pins the generic
laws and concrete implementation dependencies. Both are part of `lake build`. The import
checker prevents the abstract buffer interface and client proof from importing implementations.
