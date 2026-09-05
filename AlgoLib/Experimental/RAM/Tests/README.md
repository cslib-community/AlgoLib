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
