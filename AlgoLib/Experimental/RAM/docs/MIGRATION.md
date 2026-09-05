# Migration to the unified stack

Use `import AlgoLib.Experimental.RAM` for programs, compiler contracts, and algorithm results. This refactor deliberately removes competing frontends rather than keeping deprecated executables indefinitely.

| Previous module/API | Current location/API |
|---|---|
| Shallow `RAM.Program`, `tick`, freely supplied `.steps` | Removed; use typed `Cmd`, `Contract`, and `Method` |
| Mathematical memory portion of `RAM.lean` | Internal `Proofs/SortingSpec.lean`, without a cost monad |
| `RAM.Machine`, `RAM.Runner`, `RAM.Interface` | `Core/Machine`, `Core/Runner`, `Core/Output` |
| `RAM.Source`, `RAM.Syntax`, `imperative` | Removed; `Language/Syntax`, `program { … }` |
| `RAM.InsertionSort` machine proof | Internal `Proofs/InsertionSort`; public `Algorithms/InsertionSort` |
| `BFS/Paper`, `graph_program`, old `BFS.run` and `Input.run` | Removed; public `Algorithms.BFS.run` executes the common typed DSL |
| BFS specification and graph bridge | `Specification/Graph`, `Specification/GraphBridge` |
| BFS memory, input encoding and edge constructors | `Library/GraphMemory`, `Library/GraphInput` |
| BFS scan, main-loop and initialization proofs | `Proofs/BFS` |
| `RAM.LoopVC` instruction proof rule | Internal `Proofs/LoopVC`; source VCG is `Language/VC` |
| `Language/Demo`, old algorithm demos | `Algorithms/LanguageExamples`, `Algorithms/Examples` |
| Old scattered tests | `Tests/Language`, `Tests/Algorithms` |

The old eight-register instruction constants are retained as internal invariant certificates. The public compiled programs contain ordinary named typed variables and compiler temporaries. Existing theorem namespaces for graph specifications and certificates remain to avoid needless theorem renaming; see the architecture ledger.

The reported demo costs increase because the common compiler charges typed expression evaluation explicitly. Compare current public `run` results with current source budgets, not with the old direct-instruction example counts.
