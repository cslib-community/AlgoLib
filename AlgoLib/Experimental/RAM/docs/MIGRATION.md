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

## Paper-proof authoring revision

The recommended entry point is now `Paper/Examples.lean` and `Paper/README.md`.

| Earlier API | Recommended API |
|---|---|
| `Algorithms.InsertionSort.run xs` (`.values`) | `Paper.Insertion.run xs` (`.value`) |
| `Algorithms.BFS.run input` (`.visited`) | `Paper.BFS.run input` (`.value`) |
| Algorithm-specific source/certificate transport | `LoopProof` + `paper_steps` + `paper_credits` |
| Manual method/compiler assembly | `Interface.run` and `Interface.correct` |
| Ad hoc array/graph frame proof | Registered footprints and `Framing.frame` |

Earlier names are retained to avoid breaking clients and to preserve comparison regressions. New algorithm proofs should not copy their low-level verification bodies. The public paper proofs use local operation contracts and do not invoke the old whole-algorithm correctness theorems. Conservative cost constants differ; use the theorem belonging to the executable you run.
