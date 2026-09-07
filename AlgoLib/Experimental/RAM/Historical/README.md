# Historical adapters and regression evidence

This directory is **not a supported authoring entry point**. New programs use
[Language.Frontend](../Language/Frontend.lean) and the [modern examples](../Examples/README.md).

- `NatMachine` and `NatCompiler`: retired natural instruction semantics/compiler,
  preserved as reference and migration evidence. Shared register names and output values now live in Machine; shared natural
  arithmetic lives in Language/Model. Supported code does not import this directory.
- `Authoring`, `Programs`, `Library`, `Legacy`, `Backend`: earlier certified-operation
  frontend and algorithm adapters. Their maintained runners now target Int-RAM.
- `Prototype`: older array/graph adapters, supported-language and substitution
  certificates, and their historical regression fixtures.
- `Adapters`: compatibility theorems between logical interfaces.
- `Guides`: archived tutorials, slides, and PDFs. These describe their historical
  snapshot and are not the current onboarding path.

These files are retained because they contain distinct checked evidence, not
because users should choose among multiple public frontends. Internal maintained
natural-valued implementation views live in Implementations/Natural. Separate
ordinary-Velvet semantics experiments live in Research.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Adapters/CreditCompatibility.lean](Adapters/CreditCompatibility.lean) | historical | Preserve existing frontend programs and logical proofs |
| [Adapters/InstructionRefinement.lean](Adapters/InstructionRefinement.lean) | historical | Instruction-certificate refinement |
| [Adapters/NatEmbedding.lean](Adapters/NatEmbedding.lean) | historical | Migration of natural-number RAM to integer RAM |
| [Authoring/Interface.lean](Authoring/Interface.lean) | historical | Certified input preparation and output observation |
| [Authoring/Methods.lean](Authoring/Methods.lean) | historical | Procedures with explicit input, output, and logical credit contracts |
| [Backend/Adapters/Insertion.lean](Backend/Adapters/Insertion.lean) | historical | Insertion representation adapter |
| [Backend/Adapters/InsertionInput.lean](Backend/Adapters/InsertionInput.lean) | historical | Array input/output adapter |
| [Backend/Adapters/Search.lean](Backend/Adapters/Search.lean) | historical | Graph traversal representation adapter |
| [Backend/Adapters/SearchInput.lean](Backend/Adapters/SearchInput.lean) | historical | Graph/source input/output adapter |
| [Backend/Certificates/BFS.lean](Backend/Certificates/BFS.lean) | historical | Graph traversal implementation certificates |
| [Backend/Certificates/InsertionSort.lean](Backend/Certificates/InsertionSort.lean) | historical | Instruction-level insertion certificates |
| [Backend/Certificates/LoopVC.lean](Backend/Certificates/LoopVC.lean) | historical | Machine-level loop certificate rule |
| [Backend/Certificates/SortingSpec.lean](Backend/Certificates/SortingSpec.lean) | historical | Insertion mathematics for certificates |
| [Backend/Realization.lean](Backend/Realization.lean) | historical | Separate RAM realizations of logical credit contracts |
| [Guides/StudentDemo.lean](Guides/StudentDemo.lean) | historical | Tutorial companion for the current layer layout |
| [Legacy/BFS.lean](Legacy/BFS.lean) | historical | Legacy demonstration: BFS |
| [Legacy/Examples.lean](Legacy/Examples.lean) | historical | Legacy demonstration: Examples |
| [Legacy/InsertionSort.lean](Legacy/InsertionSort.lean) | historical | Legacy demonstration: InsertionSort |
| [Legacy/LanguageExamples.lean](Legacy/LanguageExamples.lean) | historical | Legacy demonstration: LanguageExamples |
| [Library/Insertion.lean](Library/Insertion.lean) | historical | Public insertion contracts |
| [Library/Search.lean](Library/Search.lean) | historical | Public graph traversal contracts |
| [NatCompiler/Compiler.lean](NatCompiler/Compiler.lean) | historical | Typed source-to-RAM compiler |
| [NatMachine/Machine.lean](NatMachine/Machine.lean) | historical | RAM machine and costed execution |
| [NatMachine/Output.lean](NatMachine/Output.lean) | historical | Shared output views and historical register framing |
| [NatMachine/Runner.lean](NatMachine/Runner.lean) | historical | Historical natural-machine reference evaluator |
| [Programs/Connectivity.lean](Programs/Connectivity.lean) | historical | Connectivity: specification → BFS method → obligations → theorem |
| [Programs/Examples.lean](Programs/Examples.lean) | historical | Run the canonical methods |
| [Programs/Sorting.lean](Programs/Sorting.lean) | historical | Sorting: specification → method → obligations → theorem |
| [Prototype/ArraySubstitution.lean](Prototype/ArraySubstitution.lean) | historical | Unchanged algorithms and proofs across two array implementations |
| [Prototype/Axioms.lean](Prototype/Axioms.lean) | historical | Axiom regression checks for the actual Loom/Velvet integration |
| [Prototype/BFS.lean](Prototype/BFS.lean) | historical | BFS by procedure composition: graph input → reachable set → connectivity |
| [Prototype/ExecutionBridge.lean](Prototype/ExecutionBridge.lean) | historical | Public execution witness for compiled method interfaces |
| [Prototype/FrameworkTests.lean](Prototype/FrameworkTests.lean) | historical | Regression checks for the actual upstream framework integration |
| [Prototype/Frontend.lean](Prototype/Frontend.lean) | historical | Compatibility backend for historical array methods |
| [Prototype/Graph.lean](Prototype/Graph.lean) | historical | Graph primitives and reusable adjacency-scan procedures |
| [Prototype/GraphTests.lean](Prototype/GraphTests.lean) | historical | Executable and negative tests for graph procedure composition |
| [Prototype/IndirectArrays.lean](Prototype/IndirectArrays.lean) | historical | A second implementation of the pure mutable-array interface |
| [Prototype/InsertionSort.lean](Prototype/InsertionSort.lean) | historical | Default execution adapter for the pure insertion-sort algorithm |
| [Prototype/Interpretation.lean](Prototype/Interpretation.lean) | historical | RAM compilation of the independently defined logical interpretation |
| [Prototype/LegacyArrayFrontend.lean](Prototype/LegacyArrayFrontend.lean) | historical | Frozen compatibility frontend for earlier array proofs |
| [Prototype/MultipleArrayTests.lean](Prototype/MultipleArrayTests.lean) | historical | Multiple-array frontend and frame regressions |
| [Prototype/MultipleArrays.lean](Prototype/MultipleArrays.lean) | historical | Independently mutable arrays with automatic cross-array framing |
| [Prototype/Mutable.lean](Prototype/Mutable.lean) | historical | Implementation of mutable variables and array operations |
| [Prototype/SortingAlgorithm.lean](Prototype/SortingAlgorithm.lean) | historical | Insertion sort with mutable arrays and inline loop invariants |
| [Prototype/SupportedCompilation.lean](Prototype/SupportedCompilation.lean) | historical | Every supported program: actual Loom correctness to actual RAM execution |
| [Prototype/Tests.lean](Prototype/Tests.lean) | historical | Executable and negative-contract tests for the mutable frontend |
| [Prototype/Verification.lean](Prototype/Verification.lean) | historical | Attaching a RAM backend to logical verification conditions |
| [Prototype/ZeroAlgorithm.lean](Prototype/ZeroAlgorithm.lean) | historical | A linear array algorithm proved without selecting a backend |

<!-- END GENERATED MODULE INDEX -->
