# Validation and regression checks

From the repository root:

```sh
lake build
python3 AlgoLib/Experimental/RAM/Tests/check_layers.py
python3 AlgoLib/Experimental/RAM/Tests/check_elaboration.py
python3 AlgoLib/Experimental/RAM/Tests/check_proof_edit.py
```

Run builds and the proof-edit benchmark sequentially. The latter temporarily edits
and restores the sorting proof, including on failure; do not edit that file concurrently.

- Full build: Lean proofs, executable examples, rejection tests and guarded axiom checks.
- Navigation check (included in the layer check): canonical module homes, working documentation links/imports, and complete example entry pages.
- Layer check: import DAG, logical/backend boundary, no private queue unfolding in
  BFS assembly, no retired target in author-facing witnesses, generated conformance consistency.
- [Conformance](Conformance/README.md): independent bounded reference evaluator versus
  compiled executions, including signed cases and explicit rejection tests.
- `EncoderLayout`, `OwnedBFS`, `OwnedQueues`: layout and implementation substitution.
- `ObligationAPI`: stable identities, source contexts, explorer and rejection coverage.
- Elaboration benchmark: fresh checking of representative modules against configured budgets.
- Proof-edit benchmark: successful and failing proof edits reuse specification/backend artifacts.

Tests supplement kernel-checked theorems; bounded comparisons do not establish a
universal semantics theorem for all source syntax.

Native assembly is checked transitively to exclude natural implementation adapters.
CompatibilityAxioms imports those adapters explicitly and preserves their axiom
guards; SignedAxioms and IntegerFrontend check the native path independently.

PublicAPI runs source and example clients through the seven public layer imports.
PublicCompatibility checks definitional equality of preferred and older names.
`generate_navigation.py --check` checks module metadata and generated documentation;
`test_navigation.py` rejects missing records, wrong ownership/exports, and stale indexes
in a temporary tree without editing the checkout. Both run through `check_layers.py`.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Algorithms.lean](Algorithms.lean) | test | Regression checks: Algorithms |
| [ArraySubstitution.lean](ArraySubstitution.lean) | test | Executable substitution and supported-language regressions |
| [BackendReuse.lean](BackendReuse.lean) | test | One logical proof, two executable RAM backends |
| [CompatibilityAxioms.lean](CompatibilityAxioms.lean) | test | Trust guards for explicit compatibility implementation contracts |
| [Composition.lean](Composition.lean) | test | Composition regression suite |
| [CompositionAxioms.lean](CompositionAxioms.lean) | test | Trust checks for local ownership, private resources, and concrete client linking |
| [Conformance/Generated.lean](Conformance/Generated.lean) | test | Generated frontend conformance corpus |
| [Conformance/Rejections.lean](Conformance/Rejections.lean) | test | Rejected source programs |
| [Conformance/Signed.lean](Conformance/Signed.lean) | test | Signed differential frontend tests |
| [ContractFrontend.lean](ContractFrontend.lean) | test | End-to-end contract/frontend regressions |
| [CreditAxioms.lean](CreditAxioms.lean) | test | Trust checks for unbundled credits and reconstructed compilation |
| [CreditLogic.lean](CreditLogic.lean) | test | A reusable algorithm proof with no RAM dependency |
| [EncoderLayout.lean](EncoderLayout.lean) | test | Private-layout substitution through unchanged BFS assembly |
| [GeneralityAxioms.lean](GeneralityAxioms.lean) | test | Exact trust checks for supported compilation and implementation substitution |
| [IntegerFrontend.lean](IntegerFrontend.lean) | test | Default frontend executes integer instructions |
| [IntegerRAM.lean](IntegerRAM.lean) | test | Signed execution and natural-number migration regressions |
| [Language.lean](Language.lean) | test | Regression checks: Language |
| [Methods.lean](Methods.lean) | test | Explicit method contracts: acceptance and rejection tests |
| [MixedAxioms.lean](MixedAxioms.lean) | test | Trust regression for the unified frontend and actual linked executions |
| [MixedFrontend.lean](MixedFrontend.lean) | test | Mixed scalar, array and owned-procedure regression |
| [NamedAssembly.lean](NamedAssembly.lean) | test | Named proof blocks through final executable assembly |
| [NamedProofs.lean](NamedProofs.lean) | test | Regression tests for independently checked proof blocks |
| [NativeArrays.lean](NativeArrays.lean) | test | Native array storage through ordinary frontend assembly |
| [NativeCompiler.lean](NativeCompiler.lean) | test | Native compiler regression |
| [NativeSourceFrontend.lean](NativeSourceFrontend.lean) | test | Existing source frontend linked to single-cell native signed storage |
| [ObligationAPI/Explorer.lean](ObligationAPI/Explorer.lean) | test | Explorer navigation and evidence boundaries |
| [ObligationAPI/ExplorerExamples.lean](ObligationAPI/ExplorerExamples.lean) | test | Sorting and BFS explorer acceptance |
| [ObligationAPI/Proofs.lean](ObligationAPI/Proofs.lean) | test | Proofs against an imported generated API |
| [ObligationAPI/Regression.lean](ObligationAPI/Regression.lean) | test | Stable identities and checked explicit evidence |
| [ObligationAPI/SourceContext.lean](ObligationAPI/SourceContext.lean) | test | Source contexts use explicit roles and product routes |
| [ObligationAPI/Specification.lean](ObligationAPI/Specification.lean) | test | Specification-only obligation API fixture |
| [OwnedBFS.lean](OwnedBFS.lean) | test | One BFS proof, two actual RAM queue implementations |
| [OwnedBFSAxioms.lean](OwnedBFSAxioms.lean) | test | Trust audit for owned BFS and implementation substitution |
| [OwnedQueues.lean](OwnedQueues.lean) | test | Actual RAM substitution tests for two FIFO implementations |
| [Paper.lean](Paper.lean) | test | Regression checks: Paper |
| [PaperAxioms.lean](PaperAxioms.lean) | test | Regression checks: PaperAxioms |
| [PaperLoopAxioms.lean](PaperLoopAxioms.lean) | test | Trust guards for paper loop accounting and generated executables |
| [PaperLoops.lean](PaperLoops.lean) | test | Acceptance tests for the paper loop interface |
| [PublicAPI.lean](PublicAPI.lean) | test | Public layer imports and canonical names |
| [PublicCompatibility.lean](PublicCompatibility.lean) | test | Canonical public aliases preserve existing clients |
| [SignedAxioms.lean](SignedAxioms.lean) | test | Trusted dependencies of signed source compilation |
| [SignedFrontend.lean](SignedFrontend.lean) | test | Signed source arithmetic on the certified Int-RAM runner |
| [SignedOwnership.lean](SignedOwnership.lean) | test | Composition of separately owned signed arrays |
| [SignedRejections.lean](SignedRejections.lean) | test | Signed typing and safety rejection regressions |
| [WorkAccounting.lean](WorkAccounting.lean) | test | Negative checks for remaining-work annotations |

<!-- END GENERATED MODULE INDEX -->
