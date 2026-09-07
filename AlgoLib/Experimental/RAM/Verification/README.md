# Verification: mathematical proof authoring

**Preferred public import:** `AlgoLib.Experimental.RAM.Verification`.
See [public names and stability](../docs/PUBLIC-API.md); narrower module links below explain internals.

Use [the obligation API and explorer](OBLIGATION-API.md) to understand and prove a
single source obligation. Use [the policy](API-POLICY.md) to understand which names
are stable. The older [named-block tutorial](NAMED-PROOFS.md) is convenience syntax;
separate generated declarations are preferred for interactive editing.

| Module | Responsibility |
| --- | --- |
| [SourceMetadata](SourceMetadata.lean) | Stable obligation wrappers, quantified source roles, and typed source shapes |
| [Plan](Plan.lean) | Indexed annotations, compositional VCs, and Plan.sound |
| [Algorithm](Algorithm.lean) | Annotated method interface, obligations, and completion into a verified procedure |
| [GeneratedObligations](GeneratedObligations.lean) | Generate proposition declarations and assemble checked proof evidence |
| [ObligationExplorer](ObligationExplorer.lean) | Focused contexts, source metadata, proof scaffolding, lemma discovery |
| [NamedProofs](NamedProofs.lean) | Internal structural splitting and named-block machinery |
| [ProofGoals](ProofGoals.lean) | Internal source-level goal views |
| [Loom](Loom.lean) | Composition-preserving interpretation of the owned program in actual Loom WP |
| [Semantics](Semantics/) | Costed observations and the shared logical/Loom interpretation |

The proof API sits above the Language semantics and remains independent of RAM
representations. Solving initialization, preservation, termination, and accounting
obligations produces a verified procedure. The compiler consumes its certificate;
users do not prove instruction simulations.

Loom is a reasoning interpretation, not a compiler pass. Compilation and Loom
reasoning are connected through the same abstract execution/contracts.
See [the complete sorting proof](../Examples/InsertionSort/Proofs.lean).

Framework reading order: SourceMetadata → Plan → Algorithm → GeneratedObligations.
Authors keep the single Language.Frontend import and the same proof commands.
Library authors need only Language.Contracts; they do not load this machinery.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

**Preferred import:** `AlgoLib.Experimental.RAM.Verification`.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Verification](../Verification.lean) | public | Verification: supported public entry point |
| [Algorithm.lean](Algorithm.lean) | internal | Annotated algorithms and completion |
| [GeneratedObligations.lean](GeneratedObligations.lean) | public | Generated, persistent obligation declarations |
| [Loom.lean](Loom.lean) | internal | Composition-preserving interpretation in actual Loom |
| [NamedProofs.lean](NamedProofs.lean) | internal | Structural obligation decomposition (internal) |
| [ObligationExplorer.lean](ObligationExplorer.lean) | public | Source-level obligation explorer |
| [Plan.lean](Plan.lean) | internal | Indexed verification plans and their soundness |
| [ProofGoals.lean](ProofGoals.lean) | internal | Mathematical verification-goal normalization |
| [Semantics/LogicalInterpretation.lean](Semantics/LogicalInterpretation.lean) | internal | Backend-independent logical interpretation |
| [Semantics/LogicalVerification.lean](Semantics/LogicalVerification.lean) | internal | Proof annotations and generated conditions |
| [Semantics/LoomObservation.lean](Semantics/LoomObservation.lean) | internal | The RAM observation as an actual Loom algebra |
| [Semantics/Observation.lean](Semantics/Observation.lean) | internal | A costed observation for the Loom algebra |
| [Semantics/Procedures.lean](Semantics/Procedures.lean) | internal | Typed, compositional procedures over certified data-structure interfaces |
| [SourceMetadata.lean](SourceMetadata.lean) | internal | Source identities and mathematical context metadata |

<!-- END GENERATED MODULE INDEX -->
