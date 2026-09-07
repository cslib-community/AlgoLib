# Interface status and evolution policy

New algorithms use `ram method`, `generate_obligations`, `prove_obligation`, and
`complete_algorithm`. Start with `SortingProgram` / `SortingSpec` / `SortingProofs`.
The generated Lean propositions are the proof interface; normalized goal lists are
not an alternative public API.

## Where to add a feature

| Status | Interfaces/modules | Responsibility |
| --- | --- | --- |
| Supported author interface | `LogicalFrontend`, `GeneratedObligations`, `ObligationExplorer`; `ram method`, `generate_obligations`, `prove_obligation`, `complete_algorithm`, `#named_goals`, `#explain_obligation`, `#proof_template` | Source programs and mathematical proofs |
| Supported convenience interface | `prove_algorithm … where`, `verify_array_method … where` | Sugar over the generated API; separate commands are preferred for editing |
| Supported backend interface | `Composition.Assembly`, `Encoding`, `EncoderLayout`, `Linking` | Reusable certified implementations and executable assembly |
| Maintained internal machinery | `Composition.Frontend/{Syntax,Resources,Expressions,Statements,Method}`, `NamedProofs`, `ProofGoals`, `contract_vc`, `contract_solve`, `paper_vc`, `paper_solve`, `prove_algorithm … by` | Elaboration, structural VC processing, and framework/library proofs; not the student authoring route |
| Deprecated regression interfaces | `LegacyArrayFrontend`, `Prototype.Frontend` (`legacy_ram`, `prove_ram`), earlier array/graph adapters | Preserve historical substitution/translation evidence; no new algorithm examples or features |
| Separate semantic research fixtures | `VelvetSemantics`, `ExecutableTranslation`, `RecursiveTranslation`, nondeterministic target modules | Keep independent semantic results; they are not interchangeable public frontends |

The internal `NamedProofs` module now only supplies structural splitting, source
metadata, and block syntax to the generated API. The old normalization-first
`named_proof_blocks`, `namedTree`, `#legacy_named_goals`, and `#paper_goals` interfaces
are removed. `ProofViews`/`ProofInputViews` name lists and tuple-arity inference are
also removed; typed `SourceShape` metadata is required.

The older proof-carrying array and ordinary-Velvet adapters are retained deliberately:
they carry different semantic/refinement tests, not merely aliases for the current
parser. Deleting them would discard evidence. Their maintenance status does not
expand the supported owned frontend to arbitrary Velvet, recursion, or aliasing.
Vendored Loom/Velvet and the Lean toolchain remain pinned to the versions used by
the checked proofs. “Modern interface” here means the current generated-API path,
not an unverified dependency upgrade.

## Stability guarantees

| Artifact | Stability and migration rule |
| --- | --- |
| `method.ObligationAPI.<scope>.<responsibility>.<clause>` | Stable for unchanged named scopes and clauses under source movement and automation changes. Renaming a scope/clause requires updating selectors and declaration references. |
| Frozen mathematical proposition | Authoritative checked statement. Changing the invariant, precondition, program semantics, or credit argument may change it and invalidate proofs. Stable names do not promise identical statements. |
| Assembly and completed procedure | Assembled only from checked evidence. Changed obligations require rechecking completion and downstream theorems. |
| Explicit source binding metadata | Roles come from the annotated source. Metadata is navigation information, never trusted proof evidence. |
| Local names and snapshot numbering | Presentation-level conveniences, not stable ABI. Changes to bindings, scope structure, or context simplification may require local proof-name edits. |
| Pretty-printing, hypothesis order, source positions, path count | Not stable identifiers; never select obligations by numeric position or match diagnostics as a semantic API. |
| Automatic status and suggested lemmas | May change with imports and library automation. No guarantee that a previously automatic obligation remains automatic. Its declaration is retained. |
| Inferred RAM bound | Sound upper bound for the selected backend, not a stable numerical constant. Compiler/data-structure changes can require updating polynomial-display lemmas. |

Before removing a supported command, provide its replacement, migrate maintained
examples, and retain equivalent positive/negative regression coverage. Record breaking
changes in this document and the author tutorial. Deprecation of an adapter permits
maintenance fixes, but does not authorize silently deleting its semantic theorems.

## Migration in this change

- Replace `#paper_goals` and `#legacy_named_goals` with `#named_goals`; use
  `#explain_obligation` for source roles and mathematical vocabulary.
- Replace a `named_proof_blocks` tactic inside a monolithic proof with generated
  propositions and separate `prove_obligation` commands, then `complete_algorithm`.
  `prove_algorithm … where` is available for compact examples.
- Stop reading `ProofViews` or counting product fields. Framework extensions consume
  `ProofShape` / `ProofInputShape`; ordinary proof authors need neither.

The conformance corpus runs through the supported source and compiler path. The
layer checker prevents reintroduction of the removed navigation interfaces and
checks that generated conformance fixtures agree with the independent oracle.

Failed proof blocks are checked in a fresh proof goal. Their theorem declaration is
installed only after complete evidence has been reconstructed and checked; command
error recovery must not leave a placeholder for completion to consume. The modern
negative tests check missing proofs, invalid evidence, unknown names, and overlap
without using the removed proof engine.

## Backend migration in progress

`Machine.Integer` is the checked foundation for replacing the Nat backend. It is
currently an internal migration API, not the default assembly or signed source
frontend. See [the exact milestone and remaining work](../../Machine/Integer/README.md).
Source `Nat` subtraction will remain saturating; backend replacement must not alter
its mathematical meaning. Machine costs may change and display lemmas must be rechecked.
