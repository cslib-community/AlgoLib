# Language: programs and annotations

**Preferred public import:** `AlgoLib.Experimental.RAM.Language`.
See [public names and stability](../docs/PUBLIC-API.md); narrower module links below explain internals.

**Author entry:** import `AlgoLib.Experimental.RAM.Language`.
Start with [insertion sort](../Examples/InsertionSort/README.md).

| Module | Responsibility |
| --- | --- |
| [Frontend](Frontend.lean) | Public `ram method` command and input/output syntax |
| [Program](Program.lean) | `Operation`, typed `Program A B`, logical `Run`, and basic VC soundness |
| [Contracts](Contracts.lean) | `Contract`, public procedure summaries, uniform logical allowances, and borrowing queries |
| [Expressions](Expressions.lean) | Mathematical expression semantics and logical charges |
| [Elaboration](Elaboration.lean) / [Elaboration/](Elaboration/) | Internal syntax, resource lookup, expressions, statements, and method construction |
| [Owned](Owned.lean) | Convenience import of owned language and reasoning |
| [Model](Model/) | Shared mathematical state/credit models used by the Loom interpretation and maintained adapters |

The public frontend imports the verification command interface for convenience.
The underlying program semantics are backend-free. Do not add RAM registers or
memory encodings to a source operation contract. A new executable operation needs
an implementation certificate in Implementations, not just an arbitrary Lean callback.

The elaborator creates a body and a plan for that body. Verification generates
named mathematical obligations; Compiler assembly later chooses representations.
Read [syntax](FRONTEND.md), [loop accounting](PAPER-LOOPS.md),
[signed values](SIGNED-INTEGERS.md), and [the root architecture](../README.md).

Contracts and Expressions import no Verification modules. The elaboration layer
explicitly imports Verification.Algorithm when it constructs annotated methods.
Proof plans and their soundness belong to Verification, not to library contracts.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

**Preferred import:** `AlgoLib.Experimental.RAM.Language`.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Language](../Language.lean) | public | Language: supported public entry point |
| [Contracts.lean](Contracts.lean) | internal | Public mathematical procedure contracts |
| [Elaboration.lean](Elaboration.lean) | internal | Owned mutable frontend: stable import |
| [Elaboration/Expressions.lean](Elaboration/Expressions.lean) | internal | Expression and condition elaboration |
| [Elaboration/Method.lean](Elaboration/Method.lean) | internal | Method declaration assembly |
| [Elaboration/Resources.lean](Elaboration/Resources.lean) | internal | Elaboration state and ownership routing |
| [Elaboration/Statements.lean](Elaboration/Statements.lean) | internal | Structured statements and loop annotations |
| [Elaboration/Syntax.lean](Elaboration/Syntax.lean) | internal | Surface grammar and public contract selection |
| [Expressions.lean](Expressions.lean) | internal | Expressions over separately owned values |
| [Frontend.lean](Frontend.lean) | public | Public mutable method frontend |
| [Model/ArrayFacts.lean](Model/ArrayFacts.lean) | internal | Reusable mathematical array substitution |
| [Model/Contracts.lean](Model/Contracts.lean) | internal | Backend-independent input/output algorithms and credit contracts |
| [Model/MultipleArrays.lean](Model/MultipleArrays.lean) | internal | Pure language for multiple mutable arrays |
| [Model/Mutable.lean](Model/Mutable.lean) | internal | Pure mutable-array language and logical credits |
| [Model/NatArithmetic.lean](Model/NatArithmetic.lean) | internal | Shared natural arithmetic operations |
| [Model/Semantics.lean](Model/Semantics.lean) | internal | Authoring semantics and proof rules |
| [Model/Syntax.lean](Model/Syntax.lean) | internal | Authoring syntax and credit automation |
| [Owned.lean](Owned.lean) | public | Public proof vocabulary for compositional clients |
| [Program.lean](Program.lean) | internal | Typed clients of abstract, owned interfaces |

<!-- END GENERATED MODULE INDEX -->
