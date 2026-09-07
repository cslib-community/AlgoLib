# Compiler: verified linking and integer lowering

**Preferred public import:** `AlgoLib.Experimental.RAM.Compiler`.
See [public names and stability](../docs/PUBLIC-API.md); narrower module links below explain internals.

| Entry | Responsibility |
| --- | --- |
| [Assembly](Assembly.lean) ([interface guide](Assembly/README.md)) | Public `compile_scalar_method`, `compile_array_method`, and split backend/completion commands |
| [Assembly/Native](Assembly/Native/) | Native instances of linking and executable correctness |
| [Assembly/Natural](Assembly/Natural/) | Maintained natural-valued implementation adapters using the integer target |
| [Native](Native/README.md) | Typed implementation commands, independent semantics, lowering proofs, and executable transport |

The compiler consumes an abstract verified procedure plus certified operation
implementations. Structural linking reconstructs ownership and resource certificates.
Native lowering produces `Integer.Code`; `Native.Eval.compile` connects source
execution to instruction execution, and `Native.run_eq` connects the real runner.

Logical credits and instruction costs are distinct. Assembly derives a sound
physical bound from implementation rates/potential. This is a bound, not necessarily
the exact cost of an individual input. Unsupported operations do not become
executable merely by declaring a cheap logical charge.

Compiler.Native does not transitively import the retired Nat compiler or runner.
The structural regression enforces this alongside the backend-free proof boundary.
See [the complete stack](../README.md).

Standard assembly imports only the frontend, shared certificate tactics, and native
execution. Natural-valued compatibility packages are explicit opt-in imports.
The shared result type and tactics live under Assembly, outside either representation.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

**Preferred import:** `AlgoLib.Experimental.RAM.Compiler`.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Compiler](../Compiler.lean) | public | Compiler: supported public entry point |
| [Assembly.lean](Assembly.lean) | public | Assemble an executable and its correctness/cost theorem |
| [Assembly/Native/Execution.lean](Assembly/Native/Execution.lean) | internal | Native execution of certified source procedures |
| [Assembly/Native/Linking.lean](Assembly/Native/Linking.lean) | internal | Native ownership-aware linking |
| [Assembly/Natural/CertifiedExecutable.lean](Assembly/Natural/CertifiedExecutable.lean) | compatibility | Certified executable package for natural-valued implementation contracts |
| [Assembly/Natural/Execution.lean](Assembly/Natural/Execution.lean) | compatibility | Link once, execute actual RAM, recover ordinary mathematical outputs |
| [Assembly/Natural/IntegerExecution.lean](Assembly/Natural/IntegerExecution.lean) | compatibility | Owned procedure contracts linked to native integer execution |
| [Assembly/Natural/Linking.lean](Assembly/Natural/Linking.lean) | compatibility | Resource-aware, ownership-preserving client linking |
| [Assembly/Result.lean](Assembly/Result.lean) | internal | Observed execution result |
| [Assembly/Tactics.lean](Assembly/Tactics.lean) | internal | Shared certificate reconstruction tactics |
| [Native/Basic.lean](Native/Basic.lean) | internal | Native integer implementation language |
| [Native/Compiler.lean](Native/Compiler.lean) | internal | Native integer compilation |
| [Native/Execution.lean](Native/Execution.lean) | internal | Executing certified native programs |
| [Native/Expressions.lean](Native/Expressions.lean) | internal | Verified native integer expression compilation |
| [Native/Natural.lean](Native/Natural.lean) | internal | Reusing natural implementation certificates with native compilation |
| [Native/Ownership.lean](Native/Ownership.lean) | internal | Ownership of native integer storage |

<!-- END GENERATED MODULE INDEX -->
