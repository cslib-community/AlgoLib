# Assembly: choose the interface for the task

For standard source methods, import `AlgoLib.Experimental.RAM.Compiler.Assembly`.
The commands `compile_scalar_method`, `compile_array_backend`,
`compile_array_method`, and `verify_array_method` use native storage and execution.
They do not load natural-valued implementation adapters or paired signed layouts.

| Module | Responsibility |
| --- | --- |
| [Tactics](Tactics.lean) | `ram_link` and `ram_code_eq`: backend-independent certificate reconstruction |
| [Result](Result.lean) | Shared value/instruction-count carrier; no representation or execution policy |
| [Native/Execution](Native/Execution.lean) | Run and prove correctness of a native linked procedure |
| [Native/Linking](Native/Linking.lean) | Native instance of the generic ownership/resource linking contracts |
| [Natural/CertifiedExecutable](Natural/CertifiedExecutable.lean) | Explicit package for maintained natural-valued implementation contracts |

A native frontend user needs only the public command import. A library author using
natural-valued implementation views imports that interface explicitly. Both execute
Int-RAM, but they do not need to load each other's representations.

`CertifiedExecutable` retains its existing declaration namespace and theorem names.
Its import is now `AlgoLib.Experimental.RAM.Compiler.Assembly.Natural.CertifiedExecutable`;
it is not implicitly provided by standard native assembly.

The layer regression checks the transitive dependency graph, including the sorting
backend. Shared Tactics and Result modules must have no RAM-stack dependencies.
