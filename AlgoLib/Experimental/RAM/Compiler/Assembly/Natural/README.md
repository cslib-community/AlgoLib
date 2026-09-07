# Compiler / Assembly / Natural

Internal modules of the [Compiler layer](../../README.md).
See [the full architecture](../../../README.md) before following lower-level imports.

| Module | Responsibility |
| --- | --- |
| [Execution](Execution.lean) | Link once, execute actual RAM, recover ordinary mathematical outputs |
| [IntegerExecution](IntegerExecution.lean) | Owned procedure contracts linked to native integer execution |
| [Linking](Linking.lean) | Resource-aware, ownership-preserving client linking |

[CertifiedExecutable](CertifiedExecutable.lean) packages this implementation interface.
Import it explicitly when constructing an executable from natural-valued encoders.
Standard scalar/array method commands do not depend on this directory.
