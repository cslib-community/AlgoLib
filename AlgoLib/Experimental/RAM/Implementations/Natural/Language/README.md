# Implementations / Natural / Language

Internal modules of the [Implementations layer](../../README.md).
See [the full architecture](../../../README.md) before following lower-level imports.

| Module | Responsibility |
| --- | --- |
| [Basic](Basic.lean) | Typed implementation semantics |
| [IntegerExecution](IntegerExecution.lean) | Default execution of natural-valued compiler IR on Int-RAM |
| [Interface](Interface.lean) | Lower implementation interfaces |
| [Normalization](Normalization.lean) | Internal command normalization |
| [Refinement](../../../Historical/Adapters/InstructionRefinement.lean) | Instruction-certificate refinement |
| [Syntax](Syntax.lean) | Lower typed DSL |
| [VC](VC.lean) | Typed verification conditions |
| [Verification](Verification.lean) | Typed total contracts and runner binding |
