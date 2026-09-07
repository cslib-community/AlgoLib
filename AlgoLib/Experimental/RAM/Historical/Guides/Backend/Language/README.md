> Historical guide. For the supported frontend and current layout, see [the RAM guide](../../../../README.md).

# Typed source and verified compilation

This is the lower typed language, not the public entry point for algorithm students. The public method language is documented in [Authoring](../../Authoring/README.md).

| File | Role in the verified translation |
|---|---|
| [Basic.lean](../../../../Implementations/Natural/Language/Basic.lean) | Types, variables, expressions, commands, independent costed evaluation |
| [Compiler.lean](../../../NatCompiler/Compiler.lean) | Compile typed source to RAM; `Eval.compile` preserves observation and its charged cost |
| [Verification.lean](../../../../Implementations/Natural/Language/Verification.lean) | Total command contracts, loop rules, and the fuel-free compiled `Method` runner |
| [VC.lean](../../../../Implementations/Natural/Language/VC.lean) | Lower-level symbolic obligations and soundness/completeness rules |
| [Syntax.lean](../../../../Implementations/Natural/Language/Syntax.lean) | Lower DSL for variables, indexed operations, scoped locals, and calls |
| [Normalization.lean](../../../../Implementations/Natural/Language/Normalization.lean) | Normalize command structure and transfer verified evaluations across equivalent shapes |
| [Refinement.lean](../../../Adapters/InstructionRefinement.lean) | Lift existing instruction certificates into typed contracts and account for overhead |
| [Interface.lean](../../../../Implementations/Natural/Language/Interface.lean) | Lower-level interfaces and output contracts |

The earlier lower-DSL demonstrations are in `Legacy`. Their normalization and register proofs are deliberately absent from the public algorithm files. They remain useful compiler regressions, but they are not an alternative recommended authoring workflow.
