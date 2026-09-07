# Implementations / Natural

Internal modules of the [Implementations layer](../README.md).
See [the full architecture](../../README.md) before following lower-level imports.

| Module | Responsibility |
| --- | --- |
| [DataRefinement](DataRefinement.lean) | Implement abstract operations using already verified owned programs |
| [EncoderLayout](EncoderLayout.lean) | Public allocation and initialization contracts |
| [Encoding](Encoding.lean) | Compositional resident input interfaces |
| [ExpressionImplementation](ExpressionImplementation.lean) | Ownership-directed compilation of scalar and array expressions |
| [LocalImplementation](LocalImplementation.lean) | Private method-local storage |
| [Ownership](Ownership.lean) | Local ownership of registers, heap cells, and private potential |
| [SignedArithmetic](SignedArithmetic.lean) | Exact signed arithmetic through the temporary natural-valued compiler IR |
| [SignedArrays](SignedArrays.lean) | Owned interleaved signed arrays |
| [SignedImplementation](SignedImplementation.lean) | Certified signed expression and storage interfaces |
| [SignedStorage](SignedStorage.lean) | Private canonical signed scalar representation |
| [Storage](Storage.lean) | Default separately owned scalar and array storage |
