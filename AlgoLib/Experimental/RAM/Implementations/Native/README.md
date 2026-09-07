# Implementations / Native

Internal modules of the [Implementations layer](../README.md).
See [the full architecture](../../README.md) before following lower-level imports.

| Module | Responsibility |
| --- | --- |
| [ArrayExpressions](ArrayExpressions.lean) | Native array operations with source-level contracts |
| [ArrayStorage](ArrayStorage.lean) | Relocatable single-cell native arrays |
| [Encoding](Encoding.lean) | Native resident inputs and ordinary output observations |
| [Expressions](Expressions.lean) | Native lowering of the unchanged Nat/Int source expressions |
| [Locals](Locals.lean) | Private native local storage |
| [ScalarStorage](ScalarStorage.lean) | Single-cell native scalar representations |
