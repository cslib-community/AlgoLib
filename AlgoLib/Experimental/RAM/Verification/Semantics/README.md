# Verification / Semantics

Internal modules of the [Verification layer](../README.md).
See [the full architecture](../../README.md) before following lower-level imports.

| Module | Responsibility |
| --- | --- |
| [LogicalInterpretation](LogicalInterpretation.lean) | Backend-independent logical interpretation |
| [LogicalVerification](LogicalVerification.lean) | Proof annotations and generated conditions |
| [LoomObservation](LoomObservation.lean) | The RAM observation as an actual Loom algebra |
| [Observation](Observation.lean) | A costed observation for the Loom algebra |
| [Procedures](Procedures.lean) | Typed, compositional procedures over certified data-structure interfaces |
