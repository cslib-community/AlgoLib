# Backend: implementation responsibilities

Algorithm authors should not need to open this directory to prove a program. Its modules implement and certify the interfaces in `Authoring` and `Library`. There are no canonical student algorithms here.

| Directory | What it constructs | Contract exported upward |
|---|---|---|
| [Realization.lean](Realization.lean) | Separate primitive implementations and structural certificate reconstruction | `Compilation M program`: functional refinement and cost transport |
| [Memory](Memory/README.md) | Arrays, queues, stacks, graph layouts, footprints, and input encodings | Functional/cost/frame contracts over physical memory |
| [Adapters](Adapters/README.md) | Representations of logical algorithm states and certified actions/input preparation | `ActionImplementation`, `GuardImplementation`, and `Interface` |
| [Language](Language/README.md) | Typed commands, independent evaluation, VCs, normalization, refinement, and compiler | A proof that the verified source executes as RAM with the stated result and cost |
| [Certificates](Certificates/README.md) | Earlier instruction-level invariant proofs reused for operation implementations | Concrete execution and cost facts for adapters |

The typed language is an implementation layer, while `Authoring.Program` is the algorithm-facing language of certified operations. Their semantics are related by `Run.refines`. Typed evaluation is related to RAM execution by `Eval.compile`. Method verification invokes these connections automatically through the shared runner.

Adapters depend on the authoring contract types they implement. This is not a circular dependency: the pure authoring semantics have no backend dependency; Realization imports those contracts and the typed backend, and concrete adapters sit above both. No backend module imports a complete `Programs` method or a `Legacy` demonstration.
