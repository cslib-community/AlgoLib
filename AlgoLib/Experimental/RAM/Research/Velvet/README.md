# Research / Velvet

Internal modules of the [Research layer](../README.md).
See [the full architecture](../../README.md) before following lower-level imports.

| Module | Responsibility |
| --- | --- |
| [ExecutableTranslation](ExecutableTranslation.lean) | Public execution of a certified ordinary-Velvet translation |
| [Nondeterministic](Nondeterministic.lean) | Nondeterministic RAM and all-outcome translation contracts |
| [NondeterministicRunner](NondeterministicRunner.lean) | Fuel-free execution with procedure calls and an explicit choice schedule |
| [RecursiveTranslation](RecursiveTranslation.lean) | A recursive ordinary Velvet procedure and its recursive RAM translation |
| [VelvetArrayTranslation](VelvetArrayTranslation.lean) | Two-way equivalence for an ordinary Velvet multiple-array method |
| [VelvetSemantics](VelvetSemantics.lean) | All-outcome semantics for ordinary Velvet methods |
| [VelvetTranslationTests](VelvetTranslationTests.lean) | Translation of an ordinary Velvet choice and an ordinary procedure call |
| [VelvetWP](VelvetWP.lean) | Ordinary Loom correctness transported to RAM outcomes |
