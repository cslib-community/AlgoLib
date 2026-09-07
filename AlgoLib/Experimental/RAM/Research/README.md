# Research fixtures: explicit scope

[Velvet](Velvet/) contains the ordinary-Velvet semantic boundary, nondeterministic
integer target, executable translation, recursive example, and associated tests.
These preserve independent semantic results. They do not mean that arbitrary Lean
values, general recursion, or all ordinary Velvet syntax are accepted by `ram method`.

The supported route remains [Language.Frontend](../Language/Frontend.lean).
These fixtures share the verified Int-RAM target but are not alternative public
frontends. They remain in the full Lean build and axiom/regression checks.

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Velvet/ExecutableTranslation.lean](Velvet/ExecutableTranslation.lean) | research | Public execution of a certified ordinary-Velvet translation |
| [Velvet/Nondeterministic.lean](Velvet/Nondeterministic.lean) | research | Nondeterministic RAM and all-outcome translation contracts |
| [Velvet/NondeterministicRunner.lean](Velvet/NondeterministicRunner.lean) | research | Fuel-free execution with procedure calls and an explicit choice schedule |
| [Velvet/RecursiveTranslation.lean](Velvet/RecursiveTranslation.lean) | research | A recursive ordinary Velvet procedure and its recursive RAM translation |
| [Velvet/VelvetArrayTranslation.lean](Velvet/VelvetArrayTranslation.lean) | research | Two-way equivalence for an ordinary Velvet multiple-array method |
| [Velvet/VelvetSemantics.lean](Velvet/VelvetSemantics.lean) | research | All-outcome semantics for ordinary Velvet methods |
| [Velvet/VelvetTranslationTests.lean](Velvet/VelvetTranslationTests.lean) | research | Translation of an ordinary Velvet choice and an ordinary procedure call |
| [Velvet/VelvetWP.lean](Velvet/VelvetWP.lean) | research | Ordinary Loom correctness transported to RAM outcomes |

<!-- END GENERATED MODULE INDEX -->
