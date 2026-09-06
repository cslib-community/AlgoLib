# Upstream Loom and Velvet, ported to AlgoLib’s Lean version

This directory vendors the actual frameworks, with their original Apache-2.0
licenses and AUTHORS files. This is not an independent reimplementation of their
parser or algebra hierarchy.

- [Loom](https://github.com/verse-lab/loom), commit
  `78928abc9054b31d0bea85985496490baae95244`.
- [Velvet](https://github.com/verse-lab/velvet), commit
  `d254391d5e84546f96576e5b67dfb6bafe9fc301`.

Credit belongs to the upstream authors, listed in each package’s AUTHORS file.
Please also cite the [Loom POPL 2026 paper](https://verse-lab.org/papers/loom-popl26.pdf)
when describing the monadic observation, algebra hierarchy, and generic WP approach.
AlgoLib adds the costed RAM interpretation, mutable-array compiler adapter, and
kernel-checked connection between them.

## What is included

The complete Velvet method parser, mutable-variable elaboration, loop annotations,
procedure specifications, and proof commands are available through `Velvet.Std`.
Loom supplies its actual `MAlg`, ordered/deterministic/partial/total algebra classes,
logical and monadic lifts, Id/DivM, ReaderT, StateT, ExceptT, nondeterminism,
WP generation, loop gadgets, and tactic integration. The upstream `Gen` instance
is commented out upstream and remains so; we do not claim that it is implemented.

## Port and trust policy

Upstream targets Lean 4.24; AlgoLib targets Lean 4.30.0-rc2. Compatibility edits
update chain-indexed CCPO suprema and their proofs, transformer lifts, the changed
`ForIn` arity, legacy range names, typed option accessors, and do-parser APIs.
Foundation files use Lean’s module system where unfolding core instances requires
explicit imports. All mathematical proof changes are checked by Lean.

The upstream trusted SMT module and asynchronous admission tactic are deliberately
excluded. `loom_solve` uses proof-producing Lean tactics; no solver answer becomes
an axiom. Async admission requests raise an error. Upstream example/demo files and
the unrelated Cashmere case study and older alternate NonDetT implementation are
not included. Original sources can be recovered from the pinned commits above.

The full Velvet frontend permits more programs than the current RAM compiler.
`ram method` accepts the documented RAM subset and rejects unsupported executable
constructs. Using ordinary `method` does **not** by itself prove a RAM cost bound.
See `AlgoLib/Experimental/RAM/Prototype/README.md` for that boundary and the demo.

## Executable specialization

`Loom/MonadAlgebras/NonDetT/Executable.lean` is an AlgoLib addition. Lean 4.30
retains the generic loop’s CCPO dictionary as a runtime parameter, although its
supremum is noncomputable. `DivM.iterate` specializes the loop before compilation;
`DivM.iterate_eq` and `NonDetT.runDivM_eq` prove equality with upstream semantics.
Velvet’s `extract_program_for` uses this proved specialization for its concrete
`NonDetT DivM` methods. It does not use an unchecked interpreter override.

Unused algebra dictionaries were removed from `invariantGadget`; its semantics
and proof rules are unchanged. Transformer order instances now reuse Lean core,
avoiding duplicate-instance diamonds. Supplied loop variants are explicitly typed
as `Nat` before wrapping them in `Option`, preserving inference for numeric expressions.

The ordinary recursive-method regression also exercises a `do match` port fix:
Lean 4.30 added the optional `dependent` parameter before `generalizing`. Loom's
legacy elaborator now reads discriminants and alternatives at the new indices,
instead of silently losing match alternatives. Explicit dependent-match options
are rejected with an error until this elaborator supports them.
