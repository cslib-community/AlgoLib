# Proofs as a generated Lean API

A method now generates proposition declarations **before mathematical simplification**.
A named proof is an ordinary Lean theorem against that API. You can import the API
and edit a proof without running symbolic execution or compiling the program again.

## 1. Write the paper program and generate its obligations

Put the method and mathematical definitions in a program module. In a specification
module importing that program, write:

```lean
generate_obligations insertionSort
```

For example, generation declares:

```lean
#check insertionSort.ObligationAPI.outer.initialize.prefix
#check insertionSort.ObligationAPI.outer.inner.preserve.hole
#check insertionSort.ObligationAPI.outer.terminate.decrease
#check insertionSort.ObligationAPI.assemble
```

The first three declarations have type `Prop`. The last consumes the obligation
proofs and returns `insertionSortObligations`.

The declaration types contain universally quantified source values and their justified
hypotheses. If several control-flow paths have the same responsibility, its proposition
contains all of them. No path is selected by a positional number in a user proof.
Generation structurally unfolds the annotated program and removes compiler-generated
copy variables using checked context transformations; it does not use the current
simp set to choose which responsibilities exist. Trivial obligations are retained.

`assemble` is a kernel-checked theorem, not an assumption or a trusted code generator.
It connects exactly these propositions to the existing `Algorithm.Obligations`.
The existing procedure, Loom, and RAM soundness theorems then apply unchanged.

## 2. Inspect and prove a responsibility

In a proof module importing the specification:

```lean
#named_goals insertionSort only outer.inner.preserve

prove_obligation insertionSort.ObligationAPI.outer.inner.initialize.hole by
  grind only [enter]
```

The command creates a theorem named
`insertionSort.ObligationAPI.outer.inner.initialize.hole_proof`.
It opens the source context and performs local simplification, then checks the author's
argument. If automation solves the whole responsibility, an explicit block is still
checked against its original context or the certified normalized proposition `True`;
it is never silently ignored. A block covering routine cases can use `first | omega | trivial`. No normalized program or instruction certificate is a proof argument.

The compact form remains available:

```lean
prove_algorithm insertionSort where
  case outer.initialize.prefix => by simp [Prefix]
  case outer.inner.initialize.hole => by grind only [enter]
  -- remaining mathematical responsibilities
```

For interactive editing, the main sorting and BFS proof files use standalone
`prove_obligation` commands, so each block also has its own command boundary in the
editor. The compact form is sugar for separate theorem declarations followed by
completion. It no longer
runs the entire verification-condition generator for each proof block.

## 3. Complete the algorithm

After separate `prove_obligation` commands, write:

```lean
complete_algorithm insertionSort
```

Completion proves routine remaining obligations and applies the generated assembly
theorem. It produces the existing `insertionSortVerification` and
`insertionSortProcedure` interfaces. Missing mathematical evidence is an error.
Routine proofs are cached as separate `_automatic` declarations in the specification
module. Explicit `_proof` declarations take precedence when completing the algorithm.
Adding a simp lemma can change the automatic status of an obligation; it cannot remove
its declaration or invalidate its name.

A source binding carries an explicit slot, product route, and internal/user distinction.
Input and current-state roles annotate quantifiers in the VC construction, not value
types or inferred product arity. All values retain their ordinary Lean types. A
product-valued configuration is not mistaken for mutable state; a user name starting
with an underscore remains a user variable. Source shapes are checked against the
typed state when opening it.

## 4. Keep expensive backend work outside the proof module

Insertion sort demonstrates the intended dependency graph:

```text
SortingProgram ──→ SortingSpec ──→ SortingProofs ──→ Sorting
      │                                                │
      └──────────→ SortingBackend ──────────────────────┴──→ SortingExecution
```

- `SortingProgram.lean`: paper program and mathematical invariants.
- `SortingSpec.lean`: frozen obligation API, assembly theorem, and cached routine proofs.
- `SortingProofs.lean`: the student's mathematical arguments.
- `SortingBackend.lean`: `compile_array_backend insertionSort`, checked from the body
  alone. It imports no sorting proof.
- `SortingExecution.lean`: `compile_array_method insertionSort`, which reuses that
  backend certificate and connects the completed procedure to the list runner and
  functional/RAM-cost theorem.

Changing a proof still requires Lean to check its declaration and affected downstream
modules. It does not require reconstructing the backend certificate. Separate
*declarations* help diagnostics; separate *modules* provide this build reuse.
Changing obligation automation in `SortingSpec` also reuses the backend. Changing the
program or its inline invariant annotations in `SortingProgram` rebuilds its dependents.

BFS uses `BreadthFirstProgram.lean`, `BreadthFirstSpec.lean`, and
`BreadthFirstProofs.lean` for the same separation. Its queue-substitution and RAM execution tests remain the
end-to-end checks of the assembled certificate.

## 5. What stability means

Names identify named loops, invariant clauses, and proof responsibilities. Moving code,
adding unrelated source statements, or changing automation does not renumber those
names. Changing an invariant changes its proposition: an incompatible old proof must
fail. Unnamed statements within a scope are grouped into the scope's safety/accounting
responsibility; this is not a claim of a separately stable identity for each anonymous
statement.

`Tests/ObligationAPI` checks reuse across imports and an added simplification lemma.
`check_elaboration.py` measures specification, proof, and backend checks separately.
The legacy tactic `named_proof_blocks` remains only for compatibility regressions;
new command-based authoring consumes generated declarations.


## Measured checking costs

Single-thread fresh module checks with warm dependencies on Lean 4.30.0-rc2;
these are development times, **not algorithm running times**. One sample per module:

| Component | Seconds |
| --- | ---: |
| Sorting proof declarations | 6.22 |
| Sorting executable assembly using cached backend | 8.79 |
| BFS proof declarations | 13.83 |
| BFS executable assembly | 14.09 |
| Sorting API generation plus cached routine proofs | 21.09 |
| Initial sorting backend certificate reconstruction | 100.84 |

Initial backend reconstruction is still expensive. The improvement is that ordinary
proof edits no longer repeat it. Separate commands also give the editor independent
proof-command boundaries; changing a command may still recheck later commands in that
file. The measured fresh-module times above do not claim perfect incremental caching.

Reproduce the measurements with `Tests/check_elaboration.py`; use
`Tests/check_proof_edit.py` to check an actual proof-only edit and executable rebuild.
The latter asserts that the API and backend artifacts retain both their timestamps
and content hashes, while the proof module is rechecked. Run these scripts without
concurrent builds or edits of the proof file.

The proof-edit regression measured **18.14 seconds** for an edit followed by rebuilding
the sorting executable. Both the generated API and the RAM backend artifacts were
unchanged, and the original proof file was restored and successfully rechecked.
