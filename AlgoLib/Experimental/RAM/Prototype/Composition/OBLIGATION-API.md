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

### How do I choose which goal to prove?

Start from the specification module, which contains the obligations but does not
import the completed proofs. For insertion sort, a new proof file can begin with:

```lean
import AlgoLib.Experimental.RAM.Prototype.Composition.SortingSpec

namespace AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
open Frontend SortingFacts

#named_goals insertionSort
```

Read the command's messages in Lean's information panel. The status tells you where
work remains:

| Status | What to do |
| --- | --- |
| `[open]` | Inspect the displayed hypotheses and conclusion; supply the mathematical argument. |
| `[automatic, cached]` | No block is needed: the specification already contains checked evidence. |
| `[automatic]` | No block is needed: current automation can solve it when completing the algorithm. |
| `[proved]` | A separate explicit proof already exists. |

These statuses depend on what your file imports. Importing `SortingProofs` instead
of `SortingSpec` brings in the finished proofs, so it is not the starting point for
writing your own version. Automation does not remove an obligation's declaration.

**Choose an open responsibility by its meaning in your paper proof, not by its
position in the goal list.** The name identifies the loop, the kind of argument,
and, when applicable, the invariant clause:

```text
outer.inner.preserve.hole
└─ loop path ─┘   │      └─ invariant named "hole"
                 └─ show that one iteration preserves it
```

| Name component | Paper-proof question |
| --- | --- |
| `initialize.prefix` | Why does the prefix invariant hold when this loop starts? |
| `preserve.hole` | Assuming the invariant and guard, why does the body preserve the hole invariant? |
| `terminate.positive` / `terminate.decrease` | Why can the loop make progress, and why does its termination measure decrease? |
| `account.initial` / `account.iteration` | Why is the initial allowance sufficient, and why does it pay for each iteration and the remaining work? |
| `safety` / `requires` | Why is this access in bounds, or this procedure's public precondition satisfied? |
| `exit` | Why do the invariant and loop exit establish the required result? |

For a first pass, follow the paper argument: initialization, preservation,
termination and accounting, then exit. This is a reading order, not a dependency
requirement: you can prove obligations in any order. Skip the automatically solved
ones. If you cannot recognize an open statement, inspect the corresponding invariant
and program statement before choosing tactics.

Narrow the preview to the part you are working on:

```lean
#named_goals insertionSort only outer.inner
#named_goals insertionSort only outer.inner.initialize.hole
```

The second command shows the source-level context for entering the inner loop.
Read the conclusion first, then identify which hypotheses match your mathematical
lemma. Here the existing array lemma `enter` gives the required argument:

```lean
prove_obligation insertionSort.ObligationAPI.outer.inner.initialize.hole by
  grind only [enter]

#named_goals insertionSort only outer.inner.initialize.hole
```

The final preview now reports `[proved]`. The proof command takes the **full generated
proposition name**, including `ObligationAPI`; the preview filter takes the **short
responsibility path**. You can also inspect the frozen proposition directly:

```lean
#print insertionSort.ObligationAPI.outer.inner.initialize.hole
```

One responsibility can contain several control-flow paths. For example,
`outer.inner.preserve.hole` covers both the swap and no-swap branches. You do not
pick just one branch: the proof block must discharge every remaining path for that
responsibility. The actual [sorting proof file](SortingProofs.lean) shows the focused
`swap` and `keep` arguments.

Continue with the other `[open]` responsibilities, then run
`complete_algorithm insertionSort` as described below. The single `enter` block
above is only one part of the proof; completion rejects missing mathematical
arguments. End the proof file with:

```lean
end AlgoLib.Experimental.RAM.Prototype.Composition.Sorting
```

### Explore a goal in the editor

The specification import also provides an obligation explorer. Start with one
responsibility rather than printing the entire method:

```lean
#explain_obligation insertionSort only outer.inner.preserve.hole
#proof_template insertionSort only outer.inner.preserve.hole
```

The explorer reports the mathematical purpose, source file/line/column, frozen
proposition name, number of retained execution paths, and source-variable roles.
The responsibility kind is recorded from the source annotation independently of its
name, so a loop or invariant named `account` cannot change the explanation.
It then shows the existing status and exact simplified open goals, with all their
hypotheses. For an imported specification, the message appears at the exploration
command and includes the original source location as text.

| Binding | Meaning |
| --- | --- |
| `arrInput` | The original source input `arr` |
| `arrState1` | `arr` in the first quantified loop state on this obligation's path |
| `arrState2` | `arr` in the next nested quantified loop state |
| `result` | A quantified procedure result |
| `hInvariant_hole` | A hypothesis from the invariant clause named `hole` |

The names are recorded when the explicitly tagged source quantifiers are opened;
no tuple-size or variable-name heuristic chooses their roles. Invariant hypothesis
names come from the explicit invariant labels before simplification removes their
wrappers. Repeated clauses get fresh suffixes; simplification can remove redundant
hypotheses. Other mathematical assumptions retain their ordinary Lean context.
These are also the
names available inside `prove_obligation` blocks. Ordinary configuration parameters
retain their names and types. The algorithm syntax still uses `arrOld` for its
original-input ghost; `arrInput` is the corresponding proof-context name.
Existing handwritten blocks that refer to old generated local names may need a
one-time rename. The generated proposition names and mathematical statements remain
the same; no compatibility alias is silently inserted.

A snapshot is a universally quantified loop state, **not automatically a concrete
loop-entry or post-assignment state**. Updated arrays appear as expressions in the
exact goal. Snapshot numbering follows nested quantifiers and can change when the
program's loop structure changes. Invariant and responsibility identities remain
the stable selection interface. The explorer does not invent an `arrAfter` variable
or hide the equations needed to identify a state.

The template command prints a copyable block with the exact generated name:

```lean
prove_obligation insertionSort.ObligationAPI.outer.inner.preserve.hole by
  fail "Supply the mathematical argument here"
```

Replace `fail` with your proof. The command itself creates no declaration; the
placeholder cannot satisfy a proof or complete an algorithm. Already proved or
cached automatic responsibilities are reported without generating redundant blocks.
This is a command-based editor interface, not yet a clickable code action.

### Find the mathematical lemmas

The sorting specification registers `enter` for initialization of `Hole`, and
`swap` and `keep` for preservation. The explorer displays the fully qualified theorem
names and their statements when the predicate occurs in the frozen proposition and
the responsibility phase matches. Read their hypotheses before using them.

A library author can register suggestions explicitly:

```lean
obligation_lemmas Hole for "initialize" => [enter]
obligation_lemmas Hole for "preserve" => [swap, keep]
```

Registrations persist through imports. They are navigation hints, not new axioms,
automatic invariant discovery, or promises that a theorem applies. Definitions and
axioms cannot be registered as proved theorems. Every actual application still needs
a checked proof. Matching is intentionally conservative: it checks occurrences in
the frozen proposition without unfolding arbitrary mathematical definitions.

For BFS, try this in a file importing `BreadthFirstSpec` and opening its namespace:

```lean
#explain_obligation bfs only search.preserve.frontier
#explain_obligation bfs only search.account.iteration
#proof_template bfs only search.account.iteration
```

The specification registers frontier lemmas and work-accounting lemmas such as
`process_head` and `scan_work`. The existing [BFS proof blocks](BreadthFirstProofs.lean)
show the checked arguments. Neither navigation nor lemma registration imports a RAM
backend, changes an obligation, or alters either queue implementation.

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

With the explorer enabled, the proof-edit regression measured **12.13 seconds** for
a valid tactic edit (`simp` to `simpa`) and executable rebuild, and **5.17 seconds**
for a deliberately failing proof edit. These are individual warm-dependency samples,
not a latency guarantee. In both cases the generated API and RAM backend artifacts
retained their timestamps and hashes. The original proof was restored and rechecked.

`Tests/ObligationAPI/Explorer.lean` checks persisted roles, phase-sensitive suggestions,
invalid registrations, and rejection of unfinished templates. `ExplorerExamples.lean`
checks both insertion-sort paths, imported BFS accounting suggestions, and direct use
of `hInvariant_hole` in a checked proof. Existing execution, layout-substitution, and
axiom regressions still cover the underlying stack.
