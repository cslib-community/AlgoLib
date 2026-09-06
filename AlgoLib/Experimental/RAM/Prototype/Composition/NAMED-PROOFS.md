# Write the paper argument in separate proof blocks

The current command interface uses a [generated Lean obligation API](OBLIGATION-API.md).
Program specifications, mathematical proofs, and expensive backend certificates live in
separate modules so proof edits can reuse generation and compilation work.


Start with [insertion sort](Sorting.lean) or [BFS](BreadthFirst.lean).
Both use the same owned frontend and checked compiler as before. The change is how
you supply the mathematical argument: each block has a stable responsibility,
instead of trying a collection of tactics against every generated goal.

## 1. Name the loop and its mathematical facts

An excerpt from the executable sorting program:

```lean
while i < arr.size named outer
  invariant "index" i ≤ arr.size
  invariant "prefix" Prefix arr i
  invariant "permutation" arr.toList.Perm arrOld.toList
  invariant "size" arr.size = arrOld.size
  iterations_at_most arr.size - i
  do
    let mut j := i
    while 0 < j named inner
      invariant "index" j ≤ i
      invariant "bounds" i < arr.size
      invariant "hole" Hole arr i j
      invariant "permutation" arr.toList.Perm arrOld.toList
      invariant "size" arr.size = arrOld.size
      iterations_at_most j
      do
        -- The actual file contains the adjacent comparison and array writes.
```

The inner loop's stable path is `outer.inner`. Invariant labels are identifiers,
such as `hole` or `sorted_prefix`. A named loop requires a name for every invariant;
duplicate names are errors. Moving the code does not change these identities.
Source line and column are stored separately for diagnostics.

Use `named seed do ...` around a statement or group of statements to give its
safety and procedure-call obligations a stable scope too. Names do not change
execution or charges. Unnamed syntax remains supported for existing clients.

## 2. Inspect the particular obligation you are working on

Place either command after the method declaration:

```lean
#named_goals insertionSort
#named_goals insertionSort only outer.inner.preserve
```

The preview groups obligations by stable name, reports which remaining checks
arithmetic automation can solve, and shows the mathematical context of open goals.
Messages point back to the relevant source statement. Routine definitional and
propositional checks are already closed during symbolic execution.

| Responsibility | Example name | What you prove |
|---|---|---|
| Initialization | `outer.inner.initialize.hole` | The invariant holds on entry |
| Preservation | `outer.inner.preserve.hole` | The body preserves the invariant |
| Termination | `outer.terminate.decrease` | The remaining count/work strictly decreases |
| Accounting | `search.account.iteration` | The counting argument pays for this body and remaining work |
| Initial allowance | `search.account.initial` | The initial work bound covers the loop |
| Array safety | `search.scan.safety` | An accessed vertex is within the visited array |
| Procedure precondition | `search.scan.requires` | The public queue/cursor contract applies |
| Exit | `outer.exit` | The invariant and false guard imply the requested postcondition |

Each path has its own hypotheses. An `if` can produce two obligations with the same
responsibility; the selected block is checked independently for both. A block may
use ordinary `apply`, `exact`, `simp`, `omega`, or a focused `grind only [lemmas]`.
You never select a goal by its position in a list.

## 3. Supply one block per mathematical responsibility

This excerpt is checked in [Sorting.lean](Sorting.lean):

```lean
prove_algorithm insertionSort where
  case outer.initialize.prefix => by simp [Prefix]
  case outer.inner.initialize.hole => by grind only [enter]
  case outer.inner.preserve.hole => by
    first
    | apply swap <;> first | assumption | omega
    | apply keep <;> first | assumption | omega
  case outer.inner.preserve.permutation => by
    grind only [swap_preserves_permutation]
  case outer.preserve.prefix => by grind only [exit]
  case outer.terminate => by omega
  case outer.account => by omega
  case outer.inner.account => by omega
  case outer.exit => by grind only [SortedPermutation, sorted]
```

`outer.terminate` selects its remaining termination duties; an exact name can be
used instead. Overlapping selections are rejected, so every selected responsibility
has one owner. Unknown names are errors. Every supplied block must finish its
selected goals, and every unhandled goal must be closed by routine automation.
Missing mathematical proofs prevent creation of a usable certificate.

The facts `enter`, `swap`, `keep`, and `exit` are ordinary theorems about arrays in
[SortingFacts.lean](../SortingFacts.lean). They state the familiar sorted-prefix
argument. You can develop these lemmas separately and reuse them in other proofs.
There is no normalization, register correspondence, or compiler proof in these blocks.

## 4. Separate the BFS arguments too

[BreadthFirst.lean](BreadthFirst.lean) has three named loops: `clear`, `search`, and
`search.scan`. Its blocks separate the zeroed prefix, initial frontier, queue
capacity, preservation of the scan result, and the outer work argument.

For example, `search.scan.preserve.vertices` uses `List.mem_of_mem_tail`: removing
the next neighbor cannot introduce a vertex outside the graph. The
`search.account.iteration` block uses the mathematical `process_head` and
`scan_work` lemmas: processing a vertex consumes its own work and its adjacency
entries, while scanning preserves the set of already processed vertices.

The frontend still infers the local charges of reads, writes, guards, and calls.
For nested loops, the inner allowance can depend on the current outer vertex's
degree. The author proves a counting argument about that work; RAM instruction
conversion and the queue's private amortization potential remain behind the linker.

Procedure calls are verified through their public summaries. A caller's block
does not expand queue addresses or prove that a visited write preserves graph storage.
The **same `bfsVerification`** is used for the circular queue, the two-stack queue,
and the private-layout relocation regression.

## 5. Obtain the existing executable and joint theorem

`prove_algorithm insertionSort where ...` creates `insertionSortVerification` and
`insertionSortProcedure`. In the backend assembly file, the existing single
`compile_array_method insertionSort` command generates the executable interface,
functional correctness, and inferred RAM upper bound together.

As a library user, import the assembled method and run it directly:

```lean
import AlgoLib.Experimental.RAM.Prototype.Composition.SortingExecution
open AlgoLib.Experimental.RAM.Prototype.Composition

#eval (Sorting.run [5, 2, 4, 2]).value  -- [2, 2, 4, 5]
#check Sorting.main
#check Sorting.quadratic
```

For a single teaching file, `verify_array_method name where ...` accepts the same
blocks and performs proof checking and standard array assembly in one command.
[NamedAssembly.lean](../../Tests/NamedAssembly.lean) checks this path, executes the
RAM runner, and guards the generated theorem's axioms. Library modules can keep
algorithm proofs separate from backend selection as in the sorting example.

No fuel is required. [BFSExecution.lean](BFSExecution.lean) similarly assembles
`BreadthFirst.search` and its graph-correctness and linear-time theorems for each
registered FIFO backend. See [OWNED-BFS.md](OWNED-BFS.md) for runnable graph inputs.

Under the interface, symbolic execution constructs an introduction/conjunction/
case-analysis proof tree at the original `Algorithm.Obligations` type. Blocks fill
its leaves with their justified local hypotheses; no unchecked global assumptions
are introduced. The kernel
checks the complete reconstruction, then the unchanged `Plan.sound`, Loom
interpretation, ownership refinement, and RAM compiler theorems apply. Labels and
source metadata carry no semantic authority.

## Scope and checks

This is an authoring interface for the supported owned language, not automatic
invariant discovery or a claim to compile arbitrary Lean/Velvet programs. Facts
about arrays, graphs, and counting may still require ordinary Lean proofs. Large
contexts and branch-dependent obligations can require mathematical simplification.

[NamedProofs.lean](../../Tests/NamedProofs.lean) tests separate initialization,
preservation, termination and accounting blocks, source movement and an unrelated
local, duplicate/missing names, incomplete proofs, and invalid evidence. Existing
sorting/BFS execution, backend-substitution, axiom and elaboration-time regressions
continue to check the complete stack.

Run the acceptance checks from the repository root:

```sh
lake build
python3 AlgoLib/Experimental/RAM/Tests/check_layers.py
python3 AlgoLib/Experimental/RAM/Tests/check_elaboration.py
```

The layer check also prevents the sorting and BFS teaching proofs from regressing
to broad VC goal-search scripts. The timing check includes the named-proof interface
as well as the algorithm and assembly modules; those timings are unrelated to the
proved RAM instruction costs.
