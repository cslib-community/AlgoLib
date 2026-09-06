# From a paper loop proof to an executable theorem

Start with [Sorting.lean](Sorting.lean). The program shows both insertion loops,
array accesses, and mathematical invariants. It has **no `credits` clause, no
`remaining` invariant, and no bookkeeping constants**. Its caller also infers the
allowance of the sorting procedure before reading the minimum.

## 1. State what the algorithm preserves

Write ordinary mathematical invariants beside the loop. Optional names identify
these facts in the generated proof goals:

```lean
while i < arr.size
  invariant "sorted prefix" Prefix arr i
  invariant arr.toList.Perm arrOld.toList
  invariant arr.size = arrOld.size
  invariant i ≤ arr.size
  iterations_at_most arr.size - i
  do
    -- extend the prefix
```

`iterations_at_most` is a **remaining** iteration bound, evaluated at each loop
head. On an active iteration it must be positive and must strictly decrease after
the body. It need not decrease by exactly one. A constant initial bound does not
suffice unless the loop is never entered. These facts are checked, not assumed.

The body still needs its algorithmic invariant. The system does not discover
sorted-prefix, permutation, graph-reachability, or other algorithm-specific facts.

## 2. Let the framework account for work

Expression evaluation, guard materialization, guard tests, assignments, local
initialization, and procedure calls all contribute their existing logical costs.
Sequence adds allowances; branching takes a maximum. Calls use public contracts,
including input-dependent allowances. A library may advertise a uniform allowance
when that is convenient. Caller proofs never unfold a callee implementation.

The compiler's conversion rate and private data-structure potential remain below
this interface. Logical credits are not silently identified with RAM instructions.

For nested loops, the inner allowance becomes part of the outer body cost. In
insertion sort, `j := i` gives an inner bound depending on the current outer index.
For a bound of the form `upper - index`, the frontend proposes a conservative body
allowance by replacing that index with `upper` in its cost expression. Thus it can
infer a quadratic bound without requesting a numeric allowance from the author.

**This envelope is only a candidate.** The generated body VCs must prove it is
sufficient. Non-monotone costs, changing bounds, or costs depending on unknown
callee outputs can leave an allowance goal. No unproved monotonicity assumption
enters the theorem. The older explicit-credit interface remains available for
cost arguments outside this automatic inference scheme.

## 3. Use a work potential when individual counters increase

The checked [worklist example](../../Tests/PaperLoops.lean) uses:

```lean
while 0 < jobs + pending
  invariant True
  amortized_potential 2 * jobs + pending
  do
    if 0 < pending then
      pending := pending - 1
    else
      jobs := jobs - 1
      pending := 1
```

`pending` may increase. The total work potential decreases on each iteration.
The coefficient `2` describes the algorithm's work transfer; it is not a compiler
payment constant. Each work unit is priced using the inferred body allowance.

This annotation is a natural-valued, decreasing **work potential**, not unrestricted
amortized-credit synthesis. It uses the same checked bounded-iteration rule and a
fixed body allowance for that invocation of the loop. Backend data structures can
separately use private amortization potentials behind their public call contracts.

## 4. Solve named mathematical conditions

```lean
prove_algorithm insertionSort by
  paper_solve [SortedPermutation,
    Prefix, Hole, enter, exit, keep, swap, swap_perm, sorted, List.Perm.trans]
```

`paper_solve` reconstructs proofs using the supplied mathematical lemmas and the
existing arithmetic automation. It does not trust solver answers or add axioms.

For interaction, use `paper_vc` instead. It leaves ordinary Lean goals that can be
solved with `intro`, `simp`, `omega`, `apply`, or your own lemmas. Named obligations
include:

- `sorted prefix initialized / preserved at <file>:<line>:<column>`;
- `iteration bound positive` and `iteration bound decreases`;
- `array index within bounds / operation precondition`;
- `statement allowance sufficient` and `procedure precondition`.

Use `#paper_goals methodName` to preview outstanding goals without creating a
proof or an executable. For declarations in the current file, preview messages
are attached to their source locations. Imported declarations retain their original
location in the goal name. Intermediate programs, register paths, and compiler
certificates are normalized internally.

For example, annotating an active loop with `iterations_at_most 0` leaves an
iteration-bound goal. Reading `arr[arr.size]!` leaves a bounds goal: the `!` does
not bypass verification. Neither method receives a verified executable.

## 5. Obtain the runner and theorem

With the standard resident-array backend imported, one command assembles the
execution interface:

```lean
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly
-- Declare and prove your array method here.
compile_array_method insertionSort

#eval (insertionSortRun [4, 1, 3, 1, 2]).value
-- [1, 1, 2, 3, 4]
#check insertionSortCorrect
#check insertionSortBound
```

It generates `methodRun`, `methodBound`, and `methodCorrect`. The correctness
theorem includes both the declared postcondition and a bound on the actual RAM
steps of that runner. Nontrivial preconditions remain explicit proof arguments;
there is no fuel argument. A missing storage/primitive certificate causes linking
to fail.

For a single teaching file, replace the separate proof and compilation commands
with:

```lean
verify_array_method insertionSort by
  paper_solve [my_invariant_lemma, my_preservation_lemma]
```

The combined command uses precisely the same proof and assembly paths. In library
code, keep algorithm proofs in a backend-free module and put `compile_array_method`
in the execution module, as [SortingExecution.lean](SortingExecution.lean) does.

The standard command handles methods on one mutable `Array Nat`. For other typed
interfaces, a backend supplies `CertifiedExecutable.ofEncoded` once. Its `run`,
`bound`, and `correct` are derived from stored interpretation certificates; the
package does not accept an arbitrary host runner or a user-declared step counter.
It also requires a proof that the compiled code is independent of runtime inputs;
the array command reconstructs that certificate automatically.

Input encoding and output observation are host-side conventions. Bounds concern
unit-cost RAM execution on resident inputs, not Lean wall-clock time or bit complexity.

## What is checked

- The source sorting proof uses dependent nested bounds and no manual payments.
- Its inferred RAM bound simplifies to `912*n^2 + 384*n + 648`.
- The assembled runner is compared with Lean sorting on all lists of length below
  six over `{0,1,2}`, including empty inputs and duplicates.
- Weighted-work execution is checked for a grid of starting counter values.
- One client proof covers procedures that execute different numbers of real clear
  operations. Both the inferred allowance and the measured RAM steps change by
  the expected per-iteration amount.
- Invalid bounds, non-progressing loops, invalid invariants, and invalid indexing
  are rejected or retain the expected source-level diagnostic.
- Axiom guards and the import-layer check cover the new proof path.

These are executable and formal acceptance checks. They do not substitute for a
usability study with students unfamiliar with Lean.
