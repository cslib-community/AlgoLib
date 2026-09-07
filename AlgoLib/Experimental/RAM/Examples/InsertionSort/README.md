# Insertion sort: program → proof → execution

| Read in this order | What it contains |
| --- | --- |
| [Program.lean](Program.lean) | `insertionSort`: mutable array code, nested loops, invariants, counting annotations |
| [Obligations.lean](Obligations.lean) | Generated named Lean obligation API |
| [Proofs.lean](Proofs.lean) | Independent proof blocks and completed `insertionSortProcedure` |
| [Execution.lean](Execution.lean) | `run`, `main`, `bound_eq`, `quadratic`, and executable checks |
| [Backend.lean](Backend.lean) | Cached compiler/representation certificates; no import of obligations or proofs |
| [MinimumCaller.lean](MinimumCaller.lean) | Call sorting through its public contract, then read the minimum |

```lean
import AlgoLib.Experimental.RAM.Examples
open AlgoLib.Experimental.RAM.Examples.InsertionSort

#eval (run [3, 1, 4, 1, 5]).value
-- [1, 1, 3, 4, 5]
#check main
#check quadratic
```

`main` combines sorted-permutation correctness and the inferred RAM bound.
`bound_eq` displays its polynomial; `quadratic` gives a simpler quadratic upper
bound. No fuel is supplied. Preferred public names are exported by the Examples entry point. Earlier declaration
names remain valid for compatibility.

For proof editing, import Program into Obligations, prove individual obligations
in Proofs, and assemble the result in Execution. Backend depends only on Program,
so mathematical proof edits reuse implementation certificates. See
[obligation exploration](../../Verification/OBLIGATION-API.md) and
[loop annotations and polynomial display](../../Language/PAPER-LOOPS.md).

The former `Sorting.lean` only contained the minimum caller. Its new name makes
that role explicit. This page is the single entry point for the full algorithm.
