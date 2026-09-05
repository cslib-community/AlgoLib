# RAM experiments

For claims about machine time, import
`AlgoLib.Experimental.RAM.InsertionSort` and use the
`AlgoLib.Experimental.RAM.Checked` namespace.

The original `RAM.lean` is a shallow reference model. Its `Program` accepts
arbitrary state transformations and writable cost annotations. Its costs alone
are not a sound basis for an algorithm-existence claim. The checked model below
uses its memory theorems as specifications, never its cost annotations.

## What the checked model guarantees

`Machine.lean` defines finite `Code` syntax with eight registers, a total memory
`Nat → Nat`, register/literal operands, reads, writes, moves, addition,
saturating subtraction, multiplication, conditionals, and while loops. Neither
operands nor instructions can contain arbitrary Lean functions. `Code` has no
`pure`, `tick`, state replacement, or cost replacement constructor.

`Exec code initial steps final` is a terminating execution in exactly `steps`
operations. Each instruction costs one; each conditional or while guard costs
one for the comparison and conditional transfer together. Sequence composition
has no extra cost. A block's cost is its instruction-list length. This models
unit-cost natural-number RAM arithmetic, including unbounded multiplication;
it does not claim bit complexity, fixed-width overflow behavior, or the running
time of Lean's implementation of function updates.

The checked properties include:

- `Exec.deterministic`: the same program and initial state cannot have different
  final states or operation counts.
- `Exec.zero`: zero operations cannot change state.
- `run_sound` and `Exec.run_complete`: the executable interpreter and the
  execution relation agree on terminating executions. Fuel limits interpreter
  recursion depth; it is neither the reported time nor accessible to programs.
- `Ensures.seq` and `Prefix`: compose correctness/time contracts and reason
  about loop iterations with ordinary induction and simplification.

## Sorting theorem

`sortCode` is one closed syntax tree, fixed before the input is supplied. It
sorts the existing memory interval `[base, base + count)` in place. The input
address and length are in the `base` and `count` registers; all six other
registers can initially hold arbitrary values. The code initializes its own
working registers.

`sortCode_correct` proves termination, sortedness, permutation of the original
input, preservation of every cell outside the block, and at most
`4*n^2 + 8*n + 2` operations. This includes register initialization and all loop
tests. `sortCode_quadratic` gives the explicit `O(n²)` witness `14*n²` for
`n ≥ 1`; no tight lower bound is claimed.

The theorem `exists_quadratic_sort` states:

```lean
∃ c : Code, SortsWithin c (fun n => 4 * n ^ 2 + 8 * n + 2)
```

`SortsWithin` universally quantifies over initial machine states. The input is
exactly the block already in that state: there is no uncharged preprocessing
or input-dependent code generation. Loading an external input into RAM is
outside this sorting routine's cost. The helper `initial` initializes registers
without changing the supplied memory.

The proof connects actual loop executions to the original insertion sort's
memory behavior, then reuses Mathlib's list sortedness and permutation theorems.
No compiler or shallow-cost soundness assumption is needed: the fixed `Code`
itself has an `Exec` proof.

`no_zero_time_sort` is a checked regression against the earlier cost-erasure
attack: no program in this language can sort every input in zero operations.

## Running and checking

```lean
open AlgoLib.Experimental.RAM
open AlgoLib.Experimental.RAM.Checked

#eval (run 100 sortCode (initial (ofList [3, 1, 4, 2]) 0 4)).map
  (fun (steps, final) => (contents final.memory 0 4, steps))
-- some ([1, 2, 3, 4], 71)
```

The examples also cover empty and singleton blocks, duplicates, nonzero base
addresses, sentinel cells, and ascending/descending inputs. They use kernel
reduction to check the interpreter's output.

```sh
lake build AlgoLib.Experimental.RAM.InsertionSort
lake build
```
