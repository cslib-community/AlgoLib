# Verified RAM algorithms with an imperative source language

For adjacency-list BFS, graph refinement, and linear time, see
[`BFS/README.md`](BFS/README.md) and `AlgoLib.Experimental.RAM.BFS.Demo`.

`Checked.Procedure InputType OutputType` now supplies a reusable typed RAM
interface: an input encoder, fixed code, restricted output descriptor, and
termination certificate. BFS exposes `Arguments G → Result`, with named
`visited` and `steps` fields, and a `graph_program (...) returns ...` declaration
whose body reads like the textbook algorithm. See the BFS walkthrough above.

Start with `AlgoLib.Experimental.RAM.Demo`. Its programs execute without fuel:

```lean
import AlgoLib.Experimental.RAM.Demo
open AlgoLib.Experimental.RAM.Checked
open Source Reg Demo

#eval sort [3, 1, 4, 2]
-- ([1, 2, 3, 4], 71)
```

The second component is the exact modeled RAM operation count. Termination is
checked when the program is defined. There is no fuel argument, search for a
sufficient bound, timeout, or noncomputable choice of output. `Runner.execute`
uses well-founded recursion on machine configurations; Lean erases its
accessibility proof when compiling the evaluator.

## Write code and annotate loops

`imperative` is actual Lean syntax, inspired by [Dafny's syntax](https://dafny.org/dafny/DafnyRef/DafnyRef): assignments,
`invariant` clauses, and `decreases` clauses. This is a small language implemented
and verified here, not the Dafny compiler or its full language.

The sorting source in `Demo.lean` is:

```lean
def sorting : Stmt := imperative {
  limit := base + i;
  while i > 0
    invariant (fun entry s => s.regs i ≤ entry.regs i)
    decreases (fun s => s.regs i)
  {
    i := i - 1;
    j := base + i;
    x := A[j];
    next := j + 1;
    live := 1;
    call insertion;
  }
}
```

`insertion` is also written in this syntax. It moves smaller suffix elements
into the hole `j` until it finds where `x` belongs. `call` expands the helper's
source tree; it adds no hidden operation or arbitrary Lean function call.

Each invariant receives a ghost loop-entry state and the current state. The
inner insertion loop uses this to express that the outer index is preserved.
Its variant is zero when stopped and `limit - next + 1` otherwise.

`VC` automatically generates initialization, invariant-preservation,
strict-decrease, and exit obligations. `vcgen` unfolds these and simplifies
straight-line assignments. Users supply the mathematical invariants and
variants, then discharge the resulting goals with Lean proofs; invariants
are not inferred automatically. In the sorting demo, index preservation and
arithmetic prove termination:

```lean
def insertionSort : TotalProgram := verified sorting sorting_vc
```

After that, clients call `insertionSort.run initialState`. They supply neither
fuel nor a termination proof on each call.

## A complete source-level method contract

Methods additionally support `requires` and `ensures`. The summation example
in `Demo.lean` uses the familiar paper invariant

```
2 * sum + j * (j + 1) = constant
```

and has this complete definition (the aliases and invariant are defined in `Demo.lean`):

```lean
def summation : Method := method
  requires (fun _ => True)
  ensures (fun before after =>
    2 * after.regs sum = before.regs i * (before.regs i + 1))
  {
    sum := 0;
    j := i;
    while j > 0
      invariant triangularInvariant
      decreases (fun s => s.regs j)
    {
      sum := sum + j;
      j := j - 1;
    }
  }
  verified_by (by
    intro s _
    vcgen
    simp only [triangularInvariant, sum, j, i, ne_eq, reduceCtorEq, not_false_eq_true,
      Function.update_of_ne, Function.update_self, mul_zero, zero_add, true_and]
    constructor
    · intro t ht hpos
      refine ⟨?_, hpos⟩
      have : t.regs cursor - 1 + 1 = t.regs cursor := by omega
      nlinarith
    · intro t ht hz
      simpa [hz] using ht
  )
```

This example proves functional correctness entirely through generated source
VCs. Its proof is the paper argument: the invariant holds initially, adding
`j` to the accumulator and decrementing `j` preserves it, `j` strictly decreases,
and `j = 0` at exit gives the postcondition. Running it with `n = 5` returns
`sum = 15` and `18` RAM operations. Nontrivial method preconditions are proof
obligations at a call; trivial ones are synthesized automatically and erased.

## Sorting proof, in textbook order

The sorting demo reuses already proved insertion and suffix simulation lemmas
as procedure specifications. Its termination annotations are checked by `VC`;
its functional correctness proof uses those refinement lemmas. It does not
pretend that a sorted-suffix invariant was inferred automatically.

1. **Insertion.** `insert_sorted` states that inserting a key into a sorted list
   preserves sortedness and gives a permutation of the old list plus the key.
2. **Loop invariant.** `sorted_suffix` connects actual outer-loop iterations to
   a sorted suffix with the same multiset. Initialization is the empty suffix;
   maintenance is the insertion lemma. The low-level proof also keeps the
   unprocessed prefix unchanged.
3. **Termination.** `sorting_vc` and `insertion_vc` discharge generated decreasing
   variant obligations. This certificate makes the executable total.
4. **Time.** Inserting into a suffix of length `k` takes at most `7k + 5` operations.
   Five setup instructions and the outer guard give at most `7k + 11` per pass.
   `quadratic_recurrence` checks the induction step for
   `T(k+1) ≤ T(k) + 7k + 11`. Initialization and the final test add two.
5. **Conclusion.** `Demo.insertionSort_correct` proves sortedness, permutation,
   preservation of memory outside the block, and at most `4n² + 8n + 2` operations
   for the fuel-free executable. `exists_quadratic_sort` remains a uniform
   existence theorem for one fixed RAM program.

## What is verified

| Component | Guarantee |
| --- | --- |
| `Machine.lean` | Restricted instructions, deterministic execution costs, no zero-step state changes |
| `Runner.lean` | Fuel-free evaluator agrees with `Exec`; termination certificates are erased |
| `Source.lean`: `VC.sound` | Generated conditions imply terminating source execution and the postcondition |
| `Source.lean`: `Eval.compile`, `Eval.of_compile` | Compilation preserves state and exact cost in both directions |
| `LoopVC.lean` | Modular ghost invariants and time-credit VCs imply total correctness |
| `BFS/` | FIFO BFS, graph/adjacency refinement, connectivity, and linear RAM time |
| `Syntax.lean` | Macros build source syntax; resulting terms and proofs are kernel-checked |
| `Demo.lean` | Executable insertion sort, its paper-style proof outline, and a complete summation method |
| `Tests.lean` | Runtime boundary/cost checks and rejection of a nondecreasing loop |

The compiler erases invariants and variants and lowers source assignments and
control structures to RAM instructions. The source has an independent execution
relation. Compiler correctness is a theorem for all source programs, not just
an equality check for the demo. `sorting_compiles` additionally shows that the
source compiles to the same fixed RAM program proved in `InsertionSort.lean`.

## Scope and cost discipline

Runtime expressions are deliberately flat: literals, variables, memory reads,
or one arithmetic operation on atomic operands. Introduce another assignment
for a compound expression. Identifiers denote the eight existing registers;
the demo's `i`, `j`, and `x` are aliases. This version has no general register
allocation, dynamically allocated locals, recursive procedures, or Dafny array
bounds system. `A[address]` denotes the model's total addressed memory.

The model uses unit-cost natural-number reads, writes, moves, addition,
saturating subtraction, and multiplication. A comparison with conditional
transfer costs one, including the final false test of a loop. This is a
natural-number RAM model, not a bit-complexity bound or a claim about the host
Lean evaluator's implementation of memory. External input loading is outside
the sorting routine's cost.

Runtime syntax cannot contain arbitrary Lean functions, `pure`, cost resets,
or user-supplied state transformations. Ghost annotations may use ordinary
Lean mathematics because the compiler erases them. The old shallow `RAM.lean`
remains only a reference memory specification; its cost annotations are never
used to justify the checked algorithm's time. `no_zero_time_sort` proves that
no checked program can sort every input in zero operations.

```sh
lake build AlgoLib.Experimental.RAM.Tests
lake build
```
