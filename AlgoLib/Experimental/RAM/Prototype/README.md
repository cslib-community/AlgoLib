# Mutable programs, inline invariants, verified RAM execution

The complete [owned BFS tutorial](Composition/OWNED-BFS.md) shows one paper-style
program and proof running with a circular buffer and an amortized two-stack FIFO,
with graph correctness and a linear bound on actual RAM instructions.

For the current paper-style loop workflow, see the
[paper loop tutorial](Composition/PAPER-LOOPS.md): inferred allowances, named VCs,
and automatically assembled executable theorems.

Start with **[the unified frontend tutorial](Composition/FRONTEND.md)** and
[MixedAlgorithms.lean](Composition/MixedAlgorithms.lean). Arrays, ordinary scalar
locals, and owned procedure calls now share one typed program and one contract VCG.
[Sorting.lean](Composition/Sorting.lean) contains both insertion-sort loops;
[SortingExecution.lean](Composition/SortingExecution.lean) runs that exact program
on ordinary Lean lists and proves its correctness and quadratic RAM bound.

[Composition](Composition/README.md) explains ownership, private potential, and
automatic client linking. The same mixed client proof runs with lazy and eager
buffers. Source proofs import no RAM backend, and generated locals do not appear
in public input/output types.

The older examples below remain compatibility regressions for their existing
compiler and array-substitution proofs. They use the explicit `legacy_ram` adapter;
the public `ram method` frontend never dispatches to it. The historical source/proof
workflow is described in [Generality and substitution](../docs/GENERALITY-AND-SUBSTITUTION.md).

For the ordinary-Velvet semantic bridge, nondeterministic execution, recursive
example, and precise remaining compiler work, see
[Compilation status and demos](COMPILATION-STATUS.md). Full ordinary-Velvet
compilation is not yet implemented.

For graph algorithms, start with the [BFS tutorial](GRAPH-TUTORIAL.md),
[BFS.lean](BFS.lean), and its [graph procedures](Graph.lean). The generic
`ram_do` frontend now supports typed graph/queue/cursor primitives and verified
procedure composition with real inlined RAM bodies. `Prototype.Frontend` exports
both `legacy_ram method` and `ram_do`; import `Prototype.Graph` for the graph operations.

The historical array-substitution program is [SortingAlgorithm.lean](SortingAlgorithm.lean). It exposes
both insertion-sort loops and every array operation. There is no `InsertNext` action, hidden insertion
procedure, or student-written implementation proof.

```lean
import AlgoLib.Experimental.RAM.Prototype.InsertionSort
open AlgoLib.Experimental.RAM.Prototype

#eval (InsertionSort.run [5, 2, 4, 1, 6]).value
-- [1, 2, 4, 5, 6]

#check InsertionSort.main
#check InsertionSort.quadratic
#check InsertionSort.loom_correct
```

`main` proves a sorted permutation and at most `300*n² + 300*n + 360` executed
RAM instructions for **every** input, including the empty array. `quadratic` gives
`960*n²` for nonempty inputs. These conservative constants pay for the explicit
array implementation and all its guards and scalar bookkeeping. `run` takes no fuel.

## Write the algorithm

The command is `legacy_ram method`, followed by Velvet-style input/output clauses and a
`do` body. For this adapter, the mutable inputs and outputs are one or more `Array Nat` values;
`return (u : Unit)` means the result is the updated array, with no additional scalar
return. `arrOld` denotes the input array in specifications.

The complete checked program includes these lines:

```lean
legacy_ram method insertionSort (mut arr : Array Nat) return (u : Unit)
  require True
  ensures SortedPermutation arrOld.toList arr.toList
  credits potential arr.size 0 + 20
  do
    let mut i := 0
    while i < arr.size
      invariant i ≤ arr.size
      invariant Prefix arr i
      invariant arr.toList.Perm arrOld.toList
      invariant arr.size = arrOld.size
      invariant potential arr.size i ≤ remaining
      decreasing arr.size - i
      do
        let mut j := i
        while 0 < j
          invariant j ≤ i
          invariant i < arr.size
          invariant Hole arr i j
          invariant arr.toList.Perm arrOld.toList
          invariant arr.size = arrOld.size
          invariant potential arr.size (i + 1) + 100 * j + 20 ≤ remaining
          decreasing j
          do
            let x := arr[j]!
            let y := arr[j - 1]!
            if x < y then
              arr[j] := y
              arr[j - 1] := x
            j := j - 1
        i := i + 1
    return
```

`Prefix arr i` says the positions before `i` are ordered. `Hole arr i j` says the
prefix through `i` is ordered except possibly at position `j`. A comparison and
adjacent swap move that exception left. At `j = 0`, the larger prefix is ordered.
[SortingFacts.lean](SortingFacts.lean) proves precisely those mathematical facts,
using ordinary arrays, indices, and permutation. It imports no RAM or compiler code.

`remaining` is proof-only: the credits available at a loop boundary. The user
chooses the potential; the verifier substitutes operation costs and proves the
arithmetic. The compiler derives the RAM bound automatically from those credits;
no compiler scaling factor appears in the program. A `time` clause is rejected: the
backend supplies the RAM bound automatically. Decreasing measures generate genuine
obligations as well. Invariants
are supplied by the author, never guessed by the automation.

## Prove and run it

The sorting proof uses the facts about the algorithm:

```lean
prove_ram insertionSort by
  ram_solve [potential_positive, insertion_allowance, SortedPermutation,
    Prefix, Hole, enter, exit, keep, swap, swap_perm, sorted, List.Perm.trans]
```

This command generates `insertionSortVerification` and `insertionSortVerified`.
The latter offers `.run input proofOfRequires` and `.correct input proofOfRequires`.
The list convenience wrapper `InsertionSort.run` discharges its trivial precondition.

For interactive work, use `ram_vc` to expand contracts and costs. Split logical
conditions and run `ram_names` to replace internal state projections by ordinary
array and local-variable names. `ram_solve` performs those steps and uses the
supplied mathematical lemmas with Lean’s proof-producing `grind` tactic. A failed
condition stays a Lean goal; it is never admitted.

The compiler automatically preserves locals that a nested loop does not write.
For example, the inner loop retains `i` without an extra user invariant equating it
to a saved compiler variable. Array updates preserve other locals and the allocation
size through generic checked primitive contracts. No adjacency pointers, addresses,
register relations, or compilation certificates appear in this sorting proof.

[Tests.lean](Tests.lean) also verifies a separate array-filling program using the
same frontend. This checks that the adapter is compositional, rather than recognizing
insertion sort as a special case.

## How the components connect

```text
Velvet do syntax + input/output contracts + inline invariants
                         │
                    Frontend.lean
                         │
              one fixed Program + indexed Plan
                    ┌────┴─────┐
                    │          │
             Interpretation    existing verified compiler
                    │          │
        costed state execution │
                    │          │
       actual Loom MAlg / wp   │
                    │          │
        Plan.vc → Plan.sound   │
                    │          │
               reconstruct ────┤
                               │
                      RAM execution + theorem
```

| Component | Responsibility | What the author supplies |
|---|---|---|
| [Frontend](Frontend.lean) | Parse mutable code; choose private locals; materialize guards; infer frames; attach annotations | Program, contracts, invariants, potential |
| [Mutable](Mutable.lean) | Reusable assignment, array-read, array-write, comparison and memory-frame certificates | Nothing machine-specific |
| [Observation](Observation.lean), [Interpretation](Interpretation.lean) | Independent finite execution semantics and connection to the existing source/compiler | Nothing |
| [LoomObservation](LoomObservation.lean) | Instantiate upstream `MAlgOrdered`; identify its `wp` with the cost observation | Nothing |
| [Verification](Verification.lean) | Generate conditions, prove their soundness, reconstruct a backend certificate | Mathematical lemmas for the generated conditions |
| [InsertionSort](InsertionSort.lean) | The program, inline annotations, one proof command, executable and main theorem | The textbook sorting argument |
| [Axioms](Axioms.lean), [FrameworkTests](FrameworkTests.lean), [Tests](Tests.lean) | Kernel-dependency guards, framework integration, runtime and rejection regressions | Nothing |

The body is independent of the input and invariant proofs. `Plan p` is indexed by
that exact body, so a proof for one program cannot certify another. `denote_iff_run`
and `compilation_sound` connect the independent interpretation to actual RAM
execution. The frontend creates primitive certificates automatically; those
certificates are checked, not trusted parser assertions.

## Actual upstream reuse and the compilation boundary

The [vendored frameworks](../../../../vendor/README.md) contain **the actual Velvet
parser and Loom hierarchy**, with explicit upstream authorship and Apache-2.0
licenses. This replaces the previous local-only Loom-style specialization.
Loom’s ordered, deterministic, partial, and total algebras, logical/monadic lifts,
ReaderT, StateT, ExceptT, nondeterminism, WP generation, and tactics are available.
`FrameworkTests` checks composed transformers and Velvet’s own `method`, procedure
contracts, `prove_correct`, `loom_solve`, and executable extraction.

There is one current owned frontend alongside the historical integration entry points:

- `ram method`: the unified owned frontend described in [FRONTEND.md](Composition/FRONTEND.md).
  Direct arrays, scalar locals, computed arguments, paired calls, and annotated loops
  share one program and contract VCG.

- `ram_do`: generic certified-interface code with procedure calls, branches,
  assertions, and Velvet-style annotated loops. The graph adapter provides
  adjacency, visited-set, FIFO, and cursor operations; see [the tutorial](GRAPH-TUTORIAL.md).
- `method`: upstream Velvet, with its full syntax and supported Lean effects.
- `legacy_ram method`: the verified RAM adapter, currently natural-number locals and one
  or more mutable `Array Nat` parameters; literals, size, addition/subtraction/multiplication, indexing,
  updates, comparisons, branches, nested annotated `while` loops, assertions,
  `done_with`, and final unit return. Nat subtraction is truncated at zero.

**The full Velvet language is not yet fully lowered to RAM.** Arbitrary Lean calls,
allocation, nondeterministic choice, recursive calls, early return,
`break`/`continue`, and other unimplemented RAM constructs are rejected by this
adapter. Separate checked ordinary-Velvet translation examples now cover choice,
a procedure call, multiple arrays, and recursion; see [the coverage table](COMPILATION-STATUS.md).
An ordinary Velvet correctness proof alone does not imply a RAM time bound.
This boundary is deliberate: accepting arbitrary host computations as free RAM
operations would reintroduce the cheating problem.

Time counts executed unit-cost RAM instructions, including all loop tests, array
operations, and scalar operations. Input encoding and output observation are the
interface convention: the input array is already resident in RAM. Host Lean runtime
and bit complexity of unbounded integers are not what the theorem measures.

## Trust and checks

Every proof is a Lean term checked by the kernel. Trusted SMT and asynchronous
admission paths from upstream are excluded. The port’s executable specialization
of Loom extraction is proved equal to the original extractor. Existing production
axiom checks remain in place; prototype checks cover its new bridges and theorems.

```sh
lake build AlgoLib.Experimental.RAM.Prototype.Tests \
  AlgoLib.Experimental.RAM.Prototype.FrameworkTests \
  AlgoLib.Experimental.RAM.Prototype.GraphTests \
  AlgoLib.Experimental.RAM.Prototype.Axioms
python3 AlgoLib/Experimental/RAM/Tests/check_layers.py
```

The prototype stays isolated from the production `Programs` directory. Existing
production BFS remains available. The new prototype BFS independently verifies its own
composed program, reusing the graph primitive certificates and mathematical lemmas.

Logical credits and RAM costs are now separate: methods declare `credits`, and the selected backend infers `time`. See [the credit/backend guide](../docs/CREDITS-AND-BACKENDS.md) for certificate composition and proof reuse.
