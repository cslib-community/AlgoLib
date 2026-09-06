# One frontend, one program, one proof

Start with [MixedAlgorithms.lean](MixedAlgorithms.lean) for a small example, then
[Sorting.lean](Sorting.lean) for insertion sort with both loops visible. These files
import no RAM implementation. They use the same `ram method` elaborator and produce
`Composition.Program` with its indexed `Plan`.

## What changed

There is no longer an array-versus-owned-method dispatch. Direct indexing, scalar
expressions, mutable locals, and owned procedure calls coexist in the same method,
including inside nested loops. Arrays and scalars have ownership interfaces just
like library resources.

For example, the body of `MixedAlgorithms.mixed` is:

```lean
let x := b[0]!
buffer.clear()
a[0] := x + 1
count := a[0]!
```

Its input and output type is `Array Nat × Array Nat × List Nat × Nat`.
The compiler-generated register for `x` is absent from both interfaces.
The specification requires nonempty arrays and guarantees:

```lean
a[0]! = bOld[0]! + 1
b = bOld
buffer = []
count = bOld[0]! + 1
```

The method has no explicit credit budget. The frontend adds the expression charges,
local initialization, and the public allowance of `clear`. Both lazy and eager
buffer implementations reuse this exact method and proof. Their actual step counts
differ; the caller never sees the eager implementation's saved potential.

Computed values can also cross the call boundary directly. The checked
`appendHead` example contains:

```lean
let x := a[0]!
buffer.append(capacity, x + 1)
```

Evaluation, argument copying, the call's public allowance, and private local
initialization are all included automatically. `callWithFrame` also demonstrates
`(a, b) := addBothProcedure`: a procedure updates two distinct owned variables while
an intervening buffer is framed automatically. Passing the same owned variable
in both positions is rejected.

## Writing and proving a method

1. **Declare the interface.** `(mut a : Array Nat)` and `(mut n : Nat)` are runtime
   inputs whose final values form the output. Other owned mathematical types, such
   as `List Nat` buffers, can appear beside them. Immutable binders configure fixed
   code before execution; they are not mutable runtime registers.
2. **State the mathematical contract.** `aOld` denotes the original array.
   The declared result name denotes the tuple of public final values, or `()` for
   a `Unit` result annotation. Local variables never enter that tuple.
3. **Write ordinary code.** Use assignments, arithmetic, indexing, conditionals,
   and calls. Every runtime expression becomes typed source syntax; an arbitrary
   Lean function cannot silently become a constant-cost machine operation.
4. **Annotate loops.** Supply textbook invariants and a logical allowance using
   `remaining`. `decreasing` adds a checked decrease obligation; `done_with` adds a
   checked exit assertion. Initialization, preservation, exit, array safety, and
   sufficient credits are generated. The frontend does not discover invariants.
5. **Prove the generated obligations.** `prove_algorithm name by ...` exports
   `nameProcedure`. Use `contract_vc` to inspect the mathematical conditions, or
   `contract_solve [your_lemmas]` to normalize plumbing and apply mathematical lemmas.
   This is the same procedure used for Loom reasoning and RAM compilation.
6. **Use the supplied runner.** For insertion sort:

   ```lean
   import AlgoLib.Experimental.RAM.Prototype.Composition.SortingExecution

   #eval AlgoLib.Experimental.RAM.Prototype.Composition.Sorting.run [4, 1, 3, 1]
   #eval (AlgoLib.Experimental.RAM.Prototype.Composition.Sorting.run [4, 1, 3, 1]).value
   -- [1, 1, 3, 4]
   ```

   There is no fuel argument. `Sorting.main` proves sortedness, permutation, and a
   quadratic bound for this executable.

`Sorting.minimumAfterSort` illustrates composition: call the verified array sorter,
then read `arr[0]!` into an ordinary scalar. The caller proves array safety from the
callee's permutation contract. It never opens the sorting loops or their private
register layout.

## How the components connect

| Component | Responsibility | What an algorithm author supplies |
|---|---|---|
| [LogicalFrontend](../LogicalFrontend.lean) | One declaration and proof command | Code, contracts, invariants |
| [Frontend](Frontend.lean) | Scope checking, typed paths, guard materialization, automatic frames and local hiding | Nothing additional |
| [Expressions](Expressions.lean) | Independent expression semantics, bounds and logical charges | Mathematical safety proofs |
| [Contracts](Contracts.lean) | Indexed plans; calls use public summaries; total-correctness soundness | Generated source obligations |
| [Loom](Loom.lean) | Actual Loom WP for the same program | The same source proof |
| [ExpressionImplementation](ExpressionImplementation.lean) | Ownership-directed expression certificates and updates | Nothing |
| [Storage](Storage.lean) | Verified scalar and array implementations | Nothing |
| [LocalImplementation](LocalImplementation.lean) | Private local initialization and scope boundaries | Nothing |
| [Encoding](Encoding.lean) | Compositional resident inputs, local layout reconstruction, fuel-free runner | Ordinary input values |
| [Linking](Linking.lean) | Reconstruct composition certificates and invoke the existing RAM compiler | Nothing |

`Focus` opens only the selected component and restores the surrounding ownership
and saved resources. `ArrayStorage` and `ScalarStorage` provide read/update contracts.
The compiler combines these certificates for every accepted expression. It cannot
link a missing primitive implementation, even in an unchosen branch.

At method boundaries local values are existentially hidden. Entering a method
executes and pays for their initialization; leaving hides their values while retaining
ownership. Direct array access also works through such a private-storage wrapper,
so a caller can index an array around a procedure that uses its own locals.

## Supported scope and accounting

- Scalars: `Nat`; immutable and mutable locals; literals/configuration constants;
  `+`, truncated subtraction `-`, `*`.
- Arrays: separately owned `Array Nat` values, `.size`, indexed reads and writes.
  Both `a[i]` and `a[i]!` generate bounds obligations.
- Control: scalar comparisons, certified resource queries, branches, nested annotated
  loops, assertions, and a method-final return.
- Procedures: typed owned receivers, public functional/credit summaries, automatic
  framing, and statically composed verified bodies. Inferred straight-line methods
  also export a reusable uniform allowance.
- Receiver calls support a trailing runtime `Nat` expression, with preceding
  arguments configuring fixed code. Library authors supply a verified `nameFrom`
  procedure on `(receiver, Nat)`; users write `receiver.name(config, expression)`.
  Paired assignment calls accept two distinct owned variables of arbitrary supported
  types. Argument routing is certified structural regrouping, not memory copying.
- A call expression denotes fixed code. Runtime data must travel in the procedure's
  typed input; it cannot specialize a Lean expression that manufactures the code.
  This is not a compiler for arbitrary ordinary Velvet or unrestricted Lean values.
- Natural-number locals currently have distinct names throughout a method; lexical
  scope and immutability are checked. Early returns and dynamically allocated local
  arrays are outside this frontend.

Logical credits are separate from RAM steps. Initialization and every compiled
instruction are covered by the backend theorem. Resident input encoding and final
host-side decoding remain outside the machine execution, consistently with the
existing RAM interfaces. The explicit quadratic corollary is derived from the
logical proof and the selected backend; it is not a time annotation on the algorithm.

## Compatibility and verification

[LegacyArrayFrontend](../LegacyArrayFrontend.lean) is available only through an
explicit compatibility import and the `legacy_ram` command. It preserves existing
contiguous/indirect array substitution proofs and their compiler regressions.
It is not called by the public frontend. Removing it now would delete still-used
verified examples; new methods should use the owned frontend above.

[MixedFrontend tests](../../Tests/MixedFrontend.lean) check actual RAM outputs, both
buffer implementations, nested mixed loops, inequality compilation, private locals,
lexical rejection, unsafe indexing, computed call arguments, and paired calls. [SortingExecution](SortingExecution.lean)
checks the compiled sorter against Lean's independent sorting reference.
The existing axiom checks and compiler proofs remain part of the full build.
