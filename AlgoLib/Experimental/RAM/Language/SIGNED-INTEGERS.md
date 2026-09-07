# Signed integers in `ram method`

Use `Int` when subtraction should produce a negative number. Use `Nat` for
quantities whose mathematical meaning is nonnegative. Both run on the default
Int-RAM backend, and both use the existing generated obligation API.

```lean
import AlgoLib.Experimental.RAM.Compiler.Assembly
open AlgoLib.Experimental.RAM.Prototype.Composition
open AlgoLib.Experimental.RAM.Prototype.Frontend

ram method subtractFive (mut x : Int) return (result : Int)
  ensures result = xOld - 5
  do
    x := x - 5

generate_obligations subtractFive
complete_algorithm subtractFive
compile_scalar_method subtractFive

#eval (subtractFiveRun 3).value -- -2
#check subtractFiveCorrect
#eval subtractFiveBound 3
```

`compile_scalar_method` emits `Run`, `Bound`, and `Correct`. The theorem joins the
method's functional postcondition to its inferred RAM instruction upper bound.
You supply mathematical invariants and counting arguments for loops; you do not
supply a representation proof, a fuel value, or a new compiler theorem.

## Arithmetic and conversions

| Source construct | Meaning |
| --- | --- |
| `let mut x : Int := -3` | Mutable signed local |
| `x + y`, `x - y`, `x * y`, `-x` | Ordinary integer arithmetic when operands are Int |
| `n - m` with Nat operands | Saturating natural subtraction, unchanged |
| `Int.ofNat n` | Exact embedding from Nat to Int |
| `Int.toNat x` or `x.toNat` | Explicit truncation: negative values become zero |
| `x < y`, `x ≤ y`, `x == y`, `x != y` | Comparisons in the operands' arithmetic domain |

The expected assignment type determines the type of numeric literals. An untyped
local initialized from a signed expression is inferred as `Int`; spell `: Int`
when a positive literal or fixed configuration should start a signed computation. Mixed runtime
arithmetic requires an explicit conversion. For example, write `x + Int.ofNat n`,
not `x + n`. Division, rationals, bit operations, and arbitrary Lean functions are
not part of this arithmetic frontend.

Logical credits, RAM step counts, and iteration bounds remain `Nat`. For a signed
countdown, the paper argument can use a natural measure:

```lean
ram method countdown (mut x : Int) return (result : Int)
  require 0 ≤ x
  ensures result = 0
  do
    while 0 < x named count
      invariant "nonnegative" 0 ≤ x
      iterations_at_most x.toNat
      do
        x := x - 1

generate_obligations countdown
complete_algorithm countdown
compile_scalar_method countdown
```

Nontrivial mathematical facts still belong in separate `prove_obligation` blocks.
For example, the tested absolute-value method discharges its `result` obligation
with `simp_all [abs_of_neg, abs_of_nonneg]` before completion. The obligation
explorer works on the same API as for Nat methods.

## Arrays and procedure composition

`Array Int` uses ordinary indexed reads and writes. `compile_array_method` accepts
either `Array Nat` or `Array Int`; its runner consumes and returns the corresponding
ordinary Lean lists. A natural loop counter can coexist with signed array values:

```lean
ram method shiftArray (mut arr : Array Int) return (result : Unit)
  ensures arr.size = arrOld.size
  do
    let mut i : Nat := 0
    while i < arr.size named scan
      invariant "position" i ≤ arr.size
      invariant "length" arr.size = arrOld.size
      iterations_at_most arr.size - i
      do
        let mut x : Int := arr[i]!
        x.subtractFiveProcedure()
        arr[i] := x
        i := i + 1

generate_obligations shiftArray
complete_algorithm shiftArray
compile_array_method shiftArray
```

Here the **stated** functional theorem preserves length; the executable regression
also checks that every element is shifted by five. A pointwise functional theorem
would need the corresponding processed-prefix invariant. Calling the already
certified `subtractFiveProcedure` uses its modular contract.

A signed index generates a nonnegativity requirement as well as an upper-bound
requirement. `arr[i]` with `i : Int` must prove `0 ≤ i` and `i.toNat < arr.size`.
Writing `arr[i.toNat]` instead requests explicit truncation; those are different
source programs. Mathematical Lean array formulas in invariants should use the
natural index `i.toNat`.

## Implementation and cost boundary

The source semantics and proofs use Lean `Int`. Standard scalar and array assembly
now lowers directly into the native integer implementation language and its verified
Int-RAM compiler. A signed scalar occupies one integer register, and a signed array
element occupies one consecutive heap cell. Nat values retain nonnegativity and
saturating subtraction. The source algorithm and its proof do not change.

Shared ownership, path focusing, private-local initialization, and resident-input
contracts automatically preserve unrelated components and private potential. The
same interfaces support separate array bases, mixed Nat/Int locals, and calls.

Logical credits are unchanged. Native expression certificates provide alternative
code views for signed values, their negations, and truncated natural parts. Only the
requested view executes; these are not paired storage lanes. Swapping code views
eliminates repeated negations, and truncating the negative of an embedded Nat can
emit zero directly. This preserves the existing cheap source allowances without
hiding runtime computation in decoding.

The generated RAM bound retains the conservative factor-two allowance during
migration, while the runner counts actual native instructions. Unbounded unit-cost
integer arithmetic is still not a word-RAM or bit-complexity claim. Legacy paired
storage modules remain compatibility work and are not selected by standard
`compile_scalar_method` or `compile_array_method` assembly.

## Checked evidence and navigation

- `Tests/SignedFrontend.lean`: public syntax, signed scalar/array execution, loops,
  conversions, procedure composition, and generated correctness/cost theorems.
- `Tests/Conformance/Signed.lean`: generated combinations checked against an
  independent Python evaluator, including negative inputs and nested loops.
- `Tests/SignedOwnership.lean`: one source proof for two independently placed
  signed arrays, with private signed scratch storage.
- `Tests/NativeArrays.lean`: checks consecutive native signed cells through standard assembly.
- `Native/Expressions.lean` and `Native/ArrayExpressions.lean`: semantic and credit certificates.
- `Native/ScalarStorage.lean` and `Native/ArrayStorage.lean`: native representations.
- `Native/Locals.lean`, `Native/Encoding.lean`, and `Native/Execution.lean`: automatic framing,
  resident inputs, and certified execution.
- `Frontend/Expressions.lean`: type-directed source expression elaboration.

Regenerate signed differential tests with
`python3 AlgoLib/Experimental/RAM/Tests/Conformance/generate_signed.py`;
use `--check` to detect stale fixtures.

## Source navigation after reorganization

Module import paths follow the [layer map](../README.md).
Existing declaration namespaces are retained. For the complete program / obligations /
proofs / execution reading order, use the example entry pages linked there. Older short
module names in explanatory prose can be resolved with the migration table.
