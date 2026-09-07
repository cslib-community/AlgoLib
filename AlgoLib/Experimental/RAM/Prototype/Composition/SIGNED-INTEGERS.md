# Signed integers in `ram method`

Use `Int` when subtraction should produce a negative number. Use `Nat` for
quantities whose mathematical meaning is nonnegative. Both run on the default
Int-RAM backend, and both use the existing generated obligation API.

```lean
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly
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

The source semantics and proofs use Lean `Int`. The current verified compiler IR
still has natural-valued words. Signed scalars therefore use private canonical
positive/negative lanes and staging registers; signed arrays use two adjacent
cells per element. Array layouts have independent base addresses, so separate
arrays can be linked using the existing separating encoder interface. All compiled
instructions execute on **Int-RAM**. This stage
does not claim direct, single-register signed lowering.

The representation contracts prove reads, writes, ownership framing, and decoding.
Staging evaluates indices and both result lanes before changing a destination,
so self-referential assignments preserve source evaluation order. Layout choices
and intermediate payment details do not appear in algorithm obligations.

Costs include the actual expanded expression and storage operations. The generated
RAM bound retains the conservative translation factor used by the existing stack.
Unbounded unit-cost integer arithmetic is still not a word-RAM or bit-complexity
claim. A future direct integer compiler can replace this private representation
while retaining mathematical source proofs; numerical bounds may improve.

## Checked evidence and navigation

- `Tests/SignedFrontend.lean`: public syntax, signed scalar/array execution, loops,
  conversions, procedure composition, and generated correctness/cost theorems.
- `Tests/Conformance/Signed.lean`: generated combinations checked against an
  independent Python evaluator, including negative inputs and nested loops.
- `Tests/SignedOwnership.lean`: one source proof for two independently placed
  signed arrays, with private signed scratch storage.
- `SignedArithmetic.lean`: canonical arithmetic identities.
- `SignedImplementation.lean`: reusable signed expression and storage contracts.
- `SignedStorage.lean` and `SignedArrays.lean`: private implementations and encoders.
- `Frontend/Expressions.lean`: type-directed source expression elaboration.

Regenerate signed differential tests with
`python3 AlgoLib/Experimental/RAM/Tests/Conformance/generate_signed.py`;
use `--check` to detect stale fixtures.
