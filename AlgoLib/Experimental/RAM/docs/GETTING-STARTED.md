# Your first certified RAM method

This tutorial starts with the existing sorting and BFS runners, then builds a small
integer absolute-value method. You will write its contract, inspect the generated
proof obligations, prove them, compile the method, and use its correctness theorem.
The complete checked companion is [Tests/GettingStarted.lean](../Tests/GettingStarted.lean).

You need basic Lean syntax and the idea of a Hoare triple: assuming a precondition,
executing a program establishes a postcondition. Knowledge of the RAM compiler,
register allocation, or memory representations is unnecessary for this example.

## 1. Check the working examples

Run these commands from the repository root, using the Lean version selected by
`lean-toolchain` and the repository's Lake dependencies:

```sh
lake build AlgoLib.Experimental.RAM.Tests.GettingStarted
```

This builds the dependencies and checks the tutorial, including its executions.
The first build also checks the imported sorting and BFS infrastructure and can
take substantially longer than a later edit. Once dependencies are built, use:

```sh
lake env lean AlgoLib/Experimental/RAM/Tests/GettingStarted.lean
```

Open that file in a Lean-aware editor to see each command's messages and proof
state. For a separate experiment, copy it to `RAMScratch.lean` at the repository
root and run `lake env lean RAMScratch.lean`.

The first two evaluations exercise the supported public runners:

```lean
import AlgoLib.Experimental.RAM.Examples

open AlgoLib.Experimental.RAM

#eval (Examples.InsertionSort.run [3, 1, 2, 1]).value
-- [1, 1, 2, 3]
#eval (Examples.BFS.search .circular Examples.BFS.Inputs.diamond ⟨0, by decide⟩).value
-- {0, 1, 2, 3}

#check Examples.InsertionSort.main
#check Examples.BFS.search_correct
#check Examples.BFS.linear
```

This block can be copied into a fresh Lean file by itself. The BFS input is a
four-vertex diamond; `⟨0, by decide⟩` supplies vertex zero together with a proof
that it is a valid source. The returned `Finset` contains the reachable vertices.
The source proof is required by the interface, not an unchecked integer cast.

`InsertionSort.main` proves that the output is a sorted permutation and bounds
the same runner's RAM steps. `BFS.search_correct` characterizes membership by
reachability, while `BFS.linear` bounds steps by a constant times vertices plus
edges. These are theorems for arbitrary valid inputs; the two `#eval` commands
only demonstrate particular executions. Public aliases may print their original
qualified names in `#check` output; see the [public API policy](PUBLIC-API.md).

## 2. Write, prove, and run one complete method

The following is a complete second file. Copy the entire block into a fresh Lean
file in this checkout, or work in the checked companion. It uses only the public
entry modules and ordinary Lean integer lemmas.

```lean
import AlgoLib.Experimental.RAM.Language
import AlgoLib.Experimental.RAM.Verification
import AlgoLib.Experimental.RAM.Compiler

namespace AlgoLib.Experimental.RAM.Tests.GettingStarted

set_option linter.hashCommand false

ram method magnitude (mut x : Int) return (result : Int)
  ensures result = |xOld|
  do
    if x < 0 then
      x := -x

generate_obligations magnitude

#check magnitude.ObligationAPI.result
#named_goals magnitude only result
#proof_template magnitude only result

prove_obligation magnitude.ObligationAPI.result by
  simp_all [abs_of_neg, abs_of_nonneg]

#named_goals magnitude only result

complete_algorithm magnitude
compile_scalar_method magnitude

#check magnitudeVerification
#check magnitudeProcedure
#check magnitudeCorrect

theorem magnitude_correct (x : Int) :
    (magnitudeRun x).value = |x| ∧ (magnitudeRun x).steps ≤ magnitudeBound x := by
  simpa using magnitudeCorrect x (by trivial)

theorem magnitude_nonnegative (x : Int) : 0 ≤ (magnitudeRun x).value := by
  rw [(magnitude_correct x).1]
  exact abs_nonneg x

#eval (magnitudeRun (-7)).value
-- 7
#eval (magnitudeRun 0).value
-- 0
#eval (magnitudeRun 9).value
-- 9
#eval ((magnitudeRun (-7)).steps, magnitudeBound (-7))
-- (15, 2256)
#eval (magnitude.credits (-7))
-- 47

end AlgoLib.Experimental.RAM.Tests.GettingStarted
```

The companion additionally guards the displayed values with `#guard_msgs` and
checks all three executions against the postcondition and generated bound. If a
cost-model change alters these numbers, the fixture fails until its expectations
and this tutorial are updated.

### Read the contract

`mut x : Int` is the mutable input. The header names its final scalar result
`result`; the body needs no explicit `return x`. For a negative input it negates
`x`, and otherwise leaves it unchanged. With no `require` clause, this method has
the trivial precondition: every integer is allowed.

`xOld` denotes the original input in the specification. It is a logical value,
not a request to copy the input into an extra RAM register. Thus
`ensures result = |xOld|` states the usual absolute-value specification. Absolute
value occurs only in the specification; the executable body uses a comparison
and negation supported by the frontend.

### Inspect the generated responsibility

`generate_obligations magnitude` declares ordinary Lean propositions and a
checked assembly theorem connecting their proofs to the method's obligations.
It also caches proofs for routine obligations that automation can discharge.
Generation alone does not complete the method.

`#check magnitude.ObligationAPI.result` reports a declaration of type `Prop`.
The first `#named_goals` reports `[open] result` and displays these two contexts:

```text
case result
xInput : ℤ
h✝ : xInput < 0
⊢ -xInput = |xInput|

case result
xInput : ℤ
h✝ : 0 ≤ xInput
⊢ xInput = |xInput|
```

These are the paper proof's two cases. In the negative branch, the result is
`-xInput`; in the other branch it is `xInput`. One responsibility can retain
several control-flow paths, and its proof must establish every path.
The generated `xInput` is the proof-context name for the method's original
input; local display names can evolve without changing the responsibility name.

`#proof_template magnitude only result` prints a `prove_obligation` block whose
body deliberately fails with “Supply the mathematical argument here”. This is
an editing aid: the inspection command creates no proof. Replace the failing
body with the mathematical argument shown in the full example.

`abs_of_neg` and `abs_of_nonneg` express the two familiar absolute-value facts.
`simp_all` uses the branch hypothesis to rewrite the absolute value and close the
equality. The command saves a checked theorem named
`magnitude.ObligationAPI.result_proof`; the next preview reports `[proved] result`.
Use the full proposition name with `prove_obligation` and the short responsibility
path after `only` with the preview commands.

### Finish the source proof and compile

`complete_algorithm magnitude` combines the explicit proof with checked routine
proofs. It produces `magnitudeVerification` and the verified procedure
`magnitudeProcedure`. Missing evidence is an error; completion does not assume
the desired postcondition.

`compile_scalar_method magnitude` supplies the standard scalar representation,
links the supported operations to the verified integer RAM backend, and emits:

| Declaration | What you use it for |
| --- | --- |
| `magnitudeRun x` | Execute and obtain `.value` and `.steps`, without a fuel argument |
| `magnitudeBound x` | Compute the generated upper bound on RAM steps |
| `magnitudeCorrect x valid` | Prove the procedure's postcondition and the bound for that runner |

The generated correctness theorem speaks in terms of the procedure contract.
`magnitude_correct` unfolds that contract by simplification into the familiar
statement about absolute value and steps. Its `by trivial` supplies the method's
precondition. A method with a nontrivial precondition would require a proof of it
both when running and when using its correctness theorem.

Finally, `magnitude_nonnegative` demonstrates an ordinary client proof. It uses
the correctness theorem and `abs_nonneg`; no compiler internals or execution
tests enter the argument. The theorem is universal even though the examples
evaluate only `-7`, `0`, and `9`.

## 3. Interpret the costs correctly

The current checked negative-input example reports:

| Quantity | Value | Meaning |
| --- | ---: | --- |
| `magnitude.credits (-7)` | 47 | Inferred logical allowance for source operations |
| `(magnitudeRun (-7)).steps` | 15 | Actual instructions executed by this RAM runner |
| `magnitudeBound (-7)` | 2256 | Certified upper bound on those instructions |

Logical credits are the accounting interface used by source proofs and procedure
contracts. They are not actual RAM instruction counts. The standard scalar
assembly currently uses a conversion rate of 24 and a conservative factor of 2;
with zero saved potential here, `2 * (24 * 47) = 2256`. The theorem proves an
upper bound, so the slack between 15 and 2256 is expected. These constants are
implementation details that can change; client proofs can use `magnitudeBound`
without spelling them out.

The machine uses unbounded integers with unit-cost arithmetic. The bound is not
a claim about Lean evaluation time, a physical CPU, fixed-width word overflow,
or bit complexity. Input encoding and output observation are host-side work
outside the reported instruction count. For sorting and BFS, input arrays and
graph storage are resident before the measured RAM body starts; their example
documentation explains the precise boundaries.

## 4. Extend the example without skipping proof obligations

For loops, supply a named invariant and a decreasing remaining iteration bound.
`iterations_at_most` is checked at loop heads; a constant total estimate is not
automatically a valid remaining bound. The frontend generates initialization,
preservation, termination, accounting, safety, and exit responsibilities as
appropriate. It does not discover an algorithm's mathematical invariant.

Continue with these maintained paths:

- [Insertion sort](../Examples/InsertionSort/README.md): arrays, nested loops,
  a sorted-prefix argument, and a quadratic RAM bound.
- [BFS](../Examples/BFS/README.md) and its [proof walkthrough](../Examples/BFS/TUTORIAL.md):
  reachability, work accounting, and two interchangeable queue implementations.
- [Generated obligation API](../Verification/OBLIGATION-API.md): focused previews,
  explanations, proof templates, lemma suggestions, and separate proof modules.
- [Loop accounting](../Language/PAPER-LOOPS.md) and
  [signed arithmetic](../Language/SIGNED-INTEGERS.md): the supported annotations
  and arithmetic operations.
- [Public layer map](../README.md) and [API policy](PUBLIC-API.md): where to put
  a new feature and which imports to use.

The standard convenience commands accept one `Nat` or `Int` scalar input, or one
`Array Nat` or `Array Int` input. Richer interfaces need explicit assembly and
storage contracts, as BFS demonstrates. Arbitrary Lean functions are not
automatically compilable runtime primitives; division, rationals, and bit
operations are outside this arithmetic frontend. `Nat` subtraction saturates
at zero, while `Int` subtraction can produce negative values.

This tutorial keeps everything together for a first experiment. For a maintained
algorithm, follow insertion sort's module split: source program, generated
obligations, mathematical proofs, backend certificate, and executable assembly.
That separation lets proof edits reuse expensive backend work. The repository's
[RAM contributor guide](CONTRIBUTING.md) and the RAM module
inventory describe the accompanying registration and validation work.
