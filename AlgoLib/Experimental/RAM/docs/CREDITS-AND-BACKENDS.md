# Logical credits and inferred RAM time

An algorithm author proves a mathematical result within a **logical credit budget**.
The selected backend proves how much RAM work implements those credits. The two
quantities have separate definitions and separate responsibilities.

## What you write

The input/output declaration has `requires`, `ensures`, `credits`, and the program.
There is no `time` clause:

```lean
ram_method (xs : List Nat) returns (ys : List Nat)
  using Insertion.interface;
  requires True;
  ensures SortedPermutation xs ys;
  credits (xs.length * (xs.length + 2) + 1);
do {
  while (Insertion.more) {
    call Insertion.insertNext;
  }
}
```

This is the library-procedure version of insertion sort. For both mutable loops
and inline invariants, read [Prototype/InsertionSort.lean](../Prototype/InsertionSort.lean).
That frontend also accepts only logical credits; an explicit `time` clause is rejected.

1. Supply an invariant relating the current mathematical state to the input.
2. Show preservation, exit correctness, and sufficient remaining **logical credits**.
3. Discharge the generated input/output verification conditions.
4. Call `method.certify proof` (or use `prove_ram` in the mutable frontend).
5. Run the resulting method. Its generic `correct` theorem gives the output property
   and `result.steps ≤ method.time input` together.

`method.time` is a derived bound, not a field the author can fill in. No conversion
inequality is included in the algorithm's verification conditions. A conventional
quadratic or linear theorem can still be stated as a corollary, as in the canonical
demos. The adapter library handles conversion to their familiar polynomial bounds.

## What a credit means

A credit is a unit of the logical resource counted by `Run` and propagated by `VC`.
An action consumes its `work state` allowance. Sequential composition adds charges;
a guard consumes one credit, including the final unsuccessful loop test. Calls use
the separately proved procedure budget. Unused credits may remain, but cannot be
spent twice in sequential composition.

The budget is an upper bound, not necessarily an exact measure of work. A procedure
may reserve more credits than its body uses. Library costs can therefore express
amortized or deliberately conservative allowances. The author still supplies the
algorithmic charging argument; automatic RAM time inference is not automatic
invariant discovery or automatic discovery of a complexity bound.

## How the components connect

| Component | Its definition or guarantee | Who supplies it |
|---|---|---|
| `Action State` | `requires`, mathematical `effect`, logical `work` | Logical library author |
| `Guard State` | Mathematical Boolean `test` | Logical library author |
| `Program State`, `Run`, `VC`, `Correct`, `Procedure State` | Compositional credit semantics and proofs | Shared logical core |
| `Model State` | Representation relation and instructions-per-credit bound | Backend author |
| `ActionImplementation M action` | Actual code, correct effect, paid RAM cost | Backend author |
| `GuardImplementation M guard` | Actual test, correct result, paid RAM cost | Backend author |
| `Compilation M program` | Composition certificate for the exact program | Automatically reconstructed |
| `Interface M Input Output` | Input preparation and output observation | Backend adapter author |
| `Method.certify` / `prove_ram` | Logical proof plus reconstructed implementation | User supplies only the logical proof |
| `VerifiedMethod.correct` | Same execution has the output property and inferred RAM bound | Generic library theorem |

[Authoring/Semantics.lean](../Authoring/Semantics.lean) imports no RAM machine or compiler.
A pure action does **not** carry an implementation. A logical proof can exist even
before a backend is implemented. Such an action cannot be compiled merely because
its mathematical effect is a Lean function: a matching implementation certificate
must be available.

[Backend/Realization.lean](../Backend/Realization.lean) reconstructs certificates by
following the program's constructors and verified procedure bodies. It combines
registered primitive certificates and existing soundness theorems. Lean's kernel
checks the resulting terms; the reconstruction tactic adds no axioms. Failure to
find a realization is an elaboration error, not an escape into host execution.

## How time is inferred

For the selected backend, the bound is:

```text
inferred RAM steps = input preparation allowance
                   + backend instructions-per-credit bound × logical credits
```

The backend's factor is supported by proofs for every primitive and guard that is
compiled. The composition theorems transport the logical execution into typed
command execution, and the existing compiler theorem transports it into actual RAM
execution. Encoding and decoding remain host-side views under the existing model;
this bound measures RAM instructions, not Lean wall-clock time or bit complexity.

The current conversion uses one uniform factor per backend. It is sound and
compositional but can be conservative when primitive costs differ considerably.
Changing a backend's code or representation requires its implementation proofs to
check again; it does not require rewriting the algorithm's logical invariant proof.

## A runnable proof of portability

Read these two files side by side:

- [Tests/CreditLogic.lean](../Tests/CreditLogic.lean): a one-credit increment, a
  two-credit procedure, and two calls proved correct with four logical credits.
  This file has no backend import.
- [Tests/BackendReuse.lean](../Tests/BackendReuse.lean): two realizations of that
  same action and the same `four_correct` proof. One emits a direct increment;
  the other also writes a scratch variable. The complete runs use 16 and 24 RAM
  instructions respectively, while both return `n + 4`.

Both execute through the verified runner without user-supplied fuel. The examples
check actual instruction counts, not merely different advertised allowances.

## Migration from the bundled API

Use `Action State`, `Guard State`, and `Program State` in logical definitions.
Move the old `implementation` and `correct` fields into `ActionImplementation M action`
or `GuardImplementation M guard`. Keep logical effects and charges independent of
compiled expressions. Remove the method's `time` clause and the old second RAM-payment
subgoal. Use `method.certify verification` to assemble the executable automatically.

The executable input/output `Interface` still selects a backend. The reusable
`Program`, `Correct`, and procedure proofs do not. This refactor does not complete
the separate experimental compiler for all ordinary Velvet methods; its supported
boundary is documented in [Prototype/COMPILATION-STATUS.md](../Prototype/COMPILATION-STATUS.md).
