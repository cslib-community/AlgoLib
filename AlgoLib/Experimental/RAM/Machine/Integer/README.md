# Int-RAM: default owned-frontend execution

The supported owned frontend now executes on Int-RAM by default. Existing `Nat`
source programs keep their meanings and their Lean input/output interfaces. Source
proofs and logical credits are unchanged; assembly derives the integer instruction
bound automatically. The old Nat machine remains a compiler intermediate and a
regression reference until direct integer lowering replaces it.

## What is checked

- `Machine.lean`: independent integer registers and heap cells; nonnegative addresses;
  signed addition/subtraction/multiplication, maximum, comparisons, loads and stores.
  Each instruction costs one operation. Sequence bookkeeping is free; every guard
  is charged, including the final false guard.
- `Runner.lean`: executable interpreter with proof-derived termination, no user fuel,
  and a theorem connecting the returned state and exact count to machine execution.
  Internal evaluation returns `none` on a fault. The certified public runner requires
  successful termination, so a fault cannot masquerade as a successful result.
- `NatEmbedding.lean`: a fixed syntax-directed translation of every old instruction
  and structured program. Nat subtraction becomes signed subtraction followed by
  `max result 0`. Its generic simulation proves the same embedded final state and
  at most twice the original instruction count, including loops.
- `Composition.integer_procedure_linking`: transports existing owned procedure
  proofs, frames, and private-potential bounds to actual Int-RAM execution. Clients
  do not supply a new algorithm simulation proof.

Machine integers are unbounded; unit-cost arithmetic is **not** a word-RAM or
bit-complexity guarantee. Logical credits, operation counts, and private potentials
remain mathematical natural numbers. The migration bound scales saved potential
as well as logical charges; it does not forget initialization resources.

## Signed execution demo

See `Tests/IntegerRAM.lean` for the checked declarations:

```lean
def signed : Code := .block [
  .bin .sub .key (.lit 3) (.lit 5),
  .store (.lit 0) (.reg .key),
  .load .temp (.lit 0)]
```

The fuel-free runner returns `-2` in `temp`, in exactly three instructions. A load
or store at `-1` fails; it does not access address zero. Heap cell zero may hold a
negative *value* without being an invalid address.

For existing Nat code, `Migration.run code input terminationProof` executes the
translated integer instructions. `Migration.run_correct` proves agreement with the
old result and the derived upper bound. It does not execute the old interpreter to
obtain its result; the old runner appears only in the erased comparison theorem.

The tests cover 243 small subtraction cases, including destination/input register
aliasing, and a three-iteration countdown whose translated count is 10. Axiom guards
reject changes to the current trusted dependencies. The full repository build also
retains the existing frontend conformance and algorithm regressions.

## Default assembly and theorem transport

`Backend.Language.IntegerExecution` gives each certified Method an `integerCode`,
a fuel-free `integerRun`, and `integerCorrect`. The shared owned `run`,
`runProcedure`, and `runEncoded` use this runner. Thus `compile_array_method`,
`CertifiedExecutable.run`, insertion sort, and all BFS queue choices execute integer
instructions. No user-written migration theorem or backend selector is needed.

Decoding natural source values uses an observation justified by the embedding
proof; this is not silent coercion of a negative address. Runtime addresses are still
checked by the integer instruction semantics.

The inferred bound is `2 * (rate * credits + initialPotential)`. This is a conservative
simulation bound, not a promise that every execution doubles in length. The runner
counts its actual instructions. Sorting's displayed polynomial is now
`1824*n^2 + 768*n + 1296`; BFS has the linear bound `4896*(n+m)`.

## Remaining replacement work

1. Add typed `Int` locals, arrays, calls, and explicit conversions to the frontend;
   preserve current `Nat` meaning and generate signed-index safety obligations.
2. Replace the temporary Nat compiler intermediate with direct integer lowering,
   then remove the old machine after its regression evidence has replacements.

Signed `Int` source syntax is not implemented yet. The direct machine demo is for
framework development; users continue through the generated proof API. Default
execution is integer-valued, while the compiler intermediate is still Nat-valued.
