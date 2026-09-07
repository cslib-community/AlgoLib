# Int-RAM replacement: first checked migration milestone

The destination is one supported Int-RAM backend with both `Nat` and `Int` source
types. This directory establishes the machine and migration foundation. The current
frontend and default assembly still use the old Nat implementation while their
representations are ported. This is an intermediate migration state, not a promise
to maintain two public backends indefinitely.

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

## Remaining replacement work

1. Port compiler/storage interfaces to the integer machine, using this simulation
   as the migration specification and accounting explicitly for Nat subtraction.
2. Add typed `Int` locals, arrays, calls, and explicit conversions to the frontend;
   preserve current `Nat` source meaning and generate signed-index safety obligations.
3. Migrate executable assembly, sorting and BFS, regenerate affected bounds, and
   extend independent conformance testing to signed source programs.
4. Switch the sole public backend and remove the old machine after its regression
   evidence has replacements.

No signed `ram method` syntax or completed backend replacement is claimed by this
first milestone. The direct machine demo is for framework development; final users
should continue to work through the generated proof API.
