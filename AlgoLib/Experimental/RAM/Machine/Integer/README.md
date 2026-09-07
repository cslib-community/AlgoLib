# Int-RAM: default owned-frontend execution

The supported owned frontend now executes on Int-RAM by default. Existing `Nat`
source programs keep their meanings and their Lean input/output interfaces. Source
proofs and logical credits are unchanged; assembly derives the integer instruction
bound automatically. The default runner uses the verified native integer compiler. Existing implementation
contracts still use a Nat-valued IR, translated directly into the native IR. The old
Nat machine is no longer an instruction intermediate for that runner; historical
proof APIs and regression references still await retirement.

## What is checked

- `Machine.lean`: independent integer registers and heap cells; nonnegative addresses;
  signed addition/subtraction/multiplication, maximum, comparisons, loads and stores.
  Each instruction costs one operation. Sequence bookkeeping is free; every guard
  is charged, including the final false guard.
- `Runner.lean`: executable interpreter with proof-derived termination, no user fuel,
  and a theorem connecting the returned state and exact count to machine execution.
  Internal evaluation returns `none` on a fault. The certified public runner requires
  successful termination, so a fault cannot masquerade as a successful result.
- `Backend/Native/Compiler.lean`: direct typed compilation with exact-cost semantic
  preservation for arithmetic, memory, branches, loops, and scoped locals.
- `Backend/Native/Natural.lean`: reuses legacy natural implementation certificates
  through native IR, preserving stores and the existing factor-two cost allowance.
- `NatEmbedding.lean` (historical regression interface): a fixed syntax-directed translation of every old instruction
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

The historical migration tests use `Migration.run code input terminationProof`
to execute translated old instructions. This reference route is not selected by
method assembly. `Migration.run_correct` proves agreement with the
old result and the derived upper bound. It does not execute the old interpreter to
obtain its result; the old runner appears only in the erased comparison theorem.

The tests cover 243 small subtraction cases, including destination/input register
aliasing, and a three-iteration countdown whose translated count is 10. Axiom guards
reject changes to the current trusted dependencies. The full repository build also
retains the existing frontend conformance and algorithm regressions.

## Default assembly and theorem transport

`Backend.Language.Verification` now makes the ordinary `Method.run` execute
native integer code. `Method.run_exec` witnesses that exact execution;
`Method.correct` connects its decoded result to the source contract and derives
the machine bound. `Backend.Language.IntegerExecution` retains `integerRun` and
`integerCorrect` as compatibility aliases to those same definitions.

Both the owned frontend and the older `Authoring.VerifiedMethod.run` therefore
use the native integer compiler. The lower `Function.run` input/output interface
also uses this runner. No user-written migration theorem or backend selector is
needed. The logical budget is unchanged; `Authoring.Method.time` derives twice the
preparation-plus-credit allowance as a conservative integer instruction bound.

Decoding natural source values uses an observation justified by the native IR
translation proof; this is not silent coercion of a negative address. Runtime addresses are still
checked by the integer instruction semantics.

The inferred bound is `2 * (rate * credits + initialPotential)`. This is a conservative
simulation bound, not a promise that every execution doubles in length. The runner
counts its actual instructions. Sorting's displayed polynomial is now
`1824*n^2 + 768*n + 1296`; BFS has the linear bound `4896*(n+m)`.

## Signed source interface

The owned frontend now supports `Int` locals, arithmetic, comparisons, arrays,
procedure composition, and explicit `Int.ofNat`/`Int.toNat` conversions. Nat
subtraction remains saturating. Signed indices generate nonnegativity and bounds
obligations. See [the signed source tutorial](../../Prototype/Composition/SIGNED-INTEGERS.md).

`compile_scalar_method` assembles ordinary Nat/Int inputs and outputs;
`compile_array_method` assembles lists of Nat or Int. Both use the existing
obligation API, actual Int-RAM execution, and inferred instruction bounds.

## Execution boundary

The native compiler is the execution target for scalar/array frontend assembly,
owned library assembly, the older typed Method/Function interfaces, and the
ordinary-Velvet translation fixtures. Signed frontend storage uses one integer
cell. Natural-valued library views keep their source proofs through
`Native.Natural`, which translates source semantics without invoking the old
instruction compiler. Logical credits remain natural-number resources.

The nondeterministic interpreter embeds integer instructions too. Its natural
choice schedules and charged call/return convention are unchanged. Negative
addresses cannot produce successful traces. The recursive example still returns
`n` in exactly `5*n + 4` instructions, and the multiple-array equivalence theorem
uses the same native execution witness as the public runner.

The obsolete Nat `TotalProgram`, `Procedure`, and `Output` wrappers are removed.
`Checked.run` and the old instruction/compiler theorems remain internal historical
references for regression and refinement proofs. They are not a selectable
execution backend. Use `Integer.TotalProgram` for direct machine code and the
native or generated method interfaces for typed programs.
