# Ordinary Velvet → nondeterministic RAM: checked scope

The intended compilation boundary is **natural numbers, booleans, finite arrays,
graph handles, and first-order procedures, including recursion**. Unsupported Lean
runtime values must be rejected. All nondeterministic Velvet outcomes must be
preserved, so the target has a charged choice instruction.

**The full compiler for that boundary is not implemented yet.** This extension
provides a checked semantic bridge, a recursive target and executable interpreter,
multiple-array frontend support, and concrete ordinary-Velvet translation
certificates. It does not turn an arbitrary `method` declaration into RAM code.
A certificate whose fields ask for an equivalence proof is not itself a proof that
an automatic compiler produces such a certificate for every supported method.

## What users can run now

```lean
import AlgoLib.Experimental.RAM.Prototype.MultipleArrayTests
import AlgoLib.Experimental.RAM.Prototype.RecursiveTranslation
import AlgoLib.Experimental.RAM.Prototype.VelvetTranslationTests
open AlgoLib.Experimental.RAM.Prototype

#eval let r := MultipleArrayTests.exchange #[1, 2] #[8, 9, 10]
        (by decide) (by decide)
      (r.value 0, r.value 1)
-- (#[8, 2], #[1, 9, 10])

#eval let r := RecursiveTranslation.run 10; (r.value, r.steps)
-- (10, 54): actual recursive RAM execution, without fuel

#eval let r := VelvetTranslationTests.chooseWordExecutable.run () trivial (fun _ => 42)
      (r.value, r.steps)
-- (42, 1): this external schedule selects the outcome 42
```

A schedule chooses a natural word at each `choose` instruction. It is an explicit
way to run a nondeterministic program once, not an algorithm parameter used to hide
computation. The outcome semantics and worst-case theorems still quantify over
**all** choices. The one-instruction choice example proves that every natural word
can be produced by a schedule, rather than using Velvet's deterministic extractor.

## Multiple arrays in the existing frontend

```lean
ram method exchangeHeads (mut left : Array Nat) (mut right : Array Nat)
  return (u : Unit)
  require 0 < left.size
  require 0 < right.size
  ensures left = leftOld.set! 0 rightOld[0]!
  ensures right = rightOld.set! 0 leftOld[0]!
  credits 50
  do
    let x := left[0]!
    let y := right[0]!
    left[0] := y
    right[0] := x
    return

prove_ram exchangeHeads by
  ram_solve []
```

The checked declaration is in [MultipleArrayTests.lean](MultipleArrayTests.lean).
The same syntax works for any fixed positive number of mutable `Array Nat`
parameters. Each array has its own length and `Old` ghost name. Bounds checks and
costs are generated for the array actually indexed. Loops automatically frame
arrays that their bodies do not modify. The tests include three arrays, unequal
lengths, an empty first array, and a loop that writes one array while preserving
another. Function-valued inputs and uncompiled host calls produce elaboration errors.

At the Lean interface, multiple arrays are represented by `Fin count → Array Nat`;
this is a finite tuple, not a runtime closure. Parameters have value semantics:
passing the same Lean array twice creates independently mutable RAM lanes. The
backend proves lane disjointness once. Array allocation, resizing, aliasing views,
and general array-valued procedure arguments are not implemented by this adapter.

## What exactly is proved

1. **Ordinary source outcomes.** [VelvetSemantics.lean](VelvetSemantics.lean)
   defines `Returns` on the actual upstream `VelvetM` produced by `method`.
   Choice ranges over every value satisfying its predicate. Finite loop
   executions use their operational meaning; the deterministic extractor is not
   used to define all outcomes.
2. **Loom correctness.** [VelvetWP.lean](VelvetWP.lean) proves
   `Returns.satisfies_wp`: every successful outcome satisfies the actual upstream
   total, demonic Loom WP. The proof covers choice and loops. An ordinary Loom
   proof can therefore supply functional correctness to a translation certificate.
3. **Target instructions and calls.** [Nondeterministic.lean](Nondeterministic.lean)
   embeds the existing deterministic instruction semantics and adds choice and a
   fixed finite procedure table. Calls may be recursive or mutually recursive.
   Every call and return costs one step. Registers and heap are shared: a call
   does not copy locals or arrays, or secretly restore registers.
4. **Preservation and reflection.** `Translation.equivalent` states, on valid
   inputs, `Returns (source input) output` iff some target execution decodes to
   that output. Source and target are independently defined. Both directions are
   proved for ordinary choice, a call to that choice procedure, the two-array
   exchange, and the recursive `countBack` method.
5. **Actual execution.** [NondeterministicRunner.lean](NondeterministicRunner.lean)
   implements a control-stack interpreter. A call pushes a body and return marker;
   no activation data is copied. `Trace.exec` and `run_correct` prove that every
   successful run reconstructs the target execution relation. For choice-free
   procedures, `ExecIn.trace` turns the big-step termination proof into an
   interpreter termination proof, including recursive calls.
6. **Time.** `Translation.Within budget` bounds the cost of **every terminating
   target execution**. It is not merely a favorable execution's cost. The
   recursive example proves the exact count `5*n + 4`, independently of its
   source functional theorem.
7. **Total execution and the public result.**
   [ExecutableTranslation.lean](ExecutableTranslation.lean) adds target
   termination for every valid input and every schedule. Its runner takes no fuel.
   `run_correct_and_cost` combines an ordinary Loom WP, the universal RAM bound,
   and the interpreter soundness theorem for the returned Lean value.

The two-array example in [VelvetArrayTranslation.lean](VelvetArrayTranslation.lean)
uses [ExecutionBridge.lean](ExecutionBridge.lean) to expose the machine execution
behind the existing `VerifiedMethod.run`. Its source theorem refers to an ordinary
Velvet method, not to a second WP over the RAM authoring representation.

## Outcome equivalence, termination, and time are different obligations

Finite successful-outcome equivalence does not distinguish divergence from a
stuck computation with no output. It also does not transfer demonic termination:
a target could retain every successful source outcome and introduce a divergent
branch. Similarly, a bound on terminating runs alone does not rule out divergence.

That is why `ExecutableTranslation` requires an additional target termination
proof for every schedule. The current bridge transfers **functional correctness**
from Loom; it does not claim divergence-sensitive equivalence of arbitrary methods.
The chosen runtime type boundary does not remove this obligation.

Costs use the existing unit-cost, unbounded-natural RAM convention. Input arrays
are already resident in the certified layout, and decoding is the observation
convention. The theorem does not count Lean host execution or integer bit complexity.
A compiler must fix its program and procedure table before runtime inputs, and use
certified layouts; arbitrary user-written encoders are not automatically certified
representations of an algorithm's input.

## Remaining compiler work

| Area | Checked now | Still required for the requested full compiler |
|---|---|---|
| Frontend | Nat locals, multiple `Array Nat` parameters, branches, nested annotated loops | Unified reification of ordinary `method`, Bool parameters/locals, general returns and calls |
| Procedures | Finite target table, recursive execution, a recursive Velvet equivalence example | General argument/return ABI, explicit charged saving of caller-local data, mutual-recursion frontend |
| Arrays | Independent lengths, reads/writes, framing, executable decoding | Allocation/resizing, array-valued calls and broader array operations |
| Graphs | Existing certified graph/queue operations and BFS composition | Integrating graph handles into the same ordinary-method reifier and general call ABI |
| Proofs | Actual Loom WP → successful RAM outcomes; checked example equivalences | Automatic semantic-certificate reconstruction for every accepted construct; divergence-sensitive preservation |
| Costs | Instruction-derived costs and universal example bounds | Modular recursive contracts and automatic stack/argument cost accounting |

Unsupported code must fail compilation until it has a checked lowering. In
particular, a Lean function having type `Nat → Nat` is not a constant-time RAM
primitive: its body must be compiled, or a registered implementation and simulation
proof must be supplied. Narrowing runtime types alone does not justify accepting
arbitrary host functions without this work.

## Trust and navigation

[Axioms.lean](Axioms.lean) pins kernel dependencies for the new bridges, interpreter,
framing proofs, and examples alongside the existing insertion-sort/BFS checks.
No admissions, trusted SMT answers, or native-decide axioms are introduced.
The layer check prevents production code from depending on this isolated prototype.

The actual Loom/Velvet sources retain their attribution in
[vendor/README.md](../../../../vendor/README.md). This extension also fixes Loom's
Lean 4.30 `match` syntax indexing; the recursive ordinary-method test exercises
that compatibility path.

## Supported deterministic frontend

The `ram method` frontend now emits a backend-independent `Specification`; `prove_algorithm` verifies it without RAM imports. `Supported.compile` and `loom_to_supported_ram` give the structural compilation guarantee for this deterministic DSL. Contiguous and indirect arrays reuse the same sorting/zeroing proofs. See [the precise scope](../docs/GENERALITY-AND-SUBSTITUTION.md). This does not complete the ordinary-Velvet compiler described above.

## Owned composition and private potential

[Composition](Composition/README.md) now adds typed input/output operations, contract-based
procedure composition, local ownership, private potential, and a structural client linker.
Loom reasoning and the existing RAM compiler are reused. The buffer example links one proof
to all four lazy/eager implementation combinations and counts actual instructions. Existing
Authoring VCs embed unchanged. This does not add arbitrary ordinary-method reification,
runtime recursion, allocation, or shared-permission inference to the compiler boundary above.
