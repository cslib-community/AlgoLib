# Modularity under composition

For a complete graph algorithm, start with [one BFS proof, two FIFO backends](OWNED-BFS.md).
The same owned source program mixes mutable arrays, scalar locals, nested loops, and
procedure calls, then runs with a circular buffer or an amortized two-stack queue.

For implementation changes, see [stable encoder/layout contracts and frontend modules](IMPLEMENTATION-CONTRACTS.md).
This includes the private-layout substitution test and elaboration timing checks.

For automatic loop accounting and source-level proof goals, start with
[the paper loop tutorial](PAPER-LOOPS.md).

An algorithm is verified using **typed abstract operations and logical credits**.
An implementation supplies **local ownership contracts and private potential**.
The linker reconstructs a certificate for the complete client, and the existing
compiler and runner execute the resulting RAM instructions.

For algorithm proofs, `import AlgoLib.Experimental.RAM.Prototype.Composition` exposes
the pure proof vocabulary without importing a RAM backend. A particular abstract data
structure adds its own operation interface, such as `Composition.Buffer`.

## The four boundaries

| Layer | Start here | What the author sees |
|---|---|---|
| Algorithm | [BufferClient.lean](BufferClient.lean) | Mathematical lists, typed calls, a loop invariant, logical budgets |
| Abstract library | [Buffer.lean](Buffer.lean), [Language.lean](Language.lean) | Operation signatures, functional behavior, procedure contracts, public charges |
| Implementation | [BufferImplementation.lean](BufferImplementation.lean), [Ownership.lean](Ownership.lean) | Private layouts, owned registers/cells, saved potential, local primitive proofs |
| Compiler/linker | [Linking.lean](Linking.lean), [Execution.lean](Execution.lean) | Structural certificate reconstruction, existing RAM compilation, inferred execution bounds |

[Loom.lean](Loom.lean) gives the actual upstream Loom interpretation and proves its
identity, sequencing, and associativity laws. [Demo.lean](Demo.lean) selects implementations
and supplies resident input/output views; it contains no repeated algorithm proof.

## Read the mutable program first

Start with [BufferAlgorithms.lean](BufferAlgorithms.lean). It uses the existing
`ram method` / `prove_algorithm` entry points, now connected to owned procedure
composition. This is executable source syntax:

```lean
open Buffer.API

ram method recycle (capacity : Nat) (mut left : List Nat) (mut right : List Nat)
  return (result : List Nat × List Nat)
  require left.length + 2 ≤ capacity
  require right.length + 2 ≤ capacity
  ensures result = ([], [])
  do
    left.append(capacity, 7)
    left.append(capacity, 8)
    left.clear()
    right.append(capacity, 9)
    right.append(capacity, 10)
    right.clear()

prove_algorithm recycle by
  contract_vc
  omega
```

`capacity` configures fixed code before execution. `left` and `right` are runtime
inputs, and the returned pair contains their final mathematical values. Receiver
calls resolve public procedure names in the open namespace. `left := someProcedure`
is the general assignment form. The frontend automatically frames every other
mutable resource, including heterogeneous products and three or more resources.
There is no address arithmetic or explicit `.frame` in the source or its proof.

Append's public allowance is two credits, including argument setup. Clear's is one.
The straight-line allowance is therefore inferred as ten. `UniformCredits` is
library metadata certifying a state-independent allowance. Input-dependent public
allowances also participate in inference. No caller specifies RAM time.

The same file demonstrates a call inside a branch inside an annotated loop. Users
supply a mathematical invariant mentioning `remaining` when needed. The frontend
adds preservation facts for resources that the loop does not modify. Assertions
and loop invariants generate obligations and are never unchecked hints.

`BufferClient.lean` remains a small low-level algebra example and compatibility
regression. New users should begin with `BufferAlgorithms.lean`.

## A call is now a proof boundary

[Contracts.lean](Contracts.lean) adds annotations indexed by the exact existing
`Program`. `Plan.call proc` is indexed by `.call proc.body`: changing the body
cannot silently reuse an unrelated certificate. The call VC is:

```text
proc.requires input
and proc.credits input ≤ available
and for every output satisfying proc.ensures input output,
    the continuation holds with available - proc.credits input credits
```

It does not unfold the procedure body. `Plan.call_implementation_independent`
proves equality of these obligations for any two realizations of the same public
`Contract`, for every continuation. `Tests/ContractFrontend.lean` additionally
verifies a mutable client parameterized by an arbitrary verified procedure.
Its proof cannot inspect the procedure's unknown body.

Allowances are upper bounds. `Plan.sound` returns an actual source run with
`actual logical work + remaining ≤ initial budget`; this explicit weakening
permits discarding unused credits. It remains sound even for non-monotone
postconditions on the remaining credits. It does not pretend that a callee
consumes exactly its advertised allowance.

`prove_algorithm` reconstructs a reusable `Procedure`. `Algorithm.loom_correct`
connects the same program to actual upstream Loom WP. `procedure_linking` and
`runProcedure_correct` connect that procedure to the existing RAM compiler and
fuel-free runner. The structural linker must still check **every executable body**,
including unchosen branches. A verified abstract summary cannot authorize an
unimplemented RAM operation.

The parser/elaborator is untrusted: its output is an indexed plan and ordinary Lean
proof terms. The supported-language theorem applies to that elaborated program,
not an independently formalized semantics of raw parser text.

## Two implementations, one proof

The lazy implementation clears a buffer by resetting its length. Inactive payloads
may retain old values. The eager implementation maintains zero inactive cells and
clears by overwriting every occupied cell in a loop. Its RAM count is proved to be
`12*n + 3`, including every loop test, decrement, and store.

Eager append saves twelve units of private potential per element. Clearing spends
these savings. The lazy implementation stores zero potential. Both satisfy the
same one-credit public contracts under a library-selected calibration of 24 RAM
instructions per logical credit. This is a conservative bound, not optimal cost inference.

For every primitive the backend proves:

```text
actual steps + final private potential
  ≤ calibration * logical charge + initial private potential
```

Sequencing cancels the intermediate potential. Spatial framing preserves the
unrelated component's potential exactly. A client's proof never mentions either
implementation's potential function.

The runner selects the two implementations independently:

```lean
import AlgoLib.Experimental.RAM.Prototype.Composition.Demo
open AlgoLib.Experimental.RAM.Prototype.Composition

#eval Demo.execute false false 4 [1, 2] [3] (by decide) (by decide)
#eval Demo.execute true  false 4 [1, 2] [3] (by decide) (by decide)
#eval Demo.execute false true  4 [1, 2] [3] (by decide) (by decide)
#eval Demo.execute true  true  4 [1, 2] [3] (by decide) (by decide)
```

All four return `([], [])`, using respectively 48, 97, 85, and 134 RAM steps.
`Demo.correct` supplies correctness and the inferred `Demo.time` bound. The implementation
selection changes neither the mutable `BufferAlgorithms.recycle` nor its proof. No fuel is supplied.
These are resident-input RAM counts; executing Lean host encoders/decoders is not included.

## The laws, precisely

- `Plan.sound`: contract-based annotations establish termination and an affine logical bound.
- `VC.sound`: the lower-level compatibility conditions prove a terminating source run and a
  logical credit bound. Invariants are supplied, not discovered.
- `Procedure.then`: typed procedure contracts compose using their public pre/post
  conditions and budgets, without reopening their implementations.
- `Representation.sep_comm`, `sep_assoc`, and `sep_unit`: spatial composition
  respects ownership and adds private potential. Exclusive ownership cannot be duplicated.
- `Representation.frame`: writes within one footprint preserve **any** disjoint
  local representation, including its exact saved potential.
- `Supported.compile`: total structural certificate reconstruction for identity,
  interface swap, implemented operations, sequences, frames, branches, loops, and
  finite procedure calls. Both branch arms and every loop body must be supported.
- `Supported.compile_seq` and `compile_frame`: compilation preserves sequencing;
  framing introduces no executable copying.
- `Refinement.compose`: independently established conversion rates combine using
  their maximum; intermediate private resources still cancel.
- `client_linking`: for **every supported client**, logical VCs and a represented
  initial state imply actual RAM execution, the logical postcondition, the final
  owned representation, preservation outside the footprint, and the potential-aware bound.
- `loom_linking`: the same conclusion follows directly from actual upstream Loom WP.
- `procedure_linking`: a previously established procedure contract links directly.

`Linked` typeclass instances reconstruct the structural witness from registered
primitive and guard contracts. The witness is indexed by the exact client and its
input/output ownership interfaces. A whole-client simulation proof is not an acceptance
premise. The emitted certificate and every leaf proof are checked by Lean's kernel.

## Existing frontend and proof reuse

[Compatibility.lean](Compatibility.lean) embeds the existing `Authoring.Program`.
`ofProgram_vc` proves equality of the verification conditions for every old program.
`reuse_specification` therefore transports an existing `Specification.VCs` proof
unchanged. The regression suite instantiates it with the current insertion-sort proof.

This is an additive contract boundary retaining Loom, the frontend, and the existing
RAM compiler. Old backend certificates do **not** acquire locality automatically:
a migrated primitive must certify its footprint/non-interference obligations. The
existing sorting and BFS runners remain supported; this change does not claim they
have all been migrated to owned interfaces, or that the ordinary Velvet compiler is complete.

## Frontend scope

Every public `ram method` now uses one owned-program elaborator. Direct array
indexing, scalar expressions and locals, receiver calls, branches, assertions, and
nested annotated loops can be mixed in one body. Calls use public contracts;
expressions reconstruct ownership-aware semantic and cost certificates. Private
locals are initialized with charged machine code and hidden from input/output types.

Start with [the unified frontend tutorial](FRONTEND.md), [mixed algorithms](MixedAlgorithms.lean),
and [insertion sort](Sorting.lean). The old array adapter is isolated in
`LegacyArrayFrontend.lean` behind `legacy_ram`, solely for compatibility regressions.
There is no parameter-type dispatch to it. This does not claim arbitrary ordinary
Velvet support.

Procedure expressions describe fixed code. A runtime mutable input cannot specialize
that code. Receiver calls now route a trailing runtime Nat expression through the
library's certified typed argument procedure. Paired calls can also pass two distinct
owned variables; the frontend reconstructs their routing and frames all other values.
The declared mutable resource names must be distinct; physical disjointness remains
an implementation-package obligation checked by the linker.

## Supported ownership and execution boundary

Ownership covers finite sets of both registers and heap cells. Representations must
be local to those sets. Footprints remain fixed through a call and may reserve inactive
capacity. This supports bounded buffers and independent component composition.
Dynamic allocation, deallocation, shared read permissions, and aliased views require
additional resource contracts; they are not silently treated as disjoint resources.

Typed interfaces describe mathematical values transferred through calls. Implementations
provide their register/storage ABI. Structured client calls inline finite bodies;
this is not a general recursive calling-convention implementation. Source semantics
are deterministic. No nondeterministic or divergence-sensitive compiler claim is added.

Logical effects and tests may use Lean mathematics for their specifications, but they
are not executable callbacks. Each accepted executable leaf needs a RAM implementation.
A client program is fixed before its runtime input; specializing a program generator
on inputs is not a charged RAM execution of that generator.

The final bound includes initial private potential. The initial representation cannot
supply free time by omitting that potential from the bound. Inputs are already resident
in the chosen layout, as in the existing library. Host encoding/decoding, allocation
of that resident input, and unbounded-integer bit complexity remain outside this convention.

## Attribution

This design is informed by Peter Lammich's **Sepref / Imperative Refinement Framework**,
especially abstract-data-type interfaces, implementation substitution, and automatic
reconstruction of refinement proofs. See [Refinement Based Verification of Imperative
Data Structures (CPP 2016)](https://www21.in.tum.de/~lammich/pub/cpp2016_impds.pdf).
These are new Lean definitions and proofs; we do not claim to port Sepref or reproduce
its supported language, automation, or data-structure coverage.

The combination of ownership and private amortized resources follows established
separation-logic work, including Robert Atkey's [Amortised Resource Analysis with
Separation Logic](https://bentnib.org/amortised-sep-logic-journal.html).

The actual monad algebra and WP infrastructure is **Loom**, by its upstream authors:
[Foundational Multi-Modal Program Verifiers](https://verse-lab.org/papers/loom-popl26.pdf).
The vendored code, licensing, and compatibility changes remain documented in
[the upstream attribution](../../../../../vendor/README.md).

## Validation

Build with `lake build`. [Tests/Composition.lean](../../Tests/Composition.lean) checks
all four implementation combinations and exact RAM counts for different initial
lengths, duplicates, and empty buffers. It also checks typed composition, framed
ownership, source proof reuse, Loom WP, nested loop/branch support, missing primitive
rejection, overlapping ownership rejection, and unpaid logical work.
The axiom guards inspect both generic laws and concrete implementation certificates.
The dependency checker keeps logical interfaces and client proofs free of RAM imports.

The frontend/contract regression suite additionally checks inferred budgets,
parameterized opaque procedures, three-resource framing, nested calls, unchanged
RAM instruction counts, unsupported-body rejection, and unused credit allowances.
