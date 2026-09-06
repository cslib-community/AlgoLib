# Modularity under composition

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

## Read the client first

`Buffer.argument` prepares a typed argument, `Buffer.append` appends it, and
`Buffer.clear` returns the empty mathematical list. Each consumes one logical credit.
`push` composes argument preparation and append, changing the intermediate type from
`List Nat` to `List Nat × Nat`, then back to `List Nat`.

`recycle` calls push twice and clears the buffer. Its five-credit proof says that,
provided two slots are available, its final list is empty. `recycle_both` composes
two such clients on independently owned buffers; it needs ten credits. The client
knows neither how clearing is implemented nor where either buffer is stored.

`Program.both p q` is **sequential execution on separate components**, not parallel
execution. Its implementation frames the second component while running the first,
then frames the first while running the second. The swap is a reassociation of
logical interface views and emits no machine copying.

`Buffer.drain` additionally demonstrates a loop and a user-supplied mathematical
invariant. Its three-credit proof covers both empty and nonempty inputs. A guard
must have a certified implementation just like any other executable operation.

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
selection changes neither `Buffer.recycle_both` nor its proof. No fuel is supplied.
These are resident-input RAM counts; executing Lean host encoders/decoders is not included.

## The laws, precisely

- `VC.sound`: generated logical conditions prove a terminating source run and a
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
