# One algorithm proof, supported compilation, and interchangeable arrays

The source-language layer now has no transitive RAM dependency. It contains the
program, mathematical input/output specification, local logical credits, annotated
loops, generated verification conditions, and actual Loom WP interpretation.
A separate execution layer chooses a verified data-structure implementation.

## Read these files in order

| File | What to look for |
|---|---|
| [SortingAlgorithm.lean](../Prototype/SortingAlgorithm.lean) | One mutable insertion-sort program, its invariants, and `prove_algorithm` |
| [ZeroAlgorithm.lean](../Prototype/ZeroAlgorithm.lean) | A second, linear algorithm using the same frontend and VCG |
| [ArraySubstitution.lean](../Prototype/ArraySubstitution.lean) | Each unchanged specification and proof attached to two backends |
| [Authoring/Contracts.lean](../Authoring/Contracts.lean) | Complete logical input/output `Specification`, with no backend parameter |
| [Authoring/Mutable.lean](../Authoring/Mutable.lean) | Pure scalar expressions, array operations, guards, and logical charges |
| [LogicalFrontend.lean](../Prototype/LogicalFrontend.lean) | Shared source syntax and proof automation; no machine or compiler imports |
| [IndirectArrays.lean](../Prototype/IndirectArrays.lean) | The second array implementation and its representation/cost proofs |
| [Backend/Realization.lean](../Backend/Realization.lean) | Supported-language grammar, total compiler, and universal soundness theorem |
| [SupportedCompilation.lean](../Prototype/SupportedCompilation.lean) | Actual Loom WP transported to actual RAM execution for every supported program |

The layer checker enforces the pure boundary, including the frontend and the two
algorithm proof files. This is not just a convention about which definitions
students should avoid unfolding.

## Write and prove the algorithm before choosing RAM storage

Import `Prototype.LogicalFrontend` to use `ram method` and `prove_algorithm`.
The method declaration now produces:

```lean
Specification Mutable.State (Array Nat) (Array Nat)
```

It contains `body`, `initial`, `observes`, `requires`, `ensures`, and `credits`.
It has no RAM model, memory representation, compiler certificate, or `time` field.

`prove_algorithm insertionSort by ...` generates:

- `insertionSortVerification`: proof of the annotated logical obligations;
- `insertionSortCorrect`: the reconstructed pure `Specification.VCs` proof.

The algorithm author supplies the mathematical invariant and local charging
argument. The existing VCG propagates logical effects and credits. The actual Loom
algebra and `algorithm_loom_correct` connect these obligations to upstream Loom WP.
No second algorithm invariant or proof is needed for that connection.

The execution file then contains exactly this:

```lean
def denseSort :=
  Mutable.interface.realize insertionSort insertionSortCorrect

def indirectSort :=
  IndirectArrays.interface.realize insertionSort insertionSortCorrect
```

Both calls receive the **same specification object and the same proof term**.
The linear zeroing algorithm is attached in the same way. `prove_ram` remains a
convenience command for proving the pure specification and immediately attaching
the default array backend.

For either executable, `.correct` gives the output property and the inferred
RAM-step bound for its `.run`. The compiler does not execute logical effects to
obtain the result. The runner executes the separately certified RAM instructions.

## Why these implementations are materially different

The first array stores values directly at their indices. The second stores pointers
in even-addressed table cells, with payloads at distinct odd addresses. Every read
or write loads its pointer from the table before accessing the payload.

For input `#[3, 1, 2]`, the supplied encoders produce:

| Logical element | Contiguous access | Indirect access |
|---|---|---|
| `arr[0] = 3` | heap[0] | table at heap[0] contains 5; heap[5] contains 3 |
| `arr[1] = 1` | heap[1] | table at heap[2] contains 3; heap[3] contains 1 |
| `arr[2] = 2` | heap[2] | table at heap[4] contains 1; heap[1] contains 2 |

The indirect representation theorem permits **any injective odd-address placement**,
not only this reverse placement. Its implementation cannot assume that the logical
index determines the payload address without reading the pointer table.

The backend establishes once that:

1. a payload write preserves every pointer-table cell;
2. distinct logical indices have distinct payloads;
3. updating one element preserves all other elements;
4. scalar assignments preserve the array representation;
5. each primitive implements the same logical action and pays its RAM cost.

The sorting and zeroing proofs mention none of these memory facts. This is an
immutable pointer table with independently mutable payloads; resizing, shared
payload aliases, and allocation are outside this adapter's contract.

Both interfaces use resident input representations. Host encoding/decoding, including
constructing the indirect input table, is outside the RAM-step bound, just as host
array encoding is outside the existing contiguous interface. A conversion algorithm
from one resident representation to another would need its own charged preparation
contract. The bound measures unit-cost RAM instructions, not host wall-clock time
or the bit complexity of unbounded natural arithmetic.

## The precise supported-language guarantee

`Supported M p` is an inductive, syntax-directed grammar of programs supported by
backend `M`. It is **not** a field asking for an arbitrary whole-program simulation.
Its constructors cover:

- skip;
- an action with a registered primitive implementation;
- sequence, requiring support for both children;
- a branch, requiring an implemented guard and both branches;
- a loop, requiring an implemented guard and its body;
- a verified nonrecursive procedure call, requiring support for its actual body.

Bodies and branches must be supported even if a particular input would never
execute them. A procedure summary alone is insufficient to compile its call.

`Supported.compile` is a **total Lean function**, defined by structural recursion
on that grammar. It assembles the implementation and its functional/cost certificate
from primitive and existing composition proofs. It introduces no algorithm-specific
proof obligation. `Method.certify`, `Interface.realize`, and `prove_ram` reconstruct
this support evidence automatically before attaching an executable backend.

The universal theorem `Supported.vc_sound` states, schematically:

```text
For every p, supported : Supported M p, state s, credits c, and postcondition Q:
  logical VCs for p from s with c credits establish Q
  + a RAM state representing s
  imply existence of a terminating execution of supported.compile,
         a final logical state satisfying Q,
         a matching final RAM state,
         and RAM steps ≤ M.overhead × c.
```

Input preparation is composed and charged by `Interface.realize` and the generic
verified-method runner. The final bound is preparation allowance plus the backend
factor times logical credits. The current factors are conservative uniform bounds;
both array implementations can use factor three even though their actual instruction
counts differ. No claim of optimal bound inference is made.

`loom_to_supported_ram` gives the same guarantee directly from the **actual Loom WP**
of the independent logical interpretation. It reuses the Loom observation equation
and supported compiler theorem; it does not require a separate translation proof
for each algorithm.

The parser/elaborator produces the logical `Program` and indexed annotations.
The theorem's boundary is that elaborated program, not an independently formalized
semantics of raw source text. Metaprogram acceptance produces evidence checked by
Lean's kernel; the metaprogram itself is not claimed to have a termination or parser
correctness proof. Logical declarations can exist without a backend, but cannot run
until their implementations and verification conditions have been checked.

## What is and is not generalized

This is a generic compilation theorem for the supported deterministic authoring
language and certified operation libraries. It is not the missing full compiler
for arbitrary ordinary Velvet methods, general recursive calls, allocation, or
nondeterministic source constructs. The separate experimental boundary remains in
[COMPILATION-STATUS.md](../Prototype/COMPILATION-STATUS.md).

The integration reuses the existing logical VCG, operation proofs, typed compiler,
runner, and upstream Loom `MAlgOrdered`/WP interface. It does not reimplement the
Loom transformer hierarchy or introduce a competing solver trust path.

## Evidence and regression checks

[Tests/ArraySubstitution.lean](../Tests/ArraySubstitution.lean) checks both algorithms
on both backends against independent list-sort and all-zero-array references for
all lists of length below six over `{0,1,2}`. It checks actual RAM counts against
inferred bounds and confirms extra pointer loads in indirect sorting.

`sorting_outputs_equal` proves equality of the returned lists for **every input**,
using the shared sorted-permutation specification. Constructor coverage and rejection
tests check nested control flow, missing implementations, and insufficient credits.
Exact axiom guards cover concrete realizations and generic compiler/Loom bridges.
These tests establish this supported scope; they are not evidence of predictable
automation across an unrestricted algorithm library or of student usability.
