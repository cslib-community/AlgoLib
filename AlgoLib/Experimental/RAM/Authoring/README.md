# From a paper argument to a checked method

Start with [Pure algorithms and interchangeable array backends](../docs/GENERALITY-AND-SUBSTITUTION.md) for the current source/proof workflow and supported-language theorem.


Start with a complete example in [Programs](../Programs). This directory supplies the reusable proof rules; it does not contain additional sorting or BFS programs.

## 1. State what the algorithm returns

Use ordinary mathematical properties. Sorting needs both sortedness and permutation, so duplicates cannot disappear. BFS needs `v ∈ S ↔ Reachable G source v`; from that, the connectivity theorem follows by set equality. The `Claim` definitions in the example files state these properties and the time bounds before introducing the proofs.

## 2. Declare the method with input and output

`ram_method (input : InputType) returns (output : OutputType)` binds names in the precondition, postcondition, and budgets. `using` selects a **certified library input/output interface**. The body is a fixed `Program`; it cannot inspect the host input to generate specialized code.

- `requires`: facts the caller must supply. Certified graph/source input already carries graph validity.
- `ensures`: the relationship between input and returned value.
- `credits`: an upper bound on abstract algorithm work, including loop guards.
- `do { ... }`: the actual code compiled and executed, composed from certified operations.

A return name describes the adapter's output observation. It is not an arbitrary host-side return expression. Sorting's output is the represented array; BFS's is the visited-set membership view. Displaying a view as a list is a separate host operation.

## 3. Read the code as textbook subroutine calls

| Textbook BFS line | Current certified program |
|---|---|
| Clear visited; mark source; Q := [source] | Paid input preparation selected by `using` |
| while Q is nonempty | `while (queueNonempty a)` |
| u := dequeue(Q) | `call dequeue a;` also opens u's adjacency row |
| for v in adjacency[u] | `call (scanNeighbors a).call;` |
| if not visited[v]: mark v; enqueue v | `visit`, inside the certified row procedure |
| Record u as fully processed in the proof | `call finish a;` is a ghost update with no instructions |

The high-level API has `call`, `while`, and `if`. The full neighbor loop is a reusable procedure in [Library/Search.lean](../Library/Search.lean). This grouping is explicit; the source is not claimed to parse every line of Dafny. The lower typed DSL supports variables and indexed memory expressions, but its implementation details are not prerequisites for this authoring path.

## 4. Supply the invariant and charging argument

`LoopProof` gives three named obligations:

| Field | Paper argument |
|---|---|
| `preservation` | The body preserves the invariant and leaves enough potential for the next state |
| `payment` | A true guard can pay its positive cost |
| `exit` | The invariant and false guard imply the postcondition |

Inside preservation, `paper_steps [logicalDefinitions]` expands control flow and registered logical effects. It generates call preconditions, credit inequalities, and the desired postcondition. The writer supplies facts such as permutation preservation or “this dequeued vertex is fresh.” `paper_credits`/arithmetic tactics handle the resulting arithmetic. The positive guard cost makes the potential proof a termination proof as well.

Invariants are supplied and refined by the author. They are not guessed. A wrong invariant, a missed precondition, or an insufficient budget leaves an unproved goal.

## 5. Generate the input/output method obligations

`method_vc [methodName]` opens `methodName.VCs`. For each valid input it asks for:

Symbolic correctness of the displayed body from the prepared logical state, within the declared credits, for the declared output property. RAM time is inferred automatically from the selected backend; there is no second payment obligation.

A completed body/loop contract can be reused through `Correct.output_vc`. Its remaining obligations are initial validity, sufficient credits, and interpretation of the logical result. Public library equations expose these as list/set facts, without revealing the adapter implementation. The algorithm files show the complete proofs.

`method.certify proof` checks these obligations and reconstructs backend certificates before exposing `run`. Its generic `correct` theorem produces both `ensures input result.value` and `result.steps ≤ time input`. The examples specialize that theorem into their advertised `main` statements.

## Files in this layer

| File | Construction and relation to the next component |
|---|---|
| [Semantics.lean](Semantics.lean) | Mathematical `Program`/`Run`, pure `Action`/`Procedure` contracts, VC soundness, and loop rules; no RAM dependency |
| [Syntax.lean](Syntax.lean) | Compositional body syntax, logical symbolic execution, and time-credit arithmetic |
| [Interface.lean](Interface.lean) | Library preparation/observation interface and generic certified execution binding |
| [Methods.lean](Methods.lean) | Input/output declarations, generated method obligations, fixed-body certificates, and the user-facing theorem |

The executable interface connects to [Backend/Realization.lean](../Backend/Realization.lean), which separately implements the pure contracts. See [Credits and backends](../docs/CREDITS-AND-BACKENDS.md). Program proofs use those connections through these rules, not through normalization, register correspondence, instruction lifting, or cost-transport lemmas.
