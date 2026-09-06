# Stable implementation boundaries

An algorithm uses mathematical values, procedure contracts, and logical credits.
Assembly needs to know where components may live and how to initialize them. It
should not know which registers implement a queue, how its cells are indexed, or
where it stores amortization potential.

## The two assembly contracts

[EncoderLayout.lean](EncoderLayout.lean) adds:

| Interface | Guarantee | What stays private |
|---|---|---|
| `MemoryRegion` | Permitted register names and heap addresses | The exact finite allocation |
| `Encoder.Within` | Every owned location lies in that region | Representation predicates and store construction |
| `Encoder.InputContract` | A public precondition suffices to initialize; initial saved resources equal the advertised amount | How the input is encoded and how potential is distributed |

These are kernel-checked propositions. A permission envelope is an upper bound,
not a claim that every permitted cell is allocated. Overlapping envelopes cannot
be separated by the generic rule without a proof that their permissions are
incompatible. The actual encoder footprints remain finite.

`Encoder.Within.disjoint` proves actual footprint separation from public region
separation. `Encoder.Within.sep` composes region contracts. Input contracts compose
with `Encoder.InputContract.sep` and `.hide`; the latter accounts for the generated
private locals as well. Scalar and array encoders provide reusable contracts.

These contracts concern resident input assembly. They do not add RAM instructions
or silently charge host encoding to the algorithm's instruction count.

## Follow BFS through the boundary

1. [BreadthFirst.lean](BreadthFirst.lean) remains the same algorithm and proof. It
   invokes the abstract queue operations and supplies the BFS invariants.
2. [BFSQueue.lean](BFSQueue.lean) registers the queue implementations and publishes
   `queue_within` and `queue_input`. Queue registers live under `bfs.queue.` and
   queue cells lie at or above the supplied arena start. An empty queue requires
   zero initial saved resources, even for the two-stack implementation.
3. [BFSStorage.lean](BFSStorage.lean) combines queue, bitmap, source, and graph
   encoders using permission envelopes. Only public regions are unfolded to prove
   them disjoint. The graph implementation publishes its own encoder contract.
4. [BFSExecution.lean](BFSExecution.lean) combines resident storage with generated
   scratch and invokes `ram_link`. Its input and cost proofs use `resident_input`
   through `encoder_input`. No queue representation, address formula, or private
   potential definition appears in these proofs.
5. The existing `client_linking` and compiler proofs still establish actual RAM
   execution, correctness, ownership preservation, and the inferred cost bound.

The BFS queue is the last heap allocation, so its public region deliberately has
only a lower bound. Another client that allocates objects after its queue should
publish a bounded queue region instead; `MemoryRegion` supports arbitrary bounds.
This remains fixed-arena assembly, not a dynamic allocator.

## Regression: change private layout, retain the proofs

`FIFO.relocated` selects the circular queue with a different private register stem
and a 17-cell pad before its storage. Both changes are confined to `BFSQueue.lean`.

```lean
#eval (BreadthFirst.search .relocated
  Legacy.Examples.diamond ⟨0, by decide⟩).value
```

[Tests/EncoderLayout.lean](../../Tests/EncoderLayout.lean) checks that the actual
owned footprints differ. It then instantiates the **existing** `search_correct`
and `linear` theorems. A universally quantified result-equality theorem and runtime
checks cover all 64 simple four-vertex graphs and every source, plus isolated
vertices, loops, and parallel edges. There is no relocated BFS body, algorithm
certificate, or special assembly proof. An axiom guard covers substitution.

`Tests/check_layers.py` also rejects direct references to private queue layouts
in `BFSStorage` and `BFSExecution`. It is a maintenance guard; the Lean theorems
remain the semantic guarantee.

## Frontend implementation map

The stable [Frontend.lean](Frontend.lean) import now re-exports five focused modules:

| Module | Responsibility |
|---|---|
| [Frontend/Syntax.lean](Frontend/Syntax.lean) | Statement grammar, loop annotations, contract selection |
| [Frontend/Resources.lean](Frontend/Resources.lean) | Resource trees, state views, fragment composition, ownership routing |
| [Frontend/Expressions.lean](Frontend/Expressions.lean) | Scalar/array expressions, conditions, source locations, local charges |
| [Frontend/Statements.lean](Frontend/Statements.lean) | Calls, assignments, branches, nested loops, generated plans |
| [Frontend/Method.lean](Frontend/Method.lean) | Local collection and final method declaration assembly |

The dependency direction follows the table. Helpers are namespaced implementation
APIs; algorithm authors continue importing `Prototype.LogicalFrontend`. There is
one frontend and one source semantics, with no duplicate elaborator left in the
old file. All five modules remain subject to the transitive backend-free import
check.

## Elaboration performance regressions

Run from the repository root:

```sh
python3 AlgoLib/Experimental/RAM/Tests/check_elaboration.py --runs 3
```

The script first builds dependencies outside the measured interval. It then
invokes `lake env lean -j1 --profile --setup=SETUP FILE` to **re-elaborate** the sorting and BFS
proof and assembly modules, plus the named-proof interface regressions. `SETUP` is Lake's generated module setup, preserving
the project's elaboration options. A cached `lake build` is not counted as an elaboration
measurement. Each log contains Lean's elaboration/type-checking profile; `report.json`
records wall times, budgets, toolchain, platform, revision, and working-tree status.

The checked budgets are in
[Tests/performance/budgets.json](../../Tests/performance/budgets.json). They are
coarse regression ceilings, not performance promises. Each run has a hard timeout;
compiler errors, timeouts, or over-budget results fail the command. `--case` selects
a case; `--budget-scale` explicitly adjusts hardware tolerance and records it in
the report. No baseline is silently rewritten.

CI runs one sample per case and preserves reports and profiles as the
`ram-elaboration` artifact even on failure. Local reports default to
`.lake/build/ram-elaboration/`. These measurements cover module checking (including
startup and import loading), not only a tactic's CPU time, and are unrelated to
the proved RAM instruction bound. Use the profiles to investigate a
regression before changing a budget.
