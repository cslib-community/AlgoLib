# Contributing to the verified RAM stack

Start with [your first certified method](GETTING-STARTED.md). It takes you from a
short program and a mathematical specification to a checked proof and an executable.
Then choose one contribution below. You do not need to read the compiler to add a
proof or an algorithm using existing operations.

The [architecture policy](ARCHITECTURE-POLICY.md) makes the dependency and algorithm
role rules explicit. [Review ownership](REVIEW-OWNERSHIP.md) routes changes to area
maintainers; Sorrachai is the initial sole owner.

## Set up a working checkout

Install Git, Python 3.10 or later, and Lean's `elan` toolchain manager. For
interactive proof editing, open the repository in VS Code with the Lean 4
extension. Follow [Lean's installation instructions](https://lean-lang.org/install/)
if these tools are new to you.

```sh
git clone --branch experimental-RAM-model https://github.com/cslib-community/AlgoLib.git
cd AlgoLib
lake env lean --version
lake build AlgoLib.Experimental.RAM.Tests.GettingStarted
```

Use the checked-in `lean-toolchain` and `lake-manifest.json`; do not run
`lake update` as part of ordinary setup. The current toolchain is
`leanprover/lean4:v4.30.0-rc2`. The first build downloads dependencies and can take
considerably longer than subsequent checks. Loom and Velvet are vendored at pinned
revisions; their [attribution and port policy](../../../../vendor/README.md) explain
the local changes.

Open [the tutorial's Lean file](../Tests/GettingStarted.lean), place the cursor at
each inspection command, and read the editor's messages. Basic Lean proof skills
are still required: the interface exposes mathematical obligations, but does not
invent invariants or eliminate the need to understand a proof context.

## Choose a contribution and its home

| Contribution | Start here | Check the change with |
| --- | --- | --- |
| Explain an example or improve a proof | [Examples](../Examples/README.md), [tutorial](GETTING-STARTED.md) | The affected Lean module and its executable example |
| Add an algorithm using existing operations | [Insertion sort's module split](../Examples/InsertionSort/README.md) | Universal correctness/bound theorem, execution examples, invalid-input cases where relevant |
| Improve obligation messages or proof editing | [Verification](../Verification/README.md) | `Tests/ObligationAPI/`, named-proof regressions, focused elaboration checks |
| Extend syntax or expression support | [Language](../Language/README.md) | Independent [conformance](../Tests/Conformance/README.md) comparisons and rejection cases |
| Add a data-structure operation | [Library](../Library/README.md) and [Implementations](../Implementations/README.md) | Functional/resource contracts, framing, a client, and implementation substitution |
| Change linking or lowering | [Compiler](../Compiler/README.md) | Semantic/cost preservation, native compiler and axiom regressions |
| Change instructions or counted execution | [Machine](../Machine/README.md) | Instruction semantics, runner agreement, affected compiler proofs and bounds |

Good first contributions include explaining one generated goal, adding an edge
case to an existing example, or proving a small client theorem from a public
contract. Extending the source language or changing a memory representation is a
larger task because it crosses additional proof boundaries.

Use the seven public layer imports listed in [PUBLIC-API.md](PUBLIC-API.md) for
clients. Within the implementation, use narrow imports and respect the checked
dependency DAG. [Historical](../Historical/README.md) and
[Research](../Research/README.md) preserve experiments and compatibility evidence;
they are not alternative starting points. Older `Prototype.Composition` declaration
names may still appear in diagnostics: the public names alias those definitions,
rather than introducing another implementation.

## Follow one algorithm through the stack

The tutorial keeps its code in one file. For a maintained algorithm, follow this
division so editing a proof need not recheck its backend certificate:

| File | Author's responsibility |
| --- | --- |
| `Program.lean` | Inputs, output contract, source code, named invariants and counting arguments |
| `Obligations.lean` | Generate the method's proposition declarations |
| `Proofs.lean` | Discharge each named mathematical responsibility separately |
| `Backend.lean` or storage modules | Select and certify implementations; depend on the program, not its proof file |
| `Execution.lean` | Combine those certificates with the source proof; expose the runner and final theorem |

The [sorting example](../Examples/InsertionSort/README.md) shows this split.
[BFS](../Examples/BFS/README.md) adds graph inputs and interchangeable queue
implementations. Before writing a similar algorithm, read its final theorem to
check that its inputs, output, and cost boundary match your intended problem.

In the authoring loop, use `generate_obligations`, inspect a responsibility with
`#named_goals` or `#explain_obligation`, then save its proof with
`prove_obligation`. `complete_algorithm` checks their assembly; the standard
compilation commands supply the backend connection for supported scalar and array
interfaces. Richer interfaces require an implementation author to supply linking
and storage certificates. See the [obligation API](../Verification/OBLIGATION-API.md)
for the exact commands and [API policy](../Verification/API-POLICY.md) for changes
that require proof migration. Stable responsibility names do not imply stable
pretty-printing, temporary variable names, or inferred numerical constants.

## Know which claims you are contributing

The current supported path connects source proofs, owned implementation contracts,
and the executable integer machine. Its core connections can be reviewed in:

| Claim | Definition or theorem to follow |
| --- | --- |
| Discharged VCs establish abstract execution and sufficient credits | `Plan.sound` in [Plan.lean](../Verification/Plan.lean); `Algorithm.certify` in [Algorithm.lean](../Verification/Algorithm.lean) |
| Loom reasons about that same method | `Algorithm.loom_correct` in [Loom.lean](../Verification/Loom.lean) |
| Certified operations compose into a client implementation | `client_linking` in [native linking](../Compiler/Assembly/Native/Linking.lean) |
| Typed execution lowers to RAM with its counted cost and observation | `Native.Eval.compile` in [Compiler.lean](../Compiler/Native/Compiler.lean) |
| The returned runner value and upper bound satisfy the contract | `runEncoded_correct` in [native execution](../Compiler/Assembly/Native/Execution.lean), exposed through `Compiler` |

Logical credits are the algorithm proof's resource interface, **not RAM steps**.
Implementation rates and private potential justify the final bound. State any
initial potential and preconditions rather than treating them as free work.
The current target is structured, unit-cost, unbounded **Int-RAM**. Natural-valued
source operations retain their semantics, including subtraction truncated at zero.
This does not establish word-RAM or bit-complexity bounds. Resident-input execution
does not automatically charge host-side encoding, decoding, or Lean runtime work.

The supported frontend has structured loops and calls with finite bodies;
general runtime recursion, arbitrary Lean runtime values, and dynamic allocation
are not established capabilities of this path. Compiler theorems and reconstructed
certificates do not amount to a universal correctness theorem for the surface
parser. Bounded independent conformance tests provide additional testing evidence.

The onboarding review used branch baseline `b7cd6be`: its full build and structural
checks passed. It found broken repository entry links, now corrected, and a missing
small authoring walkthrough, now supplied by the tutorial. This is an engineering
and documentation review, not an independent soundness audit. The
[design and review draft](DESIGN-AND-REVIEW-DRAFT.md) identifies the specification
alignment questions humans still need to examine.

## Register files and validate a patch

Every new RAM Lean module needs a module docstring immediately after its imports,
a record in [modules.json](modules.json), and an appropriate import or build target.
Use an existing record in the same layer as a template; the tutorial fixture is
registered as a test and imported by the root `AlgoLib.lean`. Add new public aliases
only deliberately, following [PUBLIC-API.md](PUBLIC-API.md).

For a maintained algorithm, also register its program/proof/backend/execution roles
and importing tests in [algorithms.json](algorithms.json). Every example module must
be classified; adding a file does not exempt it from logical independence or proof-edit
boundaries. The [architecture policy](ARCHITECTURE-POLICY.md) describes each role.

Regenerate the indexes instead of editing their generated sections:

```sh
python3 AlgoLib/Experimental/RAM/Tests/generate_navigation.py
python3 AlgoLib/Experimental/RAM/Tests/check_layers.py
```

The layer check includes navigation and metadata regressions, dependency rules,
and generated conformance consistency. It does not execute the generated Lean
programs; the Lean build does that. A focused iteration can use:

```sh
lake build AlgoLib.Experimental.RAM.Tests.GettingStarted
lake env lean AlgoLib/Experimental/RAM/Tests/GettingStarted.lean
```

Before submitting, run the full build and structural check. For elaborator or
proof-API changes, also check elaboration budgets; the focused example below can
be replaced by the full suite (omit `--case`):

```sh
lake build
python3 AlgoLib/Experimental/RAM/Tests/check_layers.py
python3 AlgoLib/Experimental/RAM/Tests/check_elaboration.py --case named-proof-interface
```

If changing proof-edit dependencies or caching, run
`python3 AlgoLib/Experimental/RAM/Tests/check_proof_edit.py` in a disposable
checkout. It temporarily edits and restores a proof file; run it separately from
builds and editor changes. Elaborator timings measure Lean checking, not RAM cost.
See [Tests](../Tests/README.md) for the complete suite.

For new semantics or contracts, include the relevant universal theorem and a
regression that would fail for the bug you intend to prevent. Rejection tests should
check the intended diagnostic, not merely any failure. Preserve existing axiom
guards; do not introduce `sorry`, new axioms, or unchecked solver admissions.
Explain changed theorem assumptions, ownership requirements, cost boundaries, and
any API migration in the pull request. Report executed checks accurately, keeping
bounded tests distinct from universal proofs. The repository's
[general contribution rules](../../../../.github/CONTRIBUTING.md) also apply.
