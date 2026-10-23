# Maintaining the RAM architecture

The contribution path is [tutorial](GETTING-STARTED.md) →
[contributor guide](CONTRIBUTING.md) → a small patch in the appropriate layer.
This policy explains the boundaries CI checks as the library grows.
[Review ownership](REVIEW-OWNERSHIP.md) identifies who reviews changes to them.

## Four registries with different responsibilities

| Registry | What it controls |
| --- | --- |
| [modules.json](modules.json) | Complete Lean module inventory, physical layer, interface status, and public entry points |
| [architecture.json](architecture.json) | Allowed layer imports and additional protected semantic interfaces |
| [algorithms.json](algorithms.json) | Each maintained algorithm's program, obligations, proofs, implementation assembly, and execution tests |
| [reviewers.json](reviewers.json) | Reviewer identities and path routing; generates the managed CODEOWNERS section |

These are engineering metadata. They do not define execution semantics, discharge
proofs, or grant a soundness claim. Public declaration exports remain recorded in
[public-exports.json](public-exports.json) under the existing
[API policy](PUBLIC-API.md).

## Dependency rules apply to every module

Every module in Language, Verification, and Library must remain backend-independent.
A new file inherits this rule from its layer; nobody needs to remember to add it to
a Python allowlist. The check also follows repository-local imports outside the RAM
directory, so an ordinary AlgoLib helper cannot hide a compiler dependency. Public
umbrella imports are checked just like narrower imports.
This traversal covers source modules rooted at the repository, not the separate
package roots of vendored Loom/Velvet or other dependencies. Their pinned packages
are checked by Lean; this script does not audit their internal dependency policy.

The allowed-import table describes direct dependencies, including dependencies
reached through those external helpers. Separate transitive rules preserve logical
independence, prevent supported modules from loading historical/research/test code,
and protect native assembly. The module graph must be acyclic. Physical layers need
not form a simple chain: the frontend's convenience imports and implementation
compiler dependencies already require a more precise graph.

Additional named roots protect specific contracts, standalone utilities, and
historical evidence. Each record needs an existing module and an explanation.
These records add restrictions; they do not exempt new logical modules from their
default boundary. Changes to the policy itself are reviewed infrastructure changes.

The shared [Lean header reader](../Tests/lean_imports.py) replaces the old import
regex in both architecture inspection and navigation generation. It understands
indentation, nested comments, imports split across lines, repeated import commands,
and the supported module modifiers. It explicitly rejects unsupported header forms
such as escaped module names. Ordinary dotted ASCII module names and one module
name per import are the supported repository convention. The first body command
must start on a new line after the final import. Strings and documentation in the
body are not additional imports. Lean remains responsible for accepting the whole
file and checking its proofs.

## Every maintained algorithm declares its roles

Insertion sort and BFS are registered as maintained algorithms. Every Lean file
under Examples, except its umbrella module, must belong to exactly one algorithm
role or an explicitly explained fixture. Register a new algorithm with these roles:

| Role | Responsibility and boundary |
| --- | --- |
| `program` | Source method and mathematical annotations; backend-independent |
| `obligations` | Generated proposition API; backend-independent |
| `proofs` | Mathematical proof blocks; backend-independent and uses the named interface |
| `facts` | Optional mathematical lemmas; backend-independent |
| `client` | Optional calls through verified procedure contracts; backend-independent |
| `backend` | Implementation certificates; cannot import any registered algorithm's proof or obligation modules |
| `storage` | Optional assembly of storage contracts; same proof-independence rule |
| `execution` | Combines algorithm proofs and backend certificates into the executable and final theorem |
| `inputs` | Optional host-side example input construction; may use implementation encoders |

Program, obligations, proofs, backend, and execution must each have at least one
module. Other roles may be empty. The algorithm needs an entry page, a review area,
and registered tests that transitively import its execution modules. The checker
verifies this connection; it cannot infer whether a test is mathematically adequate.
Reviewers still inspect the final theorem, its assumptions, and its cost scope.

The existing composition exercises are classified individually as fixtures with
reasons. Logical fixtures retain backend independence; integration fixtures may
assemble implementations. This preserves useful evidence without calling their
older combined proof scripts the supported authoring workflow. Classifying an
algorithm as a fixture is a reviewable scope decision, not a way to claim that it
meets the maintained algorithm requirements.

Known broad proof-search tactics are rejected in maintained proof/client roles.
Known private-layout references are rejected in storage/execution roles. These
source-name checks are intentionally narrow regression guards. They are not Lean
access control or a universal privacy theorem: renamed or aliased implementation
details still require human review and substitution tests. Ownership/refinement
theorems supply the semantic guarantees.

## Make a change without weakening the boundary

For a new module, add its module record and docstring. For an algorithm, start from
an existing entry in `algorithms.json`, register every file and test, and explain
the public result in its entry page. Use the existing contracts first; a new
primitive needs its functional, ownership, and resource certificates.

Run:

```sh
python3 AlgoLib/Experimental/RAM/Tests/generate_navigation.py
python3 AlgoLib/Experimental/RAM/Tests/check_layers.py
lake build
```

The existing CI layer-check command now also runs import-reader, architecture,
algorithm-role, and reviewer-routing regressions. These tests use temporary trees;
they do not corrupt the working checkout to test rejection. They cover a newly
named algorithm, backend leakage through a local bridge, missing classifications,
proof/backend coupling, and stale ownership routing. No Lean or GitHub account is
needed for these structural tests; the full Lean build checks the actual programs.
The build job also compares representative accepted import headers against the
pinned Lean compiler's `--deps` output. To run that check locally after setup, use
`python3 AlgoLib/Experimental/RAM/Tests/test_lean_imports.py --check-lean`.

When assigning a reviewer, edit `reviewers.json` and run
`python3 AlgoLib/Experimental/RAM/Tests/check_reviewers.py --write` before the checks.
Sorrachai is the initial sole owner. Appoint a separate eligible reviewer before
claiming independent review of his changes; CODEOWNERS alone does not enforce
mandatory approval.

If a feature requires a new dependency or a change to a central contract, explain
the motivating client, the affected semantic/cost statements, and the migration in
the pull request. Keep policy changes visible to the area owner. Preserve the
existing proof-edit and axiom checks when changing those interfaces. A green
architecture check confirms the encoded structural rules, not the intended meaning
of a theorem or the suitability of its computational model.
