# AlgoLib

A [Lean 4](https://lean-lang.org/) library for **algorithms**, built on top of
[Mathlib](https://github.com/leanprover-community/mathlib4) and
[CSLib](https://github.com/leanprover/cslib). AlgoLib aims to provide machine-checked
definitions, theorems, and algorithm implementations covering the standard
undergraduate-through-graduate curriculum on algorithms.

We focus on computable definitions and algorithms. Where needed, we introduce
definitions for concepts already formalized in Mathlib, such as graphs. Our goal
is to stay close to textbook formulations without compromising on generality.

## Using AlgoLib in your project

### Prerequisites

Install [Lean and its editor support](https://lean-lang.org/install/) and
[Git](https://git-scm.com/downloads). The Lean installation includes `elan`, the
toolchain manager, and `lake`, the build tool and package manager.

To start a new project with the supported Lean version:

```sh
lake +leanprover/lean4:v4.35.0 new my_algolib_project lib
cd my_algolib_project
```

Use the Lean version specified by AlgoLib's [`lean-toolchain`](lean-toolchain)
at the revision you depend on. The current version is:

```text
leanprover/lean4:v4.35.0
```

For an existing project, its `lean-toolchain` must match this version, and any
direct Mathlib or CSLib dependencies must be compatible with AlgoLib's
[`lakefile.toml`](lakefile.toml) and [`lake-manifest.json`](lake-manifest.json).
When you run Lake, `elan` downloads the specified Lean toolchain if needed.

### Add the dependency

Add the following to your project's `lakefile.toml`:

```toml
[[require]]
name = "AlgoLib"
git = "https://github.com/cslib-community/AlgoLib"
rev = "v4.35.0"
```

Alternatively, if your project uses `lakefile.lean`, add:

```lean
require AlgoLib from git
  "https://github.com/cslib-community/AlgoLib" @ "v4.35.0"
```

Use the configuration format your project already uses. The package name is
case-sensitive: `AlgoLib`.

From your project's root directory, fetch the dependency and the Mathlib cache:

```sh
lake update AlgoLib
lake exe cache get
```

The cache command downloads precompiled Mathlib dependencies to reduce the first
build's work. AlgoLib's dependencies are fetched automatically, including Mathlib
and CSLib pinned to `v4.35.0`.

### Import and build

AlgoLib uses Lean's module system. A new Lean file can import the modules it
needs as follows:

```lean
module

import AlgoLib.Theory.Graph.Basic

#check AlgoLib.Graph
#check AlgoLib.SimpleGraph
#check AlgoLib.DiGraph
```

You can also import the modules collected in the library's root file with:

```lean
module

import AlgoLib
```

Run `lake build` after adding the import to one of your project's build targets.
For a standalone file named `Example.lean` in the project root, use:

```sh
lake build AlgoLib
lake env lean Example.lean
```

Open the project root in VS Code so the Lean extension uses the project's
toolchain and dependencies.

### Pinning a revision

The examples above use the fixed `v4.35.0` tag for Lean 4.35.0. To use an older
Lean version, choose an available matching [tag](https://github.com/cslib-community/AlgoLib/tags)
and use the `lean-toolchain` from that revision. Only versions with a published
tag are supported this way.

You can also pin a full commit hash you have tested. Commit the generated
`lake-manifest.json` to keep the resolved dependency versions reproducible.
Use `main` instead of a tag only if you want to follow ongoing development when
running `lake update AlgoLib`.

New stable Lean versions receive a tag and a dated
[GitHub release](https://github.com/cslib-community/AlgoLib/releases) after CI
passes on `main`. Existing tags stay fixed; later fixes can be selected by their
commit hash. There is no need to put a timestamp in the dependency name.

### Upgrading an existing project

Set your project's `lean-toolchain` to `leanprover/lean4:v4.35.0`, then run the
dependency and build commands above. If you require Mathlib or CSLib directly,
align those requirements with their `v4.35.0` releases.

Mathlib renamed `Tree` to `BinaryTree`. AlgoLib's binary-tree API now uses the
`BinaryTree` namespace too: update `Tree α`, `open Tree`, and qualified names
such as `Tree.num_nodes` to `BinaryTree α`, `open BinaryTree`, and
`BinaryTree.num_nodes`. The module import paths are unchanged.

## Building AlgoLib locally

To work on AlgoLib itself, clone the repository and build it:

```sh
git clone https://github.com/cslib-community/AlgoLib.git
cd AlgoLib
lake exe cache get
lake build
```

The checkout includes its toolchain and dependency manifest. Keep these files
when reproducing a build. See the [contribution guide](.github/CONTRIBUTING.md)
before making changes.

CI checks daily for new stable Lean releases and waits for matching Mathlib and
CSLib tags using the same toolchain. Once available, it opens one upgrade issue.
Maintainers make the upgrade PR and fix breaking changes. CI checks the build
and publishes version tags after successful merges. See the
[maintenance notes](.github/CONTRIBUTING.md#lean-version-updates) for the process.

## Repository layout

```text
AlgoLib.lean            # imports the library's modules
AlgoLib/
├── Theory/            # graph definitions and mathematical results
├── Algorithms/        # algorithms and correctness proofs
├── DataStructures/    # binary trees, splay trees, union-find, …
└── Util/              # supporting lemmas and utilities
blueprint/             # mathematical exposition
website/               # website sources
```

## Roadmap — v1

The following topics describe our goals for the library.

### Theory

- **Walks and connectivity.** Walks, paths, cycles, Eulerian walks, components.
- **Trees.** Trees and forests, Cayley's theorem on the number of labeled trees.
- **Spectral graph theory.** Laplacians, Cheeger's inequality, expansion and expander graphs.
- **Matchings.** Matchings, augmenting paths, Hall's theorem, König's theorem.
- **Colorings.** Proper vertex and edge colorings, chromatic number, basic bounds.
- **Contractions and minors.** Edge and vertex contractions, minors and topological minors.
- **Embeddings and planarity.** Planar graphs, Euler's formula, Kuratowski's theorem, toroidal graphs.

### Algorithms

- **Flows.** Ford–Fulkerson, Edmonds–Karp, Push–Relabel.
- **Graph traversal.** BFS, DFS.
- **Shortest paths.** Dijkstra, Bellman–Ford, Floyd–Warshall.
- **Minimum spanning trees.** Kruskal, Prim, Borůvka.
- **Strongly connected components.** Tarjan / Kosaraju.
- **Union–Find.** Disjoint-set forests with union-by-rank and path compression.

We aim to accompany each algorithm with proofs of correctness and runtime.

## License

AlgoLib is released under the [Apache License 2.0](LICENSE).
