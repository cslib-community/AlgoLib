# AlgoLib

A [Lean 4](https://lean-lang.org/) library for **algorithms**, built on top of [Mathlib](https://github.com/leanprover-community/mathlib4). AlgoLib aims to provide machine-checked definitions, theorems, and algorithm implementations covering the standard undergraduate-through-graduate curriculum on algorithms.

Since we focus on computable definitions and algorithms, we introduce new definitions for concepts already formalized in Mathlib (e.g., out definition of graphs). Our primarly goals is to provide a concise formalization of algorithms that stays close to their textbook formulation without compromising on generality. 

## Roadmap — v1

### Theory

Among others:

- **Walks & connectivity.** Walks, paths, cycles, Eulerian walks, components.
- **Trees.** Trees and forests, Cayley's theorem on the number of labeled trees.
- **Spectral graph theory.** Laplacian, Cheeger's inequality (upper and lower bounds), expansion / expander graphs.
- **Matchings.** Matchings, augmenting paths, Hall's theorem, König's theorem.
- **Colorings.** Proper vertex and edge colorings, chromatic number, basic bounds.
- **Contractions, minors, topological minors.** Edge/vertex contractions and the minor and topological-minor relations.
- **Embeddings & planarity.** Planar graphs, Euler's formula, Kuratowski's theorem, toroidal graphs.

### Algorithms

- **Flows.** Ford–Fulkerson, Edmonds–Karp, Push–Relabel.
- **Graph traversal.** BFS, DFS.
- **Shortest paths.** Dijkstra, Bellman–Ford, Floyd–Warshall.
- **Minimum spanning trees.** Kruskal, Prim, Borůvka.
- **Strongly connected components.** Tarjan / Kosaraju.
- **Union–Find.** Disjoint-set forests with union-by-rank and path compression.

Every algorithm comes with a proof of correctness and a proof of runtime.

## Repository layout

```
AlgoLib/
├── Basic/          -- core graph structures (Graph, SimpleGraph, DiGraph, SimpleDiGraph)
├── Theory/         -- mathematical results (walks, trees, spectral, matching, …)
└── Algorithms/     -- algorithm implementations and correctness proofs
```

## Building

```
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain`. `elan` will install it automatically.

## Experimental verified RAM algorithms

The [`experimental-RAM-model` stack](AlgoLib/Experimental/RAM/README.md) provides a typed DSL,
verified compiler, correctness/time VCs, and fuel-free insertion sort and BFS.
Start with its [executable examples](AlgoLib/Experimental/RAM/Algorithms/Examples.lean) or
[architecture guide](AlgoLib/Experimental/RAM/docs/ARCHITECTURE.md).
