# Verified RAM algorithms, by abstraction layer

The [Loom-connected BFS tutorial](Prototype/GRAPH-TUTORIAL.md) demonstrates typed
graph primitives, modular neighbor-scan and vertex-processing procedures, and a
checked connectivity/linear-time theorem for their composed RAM program.

Start with **[sorting](Programs/Sorting.lean)** or **[connectivity via BFS](Programs/Connectivity.lean)**. Each file contains one complete story: the target statement, an input/output method, the generated verification conditions, the invariant proof, the executable, and the main theorem. There is no separate algorithm to find in an executable or proof directory.

For the isolated mutable Velvet/Loom integration, see **[Prototype](Prototype/README.md)**.
It verifies explicit mutable-array insertion sort using the actual Loom algebra and inline annotations,
then reconstructs the existing RAM certificate for the same executable program. Its guide
explains the connection, explicit Loom/Velvet attribution, and the RAM compilation boundary.

```lean
import AlgoLib.Experimental.RAM
open AlgoLib.Experimental.RAM

#eval (Programs.Sorting.run [3, 1, 4, 1]).value
-- [1, 1, 3, 4]

example (xs : List Nat) :
    Programs.Sorting.SortedPermutation xs (Programs.Sorting.run xs).value :=
  (Programs.Sorting.main xs).1
```

## Read from the theorem to its proof

| Step | Sorting | BFS connectivity |
|---|---|---|
| State the target | `SortedPermutation`, `Claim` | `Returns`, `Claim` |
| Read the input/output program | `insertionSort` | `breadthFirstSearch` |
| Choose the paper argument | sorted suffix + permutation | frontier + processed vertices |
| Supply the charging argument | `potential` | `potential` |
| Prove the algorithm obligations | `loopProof` | `loopProof` |
| Check the generated method obligations | `verification : insertionSort.VCs` | `verification : (breadthFirstSearch a G).VCs` |
| Run and use the theorem | `run`, `main`, `quadratic` | `run`, `main`, `connected_iff_set`, `linear` |

For every list, sorting returns a sorted permutation in at most `50n² + 100n + 55` RAM steps. For nonempty lists, `quadratic` gives `205n²`. The constant term matters for empty input. `exists_quadratic_sort` also states existence using a **verified procedure** as its witness.

BFS takes a graph represented by adjacency lists and a valid source, and returns a vertex-set membership view. `main` proves exact reachability, **`Connected G ↔ vertices S = G.vertexSet`**, and at most `370(|V| + |E|)` RAM steps. Disconnected graphs, isolated vertices, loops, and parallel labelled edges are supported. An empty graph cannot supply a valid source.

## The displayed program is the executable program

The method syntax is Dafny-inspired. For example, inside the sorting file:

```lean
def insertionSort : Method Insertion.interface :=
  ram_method (xs : List Nat) returns (ys : List Nat)
    using Insertion.interface;
    requires True;
    ensures SortedPermutation xs ys;
    credits (xs.length * (xs.length + 2) + 1);
    time (50 * xs.length ^ 2 + 100 * xs.length + 55);
  do {
    while (more) {
      call insertNext;
    }
  }
```

`insertNext` is the separately certified INSERT subroutine. It consumes one unprocessed value and inserts it into the sorted suffix. The implementation processes the input right to left. Its logical effect and cost are in [Library/Insertion.lean](Library/Insertion.lean); its memory proof belongs to the backend.

For BFS, the method calls `dequeue`, `scanNeighbors`, and `finish` inside the frontier loop. `scanNeighbors` implements the neighbor loop and the mark-before-enqueue test. `finish` updates the proof's processed set and emits no instructions. Input preparation clears flags and seeds the queue. The [authoring guide](Authoring/README.md) maps these operations to textbook pseudocode.

This is a language over certified operations, with compositional `while`, `if`, and procedure calls. It is **not a complete Dafny parser**: arbitrary `visited[v] := ...` statements are not yet part of this public mathematical API. New primitives must come with library contracts; they cannot acquire a cost bound merely by being given a name.

## Choose the layer for your task

| Layer | Responsibility | Who normally reads it? |
|---|---|---|
| [Programs](Programs/README.md) | Complete algorithm specifications, methods, proofs, and demos | Algorithm students and authors |
| [Authoring](Authoring/README.md) | Mathematical semantics, VC rules, method syntax, verified runner interface | Authors reusing proof rules; framework maintainers |
| [Library](Library/README.md) | Public logical effects, preconditions, functional/cost contracts, input/output adapters | Authors choosing reusable operations |
| [Specification](Specification/README.md) | Repository `Graph`, reachability, connectivity, adjacency representation | Authors proving graph mathematics |
| [Backend](Backend/README.md) | Memory layouts, implementation certificates, typed language, compiler and refinement | Library and compiler maintainers |
| [Machine](Machine/README.md) | RAM instructions, execution semantics, total runner, output views | Machine-model maintainers |
| [Tests](Tests/README.md) | Runtime, negative-contract, compiler, and axiom regressions | Maintainers |
| [Legacy](Legacy/README.md) | Older alternative demonstrations, explicitly opt-in | Historical comparison only |

These are responsibility boundaries. Some backend adapters implement authoring contracts, so the directory order is not itself a strict module-dependency order. No backend, library, machine, or authoring module imports a `Programs` or `Legacy` algorithm. The [architecture guide](docs/ARCHITECTURE.md) explains the actual handoffs.

## What you prove, and what the library does

You supply an invariant, preservation/exit arguments, operation preconditions, and the charging facts. `paper_steps` substitutes logical effects and generates call payments. `method_vc` opens the declared output and total-time obligations. Registered adapter equations and arithmetic automation discharge the routine representation-independent bookkeeping.

The library establishes physical framing, implements the operations, relates logical states to memory, compiles the declared body, transports its certificate, and runs it without fuel. The same certificate proves the output contract and the bound on actual compiled steps. Proof checking, host input encoding, and host output enumeration are outside the unit-cost RAM count; compiled preparation is included.

`Programs.Connectivity.search graph source` is the convenience API with explicit graph and source arguments (`source : Fin graph.n`). Its `search_correct` theorem gives the same reachable-set, connectivity, and time guarantees.

For runnable examples see [Programs/Examples.lean](Programs/Examples.lean). For the former layout and updated names see [migration](docs/MIGRATION.md). The [PDF tutorial](docs/verified-ram-student-tutorial.pdf) and slide deck document the earlier `2c78e53` layout; use the current source guides and [updated Lean companion](docs/StudentDemo.lean) for this layout.
