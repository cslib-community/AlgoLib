> This deck documents the earlier typed stack. For the new automated paper-proof authoring layer, see [Architecture](ARCHITECTURE.md) and the [authoring tutorial](../Paper/README.md). The existing compiler and RAM layers remain in use.

# Verified RAM in Lean: presentation

[Download the editable slides](verified-ram-stack.pptx). The slides cover the executable stack, proof dependencies, algorithm guarantees, and repository reading routes.

See [Architecture](ARCHITECTURE.md) for clickable theorem paths and [Examples](../Algorithms/Examples.lean) to run the demos.

## 1. Verified RAM in Lean

One public import: AlgoLib.Experimental.RAM. The two complete algorithms execute the compiled typed DSL.

## 2. One source program One execution theorem

The refactor removes the shallow cost monad and specialized BFS frontend. Instruction certificates are internal proof tools.

## 3. A tour of the stack

Follow the repository reading routes shown near the end. All paths are relative to AlgoLib/Experimental/RAM.

## 4. The model and its cost boundary

Unit-cost natural RAM is an explicit modeling convention. Input encoding, host display, and bit costs are excluded.

## 5. Independent source and machine semantics

Source Eval is independently defined. Compiler preservation proves observable-store equality and exact cost.

## 6. A small compositional language

Procedures have one typed parameter and one typed result variable. Calls are finite, inlined bodies; recursive procedures and allocation are not implemented.

## 7. Reusable contracts

Library.Sequences supplies fixed-capacity arrays for queues and stacks. GraphMemory supplies the linked representation used by BFS. Graph supplies a separate CSR interface; BFS is not yet ported to CSR.

## 8. Proofs describe the algorithm

Ghost computations are unrestricted mathematical definitions but cannot occur as arbitrary host callbacks in Cmd or Instr.

## 9. Time credits also prove termination

The source VCG includes guard costs. A strictly decreasing natural credit yields total correctness and hence a termination witness.

## 10. Verification conditions

VC.complete and Contract.vc let an existing semantic contract discharge the generated VCs. This is proof reuse, not automatic invariant inference.

## 11. Two ways to discharge the same VCs

The full demos currently use internal instruction certificates lifted to typed source. Normalization checks sequencing structure; lift_correct pays expression costs. Method.run still executes only the ordinary source compiler.

## 12. Design principles

Proof soundness depends on the Lean kernel and the imported mathematical library. Inspect the checked theorem statements and run the repository tests.

## 13. Library interfaces

Array contracts include bounds and frames. Queue contracts include capacity and register separation. Pointer typing is not a separation logic or an automatic alias analysis.

## 14. The theorem map

Exact declarations and namespaces are indexed in docs/ARCHITECTURE.md. The source compilation and runner theorems carry the exact cost; algorithm theorems supply upper bounds.

## 15. Insertion sort

The complete algorithm sorts a suffix from right to left. Correctness includes sortedness, permutation, and frame. Bound: 20n²+40n+10; 70n² for n≥1.

## 16. BFS, in the order of the paper proof

BFS processes linked adjacency rows. The source is valid even when the graph is disconnected. It returns exactly the source component.

## 17. Execution and proof paths

Runtime path: Cmd.compile produces Code; Runner uses a termination witness. Proof path: VC.sound establishes Eval, then Eval.compile establishes Exec. Public output decodes the final observable store.

## 18. BFS representation refinement

Represents connects adjacency membership to Graph edges. GraphBridge proves equivalence with the repository’s graph reachability/connectivity relations. Loops and labelled parallel edges are supported.

## 19. The BFS time argument

Instruction potential is Σ over unprocessed vertices of (8 + 16 degree(v)). Initial total is 8n + 16 entries ≤ 8n + 32m. Initialization is added. The adapter yields source bound 65n + 160m + 45.

## 20. Adapter costs

The lifted primitive costs are move 2, binary operation 4, load 5, store 5. Certificate instruction costs are one each. This comparison describes the proof adapter; it is not a compiler optimization benchmark.

## 21. Sorting upper bounds

Bounds computed at n=1,2,4,8: general [70,170,490,1610]; simplified [70,280,1120,4480]. No timing measurements are plotted.

## 22. BFS upper bounds

Graphs: singleton (n=1,m=0), path (4,3), split (4,2), multigraph (3,5). General bounds [110,785,625,1040]; uniform [160,1120,960,1280]. Input encoding excluded.

## 23. Public algorithm contracts

BFS always returns all reachable vertices. Its output equals the whole vertex set iff the graph is connected, assuming a valid source. Enumerating or testing all output flags has an additional linear host cost outside run.steps.

## 24. Component dependencies

Dependency spans express logical responsibilities, not project dates. Specifications support library representations; source VCs plus invariant proofs establish contracts; compiler and runner connect contracts to returned execution.

## 25. Repository reading routes

Public programs: Algorithms/InsertionSort.lean and Algorithms/BFS.lean. Examples has executable clients; Tests includes exhaustive small graph checks and bounded sorting inputs. docs includes architecture, principles, and migration.

## 26. Read the program Follow the theorem

Import AlgoLib.Experimental.RAM and run lake build. Read README, Algorithms/Examples, then the matching correctness and ram_correct theorem.
