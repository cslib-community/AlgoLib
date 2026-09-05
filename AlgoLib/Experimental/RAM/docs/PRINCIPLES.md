# Principles and current limits

## Algorithm authors prove mathematics

The primary interface is `Programs` for complete algorithms and `Authoring` for reusable proof rules. Users supply an algorithm invariant, its initialization, a charging scheme, and mathematical preservation/exit arguments. They do not prove normalization equalities, register correspondence, address disjointness inside queue operations, instruction-certificate lifting, or compiler-overhead transport.

`Programs/Connectivity.lean` and `Programs/Sorting.lean` are the acceptance examples: neither mentions `Store`, `Exec`, heap addresses, normalization, or the compiler. Each file contains its input/output method declaration, generated VCs, proof, and executable. Existing low-level proofs remain reusable implementation evidence inside the library.

## Automation must produce checked proofs

`ram_method` binds a displayed, input-independent body to input/output contracts and declared budgets. `method_vc` opens its generated obligations; `method_time` pays routine adapter overhead using public library equations. `VerifiedMethod.correct` provides the output and time theorem for its actual run.

`paper_steps` substitutes logical operation contracts and composes verification conditions. It uses a curated `paper_simps` theorem set; it does not unfold physical implementations. `paper_credits` handles routine natural-number polynomial arithmetic and subtraction. `LoopProof` leaves named preservation, payment, and exit obligations for the author.

The generic `VC.sound` theorem proves total correctness of the mathematical program. `Run.refines` automatically connects every certified operation and control-flow construct to typed source execution. The existing verified compiler and runner then provide actual RAM execution. These links are proved once for the framework, not once per user algorithm.

No invariant inference, unverified oracle, new axiom, or `sorry` is introduced. When automation cannot solve an obligation, it remains a Lean goal.

## Library contracts own memory details

An operation specifies a mathematical precondition, effect, and work bound. Its fixed typed implementation must establish the representation of that effect for every represented input satisfying the precondition. This obligation cannot be replaced by a freely chosen cost annotation.

A representation declares a read footprint. A mutation proves its write footprint. The generic frame rule preserves any assertion with a disjoint read footprint, including composed assertions. Graph tables and array segments use this mechanism; clients of certified operations receive their physical frames automatically. Logical ghost fields frame by effect substitution.

This is a reusable footprint discipline, not a complete separation-logic engine. Library developers still establish footprints and disjointness. Arbitrary composition of new layouts, alias inference, ownership inference, and automatic allocation are not implemented. Existing array/stack/queue contracts remain available to library implementers.

## Procedures hide proofs, never work

A `Procedure` packages a program, mathematical effect, precondition, cost budget, and proof. Calls expose the summary to the VCG and emit the verified body to the compiler. BFS's row traversal is proved independently and reused through this interface. Insertion sort uses a linear-time insertion contract; its outer sortedness/permutation proof is independent of the insertion implementation.

Ghost state never executes. In particular BFS's processed-set update emits no instructions. Guards must be certified against real source tests, so ghost-only state cannot silently become an executable oracle. Calls inline finite bodies; recursion, dynamic allocation, and polymorphic runtime objects are future work.

## Cost and termination have the same execution witness

Every RAM instruction and guard costs one. A library work unit has a proved upper bound on actual compiled cost, including expression evaluation, loads/stores, and control flow. Framework theorems multiply and compose these bounds automatically. A true paper loop spends a positive guard credit, making its verified potential argument establish termination. No fuel is supplied to the runner.

The new conservative bounds are `50n² + 100n + 55` for insertion sort and `370(n+m)` for BFS with a valid source. The executable theorem counts input preparation, including clearing arbitrary visited flags. Explicitly imported legacy APIs retain their earlier tighter constants; these are different contracts for related compiled programs, not contradictory measurements.

These are upper bounds, not exact runtimes or lower bounds. Time receipts are deferred.

## State the boundary of the claim

The machine is a unit-cost RAM over unbounded natural numbers with saturating subtraction and unit-cost multiplication. It models RAM operation counts, not bit complexity, caches, physical memory capacity, or Lean wall-clock time. Typed words/pointers do not alone prove memory safety; the contracts establish the bounds and representation conditions used by the program.

Input encoders are host conveniences. Output list construction and bitmap formatting are host observations. Their cost is outside the RAM step count; an external file-to-file complexity theorem would need charged I/O code. A cost statement must be read together with its representation and input preconditions.

For graphs, `m` counts labelled edges, including parallel edges, and an undirected self-loop contributes two adjacency incidences. A valid source excludes the empty graph. BFS returns exactly the reachable set on connected and disconnected inputs; returning every vertex is equivalent to connectivity.

## Usability is tested, not declared finished

The public examples run the actual compiler/runner and are checked against independent sorting and reachability references. Negative tests reject zero budgets at true guards, unpaid calls, and invalid frames. Kernel axiom checks audit the end-to-end theorems.

This revision hides implementation obligations for the demonstrated authoring libraries. It still requires Lean syntax and mathematical proof skills. It does not claim Dafny-level automation, a rich IDE, or classroom usability established by student testing. The next usability work should expand certified operation libraries and test the workflow with users, rather than expose more compiler internals.
