# Design principles and current limits

## One algorithm, one execution claim

A runnable algorithm is a fixed typed syntax tree, not a host function that can compute arbitrary results and choose a cost. Its generated verification conditions refer to independently specified source execution. Its final theorem refers to the compiled RAM instructions. Correctness and time quantify over the same result and step count.

Changing the displayed source changes the command tree. A reused certificate must still satisfy the checked normalization equality. A false cost bound must still prove a real `Eval`/`Exec` derivation; merely writing a smaller budget does not establish the contract.

## Pay for the work the model permits

Every RAM instruction and guard costs one. Source expressions pay for their generated instructions, including subexpressions, address arithmetic, loads, and stores. Scoped variables also pay to save, bind, and restore their values. Ghost proofs and specifications do not execute in the machine.

This prevents freely declaring a sorting operation to cost one inside the restricted language. It does not make all possible complexity statements comparable automatically. A client can choose a precondition that already assumes sorted input, or a representation containing precomputed answers. Review preconditions, encoders, output decoders, and the chosen unit-cost arithmetic when interpreting a theorem.

The input encoders are specification/host conveniences. Their construction cost is excluded. The list returned by the sort wrapper and the bitmap's `.toList` are also host views; the charged result is in RAM memory. A theorem about a full external file-to-file pipeline would need additional input/output programs and their costs.

## Independent semantics, a small compiler theorem

`Store`, typed expressions, and `Eval` are defined before compilation. Correctness is not defined as “whatever the compiler does.” The compiler proves source/machine agreement, scratch-register preservation, and exact cost. The evaluator is justified separately against machine execution.

Words and pointers are distinct types. This catches a class of mistakes but does not itself establish memory safety: array bounds, capacity, nonaliasing, and frame obligations remain in contracts. Memory is total, with no faulting out-of-bounds primitive.

## Modular proof state

Functional contracts describe abstract sequences or graph rows. Representation predicates connect those values to addressed memory. Frame lemmas explain which cells remain unchanged. Loop invariants describe algorithm progress, and potentials account for remaining work. Keep these facts separate so a memory-layout change need not change the graph theorem.

The current queue uses append-only fixed-capacity storage. Dequeue does not reclaim earlier slots. It supports BFS because each vertex is enqueued at most once. It does not implement resizing, allocation, or an unbounded reusable queue.

## Honest ergonomics

The common DSL supports named typed variables, nested expressions, indexed arrays, branches, loops, scoped locals, and procedures with a typed parameter/result. Calls inline finite command bodies. Recursive procedures, dynamic allocation, polymorphic data types, inferred separation assertions, and automatic invariant synthesis are not implemented.

The complete algorithms are now on this common frontend. Their source still shows low-level indexing and loop bookkeeping. BFS's most concise textbook presentation is its mathematical invariant and high-level loop structure; the current generic frontend does not restore the removed BFS-specific parser patterns. Further syntax should desugar compositionally and carry library contracts, rather than recognize one whole algorithm.

The complete demos currently discharge generated VCs through verified instruction certificates; the smaller language examples show direct source proofs. This is a unified executable stack with two sound proof techniques. It is still an experimental teaching/research library, not a claim of Dafny-level automation or a finished undergraduate IDE.

## Cost convention

The machine is a unit-cost RAM over unbounded natural numbers. Subtraction saturates at zero; multiplication has unit cost. Registers are named in the formal model, but every fixed program references finitely many. These conventions establish RAM operation bounds, not bit bounds, cache behavior, physical memory limits, or Lean evaluation time.

For insertion sort the proved bound is an upper bound for every input. `O(n²)` does not state exact `n²` time, and no worst-case lower bound is proved here. For BFS a valid source implies at least one vertex; the empty graph has no admissible source. Loops and parallel labelled edges are supported and counted in `m`.
