# The typed language

This is the only public source language. See the [stack guide](../README.md) for
complete algorithms and the [architecture](../docs/ARCHITECTURE.md) for proof dependencies.

## Write an ordinary program

```lean
import AlgoLib.Experimental.RAM
open AlgoLib.Experimental.RAM.Checked.Language

def counter : Var .word := ⟨"counter"⟩
def answer : Var .word := ⟨"answer"⟩

def count : Cmd := program {
  answer := 0;
  while 0 < counter {
    counter := counter - 1;
    answer := answer + 1;
  }
}

def twicePlusOne : Procedure .word .word := procedure (input) returns output {
  output := 2 * input + 1;
}
```

Variables are typed named locations, not aliases for an eight-register bank.
Expressions nest arbitrarily; numeric literals in paper syntax are words.
Explicit address literals can be constructed with `Expr.lit (ty := .ptr)`.
A word and an address are different types: adding
two words is permitted; treating an address as a word is rejected by Lean.
`ArrayRef.address` provides typed address arithmetic. Conditions compare
expressions of the same type.

Procedures have **scoped, call-by-value parameters** and an explicit output
variable. Calls use `answer := twicePlusOne(counter);`. The argument
is evaluated once; the parameter slot is restored on return. `procedure` creates
a fresh parameter name. A caller must not deliberately alias the result with
that private slot. Calls are statically inlined into finite source syntax.
`local counter := counter + 1 { ... }` similarly restores the prior value at
block exit. Nested scopes use distinct saved registers; saving, binding, and
restoring cost three instructions in addition to argument evaluation and the body.

Workspace variables and array handles are explicit parameters. This version
does not implement recursive calls, dynamic stack frames, heap allocation,
polymorphic element types, or an ownership type system. Different
Lean identifiers containing the same typed variable name deliberately alias;
clients must meet the library's aliasing and memory-disjointness obligations.

## Run with explicit input and output

The runnable example in `Demo.lean` packages its verification once:

```lean
open AlgoLib.Experimental.RAM.Checked.Language.Demo
#eval (countFunction.run 5).output  -- 5
#eval (countFunction.run 5).steps   -- 60
```

`Function Input` has fields `body`, `input`, `output`, `ensures`, `budget`, and
`verification`. Its body is fixed before the runtime input is supplied. `run`
takes only the typed input and returns `Execution Nat`, with named `output` and
`steps` fields. `Function.correct` proves both the output specification and the
RAM cost bound. `Method` is the lower-level interface for programs with a source
store and a precondition.

Neither runner takes fuel. A verified execution supplies the termination proof,
which is erased before evaluation. An unproved loop cannot become a verified
executable merely by assigning it a budget.

## Prove it as on paper

For `count`, let `n` be the original counter. The proof in `Demo.count_verified`
uses:

- **Invariant:** `counter + answer = n`; the heap remains unchanged.
- **Remaining credits:** `11 * counter + 3`.
- **Maintenance:** a positive counter decreases by one and the answer increases
  by one. The body costs eight instructions; the guard costs three.
- **Exit:** the counter is zero, so the answer is `n`.

Initialization costs two, giving the proved bound `11*n + 5`.

`VC` performs substitutions and charges expressions, loads, stores, and tests.
At each loop it asks for a store-and-credit invariant, initialization, and a
maintenance/exit proof. `VC.sound` proves these conditions establish total
correctness and the budget for **every** source command. `VC.contract` turns
these VCs into a reusable functional/cost contract. `LoopVC.sound` is an
alternative rule for the familiar invariant-plus-potential presentation.

For modular proofs, `Triple.seq` composes time-credit contracts.
`Contract.ram` transfers a source contract to the generated RAM instructions.
There is no need to reopen compiler internals in a client proof.

## Extend BFS without changing the language

This is real syntax from `Demo.lean`:

```lean
def recordDiscovery (distance parent : ArrayRef) (u v : Var .word) : Cmd := program {
  distance[v] := distance[u] + 1;
  parent[v] := u;
}
```

`recordDiscovery_spec` proves the two mathematical heap updates and a
15-operation bound, for arbitrary runtime array bases. Its exact state equation
also describes every untouched variable and memory cell. To retain both values,
the client proves the two output cells are distinct; array bounds are obligations
of the surrounding array representation. `discoverAndEnqueue` shows this block
composed with a visited test and `QueueRef.enqueue` using the same public syntax.

The established BFS reachability and linear-time theorems remain attached to the
existing BFS implementation. The new discovery block is verified, but this change
does **not** claim a distance/shortest-path theorem or a port of the entire BFS
proof to the new CSR-based graph interface.

## Library contracts

Every operational contract below is proved against independent source execution
and therefore yields an actual RAM execution through `Contract.ram`.
`e.cost` is computed from expression syntax, not supplied by the programmer.

| Interface | Functional abstraction | RAM cost |
| --- | --- | --- |
| Array read | Read the indexed element of a represented list | `index.cost + 4` |
| Array write | `List.set`; one-cell update and frame | `index.cost + value.cost + 3` |
| Stack clear | Empty list; preserve heap | 2 |
| Stack push | Append one element | `value.cost + 8` |
| Stack pop | Return last element; retain prefix | 9 |
| Queue clear | Empty list; preserve heap | 4 |
| Queue enqueue | Append one element | `value.cost + 8` |
| Queue dequeue | Return head; retain tail | 9 |
| Stack/queue empty test | Equivalent to logical list being empty | 3 |
| Graph row begin | Read CSR starting offset | `vertex.cost + 4` |
| Graph row end | Start plus abstract row length | `vertex.cost + 6` |
| Graph neighbor | Corresponding abstract adjacency-list element | `cursor.cost + 4` |

`ArrayRef.set_spec` includes bounds and list refinement. `put_spec` is the
lower-level single-cell frame contract. `Segment.frame_write` preserves a
disjoint array segment. Stack and queue pop contracts require nonemptiness and
prevent output/cursor aliasing. Push contracts require available capacity.

Queues use append-only contiguous storage, suitable for BFS where each vertex is
enqueued once. Capacity bounds total enqueues since clearing; dequeuing does not
reclaim slots. There is no hidden resize or host-language list operation.

`GraphRef.Rep` represents adjacency lists with an offsets array and a targets
array. `BFS.Represents` connects those lists to the repository's labelled
undirected `Graph`. `neighbor_is_edge` proves each abstract neighbor is a graph
edge. `traversal_budget` supplies the reusable incidence-count argument for a
client that visits each row once with proved per-row and per-entry budgets:
`rowCost*n + entryCost*2*m`. It is an accounting lemma, not by itself a theorem
about executing an arbitrary traversal. Parallel edges are counted by labels.

## Trust and cost boundaries

- Runtime commands contain only first-order syntax. There is no arbitrary
  Lean state transformer, evaluator, or user-selected time charge in a command.
- Source `Store`, `Expr.eval`, and `Eval` are defined before the compiler and do
  not refer to compilation. The compiler theorem relates them to RAM `Exec`.
- Expression correctness includes temporary-register preservation. Later
  subexpressions cannot overwrite the values needed by earlier ones.
- RAM now has named user registers, indexed temporaries, and scoped saved registers. Each fixed finite
  compiled program mentions only finitely many. Register lookup remains one
  unit in this abstract model, irrespective of host string-lookup performance.
- Words remain unbounded naturals with unit-cost arithmetic and saturating
  subtraction. This is not bit complexity or a host-runtime claim.
- Input representation construction, result formatting, and Lean proof checking
  are outside the RAM cost. They cannot be used as uncharged algorithm steps.

## Files and checks

`Basic.lean`: syntax and independent semantics. `Compiler.lean`: generic
expression and command compilation theorems. `Verification.lean` and `VC.lean`:
contracts, time credits, loop reasoning, and VCG soundness. `Syntax.lean`:
compositional macros. `Interface.lean`: explicit runnable input/output.
`Library/Array.lean`, `Library/Sequences.lean`, and `Library/Graph.lean`: reusable
representations and operational contracts. [`LanguageExamples.lean`](../Algorithms/LanguageExamples.lean): client proofs.

[`Tests/Language.lean`](../Tests/Language.lean) runs compiled nested expressions at 51 inputs, the verified counter
at 51 inputs, nested scope restoration and procedure calls at 51 inputs, and
verified queue/stack operations. It also checks rejected
word/address mixing, zero-credit assignment, and illegal cursor aliasing. The
full repository build continues to check the complete typed insertion-sort and BFS
correctness, cost, and runtime regressions.
