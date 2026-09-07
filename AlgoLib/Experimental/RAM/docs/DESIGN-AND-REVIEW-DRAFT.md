# From Paper Proofs to RAM Bounds: Compositional Refinement and Its Review Obligations

**DRAFT — design exposition and reviewer guide**

**Artifact:** AlgoLib, revision `6088e3bae659c671aa8eb9363339522e9f3de1f1`

**Status:** technical exposition, not a submission-ready novelty claim or independent audit approval.

## Abstract

A verified algorithm library should let an author reason about mathematical values, invariants, and logical work allowances while implementations discharge obligations about memory layout and machine execution. AlgoLib’s experimental RAM stack approaches this goal through a typed client language, contract-directed verification conditions, ownership-indexed implementations, and resource-aware refinement to a structured integer RAM. Its organizing law is compositional: implementation steps and remaining private potential are bounded by the client’s logical allowance and initial private potential. The same client proof can therefore support different certified data structures. We explain this design through breadth-first search and identify the small set of semantic connections that merit detailed human review. Lean checks the formal implications between definitions; it does not establish that a specification expresses the intended problem, that a surface program is interpreted as its author expects, or that a chosen cost model matches the intended complexity claim. We state these alignment obligations explicitly and distinguish them from the stack’s checked theorems.

## 1. Problem and contribution

A paper proof of breadth-first search (BFS) says that discovered vertices are reachable, that the frontier eventually becomes empty, and that each vertex and adjacency entry contributes bounded work. It does not mention register assignments, queue addresses, or compilation certificates. A usable formalization should preserve that division of responsibility.

The difficulty is not merely connecting a high-level program to a machine. Independently verified components must compose without exposing either their representations or their amortization arguments. A circular queue and a two-stack queue have different internal states and payment strategies. If changing between them requires rewriting the BFS invariant or its preservation proof, the abstraction has failed its intended client.

The stack therefore separates four responsibilities:

| Layer | Exposed information |
|---|---|
| Algorithm | Typed values, visible control flow, mathematical invariants and counting arguments |
| Abstract library | Preconditions, functional effects and logical resource contracts |
| Implementation | Private representation, potential and certified primitive code |
| Compiler and machine | Lowering, observations, execution and counted operations |

The contribution examined here is this integration and its reviewable assurance structure. We do not claim a new general separation logic, universal compilation of ordinary Velvet, or demonstrated usability across a broad algorithm curriculum. Ownership with amortized resources and refinement-based implementation substitution have substantial prior foundations; Section 7 attributes them.

## 2. A single client and two connected interpretations

### 2.1 Logical programs and contracts

A client has type `Program A B`, where `A` and `B` describe mathematical inputs and outputs. Its constructors include operations, sequencing, framing, branches, loops and calls to finite bodies. An operation supplies a precondition, a mathematical effect and a natural-number logical charge. These effects may be ordinary Lean functions, but they are specifications: a machine implementation must separately be supplied and verified.

Write `Run(p, a, k, b)` for a finite logical execution consuming `k` credits. Sequencing adds charges; a branch or loop guard consumes one logical credit. A procedure packages a body, a precondition, a postcondition and a credit allowance, together with a proof that valid inputs admit a finite execution satisfying the postcondition within that allowance.

The surface interface adds mutable variables, indexed array operations and annotated loops. Authors supply invariants and iteration or remaining-work bounds. Generated obligations are frozen as Lean propositions and discharged in separate proof blocks. The metadata is an authoring interface; the proof evidence is an assembly declaration whose conclusion is the algorithm’s actual obligation proposition.

**Theorem 1 — Annotated verification soundness (schematic).** If `plan.vc Q a B` holds for a plan indexed by `p`, then there exist `k`, `b` and `ℓ` such that

\[
\operatorname{Run}(p,a,k,b)\;\land\;k+\ell\le B\;\land\;Q(b,\ell).
\]

This is `Plan.sound`; `Algorithm.certify` specializes the result to a procedure contract. The residual parameter matters: the proof may conservatively discard unused allowance rather than promise exact credit consumption. Loop soundness requires the supplied decrease and accounting conditions. It does not infer algorithmic invariants automatically.

### 2.2 Loom and implementation semantics

The same `Run` relation defines a finite costed computation interpreted through Loom. Identity and sequencing commute with that interpretation; `Algorithm.loom_correct` connects discharged obligations to the corresponding Loom WP. This is reasoning about the shared client, not a second independently written algorithm.

The implementation interpretation is separately indexed by representations and verified primitive implementations. Thus a Loom WP theorem alone is not a machine-cost theorem. The implementation certificates and compiler connection supply the additional premises. The supported client is deterministic and first-order with finite procedure bodies; importing the fuller upstream framework does not extend this RAM theorem to all of its effects.

## 3. Ownership and the resource-refinement law

Let `P(a,r,s,φ)` mean that observable store `s`, on footprint `r`, represents mathematical value `a` with private potential `φ`. Potentials are natural numbers. Representations satisfy locality: agreement on their footprint suffices to preserve the represented assertion and potential.

Separating composition splits both footprint and potential:

\[
(P*Q)((a,b),r,s,\phi)
\]

holds when `r` is a disjoint union of component footprints and `φ` is the sum of their potentials, with the corresponding representations holding. This prevents overlapping writable ownership from being silently treated as independent. Locality and final-state write framing then preserve an untouched component and its savings.

**Theorem 2 — Supported implementation refinement (schematic).** A `Supported` certificate for `p`, at calibration rate `α`, reconstructs code `c` such that

\[
\operatorname{Run}(p,a,k,b)\land P(a,r,s,\phi)
\]

implies the existence of `t`, `T` and `φ′` satisfying

\[
\operatorname{Eval}(c,s,T,t)\land Q(b,r,t,\phi')
\land\operatorname{Writes}(r,s,t)
\land T+\phi'\le\alpha k+\phi.
\]

The code is part of the reconstructed certificate; it is not chosen afresh for each execution by the theorem. `Primitive.correct` requires this property for every valid represented input state. Guard implementations additionally prove agreement with the logical test and a sufficient cost calibration. `Supported.compile` combines those leaf certificates.

The crucial composition argument is short. If the first component establishes

\[
T_1+\phi_1\le\alpha k_1+\phi_0
\]

and the second establishes

\[
T_2+\phi_2\le\alpha k_2+\phi_1,
\]

then the intermediate potential cancels. The client receives a bound on the composed computation without knowing what `φ₁` measures. Framing carries a disjoint component’s potential unchanged. Different certified rates can be reconciled using their maximum. Calls use the public functional and credit contract; they do not require the caller to reproduce the callee’s payment argument.

This law does not make initial potential free. Any final bound must include or otherwise justify it. Likewise, abstract logical charges do not establish machine complexity by themselves: the implementation inequality is essential.

## 4. From refinement to an executable theorem

Native typed-command compilation proves a forward simulation to `Integer.Exec` with the same observation and counted command cost. The machine has atomic integer instructions and structured control. Its runner agrees with terminating formal execution; a generated termination certificate removes the need for user-supplied runtime fuel.

**Theorem 3 — Client linking (schematic).** Given source correctness within budget `B`, a supported implementation, and an initial representation with potential `φ`, the compiled machine has a terminating execution producing a represented output satisfying the source postcondition, preserving unowned observable locations, and obeying

\[
T+\phi'\le\alpha B+\phi.
\]

`Native.client_linking` states this connection explicitly with `Integer.Exec`. Encoders establish input representations and decoders recover mathematical outputs. `runEncoded_correct` connects the function users call to its procedure contract and exposes the conservative upper bound `2 × (α × credits(a) + saved(a))`.

Three qualifications are essential. First, framing concerns the observable user store and heap, not every raw scratch register. Second, this compilation theorem is a forward simulation from terminating executions, not a universal equivalence including divergence. Third, the reported counter excludes host input encoding and output decoding. It measures the resident-input RAM computation, not the wall-clock cost of invoking the Lean wrapper.

## 5. A running example: BFS with interchangeable queues

The following is explanatory pseudocode, not a copy-paste frontend declaration:

```text
procedure bfs(G, s) returns S
    require s is a vertex of G
    visited := all false
    Q := empty
    visited[s] := true
    enqueue(Q, s)
    while Q is nonempty
        invariant discovered vertices are reachable
        invariant Q contains the discovered, unprocessed vertices
        work allowance: remaining vertices and adjacency entries
        u := dequeue(Q)
        for v in adjacency[u]
            if not visited[v]
                visited[v] := true
                enqueue(Q, v)
    return marked vertices
```

The actual source contains explicit visited initialization, queue calls and nested neighbor scanning. The queue abstraction is a list in FIFO order. Enqueue requires spare capacity; dequeue requires a nonempty queue. Implementations may realize this list as a ring or as two stacks. The two-stack implementation keeps its transfer potential private. In the BFS assembly, empty initial queue storage has zero saved potential, established through its input contract.

The graph specification uses the repository’s labelled undirected graph. A representation certificate connects adjacency membership to edges and bounds the number of stored adjacency entries by twice the labelled edge count. This counting fact is proved for concrete edge inputs; it is not automatic for an arbitrary neighbor function.

The public results establish exact reachability, connectivity iff all vertices are marked, and

\[
T\le4896(|V|+|E|).
\]

A valid source excludes the empty graph. The result is a reachable vertex set, not a shortest-path tree or distance map. `same_result` proves equality of the circular-queue and two-stack results through the unchanged algorithm specification. A separate relocated-layout regression changes private storage without a new client or special assembly proof.

Insertion sort provides a second witness: its public theorem accepts every `List Nat` and returns a pairwise ordered permutation. The generated bound normalizes to `1824n² + 768n + 1296`. These conservative constants are established upper bounds; no optimality or matching lower-bound claim is intended.

## 6. Human review: alignment beyond kernel checking

Lean validates implications between the chosen definitions. Some alignment questions can themselves be formalized, but they require additional specifications and theorems; they do not follow merely because the current development compiles. Others concern external intent or empirical usability.

| Reviewer statement | What to inspect | What existing proofs do not decide |
|---|---|---|
| **A1. The result means the intended algorithmic property.** | Sorted permutation, graph reachability, labelled-edge counting and input quantifiers | Whether these are the problem and conventions the researcher intended |
| **A2. The generated program means the written source.** | Representative elaborations, source bindings, assignment order, calls and independent conformance tests | Universal raw-syntax semantics preservation; a valid theorem may concern an unintended translation |
| **A3. The cost model matches the claimed complexity model.** | Atomic operations, structured control, integer sizes and preprocessing boundaries | Bit complexity, word-RAM complexity or actual execution time |
| **A4. The theorem describes a uniform algorithm.** | Which parameters select code or layouts; input-dependent setup; BFS’s `code_independent` theorem | A general guarantee that preprocessing cannot encode answers or choose input-specific code |
| **A5. Contracts hide only legitimate implementation details.** | Locality, primitive contracts, initial savings and frame composition | Whether a restrictive precondition or expensive resident-input preparation weakens the intended abstraction |
| **A6. Verification reaches the executable users invoke.** | `runEncoded`, encoder/decoder laws, native simulation and runner theorem | Correctness of the host Lean compiler/runtime or excluded wrapper costs |
| **A7. The interface is maintainable and understandable.** | An independent implementation change and a new algorithm proof | Predictable proof effort, diagnostic quality or student usability across untested tasks |

A4 deserves particular attention. A theorem about each input can be logically valid while failing to express a single uniform algorithm in the intended complexity model. The reviewer should ask what is fixed before the input arrives and what work is performed outside the charged execution. A family indexed by capacity or input size may be appropriate, but that convention must be stated. The generic refinement theorem should not be mistaken for a universal restriction on all possible input preparation functions.

For an efficient review, begin with Theorem 3 and follow its premises backward through Theorem 2 and Theorem 1. Read definitions and exact types before proof scripts. Review one primitive and its representation in detail, then examine sequence, frame, loop and call composition. Use BFS substitution to test that the advertised boundary is actually exercised. Kernel-checked auxiliary arithmetic need not receive the same manual attention as the choice of machine semantics or postcondition.

The technical audit of the pinned revision reconstructed a 3,681-job build and inventoried 5,576 declarations in 106 RAM modules reachable from public roots. Their transitive axiom dependencies contained only `propext`, `Classical.choice` and `Quot.sound`. Bounded conformance covers 765 natural and 160 signed observations; it is testing evidence, not a universal frontend theorem. The oracle is separate from lowering, but its call case is a fixed increment operation. These results support review; they do not replace independent expert approval, which remains pending.

## 7. Relation to prior work and limits of the contribution

The stack reuses the actual Loom algebra/WP infrastructure and ports upstream Velvet components. The upstream work develops foundational verifiers through monad transformer algebras and includes a Dafny-style verifier; those foundations belong to its authors. The narrower `ram method` interface and RAM interpretation described here must not be conflated with all upstream capabilities. [Gladshtein et al., *Foundational Multi-Modal Program Verifiers*, POPL 2026](https://verse-lab.org/papers/loom-popl26.pdf).

Private amortization with ownership draws on resource reasoning in separation logic. The present potential inequality and framing discipline follow that established direction; this draft makes no priority claim for combining heap ownership and credits. [Atkey, *Amortised Resource Analysis with Separation Logic*, LMCS 2011](https://bentnib.org/amortised-sep-logic-journal.html).

Contract-based replacement of abstract operations by verified imperative data structures follows the refinement approach exemplified by Sepref. These are new Lean interfaces and proofs, not a port of Sepref or a claim to match its automation and library coverage. [Lammich, *Refinement Based Verification of Imperative Data Structures*, CPP 2016](https://www21.in.tum.de/~lammich/pub/cpp2016_impds.pdf).

The design’s current value is a shared program with connected correctness and resource interpretations, reusable implementation contracts, and a reconstructible executable theorem. Its research evaluation should establish how far these properties scale beyond the present examples, and its assurance argument should retain the explicit model and frontend boundaries above.

## Artifact reading route

The following links are pinned to the audited revision. The full theorem types and per-declaration axioms are recorded in the separate technical assurance package for this revision; that package is not included with this draft.

1. **Final connection:** [Native linking](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Compiler/Assembly/Native/Linking.lean), [encoded execution](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Compiler/Assembly/Native/Execution.lean).
2. **Composition core:** [resource refinement](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Implementations/Contracts/ResourceRefinement.lean), [ownership](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Implementations/Contracts/Ownership.lean).
3. **Source proof:** [annotated plans](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Verification/Plan.lean), [obligation reconstruction](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Verification/GeneratedObligations.lean), [Loom interpretation](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Verification/Loom.lean).
4. **Machine boundary:** [native compiler](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Compiler/Native/Compiler.lean), [machine definitions](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Machine/Integer/Machine.lean), [runner](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Machine/Integer/Runner.lean).
5. **Witnesses:** [BFS source](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Examples/BFS/Program.lean), [BFS executable theorems](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Examples/BFS/Execution.lean), [sorting executable theorems](https://github.com/cslib-community/AlgoLib/blob/6088e3b/AlgoLib/Experimental/RAM/Examples/InsertionSort/Execution.lean).
