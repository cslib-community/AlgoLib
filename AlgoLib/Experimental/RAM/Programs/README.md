# Algorithm authors: start here

Only two files define the canonical algorithms:

- [Sorting.lean](Sorting.lean): `Programs.Sorting.main`, a sorted permutation and quadratic RAM bound.
- [Connectivity.lean](Connectivity.lean): `Programs.Connectivity.main`, exact reachability, connectivity iff the output is the whole vertex set, and a linear RAM bound.

[Examples.lean](Examples.lean) runs them and demonstrates theorem application; it does not contain another implementation.

Each algorithm file follows the same order. `Claim` states the destination before the proof. The `ram_method` declaration gives named input/output parameters and contracts. The invariant and potential express the paper argument. `loopProof` solves preservation, payment, and exit; `verification` discharges the method VCs. `certified` packages the checked declaration; `run` and `main` expose execution and the theorem. Everything below the library contracts is automatic for the algorithm author.

In Lean, a theorem using a particular executable must come after its definition. `Claim` lets you read the full target statement first; the theorem `main` later proves exactly that claim. This avoids an unproved forward declaration.

Open the file next to the [authoring guide](../Authoring/README.md). Put the editor cursor after `paper_steps` to inspect the logical obligations. Supply a mathematical lemma if one is missing; changing a compiler proof should never be a step in this workflow.
