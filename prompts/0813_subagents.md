You have access to several subagents. Use them primarily for parallel evidence gathering rather than having several agents independently design the whole architecture.

A recommended decomposition is:

Mathlib audit agent: inspect the exact Mathlib revision pinned by this project. Map the relevant foundational graph modules and APIs, identify useful conventions and abstractions, and distinguish reusable mathematical API from representation-specific machinery. Do not design the final GraphLib architecture.
Current GraphLib audit agent: inspect the existing GraphLib implementation and actual downstream usage. Identify validated abstractions, provisional code, legacy artifacts, missing foundational APIs exposed by downstream helpers, and migration constraints. Do not design the final architecture independently.
TCS requirements/stress-test agent: reason from representative graph-algorithm formalizations—BFS, SCC, deletion, contraction, path reversal, vertex splitting, weighted shortest paths, MST, flow/capacity, etc.—and identify what properties a good foundational graph API should have. Use pseudo-signatures where useful, but do not implement.
Mathlib-forward/interoperability agent: inspect current Mathlib master, relevant ongoing GraphLike/incidence/walk work, and the interoperability concerns around CSLib graph development. Clearly distinguish merged API from experimental proposals. Identify future compatibility risks and gratuitous divergences to avoid.

The main agent should perform the final synthesis itself. Do not delegate the final architecture wholesale to a subagent and merely reproduce its answer.

You may adjust this decomposition if investigation reveals a clearly better split, but preserve the principle that the first round should maximize orthogonal evidence gathering rather than redundant independent architecture proposals.

Ask each subagent for a bounded, structured report rather than a long essay. Their reports should emphasize evidence, concrete declarations/files, design lessons, and unresolved questions for synthesis.