# Graph mathematics and representation specifications

[Graph.lean](Graph.lean) defines reachability and connectivity using the repository's `Graph`, then states adjacency-list representation and BFS frontier invariants. Vertices are natural-number identifiers in a finite range; labelled undirected edges may include loops and parallel edges.

[GraphBridge.lean](GraphBridge.lean) connects this reachability/connectedness convention to existing graph APIs. These are mathematical specifications, independent of program memory layouts. The physical layout is certified under `Backend/Memory`.

For a valid source, BFS always returns its reachable component. The graph is connected exactly when that component equals the whole vertex set. The complete executable theorem is `Programs.Connectivity.main`.
