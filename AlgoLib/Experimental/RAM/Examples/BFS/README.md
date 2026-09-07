# BFS: connectivity with interchangeable queues

| Read in this order | What it contains |
| --- | --- |
| [Inputs.lean](Inputs.lean) | Small concrete graphs for running the algorithm |
| [Program.lean](Program.lean) | Paper-style BFS with queue operations, adjacency scans, invariants and loop allowances |
| [Obligations.lean](Obligations.lean) | Generated source-level obligation API |
| [Facts.lean](Facts.lean) | Mathematical reachability and counting lemmas used by the proof |
| [Proofs.lean](Proofs.lean) | Named proof blocks and the completed reusable procedure, independent of queue layout |
| [Execution.lean](Execution.lean) | `search`, `search_correct`, `connected`, `linear`, and `same_result` |
| [Storage.lean](Storage.lean) | Input/output storage assembly through layout contracts |
| [QueueBackend.lean](QueueBackend.lean) | Select the certified FIFO implementation |

The result is exactly the vertices reachable from a valid source. Consequently,
the graph is connected iff the returned set contains the whole vertex set.
The RAM theorem gives a linear bound in vertices plus edges under the documented
adjacency-list encoding and unit-cost integer model.

Both queue selections use the same `bfsProcedure` and mathematical proof:
[ring queue](../../Implementations/DataStructures/QueueRing.lean) and
[two-stack queue](../../Implementations/DataStructures/QueueStacksImplementation.lean).
Only representation and private accounting certificates change. `same_result`
connects their observed outputs; actual instruction counts can differ.

```lean
import AlgoLib.Experimental.RAM.Examples
open AlgoLib.Experimental.RAM.Examples.BFS
#eval (search .circular AlgoLib.Experimental.RAM.Examples.BFS.Inputs.diamond ⟨0, by decide⟩).value
#check search
#check search_correct
#check connected
#check linear
#check same_result
```

See [the runnable BFS tutorial](TUTORIAL.md) for concrete graph inputs and outputs.
No user-supplied execution fuel or queue-address proof is required.
