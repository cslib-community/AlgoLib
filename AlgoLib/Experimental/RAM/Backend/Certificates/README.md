# Instruction-level implementation certificates

These proofs are retained as implementation evidence, not as separate student algorithms.

| File | Role |
|---|---|
| [LoopVC.lean](LoopVC.lean) | Machine-level loop invariant, potential, and total-correctness rule |
| [SortingSpec.lean](SortingSpec.lean) | List lemmas supporting insertion correctness |
| [InsertionSort.lean](InsertionSort.lean) | Instruction-level insertion and sorting certificates, including frame and cost facts |
| [BFS.lean](BFS.lean) | Discovery/row/frontier mathematics together with certified machine operations |

The adapters reuse local certificates from these files. A public author uses the certified insertion or row procedure, and proves the outer algorithm in `Programs`. Retaining the old certificate code avoids reproving physical implementations merely to reorganize the authoring API.
