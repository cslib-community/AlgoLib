# Bind logical contracts to implementations

| Module | Logical contract implemented |
|---|---|
| [Insertion.lean](Insertion.lean) | `todo`/`sorted` state, array representation, insertion action and loop guard |
| [InsertionInput.lean](InsertionInput.lean) | Ordinary list input, prepared initial state, array output observation and preparation cost |
| [Search.lean](Search.lean) | Seen/frontier/row/processed state, BFS operations and guards |
| [SearchInput.lean](SearchInput.lean) | Certified graph/source input, clearing and seeding, returned visited bitmap |

These files own address calculations, register correspondence, instruction-certificate lifting, and implementation overhead. They reuse the memory and instruction certificates below them and construct the generic types in `Authoring`. The public `Library` modules re-export stable logical equations, so algorithm proofs do not unfold these implementations.
