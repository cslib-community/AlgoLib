# Physical data-structure contracts

These are library-maintainer APIs. Public algorithm operations are exposed through [Library](../../Library/README.md).

| Module | Purpose and principal boundary |
|---|---|
| [Framing.lean](Framing.lean) | Read/write footprints, disjoint framing, sequential composition, and preservation of cost contracts |
| [Array.lean](Array.lean) | Typed array references and cellwise segments; read/write and frame contracts |
| [Sequences.lean](Sequences.lean) | Stack and FIFO operations with reusable logical contents and cost contracts |
| [Graph.lean](Graph.lean) | Typed adjacency/visited interfaces and graph-related operation contracts |
| [GraphMemory.lean](GraphMemory.lean) | Linked adjacency layout and its relation to a logical graph representation |
| [GraphInput.lean](GraphInput.lean) | Builds a certified adjacency input from finite labelled edge data |

A new representation must prove its own read footprint and operation write bounds. Disjointness then preserves unrelated assertions through the generic frame rule. This is an explicit reusable footprint discipline, not an automatic general ownership inference engine.
