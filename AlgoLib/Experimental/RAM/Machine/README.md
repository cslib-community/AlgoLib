# The RAM execution foundation

The supported owned `ram method` frontend executes on **Int-RAM** by default.
Registers and heap cells contain unbounded integers; addresses and instruction
counts remain natural numbers. This unit-cost count is not a bit-complexity or
wall-clock theorem. Algorithm users work through the generated proof API without
supplying machine termination, register-frame, or compiler proofs.

| File | Role |
|---|---|
| [Integer/Machine.lean](Integer/Machine.lean) | Integer instructions, checked addresses, and counted execution |
| [Integer/Runner.lean](Integer/Runner.lean) | Fuel-free integer execution with a checked termination certificate |
| [Integer/NatEmbedding.lean](Integer/NatEmbedding.lean) | Preservation of Nat-IR behavior and derived lowering costs |
| [Registers.lean](Registers.lean) | Shared register identifiers, independent of the value type |
| [Machine.lean](Machine.lean) | Temporary Nat compiler intermediate and historical regression semantics |
| [Runner.lean](Runner.lean) | Nat reference runner retained during migration |
| [Output.lean](Output.lean) | Earlier Nat register/bitmap descriptors and framing evidence |

See [the migration guide](Integer/README.md) for default assembly, guarantees, and
remaining work. Signed source syntax and removal of the Nat intermediate are pending.
