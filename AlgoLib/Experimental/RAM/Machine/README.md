# Machine: the supported Int-RAM target

**Preferred public import:** `AlgoLib.Experimental.RAM.Machine`.
See [public names and stability](../docs/PUBLIC-API.md); narrower module links below explain internals.

[Integer/Machine.lean](Integer/Machine.lean) defines integer instructions and execution.
[Integer/Runner.lean](Integer/Runner.lean) supplies executable running with termination
evidence; [Integer/Frame.lean](Integer/Frame.lean) proves framing properties.
[Integer/NatEmbedding.lean](../Historical/Adapters/NatEmbedding.lean) retains verified migration
results from the historical natural machine. See [the integer model guide](Integer/README.md).

Registers and heap cells contain unbounded integers. Instructions have the stated
unit-cost semantics. Addresses remain natural indices with checked conversions.
Source Nat subtraction saturates; source Int subtraction is ordinary subtraction.

The compiler theorem is about this model, not a word-size bound or bit complexity.
Machine steps are physical accounting; source logical credits belong to Language
and Verification. The retired natural reference machine is explicitly under
[Historical/NatMachine](../Historical/NatMachine/).

<!-- BEGIN GENERATED MODULE INDEX -->

## Module index (generated)

Status and ownership come from `docs/modules.json`; summaries come from module docstrings.

**Preferred import:** `AlgoLib.Experimental.RAM.Machine`.

| Module | Status | Responsibility |
| --- | --- | --- |
| [Machine](../Machine.lean) | public | Machine: supported public entry point |
| [Integer/Frame.lean](Integer/Frame.lean) | internal | Integer RAM register framing |
| [Integer/Machine.lean](Integer/Machine.lean) | internal | Integer-valued RAM |
| [Integer/Runner.lean](Integer/Runner.lean) | internal | Fuel-free RAM runner |
| [Output.lean](Output.lean) | internal | Shared observed output values |
| [Registers.lean](Registers.lean) | internal | Register identifiers |

<!-- END GENERATED MODULE INDEX -->

Shared [register names](Registers.lean) and [output values](Output.lean) are independent
of historical instructions. The old-to-new machine embedding is a historical adapter,
not a dependency of this supported machine interface.
