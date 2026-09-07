# Native integer compiler

This is the direct compiler used by the default owned method runner. It stores
native signed values in one register or heap cell and never invokes the Nat-RAM
instruction compiler. It is an implementation interface, not a second algorithm
frontend.

| Module | Responsibility |
| --- | --- |
| `Basic` | Typed implementation expressions, commands, and independent counted semantics |
| `Expressions` | Expression lowering, exact instruction cost, and temporary framing |
| `Compiler` | Branches, loops, locals, and whole-command semantic preservation |
| `Execution` | Fuel-free executable and result/cost transport |
| `Natural` | Compatibility translation for natural implementation contracts |
| `Ownership` | Native instance of the shared ownership laws |
| [Native storage](../../Implementations/Native/README.md) and [assembly](../Assembly/Native/README.md) | Source adapters: linking, expression certificates, and scalar representations |

`Native.Eval.compile` proves that every independent terminating source execution
has a target execution with the same observed store and exact instruction count.
`Native.run_eq` connects this theorem to the actual executable runner. Native
expressions distinguish Nat words, addresses, and Int values: Nat subtraction
saturates, while Int subtraction can produce negatives. Natural reads normalize
at zero; signed reads are direct. Bounds and allocation are ownership obligations.

The compiler's instruction counts are separate from algorithmic logical credits.
The `Natural.preserves` theorem retains the existing factor-two budget transport
for legacy implementation contracts. It permits replacing their compiler without
changing algorithm proofs or logical charges.

## Execution boundary

Standard owned scalar/array assembly emits native typed commands directly.
For the older natural-valued implementation interface only,
`Checked.Language.Method.integerCode` uses `Natural.command` followed by the same
native compiler. Its procedure-linking theorem uses that route too. Signed
frontend arithmetic and single-cell storage do not pass through the natural IR;
their certificates establish native semantics and exact instruction costs.

Standard scalar and array assembly now uses native source-expression contracts,
single-cell storage, and native private locals. Multiple signed arrays also use the
shared native ownership interfaces. Natural-valued library views reuse their existing source contracts through
`Natural.preserves`; their generated instructions are native integer instructions.
The old Nat executable wrappers have been retired, and the ordinary-Velvet
translation fixtures also use the integer target.

## Shared composition and source-credit preservation

`Implementations/Contracts/Ownership`, `Implementations/Contracts/ResourceRefinement`, `Implementations/Contracts/Focus`,
`Implementations/Contracts/LocalRefinement`, and `Implementations/Contracts/ResidentInputs` now contain
the single reusable implementation of separation, private potential, structural
linking, and source-path framing. The legacy Composition interfaces are aliases
to these laws. Native contracts instantiate the same interfaces with integer cells.

The source credit contract gives negation no additional allowance and gives some
truncated expressions constant allowance. Native lowering preserves these choices
using alternative expression code views for a value, its negation, and its two
truncated natural parts. Only the requested view executes. These are syntax trees,
not two-cell value storage. Double negation swaps views twice, and truncating the
negative of a natural expression emits constant zero.

`Tests/NativeSourceFrontend` reuses an ordinary `ram method` and its generated proof
with native signed storage. Subtracting five executes in four instructions, while
an unrelated negative heap cell remains unchanged. It also checks that double
negation and cheap truncation retain their original source allowances. Standard scalar/array assembly, array operations, and private local initialization
now use this native path automatically. `Tests/NativeArrays` inspects the raw signed
cells, and the unchanged two-array source proof runs with separate native layouts.
Private library models may still use natural values and custom encodings. Those
models do not select another machine backend. New signed scalar and array
implementations use the native one-cell interfaces.

The boundary regression rejects historical target references in public authoring,
program, and prototype execution witnesses. It also checks the transitive import
graph: no native compiler module imports the old Nat compiler or runner. The old
instruction semantics remain available only as evidence for historical source
refinements and reference tests.
