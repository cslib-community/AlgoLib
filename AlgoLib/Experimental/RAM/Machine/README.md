# The RAM execution foundation

| File | Meaning |
|---|---|
| [Machine.lean](Machine.lean) | Natural-number memory/registers, primitive instructions, structured RAM code, costed execution |
| [Runner.lean](Runner.lean) | Executable small-step runner with a termination certificate instead of user-supplied fuel |
| [Output.lean](Output.lean) | Restricted register/bitmap output descriptors, output observations, and register framing |

This is the unit-cost natural-number RAM model. Its instruction count is not a bit-complexity or wall-clock theorem. Algorithm users work through `Programs` and the certified public contracts; they do not supply machine termination, register-frame, or compiler proofs.

## Int-RAM migration

The [integer machine foundation](Integer/README.md) supplies signed execution and a
generic preservation theorem for current Nat code. Default frontend assembly has
not switched yet; this is the first step toward replacing the Nat backend.
