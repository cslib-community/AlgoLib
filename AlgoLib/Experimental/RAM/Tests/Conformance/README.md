# Frontend conformance

`Generated.lean` contains nine ordinary source programs and 765 comparisons against
an independent reference evaluator. The Cartesian product varies arithmetic,
branch behavior, and loop nesting. Inputs include empty arrays, singletons, zeros,
repeated values, and both sides of the comparison boundary. Procedure calls, mutable
locals, indexed reads/writes, and sequential writes occur in the generated programs.

The generator prints source text. The real parser, elaborator, certificate generator,
RAM compiler, and RAM runner must process it. Expected arrays are computed by
`reference.py`, which imports none of those implementations. Both paths share only
the test program descriptions; they do not share evaluation or lowering code.

Run from the repository root:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 AlgoLib/Experimental/RAM/Tests/Conformance/generate.py --check
lake build AlgoLib.Experimental.RAM.Tests.Conformance.Generated
lake build AlgoLib.Experimental.RAM.Tests.Conformance.Rejections
```

Omit `--check` to regenerate fixtures after intentionally changing the corpus.
Normal `lake build` executes the checked-in comparisons. The structural checker also
checks regeneration, so changing the oracle without updating fixtures fails validation.
No random seed, network service, SMT oracle, or third-party testing package is needed.

The reference interpreter has a finite test-execution limit and checked indexing.
Its step counter is **not** a RAM cost model. The suite compares output arrays and
checks each actual RAM count against the compiler's certified upper bound. Scalar
results are made observable by writing them into the output array. The generated
functional postcondition is deliberately `True`: output correctness in this suite
comes from differential testing, independently of source proof annotations.

This is bounded testing, not a formal theorem relating raw syntax to semantics.
The oracle and printer can have bugs; handwritten oracle tests cover saturating
subtraction, call activation, sequential stores, invalid indices, scope errors, and
nontermination limits. Existing verified examples, multiple-array/owned-call tests,
and kernel axiom checks provide complementary coverage.

The corpus found a missing parenthesis case in comparison elaboration. The fix
normalizes comparison syntax while preserving the original guard-slot location.
Shadowing is explicitly rejected until the frontend has lexical binding identities;
it must not silently reuse the first resource with the same textual name.

The strict execution checks also caught eager evaluation of a discarded input to a
uniform procedure allowance. The frontend now emits `UniformCredits.amount` directly
in that case. Dependent allowances are unchanged and remain subject to their VCs.
The array encoder additionally uses a total defaulting heap accessor. `#guard_msgs`
requires silent execution, so host bounds diagnostics cannot count as a pass even
when Lean returns a default value and all output comparisons happen to match.

## Default integer target

The generated methods now execute through the shared Int-RAM runner. The reference
evaluator still implements Nat source subtraction, so underflow tests check that
integer lowering preserves saturation. Inferred bounds include lowering overhead.
`Tests/IntegerFrontend.lean` additionally pins an 11-instruction source example
(10 Nat-IR instructions plus one clamp), detecting accidental fallback to Nat-RAM.
