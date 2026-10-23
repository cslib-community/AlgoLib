We mostly follow [Mathlib's contribution guide](https://leanprover-community.github.io/contribute/index.html).

On top of Mathlib's contribution guidelines, we also enforce the following:
* Prerequisites that belong to existing Mathlib files should be put in the `AlgoLib.Mathlib` folder.
  Precisely, declarations that belong in an existing Mathlib file `Mathlib.X` will be located in `AlgoLib.Mathlib.X`.
  We aim to preserve the property that `AlgoLib.Mathlib.X` only imports `Mathlib.X` and files of the form `AlgoLib.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`.
  Prerequisites that do not belong in any existing Mathlib file should be located outside the `AlgoLib.Mathlib` folder.

For the experimental RAM stack, start with the
[checked tutorial](../AlgoLib/Experimental/RAM/docs/GETTING-STARTED.md) and
[RAM contributor guide](../AlgoLib/Experimental/RAM/docs/CONTRIBUTING.md).
They explain the supported interfaces, module responsibilities, proof workflow,
and required validation.
The [architecture policy](../AlgoLib/Experimental/RAM/docs/ARCHITECTURE-POLICY.md)
and [review ownership](../AlgoLib/Experimental/RAM/docs/REVIEW-OWNERSHIP.md)
describe the checked module roles and reviewer routing for RAM changes.
