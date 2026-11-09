We mostly follow [Mathlib's contribution guide](https://leanprover-community.github.io/contribute/index.html).

On top of Mathlib's contribution guidelines, we also enforce the following:
* Prerequisites that belong to existing Mathlib files should be put in the `AlgoLib.Mathlib` folder.
  Precisely, declarations that belong in an existing Mathlib file `Mathlib.X` will be located in `AlgoLib.Mathlib.X`.
  We aim to preserve the property that `AlgoLib.Mathlib.X` only imports `Mathlib.X` and files of the form `AlgoLib.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`.
  Prerequisites that do not belong in any existing Mathlib file should be located outside the `AlgoLib.Mathlib` folder.

## Lean version updates

Upgrades are manual PRs; there is no scheduled dependency updater. Wait for
compatible stable Lean, Mathlib and CSLib versions, then create an upgrade branch
from the current `main`.

Update `lean-toolchain` and the Mathlib and CSLib requirements in `lakefile.toml`,
then regenerate the manifest and check the library:

```sh
lake update
lake exe cache get
lake build
lake env lean tests/Import.lean
lake build checkdecls
```

Fix any breaking changes before merging. Commit `lake-manifest.json` with the
toolchain and dependency changes, and update the README's version examples and
migration notes. Review changes to the public API even when the build passes.
Configure branch protection on `main` to require **Build project** and
**Lint style** before merging.

After a push to `main` passes both jobs, CI creates the stable Lean version tag
and a GitHub release at that exact tested commit. Release dates provide the
timestamp. Existing tags, including tags made before this workflow, are left
unchanged. Each Lean version gets one automatic tag; use a tested commit hash
for later fixes on the same Lean version. Keeping a tag available does not
automatically backport future fixes to it. Publishing uses the built-in
`GITHUB_TOKEN`; no extra secret or dependency-update service is needed.
