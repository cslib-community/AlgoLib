We mostly follow [Mathlib's contribution guide](https://leanprover-community.github.io/contribute/index.html).

On top of Mathlib's contribution guidelines, we also enforce the following:
* Prerequisites that belong to existing Mathlib files should be put in the `AlgoLib.Mathlib` folder.
  Precisely, declarations that belong in an existing Mathlib file `Mathlib.X` will be located in `AlgoLib.Mathlib.X`.
  We aim to preserve the property that `AlgoLib.Mathlib.X` only imports `Mathlib.X` and files of the form `AlgoLib.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`.
  Prerequisites that do not belong in any existing Mathlib file should be located outside the `AlgoLib.Mathlib` folder.

## Lean version updates

The `Check stable Lean releases` workflow checks daily for the latest stable
Lean 4 release. It waits until Mathlib and CSLib both have matching version tags
whose `lean-toolchain` files agree with that release, then opens one upgrade
issue. Missing tags or different toolchains are retried on later runs. Release
candidates and nightlies are excluded. A closed upgrade issue is not recreated.
You can also start the check from the Actions tab.

Matching releases are a readiness signal; the build still determines whether
AlgoLib works with them. Upgrade edits and merging remain manual. From the
upgrade issue, create a branch from current `main` and link the issue in your PR.

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
`GITHUB_TOKEN`; the readiness checker uses the same token with issue-writing
permission. No extra secret or dependency-update service is needed. The checker
only reports readiness: it does not change dependencies or open upgrade PRs.
