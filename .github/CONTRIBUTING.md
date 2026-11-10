We mostly follow [Mathlib's contribution guide](https://leanprover-community.github.io/contribute/index.html).

On top of Mathlib's contribution guidelines, we also enforce the following:
* Prerequisites that belong to existing Mathlib files should be put in the `AlgoLib.Mathlib` folder.
  Precisely, declarations that belong in an existing Mathlib file `Mathlib.X` will be located in `AlgoLib.Mathlib.X`.
  We aim to preserve the property that `AlgoLib.Mathlib.X` only imports `Mathlib.X` and files of the form `AlgoLib.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`.
  Prerequisites that do not belong in any existing Mathlib file should be located outside the `AlgoLib.Mathlib` folder.

## Lean version updates

The `Upgrade stable Lean` workflow checks daily for the latest stable Lean 4
release. It waits until Mathlib and CSLib both have matching version tags whose
`lean-toolchain` files agree. Missing tags or different toolchains are retried
on later runs. Release candidates and nightlies are excluded.

Once ready, it updates the toolchain, both dependency pins and current README
version examples, regenerates the manifest, and runs the build, public-import,
declaration-checker and style checks. If all pass, it opens an upgrade PR and
starts CI on that branch. It never merges automatically. If the attempt fails,
it opens an issue naming the failed stage and linking to the logs. If `main`
advances during validation, the attempt also stops so an untested base is not
silently included in the PR.

An existing upgrade PR is left untouched, including any maintainer fixes. A
closed PR is not recreated. An existing upgrade issue stops daily attempts for
that version; use **Actions → Upgrade stable Lean → Run workflow → Retry an
upgrade with an existing issue** to try again. A failed retry adds a comment to
the same issue; a successful retry opens a PR that closes it when merged.

For breaking changes, create a manual upgrade branch from current `main` and
link the issue in your PR. Update `lean-toolchain` and the Mathlib and CSLib
requirements in `lakefile.toml`, then regenerate the manifest and check the
library:

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
**Lint style**, with branches up to date before merging.

Under **Settings → Actions → General → Workflow permissions**, enable **Allow
GitHub Actions to create and approve pull requests**. The updater explicitly
dispatches CI on the published branch using the built-in token, so an extra
bot token is not required. Publication or CI-dispatch failures are also reported
in an issue; check whether a PR was already created before retrying.

After a push to `main` passes both jobs, CI creates the stable Lean version tag
and a GitHub release at that exact tested commit. Release dates provide the
timestamp. Existing tags, including tags made before this workflow, are left
unchanged. Each Lean version gets one automatic tag; use a tested commit hash
for later fixes on the same Lean version. Keeping a tag available does not
automatically backport future fixes to it. Publishing uses the built-in
`GITHUB_TOKEN`; the updater uses it to publish PRs, report failures and dispatch
CI. No extra secret or dependency-update service is needed.
