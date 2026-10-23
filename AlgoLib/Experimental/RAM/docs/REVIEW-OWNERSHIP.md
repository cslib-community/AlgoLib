# RAM review ownership

Sorrachai (`@sorrachai`) is the sole primary reviewer for every RAM area. No
independent backup has been appointed: each `backup` list is explicitly empty.
The [reviewer registry](reviewers.json) records this assignment, the areas'
responsibilities, and their repository paths. Ownership identifies who coordinates
review; it is not evidence of theorem correctness or an additional trusted axiom.

## Areas and responsibilities

| Area ID | Responsibility | Primary | Backup |
| --- | --- | --- | --- |
| `frontend` | Source syntax, elaboration, expressions, and language contracts | `@sorrachai` | Unassigned |
| `verification` | VCs, generated obligations, proof commands, and Loom interpretation | `@sorrachai` | Unassigned |
| `library` | Mathematical models, procedure contracts, and library proofs | `@sorrachai` | Unassigned |
| `implementations` | Storage, ownership, data refinement, and operation certificates | `@sorrachai` | Unassigned |
| `compiler` | Lowering, linking, assembly, and compiler certificates | `@sorrachai` | Unassigned |
| `machine` | Integer RAM instructions, semantics, and runners | `@sorrachai` | Unassigned |
| `algorithms` | Maintained example algorithms, proofs, execution interfaces, and bounds | `@sorrachai` | Unassigned |
| `infrastructure` | Docs, metadata, tests, CI, policy, dependency pins, and vendored foundations | `@sorrachai` | Unassigned |
| `experiments` | Historical adapters and separately scoped research | `@sorrachai` | Unassigned |

Algorithm metadata uses `review_area: "algorithms"`. For a change spanning areas,
list the affected responsibilities in the pull request. A source proof change
and a compiler change can need different expertise even while their current
reviewer is the same person. The [contributor guide](CONTRIBUTING.md) describes
the validation expected for each kind of change.

## GitHub routing and approval requirements

The generated section of [`.github/CODEOWNERS`](../../../../.github/CODEOWNERS)
routes the RAM subtree to its area reviewers. A fallback covers new RAM files;
more specific layer rules follow it. Shared policy, CI, toolchain and dependency
files, the root import inventory, and both `vendor/loom/` and `vendor/velvet/`
route to infrastructure. Other repository source trees receive no new fallback.

GitHub uses the last matching ownership rule, and uses the CODEOWNERS file from
the pull request's base branch. Owners must have repository write access; listed
teams must also be visible. Non-draft pull requests request the matching owners
automatically once this configuration is on their base branch.
See [GitHub's CODEOWNERS documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-code-owners).

CODEOWNERS does not by itself require an approval to merge. Mandatory approvals
and required code-owner reviews are separate GitHub branch-protection or ruleset
settings; this repository change does not configure or assert those settings.
See [GitHub's branch-protection documentation](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches).

A pull request author cannot approve their own pull request. Consequently,
Sorrachai's own changes currently have no independent reviewer assigned by this
registry. An additional eligible reviewer must be appointed for independent
review; the empty backup fields do not supply that reviewer or imply approval.
If required code-owner approval is enabled, appoint another eligible code owner
before relying on it for those changes.
See [GitHub's review-approval documentation](https://docs.github.com/en/pull-requests/how-tos/review-pull-requests/approving-a-pull-request-with-required-reviews).

The `primary` and `backup` distinction expresses project roles. GitHub receives
both lists on the same ownership line and does not interpret them as an ordered
escalation policy or require approval from both lists. Empty backup lists remain
visible in the registry so the staffing gap is explicit.

## Change or validate an assignment

Update [reviewers.json](reviewers.json) and the assignment description above, then
regenerate and check locally:

```sh
python3 AlgoLib/Experimental/RAM/Tests/check_reviewers.py --write
python3 AlgoLib/Experimental/RAM/Tests/check_reviewers.py --check
python3 AlgoLib/Experimental/RAM/Tests/test_reviewers.py
```

With no flag, the checker performs the same read-only validation as `--check`.
`--write` changes only the managed section of CODEOWNERS. Keep unrelated ownership
rules before that section; the generator preserves them and any trailing comments.
Rules after the managed section are rejected because they could override RAM
routing. The generator never sends review requests or changes GitHub settings.

The registry has these fields:

| Field | Meaning |
| --- | --- |
| `schema_version` | Checked schema version, currently `1` |
| `fallback_area`, `fallback_paths` | Infrastructure fallback for the whole RAM subtree |
| `areas.<id>.primary` | Nonempty list of GitHub `@login` or `@org/team` identities |
| `areas.<id>.backup` | Separate eligible identities, or `[]` when unassigned |
| `areas.<id>.responsibility` | The reviewer's substantive remit |
| `areas.<id>.paths` | Rooted exact file paths or directory prefixes for that area |

The checker validates the exact nine areas and canonical scope, required paths'
existence, nonempty primary lists, identity format, duplicate identities and paths,
distinct primary/backup roles, and the generated CODEOWNERS content. Case-only
identity differences do not count as independent reviewers. Every maintained
algorithm and fixture in [algorithms.json](algorithms.json) must reference a
registered `review_area` that agrees with the generated CODEOWNERS route for
every algorithm role file or fixture path. A valid area name alone is insufficient:
declaring BFS as `machine` is rejected while its files route to `algorithms`.
The rest of the role/schema validation remains in the algorithm checker.
The isolated tests exercise failures without modifying the working repository. No network access is
needed; account existence, repository permissions, team visibility, and current
branch rules must be checked separately when appointing reviewers.

When adding a layer or a shared dependency to the review scope, update the
registry and the checker's canonical path coverage together. This prevents a typo
or an accidental broad pattern from silently expanding ownership into unrelated
source trees. Directory prefixes cover future descendants, and the RAM fallback
keeps newly added RAM files routed while their specific area is being established.
