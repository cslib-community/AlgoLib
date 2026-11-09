const { readFileSync } = require('node:fs');

const dependencies = [
  { owner: 'leanprover-community', repo: 'mathlib4', name: 'Mathlib' },
  { owner: 'leanprover', repo: 'cslib', name: 'CSLib' },
];

function compareVersions(a, b) {
  const left = a.slice(1).split('.').map(Number);
  const right = b.slice(1).split('.').map(Number);
  for (let i = 0; i < left.length; i++) {
    if (left[i] !== right[i]) return left[i] - right[i];
  }
  return 0;
}

module.exports = async function check({ github, context, core,
  toolchain = readFileSync('lean-toolchain', 'utf8').trim() }) {
  const current = /^leanprover\/lean4:(v4\.\d+\.\d+)(-rc\d+)?$/.exec(toolchain);
  if (!current) throw new Error(`Unexpected project toolchain: ${toolchain}`);

  const { data: release } = await github.rest.repos.getLatestRelease({
    owner: 'leanprover', repo: 'lean4',
  });
  const version = release.tag_name;
  if (release.draft || release.prerelease || !/^v4\.\d+\.\d+$/.test(version)) {
    throw new Error('Latest release does not identify a stable Lean 4 version.');
  }
  const order = compareVersions(version, current[1]);
  if (order < 0 || (order === 0 && !current[2])) {
    core.info(`Already using ${version} or a newer toolchain.`);
    return 'current';
  }

  const target = `leanprover/lean4:${version}`;
  core.info(`Found new stable Lean ${version}; checking matching dependencies.`);
  for (const { owner, repo, name } of dependencies) {
    let data;
    try {
      ({ data } = await github.rest.repos.getContent({
        owner, repo, path: 'lean-toolchain', ref: `refs/tags/${version}`,
      }));
    } catch (error) {
      if (error.status !== 404) throw error;
      core.info(`Waiting for ${name} tag ${version} and its lean-toolchain.`);
      return 'waiting';
    }
    if (data.encoding !== 'base64' || typeof data.content !== 'string') {
      throw new Error(`Unexpected lean-toolchain response from ${name}.`);
    }
    if (Buffer.from(data.content, 'base64').toString('utf8').trim() !== target) {
      core.info(`Waiting: ${name} ${version} uses a different Lean toolchain.`);
      return 'waiting';
    }
  }

  // Include closed issues so declining an upgrade does not create repeat alerts.
  const marker = `<!-- algolib-lean-upgrade:${version} -->`;
  const issues = await github.paginate(github.rest.issues.listForRepo, {
    ...context.repo, state: 'all', creator: 'github-actions[bot]', per_page: 100,
  });
  if (issues.some(issue => !issue.pull_request && issue.body?.includes(marker))) {
    core.info(`An upgrade issue for ${version} already exists.`);
    return 'tracked';
  }

  const links = dependencies.map(({ owner, repo, name }) =>
    `- [${name} ${version}](https://github.com/${owner}/${repo}/tree/${version})`);
  const { data: issue } = await github.rest.issues.create({
    ...context.repo,
    title: `Lean ${version} upgrade is ready to try`,
    body: [marker, '',
      `A new [stable Lean release](https://github.com/leanprover/lean4/releases/tag/${version}) is available.`,
      `Both matching dependency tags declare \`${target}\`:`, '', ...links, '',
      'This confirms upstream release availability. AlgoLib still needs a build and proof review.', '',
      'Create an upgrade PR from current `main`, update the toolchain, dependency pins, manifest and README,',
      'then fix any breaking changes and wait for CI before merging. Close this issue when the upgrade is merged.', '',
      '[Upgrade instructions](https://github.com/' + context.repo.owner + '/' + context.repo.repo +
        '/blob/main/.github/CONTRIBUTING.md#lean-version-updates)',
    ].join('\n'),
  });
  core.notice(`Upgrade ready: ${issue.html_url}`);
  return 'created';
};
