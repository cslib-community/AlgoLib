const { readFileSync, writeFileSync } = require('node:fs');
const { join } = require('node:path');

const stable = /^v4\.\d+\.\d+$/;
const dependencies = [
  { owner: 'leanprover-community', repo: 'mathlib4', name: 'mathlib' },
  { owner: 'leanprover', repo: 'cslib', name: 'cslib' },
];
const marker = version => `<!-- algolib-lean-upgrade:${version} -->`;

function compareVersions(a, b) {
  const left = a.slice(1).split('.').map(Number);
  const right = b.slice(1).split('.').map(Number);
  for (let i = 0; i < left.length; i++) {
    if (left[i] !== right[i]) return left[i] - right[i];
  }
  return 0;
}

async function findIssue(github, repo, version) {
  const issues = await github.paginate(github.rest.issues.listForRepo, {
    ...repo, state: 'all', creator: 'github-actions[bot]', per_page: 100,
  });
  return issues.find(issue => !issue.pull_request && issue.body?.includes(marker(version)));
}

async function selectUpgrade({ github, context, core, retry = false,
  toolchain = readFileSync('lean-toolchain', 'utf8').trim() }) {
  core.setOutput('ready', 'false');
  const current = /^leanprover\/lean4:(v4\.\d+\.\d+)(-rc\d+)?$/.exec(toolchain);
  if (!current) throw new Error(`Unexpected project toolchain: ${toolchain}`);
  const { data: release } = await github.rest.repos.getLatestRelease({
    owner: 'leanprover', repo: 'lean4',
  });
  const version = release.tag_name;
  if (release.draft || release.prerelease || !stable.test(version)) {
    throw new Error('Latest release does not identify a stable Lean 4 version.');
  }
  const order = compareVersions(version, current[1]);
  if (order < 0 || (order === 0 && !current[2])) {
    core.info(`Already using ${version} or a newer toolchain.`);
    return 'current';
  }

  const branch = `automation/lean-${version}`;
  const prs = await github.paginate(github.rest.pulls.list, {
    ...context.repo, state: 'all', base: 'main',
    head: `${context.repo.owner}:${branch}`, per_page: 100,
  });
  if (prs.length) {
    core.info(`An upgrade PR for ${version} already exists; preserving it and its branch.`);
    return 'tracked';
  }
  const issue = await findIssue(github, context.repo, version);
  if (issue && !retry) {
    core.info(`Upgrade tracked in #${issue.number}; use manual retry to attempt it again.`);
    return 'tracked';
  }
  core.setOutput('version', version);
  core.setOutput('branch', branch);
  core.setOutput('issue', issue?.number ?? '');
  core.setOutput('issue-reference', issue ? `Closes #${issue.number}` : '');

  const target = `leanprover/lean4:${version}`;
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
  core.setOutput('ready', 'true');
  return 'ready';
}

function updateLakefile(source, version) {
  const seen = new Set();
  const updated = source.split(/(?=^\[)/m).map(section => {
    if (!section.startsWith('[[require]]')) return section;
    const name = /^name[ \t]*=[ \t]*"([^"\n]+)"[ \t]*(?:#.*)?$/m.exec(section)?.[1];
    const dependency = dependencies.find(dep => dep.name === name);
    if (!dependency) return section;
    const scope = /^scope[ \t]*=[ \t]*"([^"\n]+)"[ \t]*(?:#.*)?$/m.exec(section)?.[1];
    const revision = /^rev([ \t]*=[ \t]*)"[^"\n]*"([^\n]*)$/gm;
    if (seen.has(name) || scope !== dependency.owner || [...section.matchAll(revision)].length !== 1) {
      throw new Error(`Expected one scoped, pinned requirement for ${name}.`);
    }
    seen.add(name);
    return section.replace(revision, (_match, spacing, comment) => `rev${spacing}"${version}"${comment}`);
  }).join('');
  if (seen.size !== dependencies.length) throw new Error('Expected both Mathlib and CSLib requirements.');
  return updated;
}

function prepareUpgrade({ version, root = '.' }) {
  if (!stable.test(version)) throw new Error('Expected a stable Lean 4 version.');
  const toolchain = readFileSync(join(root, 'lean-toolchain'), 'utf8').trim();
  const current = /^leanprover\/lean4:(v4\.\d+\.\d+)(-rc\d+)?$/.exec(toolchain);
  if (!current || compareVersions(version, current[1]) < 0 ||
      (version === current[1] && !current[2])) throw new Error('Expected a newer stable toolchain.');

  // Validate every edit before writing any file. Lake regenerates the manifest next.
  const lakefile = updateLakefile(readFileSync(join(root, 'lakefile.toml'), 'utf8'), version);
  const oldVersion = current[1] + (current[2] ?? '');
  const readme = readFileSync(join(root, 'README.md'), 'utf8')
    .replaceAll(oldVersion, version)
    .replaceAll(`Lean ${oldVersion.slice(1)}`, `Lean ${version.slice(1)}`);
  writeFileSync(join(root, 'lean-toolchain'), `leanprover/lean4:${version}\n`);
  writeFileSync(join(root, 'lakefile.toml'), lakefile);
  writeFileSync(join(root, 'README.md'), readme);
}

async function reportFailure({ github, context, core, version, steps }) {
  if (!stable.test(version)) throw new Error('Cannot report an unknown upgrade version.');
  const failed = Object.entries(steps).filter(([, step]) => step.outcome === 'failure').map(([name]) => name);
  const run = `https://github.com/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId}`;
  const details = `Automatic upgrade to ${version} failed at: **${failed.join(', ') || 'unknown stage'}**.\n\n` +
    `[Inspect the failed steps and logs](${run}). No upgrade is merged automatically.\n\n` +
    'Fix the dependency/proof conflict in a manual upgrade PR, or rerun **Upgrade stable Lean** with ' +
    '**Retry an upgrade with an existing issue** after resolving the failure.\n\n' +
    'A build failure may also come from tooling or network errors; check the linked log before changing proofs.';
  const existing = await findIssue(github, context.repo, version);
  if (existing) {
    await github.rest.issues.createComment({ ...context.repo, issue_number: existing.number, body: details });
    core.notice(`Retry failed; details added to #${existing.number}.`);
    return 'commented';
  }
  const { data: issue } = await github.rest.issues.create({ ...context.repo,
    title: `Lean ${version} upgrade needs attention`, body: `${marker(version)}\n\n${details}` });
  core.notice(`Upgrade needs attention: ${issue.html_url}`);
  return 'created';
}

module.exports = { selectUpgrade, prepareUpgrade, reportFailure };
