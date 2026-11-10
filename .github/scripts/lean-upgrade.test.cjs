const assert = require('node:assert/strict');
const test = require('node:test');
const { mkdtempSync, readFileSync, writeFileSync, rmSync } = require('node:fs');
const { tmpdir } = require('node:os');
const { join } = require('node:path');
const { selectUpgrade, prepareUpgrade, reportFailure } = require('./lean-upgrade.cjs');

function fixture(options = {}) {
  const version = options.version ?? 'v4.36.0';
  const requests = [], created = [], comments = [], outputs = {};
  const github = {
    rest: {
      repos: {
        getLatestRelease: async () => ({ data: {
          tag_name: version, draft: false, prerelease: false, ...options.release,
        } }),
        getContent: async request => {
          requests.push(request);
          if (request.repo === options.missing) throw { status: 404 };
          if (options.error) throw options.error;
          return { data: {
            encoding: 'base64',
            content: Buffer.from(request.repo === options.mismatched
              ? 'leanprover/lean4:v4.35.0\n' : `leanprover/lean4:${version}\n`).toString('base64'),
          } };
        },
      },
      pulls: { list: () => {} },
      issues: {
        listForRepo: () => {},
        create: async issue => {
          created.push(issue);
          return { data: { html_url: 'https://github.com/example/AlgoLib/issues/1' } };
        },
        createComment: async comment => { comments.push(comment); },
      },
    },
    paginate: async (method, args) => {
      assert.equal(args.state, 'all');
      if (method === github.rest.pulls.list) {
        assert.equal(args.head, `example:automation/lean-${version}`);
        return options.prs ?? [];
      }
      assert.equal(args.creator, 'github-actions[bot]');
      return options.issues ?? [];
    },
  };
  const args = { github, context: { repo: { owner: 'example', repo: 'AlgoLib' }, runId: 42 },
    core: { info() {}, notice() {}, setOutput(key, value) { outputs[key] = value; } } };
  return {
    requests, created, comments, outputs,
    select: () => selectUpgrade({ ...args, retry: options.retry,
      toolchain: options.toolchain ?? 'leanprover/lean4:v4.35.0' }),
    report: steps => reportFailure({ ...args, version, steps }),
  };
}

test('prepares only when both matching tagged toolchains are available', async () => {
  const f = fixture();
  assert.equal(await f.select(), 'ready');
  assert.deepEqual(f.requests.map(r => [r.owner, r.repo, r.ref]), [
    ['leanprover-community', 'mathlib4', 'refs/tags/v4.36.0'],
    ['leanprover', 'cslib', 'refs/tags/v4.36.0'],
  ]);
  assert.equal(f.outputs.ready, 'true');
  assert.equal(f.outputs.branch, 'automation/lean-v4.36.0');
  assert.equal(f.created.length, 0); // Readiness itself is not a failure notification.
});

test('does not upgrade the current version or downgrade a newer toolchain', async () => {
  for (const toolchain of ['v4.36.0', 'v4.37.0', 'v4.37.0-rc1']) {
    const f = fixture({ toolchain: `leanprover/lean4:${toolchain}` });
    assert.equal(await f.select(), 'current');
    assert.equal(f.requests.length, 0);
    assert.equal(f.outputs.ready, 'false');
  }
});

test('compares versions numerically and accepts the stable successor to an RC', async () => {
  for (const [current, version] of [['v4.9.0', 'v4.10.0'], ['v4.35.0', 'v4.35.1'],
    ['v4.36.0-rc2', 'v4.36.0']]) {
    const f = fixture({ toolchain: `leanprover/lean4:${current}`, version });
    assert.equal(await f.select(), 'ready');
  }
});

test('waits quietly for missing or mismatched dependencies and retries later', async () => {
  for (const repo of ['mathlib4', 'cslib']) {
    for (const condition of ['missing', 'mismatched']) {
      const options = { [condition]: repo };
      const f = fixture(options);
      assert.equal(await f.select(), 'waiting');
      assert.equal(f.outputs.ready, 'false');
      assert.equal(f.created.length, 0);
      delete options[condition];
      assert.equal(await f.select(), 'ready');
    }
  }
});

test('preserves existing open or closed upgrade PRs even on manual retry', async () => {
  for (const state of ['open', 'closed']) {
    const f = fixture({ prs: [{ state }], retry: true });
    assert.equal(await f.select(), 'tracked');
    assert.equal(f.outputs.ready, 'false');
    assert.equal(f.requests.length, 0);
  }
});

test('an issue stops repeated scheduled builds but allows an explicit retry', async () => {
  for (const state of ['open', 'closed']) {
    const options = { issues: [{ number: 17, state, body: '<!-- algolib-lean-upgrade:v4.36.0 -->' }] };
    const f = fixture(options);
    assert.equal(await f.select(), 'tracked');
    options.retry = true;
    assert.equal(await f.select(), 'ready');
    assert.equal(f.outputs['issue-reference'], 'Closes #17');
  }
});

test('previous-version issues do not suppress a new upgrade', async () => {
  const f = fixture({ issues: [{ body: '<!-- algolib-lean-upgrade:v4.35.0 -->' }] });
  assert.equal(await f.select(), 'ready');
});

test('rejects draft, prerelease and unexpected release responses', async () => {
  for (const release of [{ draft: true }, { prerelease: true },
    { tag_name: 'v4.36.0-rc2' }, { tag_name: 'nightly' }]) {
    const f = fixture({ release });
    await assert.rejects(f.select(), /stable Lean 4 version/);
    assert.equal(f.outputs.ready, 'false');
  }
});

test('reports API failures instead of treating them as missing dependencies', async () => {
  for (const status of [403, 429, 500]) {
    const error = Object.assign(new Error('API failure'), { status });
    const f = fixture({ error });
    await assert.rejects(f.select(), error);
    assert.equal(f.outputs.ready, 'false');
  }
});

test('failed resolve, build, or base validation creates an issue with the run log', async () => {
  for (const stage of ['resolve', 'build', 'base']) {
    const f = fixture();
    assert.equal(await f.report({ [stage]: { outcome: 'failure' }, checks: { outcome: 'skipped' } }), 'created');
    assert.equal(f.created.length, 1);
    assert.match(f.created[0].body, new RegExp(`\\*\\*${stage}\\*\\*`));
    assert.match(f.created[0].body, /actions\/runs\/42/);
    assert.match(f.created[0].body, /algolib-lean-upgrade:v4\.36\.0/);
  }
});

test('a failed manual retry adds details to the existing issue without replacing its body', async () => {
  const issue = { number: 17, body: '<!-- algolib-lean-upgrade:v4.36.0 -->\nMaintainer notes' };
  const f = fixture({ issues: [issue] });
  assert.equal(await f.report({ resolve: { outcome: 'failure' } }), 'commented');
  assert.equal(f.created.length, 0);
  assert.equal(f.comments[0].issue_number, 17);
  assert.match(issue.body, /Maintainer notes/);
});

const lakefile = `name = "AlgoLib"
version = "0.1.0"
[[require]]
name = "cslib"
scope = "leanprover"
rev = "v4.35.0" # keep this comment
[[require]]
name = "checkdecls"
scope = "PatrickMassot"
rev = "checker-commit"
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.35.0"
[[lean_lib]]
name = "AlgoLib"
`;

function project(t, overrides = {}) {
  const root = mkdtempSync(join(tmpdir(), 'algolib-upgrade-test-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const files = {
    'lean-toolchain': 'leanprover/lean4:v4.35.0\n',
    'lakefile.toml': lakefile,
    'README.md': 'Use v4.35.0 with Lean 4.35.0. Older releases: v4.27.0.\n',
    'lake-manifest.json': '{"regenerated": "by lake update"}\n',
    ...overrides,
  };
  for (const [name, content] of Object.entries(files)) writeFileSync(join(root, name), content);
  return { root, files, read: name => readFileSync(join(root, name), 'utf8') };
}

test('updates both pinned requirements and current README examples without touching the checker', t => {
  const p = project(t);
  prepareUpgrade({ root: p.root, version: 'v4.36.0' });
  assert.equal(p.read('lean-toolchain'), 'leanprover/lean4:v4.36.0\n');
  assert.equal(p.read('lakefile.toml'), lakefile.replaceAll('v4.35.0', 'v4.36.0'));
  assert.equal(p.read('README.md'), 'Use v4.36.0 with Lean 4.36.0. Older releases: v4.27.0.\n');
  assert.equal(p.read('lake-manifest.json'), p.files['lake-manifest.json']);
});

test('invalid or missing requirements leave every file untouched', t => {
  for (const broken of [lakefile.replace('name = "cslib"', 'name = "other"'),
    lakefile.replace('scope = "leanprover"', 'scope = "other"'),
    lakefile.replace('rev = "v4.35.0" # keep this comment', ''),
    lakefile + '\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\nrev = "old"\n']) {
    const p = project(t, { 'lakefile.toml': broken });
    assert.throws(() => prepareUpgrade({ root: p.root, version: 'v4.36.0' }), /Expected/);
    for (const [name, original] of Object.entries(p.files)) assert.equal(p.read(name), original);
  }
});

test('preparing an already current, older, or prerelease target is rejected without edits', t => {
  for (const version of ['v4.35.0', 'v4.34.0', 'v4.36.0-rc1']) {
    const p = project(t);
    assert.throws(() => prepareUpgrade({ root: p.root, version }), /Expected/);
    for (const [name, original] of Object.entries(p.files)) assert.equal(p.read(name), original);
  }
});
