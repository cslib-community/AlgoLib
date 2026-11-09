const assert = require('node:assert/strict');
const test = require('node:test');
const check = require('./check-lean-release.cjs');

function fixture(options = {}) {
  const version = options.version ?? 'v4.36.0';
  const requests = [];
  const created = [];
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
      issues: {
        listForRepo: () => {},
        create: async issue => {
          created.push(issue);
          return { data: { html_url: 'https://github.com/example/AlgoLib/issues/1' } };
        },
      },
    },
    paginate: async (_method, args) => {
      assert.equal(args.state, 'all');
      assert.equal(args.creator, 'github-actions[bot]');
      return options.issues ?? [];
    },
  };
  return {
    requests, created,
    run: () => check({ github, context: { repo: { owner: 'example', repo: 'AlgoLib' } },
      core: { info() {}, notice() {} },
      toolchain: options.toolchain ?? 'leanprover/lean4:v4.35.0' }),
  };
}

test('alerts only after both matching tagged toolchains are available', async () => {
  const f = fixture();
  assert.equal(await f.run(), 'created');
  assert.deepEqual(f.requests.map(r => [r.owner, r.repo, r.ref]), [
    ['leanprover-community', 'mathlib4', 'refs/tags/v4.36.0'],
    ['leanprover', 'cslib', 'refs/tags/v4.36.0'],
  ]);
  assert.equal(f.created.length, 1);
  assert.match(f.created[0].body, /algolib-lean-upgrade:v4\.36\.0/);
  assert.match(f.created[0].body, /still needs a build and proof review/);
});

test('does not alert for the current version or suggest a downgrade', async () => {
  for (const toolchain of ['v4.36.0', 'v4.37.0', 'v4.37.0-rc1']) {
    const f = fixture({ toolchain: `leanprover/lean4:${toolchain}` });
    assert.equal(await f.run(), 'current');
    assert.equal(f.requests.length, 0);
    assert.equal(f.created.length, 0);
  }
});

test('compares versions numerically and accepts the stable successor to an RC', async () => {
  for (const [current, version] of [['v4.9.0', 'v4.10.0'], ['v4.35.0', 'v4.35.1'],
    ['v4.36.0-rc2', 'v4.36.0']]) {
    const f = fixture({ toolchain: `leanprover/lean4:${current}`, version });
    assert.equal(await f.run(), 'created');
  }
});

test('waits quietly when either upstream tag is missing or has a different toolchain', async () => {
  for (const repo of ['mathlib4', 'cslib']) {
    for (const condition of ['missing', 'mismatched']) {
      const f = fixture({ [condition]: repo });
      assert.equal(await f.run(), 'waiting');
      assert.equal(f.created.length, 0);
    }
  }
});

test('a later run alerts when a previously missing dependency appears', async () => {
  const options = { missing: 'cslib' };
  const f = fixture(options);
  assert.equal(await f.run(), 'waiting');
  delete options.missing;
  assert.equal(await f.run(), 'created');
  assert.equal(f.created.length, 1);
});

test('does not duplicate open or closed upgrade issues', async () => {
  for (const state of ['open', 'closed']) {
    const f = fixture({ issues: [{ state, body: '<!-- algolib-lean-upgrade:v4.36.0 -->' }] });
    assert.equal(await f.run(), 'tracked');
    assert.equal(f.created.length, 0);
  }
});

test('previous-version issues and PRs do not suppress a new readiness alert', async () => {
  const f = fixture({ issues: [
    { body: '<!-- algolib-lean-upgrade:v4.35.0 -->' },
    { body: '<!-- algolib-lean-upgrade:v4.36.0 -->', pull_request: {} },
  ] });
  assert.equal(await f.run(), 'created');
});

test('rejects draft, prerelease and unexpected upstream release responses', async () => {
  for (const release of [{ draft: true }, { prerelease: true },
    { tag_name: 'v4.36.0-rc2' }, { tag_name: 'nightly' }]) {
    const f = fixture({ release });
    await assert.rejects(f.run(), /stable Lean 4 version/);
    assert.equal(f.created.length, 0);
  }
});

test('reports API failures rather than treating them as missing dependencies', async () => {
  for (const status of [403, 429, 500]) {
    const error = Object.assign(new Error('API failure'), { status });
    const f = fixture({ error });
    await assert.rejects(f.run(), error);
    assert.equal(f.created.length, 0);
  }
});
