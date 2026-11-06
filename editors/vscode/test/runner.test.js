'use strict';
// The command line side of the run icons and the Testing panel (runner.js),
// against a stub program that prints what `stitchwort test --json` prints.
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const run = require('../runner');

function stub(body) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'sw-runner-'));
  const file = path.join(dir, 'stitchwort');
  fs.writeFileSync(file, `#!/bin/sh\n${body}\n`, { mode: 0o755 });
  return file;
}

test('arguments for a file, a test, and the whole project', () => {
  assert.deepStrictEqual(run.testArgs({ target: 'a.sw' }), ['test', 'a.sw', '--json']);
  assert.deepStrictEqual(run.testArgs({ target: 'Aoc.Day01', only: 'x y' }), ['test', 'Aoc.Day01', '--only', 'x y', '--json']);
  assert.deepStrictEqual(run.testArgs({}), ['test', '--json']);
});

test('tests are found by their declarations, names unescaped', () => {
  const text = 'def f := 1\n\ntest "one" := f == 1\n  test "indented" := true\ntest "say \\"hi\\"" := true\r\ntest "x" := true\n';
  assert.deepStrictEqual(run.discoverTests(text), [
    { name: 'one', line: 2, character: 0 },
    { name: 'say "hi"', line: 4, character: 0 },
    { name: 'x', line: 5, character: 0 },
  ]);
});

test('a failing run is JSON on standard output, not an error', async () => {
  const json = JSON.stringify({
    ok: false,
    tests: [
      { name: 'a', outcome: 'passed', cached: true, file: 'a.sw', line: 3, column: 1, message: null },
      {
        name: 'b', outcome: 'failed', cached: false, file: 'a.sw', line: 4, column: 1, message: '`==` is False',
        failure: { comparison: { op: '==', left: '2', right: '3', difference: null }, part: null },
      },
    ],
  });
  const cli = stub(`echo '${json}'\nexit 1`);
  const result = await run.runTestsJson(cli, ['test', 'a.sw', '--json'], os.tmpdir());
  assert.strictEqual(result.error, undefined);
  assert.strictEqual(result.ok, false);
  assert.deepStrictEqual(result.tests.map(run.summaryLine), ['✓ a (cached)', '✗ b: `==` is False']);
  assert.strictEqual(run.failureText(result.tests[1]), '`==` is False\nleft:  2\nright: 3');
  assert.strictEqual(run.summary(result.tests), '1 passed, 1 failed (1 from the cache)');
});

test('no JSON means the program\'s own error is shown', async () => {
  const cli = stub('echo "error: no such file" >&2\nexit 1');
  const result = await run.runTestsJson(cli, ['test', 'x.sw', '--json'], os.tmpdir());
  assert.strictEqual(result.error, 'error: no such file');
  const missing = await run.runTestsJson('/no/such/stitchwort', [], os.tmpdir());
  assert.match(missing.error, /ENOENT/);
});

test('a file belongs to the nearest project at or below the workspace folder', () => {
  const yaml = new Set(['/w/p/stitchwort.yaml']);
  const exists = (p) => yaml.has(p);
  assert.strictEqual(run.projectOf('/w/p/sub/a.sw', '/w', exists), '/w/p');
  assert.strictEqual(run.projectOf('/w/p/a.sw', '/w', exists), '/w/p');
  assert.strictEqual(run.projectOf('/w/other/a.sw', '/w', exists), undefined);
});

test('a project file is tested by its namespace, any other file by its name', () => {
  assert.strictEqual(run.namespaceOf('--| doc\nnamespace Aoc.Year2020.Day01.Tests\nimport Std (List)\n'), 'Aoc.Year2020.Day01.Tests');
  assert.strictEqual(run.namespaceOf('def x := 1\n'), undefined);
  assert.deepStrictEqual(run.testTarget('/w/p/src/A.sw', '/w/p', 'namespace A.B\n'), { cwd: '/w/p', target: 'A.B' });
  assert.match(run.testTarget('/w/p/src/A.sw', '/w/p', 'def x := 1\n').error, /no `namespace` line/);
  assert.deepStrictEqual(run.testTarget('/t/01.sw', undefined, 'def x := 1\n'), { cwd: '/t', target: '01.sw' });
});

test('reported file names: project names start with the project folder', () => {
  assert.strictEqual(run.reportedPath('/w/aoc', '/w/aoc', 'aoc/src/A/B.sw'), '/w/aoc/src/A/B.sw');
  assert.strictEqual(run.reportedPath('/t', undefined, '01.sw'), '/t/01.sw');
  assert.strictEqual(run.reportedPath('/t', undefined, '/x/y.sw'), '/x/y.sw');
});

test('the server\'s tests are used, with the file\'s namespace', async () => {
  const answer = [
    { name: 'a', namespace: 'N.M', range: { start: { line: 4, character: 2 }, end: { line: 5, character: 0 } } },
    { name: 'b', namespace: null, range: { start: { line: 9, character: 0 }, end: { line: 9, character: 9 } } },
  ];
  assert.deepStrictEqual(await run.discover(async () => answer, 'unused'), [
    { name: 'a', namespace: 'N.M', line: 4, character: 2 },
    { name: 'b', namespace: undefined, line: 9, character: 0 },
  ]);
  // No regex involved: the server's list is taken as it is, even when empty.
  assert.deepStrictEqual(await run.discover(async () => [], 'test "x" := true\n'), []);
});

test('without an answer from the server the text is read', async () => {
  const text = 'namespace Q\n\ntest "t" := true\n';
  const want = [{ name: 't', line: 2, character: 0, namespace: 'Q' }];
  assert.deepStrictEqual(await run.discover(async () => { throw new Error('no server'); }, text), want);
  assert.deepStrictEqual(await run.discover(async () => ({ not: 'a list' }), () => text), want);
  const started = Date.now();
  assert.deepStrictEqual(await run.discover(() => new Promise(() => {}), text, 30), want);
  assert.ok(Date.now() - started < 2000);
});

test('namespaces are grouped to cover the project without overlap', () => {
  const found = run.groupNamespaces([
    'Aoc.Year2020.Day01', 'Aoc.Year2020.Day01.Proofs', 'Aoc.Year2020.Day02.Proofs.Deep',
    'Aoc.Common', 'Aoc.Common.Tests', 'Aoc.Common.Proofs', 'Solo',
  ]);
  assert.deepStrictEqual(found, ['Aoc.Common', 'Aoc.Year2020.Day01', 'Aoc.Year2020.Day02', 'Solo']);
  assert.ok(run.inGroup('Aoc.Common.Tests', 'Aoc.Common'));
  assert.ok(!run.inGroup('Aoc.Commonly', 'Aoc.Common'));
});

test('the pool runs a few at a time, reports each as it finishes, and stops starting on cancel', async () => {
  let running = 0;
  let peak = 0;
  const order = [];
  const jobs = [60, 10, 10, 10, 10, 10];
  let stop = false;
  await run.runPool(
    jobs.map((ms, i) => ({ ms, i })),
    2,
    async (job) => {
      running++;
      peak = Math.max(peak, running);
      await new Promise((r) => setTimeout(r, job.ms));
      running--;
      return job.i;
    },
    (job, result) => {
      order.push(result);
      if (result === 3) stop = true;
    },
    () => stop,
  );
  assert.strictEqual(peak, 2);
  // Job 0 is slow: the quick ones are reported before it, and nothing starts after the stop.
  assert.ok(order.indexOf(1) < order.indexOf(0));
  assert.ok(!order.includes(5));
});

test('per-group runs against a stub CLI report progressively and a stop kills the rest', async () => {
  // Group "slow" takes a while; the others answer at once.
  const cli = stub(`
case "$2" in
  slow) sleep 5;;
esac
echo '{"ok":true,"tests":[{"name":"'$2'","outcome":"passed","cached":false,"file":"f.sw"}]}'`);
  const groups = ['A', 'B', 'slow', 'C'];
  const abort = new AbortController();
  const done = [];
  const started = Date.now();
  await run.runPool(
    groups,
    2,
    (g) => run.runTestsJson(cli, run.testArgs({ target: g }), os.tmpdir(), abort.signal),
    (g, result) => {
      done.push([g, result.cancelled ? 'cancelled' : result.tests && result.tests[0].name]);
      if (g === 'C') abort.abort();
    },
    () => abort.signal.aborted,
  );
  assert.ok(Date.now() - started < 4000, 'the slow run was killed, not waited for');
  assert.deepStrictEqual(done.slice(0, 3), [['A', 'A'], ['B', 'B'], ['C', 'C']]);
  assert.deepStrictEqual(done[3], ['slow', 'cancelled']);
});
