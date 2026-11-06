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
