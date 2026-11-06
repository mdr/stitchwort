'use strict';
// Running tests and programs through the CLI: the pieces of the run icons
// (code lenses) and the Testing panel that don't need `vscode`, so they are
// unit tested (test/runner.test.js). The CLI side is `stitchwort test --json`
// and `stitchwort run` (docs/guide/ editor section).

const cp = require('child_process');
const path = require('path');

// Commands the server's code lenses name (crates/lsp/src/lens.rs).
const RUN_TEST = 'stitchwort.runTest';
const RUN_TESTS = 'stitchwort.runTests';
const RUN_MAIN = 'stitchwort.runMain';

// The arguments of `stitchwort test` for a `target` (a file, or a namespace of
// the project; the whole project when undefined), one test when `only` is
// given.
function testArgs({ target, only }) {
  const args = ['test'];
  if (target) args.push(target);
  if (only !== undefined) args.push('--only', only);
  args.push('--json');
  return args;
}

// Runs `stitchwort test … --json` in `cwd`. Resolves to `{ ok, tests }` from
// the program's JSON, or `{ error }` when it printed none (the file didn't
// check, no such test, no program): the error is what it wrote on standard
// error. Failing tests are not errors: the exit status is nonzero then too.
function runTestsJson(cli, args, cwd) {
  return new Promise((resolve) => {
    cp.execFile(cli, args, { cwd, maxBuffer: 64 * 1024 * 1024 }, (err, stdout, stderr) => {
      try {
        const parsed = JSON.parse(stdout);
        if (parsed && Array.isArray(parsed.tests)) return resolve({ ...parsed, stderr });
      } catch (e) {
        // fall through
      }
      resolve({ error: stderr.trim() || (err && err.message) || 'no result', stderr });
    });
  });
}

// One line for a test's outcome: `✓ name (cached)`, `✗ name: message`.
function summaryLine(t) {
  const mark = t.outcome === 'passed' ? '✓' : t.outcome === 'failed' ? '✗' : '!';
  const cached = t.cached ? ' (cached)' : '';
  const why = t.message ? `: ${t.message}` : '';
  return `${mark} ${t.name}${cached}${why}`;
}

// The text of a failed test for a message: why, then the two sides.
function failureText(t) {
  const lines = [t.message || 'failed'];
  const c = t.failure && t.failure.comparison;
  if (c) {
    lines.push(`left:  ${c.left}`, `right: ${c.right}`);
    if (c.difference) lines.push(c.difference);
  }
  const p = t.failure && t.failure.part;
  if (p) lines.push(`in: ${p.text}`);
  return lines.join('\n');
}

// "3 passed, 1 failed (2 from the cache)".
function summary(tests) {
  const n = (o) => tests.filter((t) => t.outcome === o).length;
  const parts = [`${n('passed')} passed`, `${n('failed')} failed`];
  if (n('unfinished')) parts.push(`${n('unfinished')} unfinished`);
  const cached = tests.filter((t) => t.cached).length;
  return `${parts.join(', ')}${cached ? ` (${cached} from the cache)` : ''}`;
}

// The `test "name"` declarations of a file's text, as the Testing panel lists
// them before anything has run: `{ name, line, character }`, line from 0.
// Read with a pattern rather than a parse, so it works on every keystroke;
// tests start a line, as the formatter keeps them.
function discoverTests(text) {
  const found = [];
  const re = /^test\s+"((?:[^"\\]|\\.)*)"/;
  text.split(/\r?\n/).forEach((line, i) => {
    const m = re.exec(line);
    if (!m) return;
    let name = m[1];
    try {
      name = JSON.parse(`"${m[1]}"`);
    } catch (e) {
      // keep the raw text
    }
    found.push({ name, line: i, character: 0 });
  });
  return found;
}

// The folder of the nearest `stitchwort.yaml` at or above `file`, not above
// `stop`: the project a file's tests belong to, if any. `exists` tells
// whether a path is a file (injected for tests).
function projectOf(file, stop, exists) {
  let dir = path.dirname(file);
  for (;;) {
    if (exists(path.join(dir, 'stitchwort.yaml'))) return dir;
    const up = path.dirname(dir);
    if (up === dir || dir === stop || !dir.startsWith(stop)) return undefined;
    dir = up;
  }
}

// The namespace a file declares on its `namespace` line, if it has one.
function namespaceOf(text) {
  const m = /^namespace\s+([A-Za-z_][\w.']*)/m.exec(text);
  return m ? m[1] : undefined;
}

// How to test a file: in the project it belongs to (`project`, the folder of
// its `stitchwort.yaml`), by its namespace, which also runs the other files of
// that namespace (the CLI refuses a project file on its own: its imports are
// the project's); a file outside a project by its own name. `project` and
// `text` may be undefined. Returns `{ cwd, target }`, or `{ error }` for a
// project file without a `namespace` line.
function testTarget(file, project, text) {
  if (!project) return { cwd: path.dirname(file), target: path.basename(file) };
  const namespace = namespaceOf(text || '');
  if (!namespace) {
    return { error: `${path.basename(file)} is in a project but has no \`namespace\` line, so its tests can't be selected` };
  }
  return { cwd: project, target: namespace };
}

// The path of a file as `test --json` names it. In a project the names start
// with the project's folder name (`aoc/src/…`), relative to its parent; a
// file on its own is named as given, relative to where the CLI ran (`cwd`).
function reportedPath(cwd, project, file) {
  if (path.isAbsolute(file)) return file;
  if (project && file.startsWith(`${path.basename(project)}/`)) return path.join(path.dirname(project), file);
  return path.join(cwd, file);
}

module.exports = {
  namespaceOf,
  testTarget,
  reportedPath,
  RUN_TEST,
  RUN_TESTS,
  RUN_MAIN,
  testArgs,
  runTestsJson,
  summaryLine,
  failureText,
  summary,
  discoverTests,
  projectOf,
};
