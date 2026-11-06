'use strict';
// The run icons (code lenses from the server) and the Testing panel. VS Code
// glue only: the command line side is in runner.js, which has the tests.
//
// Run icons work on every `.sw` file, a single file outside a project too
// (D2513). The Testing panel lists the tests of files that belong to a
// project, those under a `stitchwort.yaml` (D2245).

const vscode = require('vscode');
const path = require('path');
const fs = require('fs');
const run = require('./runner');
const cfg = require('./client');

/** @param {() => string} cliPath */
function register(context, cliPath) {
  const output = vscode.window.createOutputChannel('Stitchwort Tests');
  const failures = vscode.languages.createDiagnosticCollection('stitchwort-tests');
  /** @type {vscode.Terminal | undefined} */
  let runTerminal;
  context.subscriptions.push(output, failures);

  const fileOf = (uri) => vscode.Uri.parse(uri);

  async function save(uri) {
    const doc = vscode.workspace.textDocuments.find((d) => d.uri.toString() === uri.toString());
    if (doc && doc.isDirty) await doc.save();
  }

  // Run icon: the CLI on the file, its answer as a message and in the Output
  // panel, and failures marked in the file until the next run.
  async function runTestsOfFile(uriText, only) {
    const uri = fileOf(uriText);
    await save(uri);
    const project = run.projectOf(uri.fsPath, path.parse(uri.fsPath).root, fs.existsSync);
    const text = fs.readFileSync(uri.fsPath, 'utf8');
    const where = run.testTarget(uri.fsPath, project, text);
    output.clear();
    if (where.error) {
      vscode.window.showErrorMessage(`Stitchwort: ${where.error}`);
      return;
    }
    const result = await vscode.window.withProgress(
      { location: vscode.ProgressLocation.Window, title: 'Stitchwort: running tests' },
      () => run.runTestsJson(cliPath(), run.testArgs({ target: where.target, only }), where.cwd),
    );
    if (result.error) {
      output.appendLine(result.error);
      output.show(true);
      vscode.window.showErrorMessage(`Stitchwort: ${result.error.split('\n')[0]}`);
      return;
    }
    // A namespace may have more files than this one.
    const tests = result.tests.filter((t) => !t.file || run.reportedPath(where.cwd, project, t.file) === uri.fsPath);
    if (tests.length === 0) {
      vscode.window.showWarningMessage(only ? `Stitchwort: there is no test called "${only}".` : 'Stitchwort: no tests in this file.');
      return;
    }
    const marks = [];
    for (const t of tests) {
      output.appendLine(run.summaryLine(t));
      if (t.outcome === 'passed') continue;
      output.appendLine(run.failureText(t).split('\n').slice(1).map((l) => `    ${l}`).join('\n'));
      const at = t.failure && t.failure.part && t.failure.part.file === t.file ? t.failure.part : t;
      const d = new vscode.Diagnostic(range(at.line, at.column), `test "${t.name}": ${run.failureText(t)}`, vscode.DiagnosticSeverity.Error);
      d.source = 'stitchwort test';
      marks.push(d);
    }
    failures.set(uri, marks);
    const line = tests.length === 1 ? run.summaryLine(tests[0]) : run.summary(tests);
    if (tests.some((t) => t.outcome !== 'passed')) {
      output.show(true);
      vscode.window.showErrorMessage(`Stitchwort: ${line}`);
    } else {
      vscode.window.setStatusBarMessage(`Stitchwort: ${line}`, 5000);
      vscode.window.showInformationMessage(`Stitchwort: ${line}`);
    }
  }

  async function runMain(uriText) {
    const uri = fileOf(uriText);
    await save(uri);
    if (runTerminal) runTerminal.dispose();
    runTerminal = vscode.window.createTerminal({
      name: `Stitchwort: ${path.basename(uri.fsPath)}`,
      cwd: path.dirname(uri.fsPath),
      shellPath: cliPath(),
      shellArgs: ['run', path.basename(uri.fsPath)],
    });
    runTerminal.show(true);
  }

  context.subscriptions.push(
    vscode.commands.registerCommand(run.RUN_TEST, (uri, name) => runTestsOfFile(uri, name)),
    vscode.commands.registerCommand(run.RUN_TESTS, (uri) => runTestsOfFile(uri)),
    vscode.commands.registerCommand(run.RUN_MAIN, (uri) => runMain(uri)),
    vscode.workspace.onDidChangeTextDocument((e) => failures.delete(e.document.uri)),
  );

  registerTestingPanel(context, cliPath);
}

// The Testing panel: a controller whose items are the tests of the project's
// files, found by reading the text; a run asks the CLI (`stitchwort test
// --json`, in the project folder) and reports each test where it is.
function registerTestingPanel(context, cliPath) {
  const controller = vscode.tests.createTestController('stitchwort', 'Stitchwort');
  context.subscriptions.push(controller);
  const exists = (p) => fs.existsSync(p);

  // Data kept per item.
  /** @type {WeakMap<vscode.TestItem, {project: string, file?: string, name?: string}>} */
  const info = new WeakMap();
  /** @type {Map<string, vscode.TestItem>} project folder -> item */
  const projects = new Map();

  const rootOf = (uri) => {
    const folder = vscode.workspace.getWorkspaceFolder(uri);
    if (!folder) return undefined;
    return run.projectOf(uri.fsPath, folder.uri.fsPath, exists);
  };

  function projectItem(dir) {
    let item = projects.get(dir);
    if (!item) {
      item = controller.createTestItem(`project:${dir}`, path.basename(dir), vscode.Uri.file(dir));
      info.set(item, { project: dir });
      controller.items.add(item);
      projects.set(dir, item);
    }
    return item;
  }

  function fileItem(uri) {
    const dir = rootOf(uri);
    if (!dir) return undefined;
    const parent = projectItem(dir);
    const id = uri.toString();
    let item = parent.children.get(id);
    if (!item) {
      item = controller.createTestItem(id, path.relative(dir, uri.fsPath), uri);
      info.set(item, { project: dir, file: uri.fsPath });
      parent.children.add(item);
    }
    return item;
  }

  function setTests(item, uri, text) {
    const found = run.discoverTests(text);
    const keep = new Set(found.map((t) => t.name));
    item.children.forEach((child) => {
      if (!keep.has(info.get(child).name)) item.children.delete(child.id);
    });
    for (const t of found) {
      const id = `${uri.toString()}#${t.name}`;
      let child = item.children.get(id);
      if (!child) {
        child = controller.createTestItem(id, t.name, uri);
        info.set(child, { project: info.get(item).project, file: uri.fsPath, name: t.name });
        item.children.add(child);
      }
      child.range = new vscode.Range(t.line, t.character, t.line, t.character);
    }
    item.canResolveChildren = false;
  }

  async function refreshFile(uri) {
    if (uri.scheme !== 'file' || !uri.fsPath.endsWith('.sw')) return;
    const doc = await vscode.workspace.openTextDocument(uri);
    const text = doc.getText();
    const item = fileItem(uri);
    if (!item) return;
    const found = run.discoverTests(text);
    if (found.length === 0) {
      const parent = projects.get(info.get(item).project);
      if (parent) parent.children.delete(item.id);
      return;
    }
    setTests(item, uri, text);
  }

  async function discoverAll() {
    const files = await vscode.workspace.findFiles('**/*.sw', '**/{node_modules,.stitchwort,target}/**');
    for (const uri of files) {
      if (!rootOf(uri)) continue;
      // Reading the files directly keeps hundreds of unopened files out of
      // the editor's document list.
      try {
        const text = fs.readFileSync(uri.fsPath, 'utf8');
        if (!/^test\s+"/m.test(text)) continue;
        const item = fileItem(uri);
        if (item) setTests(item, uri, text);
      } catch (e) {
        // unreadable file: skip
      }
    }
  }

  controller.refreshHandler = discoverAll;
  discoverAll();

  const watcher = vscode.workspace.createFileSystemWatcher('**/*.sw');
  context.subscriptions.push(
    watcher,
    watcher.onDidChange(refreshFile),
    watcher.onDidCreate(refreshFile),
    watcher.onDidDelete((uri) => {
      for (const parent of projects.values()) parent.children.delete(uri.toString());
    }),
    vscode.workspace.onDidChangeTextDocument((e) => {
      if (e.document.languageId === cfg.LANGUAGE) refreshFile(e.document.uri);
    }),
  );

  // What a request covers, as CLI runs: the whole project, or one file, or
  // one test. A request for a project item is the project's one run; the
  // rest are grouped by file.
  function plan(request) {
    const roots = request.include && request.include.length ? [...request.include] : [...projects.values()];
    const excluded = new Set((request.exclude || []).map((i) => i.id));
    const jobs = [];
    for (const item of roots) {
      if (excluded.has(item.id)) continue;
      const data = info.get(item);
      if (!data) continue;
      jobs.push({ item, project: data.project, file: data.file, only: data.name });
    }
    return jobs;
  }

  const leaves = (item, out = []) => {
    if (item.children.size === 0) out.push(item);
    else item.children.forEach((c) => leaves(c, out));
    return out;
  };

  async function runHandler(request, token) {
    const testRun = controller.createTestRun(request);
    for (const job of plan(request)) {
      if (token.isCancellationRequested) break;
      const covered = leaves(job.item).filter((i) => info.get(i).name !== undefined);
      covered.forEach((i) => testRun.started(i));
      let target;
      if (job.file) {
        const doc = vscode.workspace.textDocuments.find((d) => d.uri.fsPath === job.file);
        if (doc && doc.isDirty) await doc.save();
        const where = run.testTarget(job.file, job.project, fs.readFileSync(job.file, 'utf8'));
        if (where.error) {
          for (const i of covered) testRun.errored(i, new vscode.TestMessage(where.error));
          continue;
        }
        target = where.target;
      }
      const result = await run.runTestsJson(cliPath(), run.testArgs({ target, only: job.only }), job.project);
      if (result.error) {
        for (const i of covered) testRun.errored(i, new vscode.TestMessage(result.error));
        testRun.appendOutput(result.error.replace(/\r?\n/g, '\r\n') + '\r\n');
        continue;
      }
      const reported = new Set();
      for (const t of result.tests) {
        const abs = t.file ? run.reportedPath(job.project, job.project, t.file) : job.file;
        const item = covered.find((i) => info.get(i).name === t.name && (!abs || info.get(i).file === abs));
        testRun.appendOutput(`${run.summaryLine(t)}\r\n`);
        if (!item) continue;
        reported.add(item.id);
        item.description = t.cached ? 'cached' : undefined;
        if (t.outcome === 'passed') {
          testRun.passed(item);
        } else {
          const message = new vscode.TestMessage(run.failureText(t));
          const c = t.failure && t.failure.comparison;
          if (c && typeof c.left === 'string') {
            message.actualOutput = c.left;
            message.expectedOutput = c.right;
          }
          const at = t.failure && t.failure.part ? t.failure.part : t;
          const where = at.file ? run.reportedPath(job.project, job.project, at.file) : info.get(item).file;
          message.location = new vscode.Location(vscode.Uri.file(where), range(at.line, at.column));
          if (t.outcome === 'failed') testRun.failed(item, message);
          else testRun.errored(item, message);
        }
      }
      // Tests the run did not mention (the file was edited meanwhile).
      for (const i of covered) if (!reported.has(i.id)) testRun.skipped(i);
    }
    testRun.end();
  }

  controller.createRunProfile('Run', vscode.TestRunProfileKind.Run, runHandler, true);
}

function range(line, column) {
  const l = Math.max(0, (line || 1) - 1);
  const c = Math.max(0, (column || 1) - 1);
  return new vscode.Range(l, c, l, c);
}

module.exports = { register };
