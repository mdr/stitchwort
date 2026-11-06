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
function register(context, cliPath, serverTests) {
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

  registerTestingPanel(context, cliPath, serverTests);
}

// The Testing panel: a controller whose items are the tests of the project's
// files, as the server lists them (`stitchwort/tests`; `serverTests(uri)`),
// or by reading the text when it doesn't answer; a run asks the CLI
// (`stitchwort test --json`, in the project folder) and reports each test
// where it is.
function registerTestingPanel(context, cliPath, serverTests) {
  const controller = vscode.tests.createTestController('stitchwort', 'Stitchwort');
  context.subscriptions.push(controller);
  const exists = (p) => fs.existsSync(p);

  // Data kept per item.
  /** @type {WeakMap<vscode.TestItem, {project: string, file?: string, name?: string, namespace?: string}>} */
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

  // The tests of a file: the server's, or the text's.
  // After one failed ask the rest of a sweep skips the server.
  let serverUp = true;
  const testsOf = (uri, text) =>
    run.discover(() => {
      if (!serverUp) return Promise.reject(new Error('server not answering'));
      return Promise.resolve(serverTests(uri.toString())).catch((e) => {
        serverUp = false;
        throw e;
      });
    }, text);

  function setTests(item, uri, found) {
    info.get(item).namespace = found.length ? found[0].namespace : undefined;
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
    const item = fileItem(uri);
    if (!item) return;
    const found = await testsOf(uri, () => doc.getText());
    if (found.length === 0) {
      const parent = projects.get(info.get(item).project);
      if (parent) parent.children.delete(item.id);
      return;
    }
    setTests(item, uri, found);
  }

  async function discoverAll() {
    serverUp = true;
    const files = await vscode.workspace.findFiles('**/*.sw', '**/{node_modules,.stitchwort,target}/**');
    for (const uri of files) {
      if (!rootOf(uri)) continue;
      // The server reads unopened files itself (and the fallback reads them
      // directly), which keeps hundreds of them out of the editor's document
      // list.
      try {
        const found = await testsOf(uri, () => fs.readFileSync(uri.fsPath, 'utf8'));
        if (found.length === 0) continue;
        const item = fileItem(uri);
        if (item) setTests(item, uri, found);
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

  // What a request covers, as CLI runs: one test, or one file, or a project.
  // A project (or any item above the files) is split into one run per group
  // of namespaces (`groupNamespaces`), so the panel fills in as each finishes
  // instead of after the slowest. Returns `{ item, project, target?, only?,
  // file?, covered, error? }` per run.
  function plan(request) {
    const roots = request.include && request.include.length ? [...request.include] : [...projects.values()];
    const excluded = new Set((request.exclude || []).map((i) => i.id));
    const jobs = [];
    for (const item of roots) {
      if (excluded.has(item.id)) continue;
      const data = info.get(item);
      if (!data) continue;
      const covered = leaves(item).filter((i) => info.get(i).name !== undefined);
      if (data.file) {
        const doc = vscode.workspace.textDocuments.find((d) => d.uri.fsPath === data.file);
        const where = run.testTarget(data.file, data.project, doc ? doc.getText() : fs.readFileSync(data.file, 'utf8'));
        jobs.push({ item, project: data.project, file: data.file, only: data.name, target: where.target, error: where.error, covered });
        continue;
      }
      // A project: its files, by namespace.
      const files = [];
      item.children.forEach((f) => files.push(f));
      const withNs = files.filter((f) => info.get(f).namespace);
      for (const f of files.filter((f) => !info.get(f).namespace)) {
        const error = run.testTarget(info.get(f).file, data.project, '').error;
        jobs.push({ item: f, project: data.project, error, covered: leaves(f).filter((i) => info.get(i).name !== undefined) });
      }
      for (const group of run.groupNamespaces(withNs.map((f) => info.get(f).namespace))) {
        const inside = withNs.filter((f) => run.inGroup(info.get(f).namespace, group));
        jobs.push({
          item,
          project: data.project,
          target: group,
          covered: inside.flatMap((f) => leaves(f).filter((i) => info.get(i).name !== undefined)),
        });
      }
    }
    return jobs;
  }

  const leaves = (item, out = []) => {
    if (item.children.size === 0) out.push(item);
    else item.children.forEach((c) => leaves(c, out));
    return out;
  };

  // Reports one finished CLI run on the items it covered.
  function report(testRun, job, result) {
    const { covered } = job;
    if (result.cancelled) {
      covered.forEach((i) => testRun.skipped(i));
      return;
    }
    if (result.error) {
      for (const i of covered) testRun.errored(i, new vscode.TestMessage(result.error));
      testRun.appendOutput(result.error.replace(/\r?\n/g, '\r\n') + '\r\n');
      return;
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

  async function runHandler(request, token) {
    const testRun = controller.createTestRun(request);
    const abort = new AbortController();
    token.onCancellationRequested(() => abort.abort());
    const jobs = plan(request);
    for (const job of jobs) {
      if (job.file) {
        const doc = vscode.workspace.textDocuments.find((d) => d.uri.fsPath === job.file);
        if (doc && doc.isDirty) await doc.save();
      }
    }
    const runnable = [];
    for (const job of jobs) {
      if (job.error) {
        for (const i of job.covered) testRun.errored(i, new vscode.TestMessage(job.error));
      } else {
        job.covered.forEach((i) => testRun.started(i));
        runnable.push(job);
      }
    }
    await run.runPool(
      runnable,
      run.PARALLEL_RUNS,
      (job) => run.runTestsJson(cliPath(), run.testArgs({ target: job.target, only: job.only }), job.project, abort.signal),
      (job, result) => {
        job.done = true;
        report(testRun, job, result);
      },
      () => token.isCancellationRequested,
    );
    // Runs that never started because of a stop.
    for (const job of runnable) if (!job.done) job.covered.forEach((i) => testRun.skipped(i));
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
