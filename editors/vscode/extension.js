'use strict';
// Stitchwort VS Code extension: go to definition, references, hover, outline,
// workspace symbols and diagnostics, from the compiler's navigation index (`stitchwort check --index -`, see
// docs/proposals/code-navigation.md). Plain CommonJS, no dependencies. The
// lookup logic lives in navindex.js (no `vscode` import, unit tested).

const vscode = require('vscode');
const cp = require('child_process');
const fs = require('fs');
const path = require('path');
const nav = require('./navindex');

const STD_SCHEME = 'stitchwort-std';
const CONFIG_FILE = 'stitchwort.yaml'; // what crates/driver/src/project.rs looks for
const DEBOUNCE_MS = 300;

/** @type {vscode.OutputChannel} */
let output;
let warnedMissingCli = false;

function cliPath() {
  return vscode.workspace.getConfiguration('stitchwort').get('path') || 'stitchwort';
}

// The project folder holding `file` (nearest ancestor with stitchwort.yaml), or
// null for a single file.
function findProjectRoot(file) {
  let dir = path.dirname(file);
  for (;;) {
    if (fs.existsSync(path.join(dir, CONFIG_FILE))) return dir;
    const up = path.dirname(dir);
    if (up === dir) return null;
    dir = up;
  }
}

// How to index the file: key (cache identity), cwd, CLI args, and the path
// the index uses for this file (relative to the root, or as given on the
// command line for a single file).
function plan(file) {
  const root = findProjectRoot(file);
  if (root) {
    return {
      key: root,
      cwd: root,
      args: ['check', '--index', '-', '--project', root],
      // Arguments for a quick check of one namespace (null for a single file,
      // which is already just one file).
      quickArgs: (namespace) => ['check', '--index', '-', '--project', root, namespace],
      indexPath: path.relative(root, file).split(path.sep).join('/'),
    };
  }
  const base = path.basename(file);
  return {
    key: file,
    cwd: path.dirname(file),
    args: ['check', '--index', '-', base],
    quickArgs: null,
    indexPath: base,
  };
}

/**
 * Per key: {index, running: {child, promise}|null, timer, plan}. `index` is the
 * last good index and survives failed runs.
 */
const roots = new Map();

/** @type {vscode.DiagnosticCollection} */
let diagnostics;

function fileUri(p, relative) {
  return vscode.Uri.file(path.resolve(p.cwd, relative));
}

// Shows `s.diag` (path -> diagnostics, see navindex.js), and clears the files
// that had some from earlier and have none now. `s.shown` is the set of URIs
// (as strings) this root has published.
function publishDiagnostics(s) {
  const p = s.plan;
  const now = new Map();
  for (const [file, list] of s.diag) {
    const uri = fileUri(p, file);
    now.set(uri.toString(), uri);
    diagnostics.set(
      uri,
      list.map((d) => {
        const diagnostic = new vscode.Diagnostic(
          toRange(d.range),
          d.message,
          d.severity === 'warning'
            ? vscode.DiagnosticSeverity.Warning
            : vscode.DiagnosticSeverity.Error,
        );
        diagnostic.code = d.code;
        diagnostic.source = 'stitchwort';
        diagnostic.relatedInformation = d.related
          .filter((r) => !r.std)
          .map(
            (r) => new vscode.DiagnosticRelatedInformation(
              new vscode.Location(fileUri(p, r.path), toRange(r.range)),
              r.message,
            ),
          );
        return diagnostic;
      }),
    );
  }
  for (const [key, uri] of s.shown || []) {
    if (!now.has(key)) diagnostics.delete(uri);
  }
  s.shown = now;
}

function stateFor(p) {
  let s = roots.get(p.key);
  if (!s) {
    s = { index: null, diag: new Map(), running: null, timer: null, gen: 0, plan: p };
    roots.set(p.key, s);
  }
  s.plan = p;
  return s;
}

// Runs the CLI with `args` and calls `done(index)` with its navigation index
// (nothing if there is none). One run at a time per root: `s.running` is the
// current one, and a superseded run is killed by its own handle. Resolves when
// the run is over (also if it was killed, or failed).
function runCli(s, args, done) {
  if (s.running) s.running.child.kill();
  const p = s.plan;
  const child = cp.spawn(cliPath(), args, { cwd: p.cwd });
  const run = { child, promise: null };
  run.promise = new Promise((resolve) => {
    const out = [];
    child.stdout.on('data', (d) => out.push(d));
    child.stderr.on('data', () => {}); // diagnostics are not needed here
    child.on('error', (err) => {
      if (s.running === run) s.running = null;
      if (err.code === 'ENOENT' && !warnedMissingCli) {
        warnedMissingCli = true;
        vscode.window.showWarningMessage(
          `Stitchwort: can't run \`${cliPath()}\`. Build the CLI and put it on PATH, or set stitchwort.path.`,
        );
      }
      output.appendLine(`failed to start ${cliPath()}: ${err.message}`);
      resolve();
    });
    child.on('close', (code, signal) => {
      if (s.running === run) s.running = null;
      if (signal) return resolve(); // killed: superseded
      // Exit status 1 means check errors, and the index is still written.
      try {
        const index = JSON.parse(Buffer.concat(out).toString('utf8'));
        if (index.version === 2) done(index);
        else output.appendLine(`unsupported index version ${index.version}`);
      } catch (e) {
        output.appendLine(`no index from ${p.cwd} (exit ${code}): ${e.message}`);
      }
      resolve();
    });
  });
  s.running = run;
  return run.promise;
}

// The full run: replaces the navigation index and all the diagnostics.
function runIndex(s) {
  return runCli(s, s.plan.args, (index) => {
    s.index = index;
    s.diag = nav.diagnosticsByFile(index);
    publishDiagnostics(s);
  });
}

// A quick run of one namespace: replaces the diagnostics of the files it
// checked (see nav.applyQuick) and leaves the navigation index alone.
function runQuick(s, namespace) {
  return runCli(s, s.plan.quickArgs(namespace), (index) => {
    s.diag = nav.applyQuick(s.diag, index);
    publishDiagnostics(s);
  });
}

// What a save starts: a quick check of the saved file's namespace, then the
// full run. A newer save bumps `s.gen` and kills the run in flight, so a stale
// sequence stops.
async function runAfterSave(s, file) {
  const gen = s.gen;
  let namespace = null;
  if (s.plan.quickArgs) {
    try {
      namespace = nav.namespaceOf(fs.readFileSync(file, 'utf8'));
    } catch (e) {
      output.appendLine(`can't read ${file}: ${e.message}`);
    }
  }
  if (namespace) {
    await runQuick(s, namespace);
    if (s.gen !== gen) return;
  }
  await runIndex(s);
}

function schedule(file, immediately) {
  const s = stateFor(plan(file));
  if (s.timer) clearTimeout(s.timer);
  // A save cancels the runs in flight at once, not when the debounce ends.
  s.gen++;
  if (s.running) s.running.child.kill();
  s.timer = setTimeout(
    () => {
      s.timer = null;
      if (immediately) runIndex(s);
      else runAfterSave(s, file);
    },
    immediately ? 0 : DEBOUNCE_MS,
  );
}

// The index to answer from: the cached one, or wait for the run in flight, or
// start the first run.
async function indexFor(file) {
  const p = plan(file);
  const s = stateFor(p);
  if (!s.index) {
    if (s.timer) {
      clearTimeout(s.timer);
      s.timer = null;
    }
    // Wait for whichever run is current, including one that supersedes it.
    if (!s.running) runIndex(s);
    while (s.running) await s.running.promise;
  }
  return s.index ? { index: s.index, p } : null;
}

function toRange(r) {
  return new vscode.Range(r[0], r[1], r[2], r[3]);
}

function stdUri(std) {
  return vscode.Uri.from({ scheme: STD_SCHEME, path: '/' + std });
}

// The root each library file was last jumped to from: its index is the one to
// answer from while the file is open (a library file has refs only in the
// indexes of programs that loaded it).
const stdRoot = new Map();

function locationOf(p, t) {
  if (t.std) stdRoot.set(t.std, p.key);
  const uri = t.std ? stdUri(t.std) : vscode.Uri.file(path.resolve(p.cwd, t.path));
  return new vscode.Location(uri, toRange(t.range));
}

// Reference at a position, or the declaration whose name is there.
async function lookup(document, position) {
  if (document.uri.scheme === STD_SCHEME) return lookupInStd(document, position);
  if (document.uri.scheme !== 'file') return null;
  const found = await indexFor(document.uri.fsPath);
  if (!found) return null;
  const { index, p } = found;
  const file = nav.fileIndexByPath(index, p.indexPath);
  if (file < 0) return null;
  const ref = nav.refAt(index, file, position.line, position.character);
  return ref ? { index, p, ref } : null;
}

// The same, in a read-only library document, from the index of the program
// it was opened from (or any that loaded it).
function lookupInStd(document, position) {
  const std = nav.stdOfPath(document.uri.path);
  const candidates = [];
  for (const [key, s] of roots) if (s.index) candidates.push({ key, index: s.index, p: s.plan });
  const picked = nav.pickIndexForStd(candidates, std, stdRoot.get(std));
  if (!picked) return null;
  const { index, p } = picked.candidate;
  const ref = nav.refAt(index, picked.file, position.line, position.character);
  return ref ? { index, p, ref } : null;
}

const definitionProvider = {
  async provideDefinition(document, position) {
    const hit = await lookup(document, position);
    const t = hit && nav.targetOf(hit.index, hit.ref);
    return t ? locationOf(hit.p, t) : null;
  },
};

const referenceProvider = {
  async provideReferences(document, position, context) {
    const hit = await lookup(document, position);
    if (!hit) return [];
    return nav
      .referencesTo(hit.index, hit.ref, context.includeDeclaration)
      .map((t) => locationOf(hit.p, t));
  },
};

const workspaceSymbolProvider = {
  async provideWorkspaceSymbols(query) {
    const out = [];
    for (const s of roots.values()) {
      if (!s.index) continue;
      for (const sym of nav.workspaceSymbols(s.index, query)) {
        out.push(
          new vscode.SymbolInformation(
            sym.name,
            SYMBOL_KINDS[sym.kind] || vscode.SymbolKind.Variable,
            sym.container || '',
            new vscode.Location(fileUri(s.plan, sym.path), toRange(sym.range)),
          ),
        );
      }
    }
    return out;
  },
};

const hoverProvider = {
  async provideHover(document, position) {
    const hit = await lookup(document, position);
    if (!hit) return null;
    const h = nav.hoverOf(hit.index, hit.ref);
    if (!h || (!h.type && !h.name)) return null;
    const md = new vscode.MarkdownString();
    if (h.type) md.appendCodeblock(h.type, 'stitchwort');
    if (h.name) md.appendMarkdown(`${h.kind}  \`${h.name}\``);
    return new vscode.Hover(md, toRange(hit.ref.range));
  },
};

const SYMBOL_KINDS = {
  def: vscode.SymbolKind.Function,
  theorem: vscode.SymbolKind.Function,
  test: vscode.SymbolKind.Function,
  instance: vscode.SymbolKind.Object,
  type: vscode.SymbolKind.Struct,
  data: vscode.SymbolKind.Enum,
  record: vscode.SymbolKind.Struct,
  interface: vscode.SymbolKind.Interface,
  ctor: vscode.SymbolKind.EnumMember,
  field: vscode.SymbolKind.Field,
  ability: vscode.SymbolKind.Interface,
  op: vscode.SymbolKind.Method,
};

function toDocumentSymbol(n) {
  const sym = new vscode.DocumentSymbol(
    n.name,
    n.type || n.kind,
    SYMBOL_KINDS[n.kind] || vscode.SymbolKind.Variable,
    toRange(n.fullRange),
    toRange(n.range),
  );
  sym.children = n.children.map(toDocumentSymbol);
  return sym;
}

const symbolProvider = {
  async provideDocumentSymbols(document) {
    const found = await indexFor(document.uri.fsPath);
    if (!found) return [];
    const file = nav.fileIndexByPath(found.index, found.p.indexPath);
    return file < 0 ? [] : nav.outlineOf(found.index, file).map(toDocumentSymbol);
  },
};

// Read-only text of embedded library files: stitchwort-std:/List/Toolkit.sw.
const stdContent = {
  provideTextDocumentContent(uri) {
    const std = uri.path.replace(/^\//, '');
    return new Promise((resolve) => {
      cp.execFile(
        cliPath(),
        ['std-source', std],
        { maxBuffer: 64 * 1024 * 1024 },
        (err, stdout) => resolve(err ? `-- can't read ${std}: ${err.message}\n` : stdout),
      );
    });
  },
};

function isStitchwort(doc) {
  return doc.languageId === 'stitchwort' && doc.uri.scheme === 'file';
}

function activate(context) {
  output = vscode.window.createOutputChannel('Stitchwort');
  diagnostics = vscode.languages.createDiagnosticCollection('stitchwort');
  const selector = { language: 'stitchwort', scheme: 'file' };
  // Definition, hover and references work in the library's read-only
  // documents too (the outline is only of files of the program).
  const withLibrary = [selector, { language: 'stitchwort', scheme: STD_SCHEME }];
  context.subscriptions.push(
    output,
    vscode.languages.registerDefinitionProvider(withLibrary, definitionProvider),
    vscode.languages.registerHoverProvider(withLibrary, hoverProvider),
    vscode.languages.registerDocumentSymbolProvider(selector, symbolProvider),
    vscode.languages.registerReferenceProvider(withLibrary, referenceProvider),
    vscode.languages.registerWorkspaceSymbolProvider(workspaceSymbolProvider),
    diagnostics,
    vscode.workspace.registerTextDocumentContentProvider(STD_SCHEME, stdContent),
    vscode.workspace.onDidOpenTextDocument((d) => {
      if (isStitchwort(d)) schedule(d.uri.fsPath, true);
    }),
    vscode.workspace.onDidSaveTextDocument((d) => {
      if (isStitchwort(d)) schedule(d.uri.fsPath, false);
    }),
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration('stitchwort.path')) warnedMissingCli = false;
    }),
    {
      dispose() {
        for (const s of roots.values()) {
          if (s.timer) clearTimeout(s.timer);
          if (s.running) s.running.child.kill();
        }
        roots.clear();
      },
    },
  );
  for (const d of vscode.workspace.textDocuments) {
    if (isStitchwort(d)) schedule(d.uri.fsPath, true);
  }
}

function deactivate() {}

module.exports = { activate, deactivate };
