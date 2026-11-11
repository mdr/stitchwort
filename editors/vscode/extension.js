'use strict';
// Stitchwort VS Code extension: a thin client for `stitchwort lsp` (see
// docs/proposals/language-server.md). The server does diagnostics, definition,
// hover, references and the outline; `vscode-languageclient` carries them.
// What stays here: starting the server, and the text of library files
// (`stitchwort-std:`, from `stitchwort std-source`), and the run icons and the
// Testing panel (runs.js), which run the CLI. The grammar and language
// configuration are declarative, in package.json.

const vscode = require('vscode');
const cp = require('child_process');
const { LanguageClient } = require('vscode-languageclient/node');
const cfg = require('./client');
const runs = require('./runs');

/** @type {LanguageClient | undefined} */
let client;
/** @type {Promise<void> | undefined} resolves when the server is up */
let clientStarted;
let warnedMissingCli = false;

function configuredPath() {
  return vscode.workspace.getConfiguration('stitchwort').get('path');
}

// The settings the server reads, from the user's configuration.
function serverSettings() {
  const config = vscode.workspace.getConfiguration('stitchwort');
  return cfg.serverSettings((name) => config.get(name));
}

function startClient() {
  const folder = (vscode.workspace.workspaceFolders || [])[0];
  const s = cfg.serverCommand(configuredPath(), folder && folder.uri.fsPath);
  const serverOptions = {
    command: s.command,
    args: s.args,
    // No `transport`: an Executable without one still talks over stdio, while
    // TransportKind.stdio appends `--stdio`, which `stitchwort lsp` rejects.
    options: s.options,
  };
  const clientOptions = {
    documentSelector: cfg.documentSelector,
    initializationOptions: serverSettings(),
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher(cfg.watchedGlob),
    },
    outputChannelName: 'Stitchwort',
    middleware: {
      // Hovering inside a selection asks for the selected expression's type.
      provideHover(document, position, token, next) {
        const editor = vscode.window.activeTextEditor;
        const params =
          editor &&
          editor.document === document &&
          cfg.hoverRangeParams(document.uri.toString(), position, editor.selection);
        if (!params) return next(document, position, token);
        return client.sendRequest('textDocument/hover', params, token).then(
          (result) => (result ? client.protocol2CodeConverter.asHover(result) : null),
          () => next(document, position, token),
        );
      },
    },
  };
  client = new LanguageClient('stitchwort', 'Stitchwort', serverOptions, clientOptions);
  clientStarted = client.start();
  clientStarted.catch((err) => {
    if (!warnedMissingCli) {
      warnedMissingCli = true;
      vscode.window.showWarningMessage(
        `Stitchwort: can't run \`${s.command} lsp\` (${err.message}). Build the CLI and put it on PATH, or set stitchwort.path.`,
      );
    }
  });
}

async function restartServer() {
  warnedMissingCli = false;
  await stopClient();
  startClient();
}

function stopClient() {
  const c = client;
  client = undefined;
  return c ? c.stop() : undefined;
}

// Read-only text of embedded library files: stitchwort-std:List/Toolkit.sw.
// Used only when the server's std is the embedded bundle; with a std
// directory it names the real files (`file:` URIs) instead.
const stdContent = {
  provideTextDocumentContent(uri) {
    const std = uri.path.replace(/^\//, '');
    return new Promise((resolve) => {
      cp.execFile(
        cfg.cliPath(configuredPath()),
        ['std-source', std],
        { maxBuffer: 64 * 1024 * 1024 },
        (err, stdout) => resolve(err ? `-- can't read ${std}: ${err.message}\n` : stdout),
      );
    });
  },
};

// The Goals panel follows the cursor everywhere (docs/proposals/
// goal-at-any-point.md, stage 1). `stitchwort/goalAt` answers from the goals
// the server already published, so it is cheap and asked 150 ms after the
// cursor or the text moves. When the cursor isn't on a hole, the goal or
// expected type of the expression there is `stitchwort/contextAt`, which
// checks the file again (0.3 to 1.6 s on real files), so it is asked only
// after the cursor has rested 300 ms. An answer that a later move has
// overtaken is dropped, and the last answer stays on screen until the next
// arrives.
const GOAL_DEBOUNCE_MS = 150;
const CONTEXT_DEBOUNCE_MS = 300;
/** @type {vscode.WebviewPanel | undefined} */
let goalPanel;
let goalTimer;
let contextTimer;
let goalAsked = 0;
/** The body last shown for an answer, kept while the next is pending. */
let lastBody;

const goalPage = (body) => `<!doctype html><html><head><meta charset="utf-8">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline';">
<style>
body { font-family: var(--vscode-editor-font-family, monospace); font-size: var(--vscode-editor-font-size, 13px); padding: 8px; }
.owner { opacity: 0.7; margin-bottom: 6px; }
.h, .goal { white-space: pre-wrap; margin: 2px 0; }
.n { color: var(--vscode-symbolIcon-variableForeground, var(--vscode-textLink-foreground)); }
.v { opacity: 0.8; }
.goal { border-top: 1px solid var(--vscode-panel-border); margin-top: 8px; padding-top: 8px; font-weight: bold; }
.none, .stale { opacity: 0.6; }
.note { font-style: italic; margin: 0 0 6px; }
</style></head><body>${body}</body></html>`;

function showGoal(body) {
  lastBody = body;
  if (goalPanel) goalPanel.webview.html = goalPage(body);
}

// An answer from the server, or null if there is none or the request failed
// (a request the server superseded fails too).
async function ask(method, editor) {
  try {
    return await client.sendRequest(method, {
      textDocument: { uri: editor.document.uri.toString() },
      position: { line: editor.selection.active.line, character: editor.selection.active.character },
    });
  } catch (err) {
    return null;
  }
}

async function refreshGoal() {
  const editor = vscode.window.activeTextEditor;
  if (!goalPanel || !client || !editor || editor.document.languageId !== cfg.LANGUAGE) return;
  const asked = goalAsked;
  const goal = await ask(cfg.GOAL_AT, editor);
  // A newer question was sent meanwhile: its answer is the one to show.
  if (asked !== goalAsked) return;
  const position = editor.selection.active;
  if (cfg.goalIsHere(goal, position)) return showGoal(cfg.goalHtml(goal));
  // Not on a hole: the nearest hole of the declaration is only a fallback.
  // Meanwhile the previous answer stays.
  clearTimeout(contextTimer);
  contextTimer = setTimeout(async () => {
    const context = await ask(cfg.CONTEXT_AT, editor);
    if (asked !== goalAsked || !goalPanel) return;
    const body = cfg.panelBody(goal, context, position);
    showGoal(body === null ? cfg.staleBody(lastBody) : body);
  }, CONTEXT_DEBOUNCE_MS - GOAL_DEBOUNCE_MS);
}

function scheduleGoal() {
  if (!goalPanel) return;
  clearTimeout(goalTimer);
  clearTimeout(contextTimer);
  goalAsked++; // answers to questions sent before this move are dropped
  goalTimer = setTimeout(refreshGoal, GOAL_DEBOUNCE_MS);
}

function openGoalPanel() {
  if (goalPanel) {
    goalPanel.reveal(undefined, true);
  } else {
    goalPanel = vscode.window.createWebviewPanel(
      'stitchwortGoals',
      'Stitchwort Goals',
      { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
      { enableScripts: false },
    );
    goalPanel.onDidDispose(() => {
      goalPanel = undefined;
      lastBody = undefined;
      clearTimeout(goalTimer);
      clearTimeout(contextTimer);
    });
  }
  showGoal(cfg.goalHtml(null));
  refreshGoal();
}

// With `stitchwort.goals.openAutomatically`, the Goals panel opens when a
// `.sw` file with a `?` is opened (once per file, and not again after the
// panel is closed by hand).
const goalsOffered = new Set();
function openGoalsFor(document) {
  if (!document || document.languageId !== cfg.LANGUAGE || document.uri.scheme !== 'file') return;
  const key = document.uri.toString();
  if (goalsOffered.has(key)) return;
  if (!vscode.workspace.getConfiguration('stitchwort').get('goals.openAutomatically')) return;
  if (!cfg.mentionsGoal(document.getText())) return;
  goalsOffered.add(key);
  if (!goalPanel) openGoalPanel();
}

function activate(context) {
  context.subscriptions.push(
    vscode.commands.registerCommand('stitchwort.showGoals', openGoalPanel),
    vscode.commands.registerCommand('stitchwort.restartServer', restartServer),
    vscode.window.onDidChangeTextEditorSelection(scheduleGoal),
    vscode.window.onDidChangeActiveTextEditor(scheduleGoal),
    // Diagnostics (so goals) arrive a moment after the text changes.
    vscode.languages.onDidChangeDiagnostics(scheduleGoal),
    vscode.workspace.registerTextDocumentContentProvider(cfg.STD_SCHEME, stdContent),
    vscode.workspace.onDidChangeConfiguration(async (e) => {
      if (e.affectsConfiguration('stitchwort.path')) {
        await restartServer();
      } else if (e.affectsConfiguration('stitchwort') && client) {
        // The server asks the editor to redraw hints, lenses and colours.
        client.sendNotification('workspace/didChangeConfiguration', {
          settings: { stitchwort: serverSettings() },
        });
      }
    }),
    vscode.workspace.onDidOpenTextDocument(openGoalsFor),
    vscode.window.onDidChangeActiveTextEditor((editor) => editor && openGoalsFor(editor.document)),
    { dispose: stopClient },
  );
  startClient();
  for (const document of vscode.workspace.textDocuments) openGoalsFor(document);
  // The server's list of a file's tests; rejects when there's no server, and
  // the Testing panel then reads the text instead.
  const serverTests = async (uri) => {
    const c = client;
    if (!c || !clientStarted) throw new Error('no server');
    await clientStarted;
    return c.sendRequest(cfg.TESTS, { textDocument: { uri } });
  };
  runs.register(context, () => cfg.cliPath(configuredPath()), serverTests);
}

function deactivate() {
  return stopClient();
}

module.exports = { activate, deactivate };
