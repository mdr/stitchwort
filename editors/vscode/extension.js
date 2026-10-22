'use strict';
// Stitchwort VS Code extension: a thin client for `stitchwort lsp` (see
// docs/proposals/language-server.md). The server does diagnostics, definition,
// hover, references and the outline; `vscode-languageclient` carries them.
// What stays here: starting the server, and the text of library files
// (`stitchwort-std:`, from `stitchwort std-source`). The grammar and language
// configuration are declarative, in package.json.

const vscode = require('vscode');
const cp = require('child_process');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');
const cfg = require('./client');

/** @type {LanguageClient | undefined} */
let client;
let warnedMissingCli = false;

function configuredPath() {
  return vscode.workspace.getConfiguration('stitchwort').get('path');
}

function startClient() {
  const folder = (vscode.workspace.workspaceFolders || [])[0];
  const s = cfg.serverCommand(configuredPath(), folder && folder.uri.fsPath);
  const serverOptions = {
    command: s.command,
    args: s.args,
    options: s.options,
    transport: TransportKind.stdio,
  };
  const clientOptions = {
    documentSelector: cfg.documentSelector,
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher(cfg.watchedGlob),
    },
    outputChannelName: 'Stitchwort',
  };
  client = new LanguageClient('stitchwort', 'Stitchwort', serverOptions, clientOptions);
  client.start().catch((err) => {
    if (!warnedMissingCli) {
      warnedMissingCli = true;
      vscode.window.showWarningMessage(
        `Stitchwort: can't run \`${s.command} lsp\` (${err.message}). Build the CLI and put it on PATH, or set stitchwort.path.`,
      );
    }
  });
}

function stopClient() {
  const c = client;
  client = undefined;
  return c ? c.stop() : undefined;
}

// Read-only text of embedded library files: stitchwort-std:/List/Toolkit.sw.
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

function activate(context) {
  context.subscriptions.push(
    vscode.workspace.registerTextDocumentContentProvider(cfg.STD_SCHEME, stdContent),
    vscode.workspace.onDidChangeConfiguration(async (e) => {
      if (!e.affectsConfiguration('stitchwort.path')) return;
      warnedMissingCli = false;
      await stopClient();
      startClient();
    }),
    { dispose: stopClient },
  );
  startClient();
}

function deactivate() {
  return stopClient();
}

module.exports = { activate, deactivate };
