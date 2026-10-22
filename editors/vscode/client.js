'use strict';
// What the extension tells vscode-languageclient: how to start the server and
// which documents it serves. No `vscode` import, so it is unit tested
// (test/client.test.js) against a fake server.

const STD_SCHEME = 'stitchwort-std';
const LANGUAGE = 'stitchwort';
const CONFIG_FILE = 'stitchwort.yaml'; // what crates/driver/src/project.rs looks for

// The `stitchwort` program from the `stitchwort.path` setting: a bare name is
// looked up on PATH by the OS when the server starts.
function cliPath(configured) {
  return configured || 'stitchwort';
}

// The server is `stitchwort lsp`, speaking LSP on stdio. `cwd` is the workspace
// folder, if any; the server finds the project from the folder and the files it
// is told about.
function serverCommand(configured, cwd) {
  const options = cwd ? { cwd } : {};
  return { command: cliPath(configured), args: ['lsp'], options };
}

// Files the server answers for: project files on disk, and the read-only
// library documents (`stitchwort-std:`, text from `stitchwort std-source`).
const documentSelector = [
  { scheme: 'file', language: LANGUAGE },
  { scheme: STD_SCHEME, language: LANGUAGE },
];

// Changes the server hears about without the editor having the file open: a
// project's configuration decides which files belong to it.
const watchedGlob = `**/${CONFIG_FILE}`;

module.exports = {
  STD_SCHEME,
  LANGUAGE,
  CONFIG_FILE,
  cliPath,
  serverCommand,
  documentSelector,
  watchedGlob,
};
