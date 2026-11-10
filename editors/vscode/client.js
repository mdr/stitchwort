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

// Files the server answers for: files on disk (a library file opened from
// navigation is one: the server reads std from a directory, and treats such a
// file as read-only library source, with navigation and hover but no
// diagnostics), and the read-only `stitchwort-std:` documents it names only
// when std is the embedded bundle (text from `stitchwort std-source`).
const documentSelector = [
  { scheme: 'file', language: LANGUAGE },
  { scheme: STD_SCHEME, language: LANGUAGE },
];

// Changes the server hears about without the editor having the file open: a
// project's configuration decides which files belong to it, and a source file
// changed on disk (a branch switch, `fmt`) is reloaded.
const watchedGlobs = [`**/${CONFIG_FILE}`, '**/*.sw'];
const watchedGlob = `{${watchedGlobs.join(',')}}`;

const before = (a, b) => a.line < b.line || (a.line === b.line && a.character < b.character);

// rust-analyzer's "hover range": when the hover position is inside a non-empty
// selection, the server answers with the type of the selected expression if the
// request carries the selection as `range`. `selection` and `position` are
// plain {line, character} pairs (`start`, `end` for the selection). Returns the
// request's params, or undefined for an ordinary hover.
function hoverRangeParams(uri, position, selection) {
  if (!selection) return undefined;
  const { start, end } = selection;
  if (!before(start, end)) return undefined; // empty
  if (before(position, start) || before(end, position)) return undefined;
  const at = (p) => ({ line: p.line, character: p.character });
  return {
    textDocument: { uri },
    position: at(position),
    range: { start: at(start), end: at(end) },
  };
}

// The settings the server reads (crates/lsp `Settings`), as the server wants
// them: sent in `initializationOptions` and, when one changes, in
// `workspace/didChangeConfiguration`. `get(name)` reads `stitchwort.<name>`;
// a setting that is unset is left out so the server keeps its default.
// (`stitchwort.goals.openAutomatically` and `stitchwort.path` are the
// extension's own.)
function serverSettings(get) {
  const pick = (names) => {
    const out = {};
    for (const [key, name] of Object.entries(names)) {
      const value = get(name);
      if (value !== undefined && value !== null) out[key] = value;
    }
    return out;
  };
  return {
    inlayHints: pick({ letTypes: 'inlayHints.letTypes' }),
    codeLens: pick({ run: 'codeLens.run' }),
    proofSearch: pick({ enabled: 'proofSearch.enabled', timeLimitMs: 'proofSearch.timeLimitMs' }),
    ...pick({ semanticColours: 'semanticColours' }),
  };
}

// Whether `text` has a goal hole to show: a `?` outside a `--` comment and
// outside a string, as a rough scan (the server decides what is a goal).
function mentionsGoal(text) {
  for (const line of String(text).split('\n')) {
    let inString = false;
    for (let i = 0; i < line.length; i++) {
      const ch = line[i];
      if (inString) {
        if (ch === '\\') i++;
        else if (ch === '"') inString = false;
      } else if (ch === '"') inString = true;
      else if (ch === '-' && line[i + 1] === '-') break;
      else if (ch === '?') return true;
    }
  }
  return false;
}

const GOAL_AT = 'stitchwort/goalAt';
const TESTS = 'stitchwort/tests';

const escapeHtml = (s) =>
  String(s).replace(/[&<>"']/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[ch]);

// The body of the Goals panel for the server's `stitchwort/goalAt` answer
// ({owner, goal, context: [{name, type, value?}]}, or null/undefined when the
// cursor is not at a goal). Everything from the server is escaped.
function goalHtml(answer) {
  if (!answer) return '<p class="none">No open goal at the cursor.</p>';
  const rows = (answer.context || [])
    .map((h) => {
      const value = h.value === undefined ? '' : ` := <span class="v">${escapeHtml(h.value)}</span>`;
      return `<div class="h"><span class="n">${escapeHtml(h.name)}</span>: ${escapeHtml(h.type)}${value}</div>`;
    })
    .join('');
  return `<div class="owner">in ${escapeHtml(answer.owner)}</div>${rows}<div class="goal">⊢ ${escapeHtml(answer.goal)}</div>`;
}

module.exports = {
  serverSettings,
  mentionsGoal,
  GOAL_AT,
  TESTS,
  escapeHtml,
  goalHtml,
  hoverRangeParams,
  STD_SCHEME,
  LANGUAGE,
  CONFIG_FILE,
  cliPath,
  serverCommand,
  documentSelector,
  watchedGlob,
};
