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

// "Search for a proof" (D3519): the code action on a `?` carries this
// command, and the server runs the search when it is executed. The answer is
// {version, range, proofs: [{title, newText}], timeLimitMs}, or null when the text moved on
// during the search; the client picks one and applies it.
const SEARCH_PROOF = 'stitchwort.searchProof';

// The command a split or "add the missing arms" action carries, run after
// its edit: argument {uri, range}, the first new `?` in the edited text.
const SELECT_RANGE = 'stitchwort.selectRange';

// Seconds as the message words them: 5000 ms is "5", 1500 ms "1.5".
const seconds = (ms) => String(Math.round(ms / 100) / 10);

const noProofMessage = (timeLimitMs) => `No proof found within ${seconds(timeLimitMs)} s`;

// The notice for a proof inserted without asking (D3532); a long proof is
// cut so the message stays a line.
const provedMessage = (newText) =>
  `Proved by \`${newText.length > 60 ? `${newText.slice(0, 57).trimEnd()}…` : newText}\``;

// QuickPick items for the proofs of an answer, best first (the server's
// order): the proof text, and how it was found.
function proofPicks(answer) {
  return ((answer && answer.proofs) || []).map((p) => ({
    label: p.newText,
    description: (/\(([^()]*)\)$/.exec(p.title) || [])[1],
    proof: p,
  }));
}

// Whether a proof found for the document at `answer.version` can still replace
// the `?` now: the document is at the same version, or the text at the answer's
// range is still a `?`.
const proofStillApplies = (answer, currentVersion, textAtRange) =>
  answer.version === currentVersion || textAtRange === '?';

const GOAL_AT = 'stitchwort/goalAt';
const CONTEXT_AT = 'stitchwort/contextAt';
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
  return `<div class="owner">in ${escapeHtml(answer.owner)}</div>${rows}<div class="goal">⊢ ${escapeHtml(answer.goal)}</div>${computesHtml(answer.goalComputed)}`;
}

// The `computes to` line under a goal printed as written, when what it
// computes to prints differently (D3522); dimmed by the panel's style, and
// cut at 240 characters like a message's notes.
const COMPUTES_TO_LIMIT = 240;
const computesHtml = (computed) => {
  if (!computed) return '';
  const cut = [...computed].length > COMPUTES_TO_LIMIT ? [...computed].slice(0, COMPUTES_TO_LIMIT - 1).join('') + '…' : computed;
  return `<div class="computed">computes to ${escapeHtml(cut)}</div>`;
};

// The context list of an answer, as rows.
const hypothesisRows = (context) =>
  (context || [])
    .map((h) => {
      const value = h.value === undefined ? '' : ` := <span class="v">${escapeHtml(h.value)}</span>`;
      return `<div class="h"><span class="n">${escapeHtml(h.name)}</span>: ${escapeHtml(h.type)}${value}</div>`;
    })
    .join('');

// The body of the Goals panel for the server's `stitchwort/contextAt` answer
// ({range, type, checked, kind, hasType, locals, declaration, step}): `⊢ T`
// for a proof being checked against a goal, `expected T` for a program
// expression checked against a type (and `has type U` below it when the type
// found differs, D3499), and `has type T` where there was no expected type.
// On a step of a proof (a rewrite rule, an arm, a calc line, a parameter, a
// `let`, a branch of `if h:`) the goal before it, and after it in bold; the
// names the step brought into scope are marked `+`.
function contextHtml(answer) {
  if (!answer) return goalHtml(null);
  const step = answer.step;
  const where = [answer.declaration && `\`${answer.declaration}\``, step && step.description]
    .filter(Boolean)
    .join(', ');
  const owner = where ? `<div class="owner">in ${escapeHtml(where)}</div>` : '';
  const added = new Set((step && step.adds) || []);
  const rows = (answer.locals || [])
    .map((h) => {
      const value = h.value === undefined ? '' : ` := <span class="v">${escapeHtml(h.value)}</span>`;
      const mark = added.has(h.name) ? ['<div class="h added">+ ', '</div>'] : ['<div class="h">', '</div>'];
      return `${mark[0]}<span class="n">${escapeHtml(h.name)}</span>: ${escapeHtml(h.type)}${value}${mark[1]}`;
    })
    .join('');
  if (step) {
    const sign = step.target ? `${step.target}: ` : step.kind === 'proof' ? '⊢ ' : 'expected ';
    const line = (cls, label, text) =>
      `<div class="${cls}"><span class="label">${label}</span>${escapeHtml(text)}</div>`;
    const parts = [];
    if (step.form === 'calcLine') {
      if (step.before) parts.push(line('before', 'so far ', step.before), computesHtml(step.beforeComputed));
      parts.push(line('goal', `line ${sign}`, step.after), computesHtml(step.afterComputed));
    } else if (step.form === 'match' || step.form === 'statement') {
      parts.push(line('goal', sign, step.after), computesHtml(step.afterComputed));
    } else {
      if (step.before) parts.push(line('before', `before ${sign}`, step.before), computesHtml(step.beforeComputed));
      if (step.rule) parts.push(line('rule', 'rule ', step.rule));
      parts.push(line('goal', `after ${sign}`, step.after), computesHtml(step.afterComputed));
    }
    return `${owner}${rows}${parts.join('')}`;
  }
  const label = !answer.checked ? 'has type ' : answer.kind === 'proof' ? '⊢ ' : 'expected ';
  const found =
    answer.checked && answer.hasType ? `<div class="found">has type ${escapeHtml(answer.hasType)}</div>` : '';
  return `${owner}${rows}<div class="goal">${label}${escapeHtml(answer.type)}</div>${computesHtml(answer.typeComputed)}${found}`;
}

const positionInRange = (p, r) =>
  !(p.line < r.start.line || (p.line === r.start.line && p.character < r.start.character)) &&
  !(p.line > r.end.line || (p.line === r.end.line && p.character > r.end.character));

// Whether a `goalAt` answer is for a hole under `position`: the server also
// answers with the nearest hole of the declaration, which is only the second
// choice when the cursor is somewhere else.
const goalIsHere = (goal, position) => !!goal && !!goal.range && positionInRange(position, goal.range);

// Which answer the panel shows: the hole under the cursor, else the
// expression's context, else the declaration's nearest hole; null when none.
function panelBody(goal, context, position) {
  if (goalIsHere(goal, position)) return goalHtml(goal);
  if (context) return contextHtml(context);
  if (goal) return goalHtml(goal);
  return null;
}

// How a missing answer is shown: the last body kept, dimmed with a note, or
// the plain "none" note when nothing was shown before.
function staleBody(last) {
  if (!last) return goalHtml(null);
  return `<div class="stale"><p class="note">Nothing at the cursor; the last answer:</p>${last}</div>`;
}

module.exports = {
  SEARCH_PROOF,
  SELECT_RANGE,
  noProofMessage,
  provedMessage,
  proofPicks,
  proofStillApplies,
  serverSettings,
  CONTEXT_AT,
  contextHtml,
  panelBody,
  staleBody,
  goalIsHere,
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
