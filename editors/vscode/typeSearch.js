'use strict';
// "Stitchwort: Search by Type…" (docs/proposals/editor-type-search.md, stage
// 1): a quick pick whose results update as you type, from the server's
// `stitchwort/search`, scoped to the file you're in. Enter writes the name at
// the cursor (or over the selection, or the `?` the search started from) and
// adds the import it needs, as one edit; the row's buttons go to the
// definition or copy `name : type`. The rows, the prefill and the scheduling
// are plain functions in client.js, tested there.

const vscode = require('vscode');
const cfg = require('./client');

const COMMAND = 'stitchwort.searchByType';
const PLACEHOLDER = 'a type, a statement, or "name": Nat -> List _ -> List _';

// The point of a VS Code position or range, as the server writes them.
const point = (p) => ({ line: p.line, character: p.character });
const plainRange = (r) => ({ start: point(r.start), end: point(r.end) });

// Where the search starts from: the active `.sw` editor, else any open `.sw`
// file (whose scope the search then has, and Enter goes to the definition).
function startingPoint() {
  const editor = vscode.window.activeTextEditor;
  if (editor && editor.document.languageId === cfg.LANGUAGE) return { editor, document: editor.document };
  const document = vscode.workspace.textDocuments.find(
    (d) => d.languageId === cfg.LANGUAGE && d.uri.scheme === 'file',
  );
  return document ? { document } : undefined;
}

// What the box starts with, and what Enter replaces: the `?` under the cursor
// (with its goal), else the selection (with its type, or its text).
async function prefill(client, editor) {
  const uri = editor.document.uri.toString();
  const selection = editor.selection;
  const position = selection.active;
  if (selection.isEmpty) {
    const goal = await client
      .sendRequest(cfg.GOAL_AT, { textDocument: { uri }, position: point(position) })
      .catch(() => null);
    if (cfg.goalIsHere(goal, position)) return { text: cfg.typeSearchPrefill({ goal }), target: goal.range };
    return { text: '', target: plainRange(selection) };
  }
  const params = cfg.hoverRangeParams(uri, position, plainRange(selection));
  const hover = params ? await client.sendRequest('textDocument/hover', params).catch(() => null) : null;
  const text = cfg.typeSearchPrefill({
    hover,
    selection: plainRange(selection),
    selectedText: editor.document.getText(selection),
  });
  return { text, target: plainRange(selection) };
}

// Writes `result` into `editor` over `target`, with its import, in one edit
// (one undo), and puts the cursor after the name.
async function insert(client, editor, result, target) {
  const document = editor.document;
  const edits = cfg.typeSearchEdits(result, target).map((e) => ({
    range: client.protocol2CodeConverter.asRange(e.range),
    newText: e.newText,
  }));
  const start = document.offsetAt(edits[0].range.start);
  // The imports go above the name, so they move where it ends up.
  const shift = edits
    .slice(1)
    .filter((e) => document.offsetAt(e.range.start) <= start)
    .reduce((n, e) => n + e.newText.length - (document.offsetAt(e.range.end) - document.offsetAt(e.range.start)), 0);
  const applied = await editor.edit((builder) => {
    for (const e of edits) builder.replace(e.range, e.newText);
  });
  if (!applied) return;
  const end = document.positionAt(start + shift + edits[0].newText.length);
  editor.selection = new vscode.Selection(end, end);
}

async function goTo(client, result) {
  const location = result.location;
  if (!location) return;
  const document = await vscode.workspace.openTextDocument(vscode.Uri.parse(location.uri));
  await vscode.window.showTextDocument(document, { selection: client.protocol2CodeConverter.asRange(location.range) });
}

const GO_TO = { icon: 'go-to-file', tooltip: 'Go to the definition' };
const COPY = { icon: 'copy', tooltip: 'Copy name : type' };

async function searchByType(getClient) {
  const client = await getClient().catch(() => undefined);
  if (!client) return;
  const from = startingPoint();
  if (!from) {
    vscode.window.showInformationMessage('Stitchwort: open a .sw file to search by type from it.');
    return;
  }
  const uri = from.document.uri.toString();
  const start = from.editor ? await prefill(client, from.editor) : { text: '' };
  const live = vscode.workspace.getConfiguration('stitchwort').get('typeSearch.live') !== false;
  const pick = vscode.window.createQuickPick();
  pick.title = 'Search by Type';
  pick.placeholder = from.editor ? PLACEHOLDER : `${PLACEHOLDER} (Enter goes to the definition)`;
  pick.matchOnDescription = false;
  pick.matchOnDetail = false;
  pick.value = start.text;
  const buttons = [GO_TO, COPY].map((b) => ({ iconPath: new vscode.ThemeIcon(b.icon), tooltip: b.tooltip }));
  const searcher = cfg.latestWins({
    run(query) {
      const source = new vscode.CancellationTokenSource();
      const promise = client.sendRequest(cfg.TYPE_SEARCH, { textDocument: { uri }, query }, source.token);
      return { promise, cancel: () => source.cancel() };
    },
    // A failed or superseded search leaves the last results listed.
    show(query, answer) {
      if (!answer) return;
      pick.title = cfg.typeSearchTitle(answer, query);
      if (answer.error) return;
      pick.items = cfg.typeSearchItems(answer).map((item) => ({ ...item, buttons }));
    },
    busy(on) {
      pick.busy = on;
    },
  });
  pick.onDidChangeValue((value) => {
    const query = value.trim();
    if (!query) {
      pick.items = [];
      pick.title = 'Search by Type';
    } else if (live) searcher.input(query);
  });
  pick.onDidAccept(async () => {
    const query = pick.value.trim();
    // Results for an older query: search for this one first.
    if (query && !searcher.settled(query)) return searcher.now(query);
    const item = pick.selectedItems[0] || pick.activeItems[0];
    if (!item) return;
    pick.hide();
    if (from.editor && start.target) await insert(client, from.editor, item.result, start.target);
    else await goTo(client, item.result);
  });
  pick.onDidTriggerItemButton(async ({ item, button }) => {
    if (button.tooltip === GO_TO.tooltip) {
      pick.hide();
      await goTo(client, item.result);
    } else if (button.tooltip === COPY.tooltip) {
      await vscode.env.clipboard.writeText(`${item.result.short || item.result.name} : ${item.result.type}`);
    }
  });
  pick.onDidHide(() => {
    searcher.dispose();
    pick.dispose();
  });
  pick.show();
  if (start.text.trim()) searcher.now(start.text.trim());
}

// "Search by type for this goal" beside a `?`'s other actions: offered where
// the editor shows an open goal, from the diagnostics it already has.
const goalActions = {
  provideCodeActions(document, range) {
    const atGoal = vscode.languages
      .getDiagnostics(document.uri)
      .some((d) => d.code === 'GOAL' && d.range.contains(range.start));
    if (!atGoal) return [];
    const action = new vscode.CodeAction('Search by type for this goal', vscode.CodeActionKind.Empty);
    action.command = { command: COMMAND, title: 'Search by type for this goal' };
    return [action];
  },
};

function register(context, getClient) {
  context.subscriptions.push(
    vscode.commands.registerCommand(COMMAND, () => searchByType(getClient)),
    vscode.languages.registerCodeActionsProvider(cfg.documentSelector, goalActions),
  );
}

module.exports = { register };
