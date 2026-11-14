'use strict';
// The client's configuration (client.js) against a fake server speaking the
// standard methods the real one offers. The VS Code glue in extension.js is
// not covered here; see "End-to-end check" in README.md.
const test = require('node:test');
const assert = require('node:assert');
const cp = require('node:child_process');
const path = require('node:path');
const { createMessageConnection, StreamMessageReader, StreamMessageWriter } = require('vscode-jsonrpc/node');
const cfg = require('../client');

const FAKE = path.join(__dirname, 'fake-server.js');

test('server command: the configured program with `lsp`, PATH name by default', () => {
  assert.deepStrictEqual(cfg.serverCommand(undefined), { command: 'stitchwort', args: ['lsp'], options: {} });
  assert.deepStrictEqual(cfg.serverCommand('', '/w'), { command: 'stitchwort', args: ['lsp'], options: { cwd: '/w' } });
  assert.strictEqual(cfg.serverCommand('/opt/sw/stitchwort').command, '/opt/sw/stitchwort');
  assert.strictEqual(cfg.cliPath('/x/stitchwort'), '/x/stitchwort');
});

test('document selector: files and library documents of the language', () => {
  assert.deepStrictEqual(cfg.documentSelector, [
    { scheme: 'file', language: 'stitchwort' },
    { scheme: 'stitchwort-std', language: 'stitchwort' },
  ]);
  assert.strictEqual(cfg.watchedGlob, '{**/stitchwort.yaml,**/*.sw}');
});

// Starts the fake the way the client starts the real server (command, args).
function startFake() {
  const s = cfg.serverCommand(process.execPath);
  const child = cp.spawn(s.command, [FAKE, ...s.args], { stdio: ['pipe', 'pipe', 'inherit'] });
  const conn = createMessageConnection(new StreamMessageReader(child.stdout), new StreamMessageWriter(child.stdin));
  const published = [];
  conn.onNotification('textDocument/publishDiagnostics', (p) => published.push(p));
  conn.listen();
  return { child, conn, published };
}

async function until(fn) {
  for (let i = 0; i < 300; i++) {
    if (fn()) return;
    await new Promise((r) => setTimeout(r, 10));
  }
  assert.fail('timed out');
}

test('fake server answers the standard methods, with full-text sync', async () => {
  const { child, conn, published } = startFake();
  const uri = 'file:///p/a.sw';
  const init = await conn.sendRequest('initialize', { processId: null, rootUri: 'file:///p', capabilities: {} });
  assert.strictEqual(init.capabilities.textDocumentSync, 1);
  await conn.sendNotification('initialized', {});

  await conn.sendNotification('textDocument/didOpen', {
    textDocument: { uri, languageId: 'stitchwort', version: 1, text: 'abc' },
  });
  await until(() => published.length === 1);
  assert.strictEqual(published[0].diagnostics[0].message, 'length 3');

  await conn.sendNotification('textDocument/didChange', {
    textDocument: { uri, version: 2 },
    contentChanges: [{ text: 'abcdef' }],
  });
  await until(() => published.length === 2);
  assert.strictEqual(published[1].diagnostics[0].message, 'length 6');

  const td = { textDocument: { uri }, position: { line: 0, character: 0 } };
  assert.deepStrictEqual((await conn.sendRequest('textDocument/definition', td)).range.start, { line: 2, character: 4 });
  assert.match((await conn.sendRequest('textDocument/hover', td)).contents.value, /Nat/);
  const refs = await conn.sendRequest('textDocument/references', { ...td, context: { includeDeclaration: true } });
  assert.strictEqual(refs.length, 2);
  assert.strictEqual((await conn.sendRequest('textDocument/documentSymbol', { textDocument: { uri } }))[0].name, 'f');

  await conn.sendNotification('textDocument/didClose', { textDocument: { uri } });
  await until(() => published.length === 3);
  assert.deepStrictEqual(published[2].diagnostics, []);

  await conn.sendRequest('shutdown');
  await conn.sendNotification('exit');
  await new Promise((r) => child.on('close', r));
});

test('hover range: only a position inside a non-empty selection sends the selection', () => {
  const p = (line, character) => ({ line, character });
  const sel = { start: p(2, 10), end: p(2, 20) };
  assert.deepStrictEqual(cfg.hoverRangeParams('file:///a.sw', p(2, 12), sel), {
    textDocument: { uri: 'file:///a.sw' },
    position: p(2, 12),
    range: { start: p(2, 10), end: p(2, 20) },
  });
  assert.ok(cfg.hoverRangeParams('u', p(2, 10), sel), 'at the start');
  assert.ok(cfg.hoverRangeParams('u', p(2, 20), sel), 'at the end');
  assert.strictEqual(cfg.hoverRangeParams('u', p(2, 9), sel), undefined);
  assert.strictEqual(cfg.hoverRangeParams('u', p(3, 0), sel), undefined);
  assert.strictEqual(cfg.hoverRangeParams('u', p(2, 10), { start: p(2, 10), end: p(2, 10) }), undefined);
  assert.strictEqual(cfg.hoverRangeParams('u', p(2, 10), undefined), undefined);
});

test('goals panel: the goalAt answer as escaped html, or a note when there is none', () => {
  assert.strictEqual(cfg.GOAL_AT, 'stitchwort/goalAt');
  assert.match(cfg.goalHtml(null), /No open goal/);
  const html = cfg.goalHtml({
    owner: '`f`',
    goal: 'a < b',
    context: [{ name: 'n', type: 'Nat' }, { name: 't', type: 'Nat', value: 'n + 1' }],
  });
  assert.match(html, /in `f`/);
  assert.match(html, /<span class="n">n<\/span>: Nat<\/div>/);
  assert.match(html, /<span class="n">t<\/span>: Nat := <span class="v">n \+ 1<\/span>/);
  assert.match(html, /⊢ a &lt; b/);
});

test('goals panel: a context answer is a goal in a proof, an expected type in a program', () => {
  assert.strictEqual(cfg.CONTEXT_AT, 'stitchwort/contextAt');
  const locals = [{ name: 'n', type: 'Nat' }];
  const proof = cfg.contextHtml({ type: 'a < b', checked: true, kind: 'proof', locals });
  assert.match(proof, /<span class="n">n<\/span>: Nat/);
  assert.match(proof, /⊢ a &lt; b/);
  const program = cfg.contextHtml({ type: 'List <Nat>', checked: true, kind: 'program', locals });
  assert.match(program, /expected List &lt;Nat&gt;/);
  assert.doesNotMatch(program, /⊢/);
  // No expected type: the type found.
  assert.match(cfg.contextHtml({ type: 'Nat', checked: false, kind: 'program', locals: [] }), /has type Nat/);
  assert.match(cfg.contextHtml(null), /No open goal/);
});

test('goals panel: a goal as written has a dimmed computes-to line under it, cut at 240 characters', () => {
  const html = cfg.goalHtml({ owner: '`f`', goal: 'beats Rock Rock = False', goalComputed: 'False = False', context: [] });
  assert.match(html, /⊢ beats Rock Rock = False<\/div><div class="computed">computes to False = False<\/div>/);
  assert.doesNotMatch(cfg.goalHtml({ owner: 'f', goal: 'a', goalComputed: null, context: [] }), /computes to/);
  const step = cfg.contextHtml({
    type: 'x', checked: true, kind: 'proof', locals: [],
    step: { form: 'arm', kind: 'proof', before: 'beats m m = False', after: 'beats Rock Rock = False', afterComputed: 'False = False' },
  });
  assert.match(step, /after ⊢ <\/span>beats Rock Rock = False<\/div><div class="computed">computes to False = False/);
  const long = cfg.contextHtml({ type: 'a', typeComputed: 'x'.repeat(300), checked: true, kind: 'proof', locals: [] });
  assert.match(long, /computes to x{239}…</);
});

test('goals panel: expected T and has type U when they differ', () => {
  const body = cfg.contextHtml({
    type: 'Int', checked: true, kind: 'program', hasType: 'Nat', locals: [], declaration: 'widen',
  });
  assert.match(body, /in `widen`/);
  assert.match(body, /expected Int/);
  assert.match(body, /has type Nat/);
  assert.doesNotMatch(cfg.contextHtml({ type: 'Nat', checked: true, kind: 'program', locals: [] }), /has type/);
});

test('goals panel: a step shows the goal before and after, and what it added', () => {
  const rule = cfg.contextHtml({
    type: '0 = 0', checked: true, kind: 'proof', declaration: 'multN0M0',
    locals: [{ name: 'q', type: 'Nat' }],
    step: { form: 'rewriteRule', description: 'rule 2 of 2 of `rewrite`', kind: 'proof',
      before: 'q * 0 = 0', after: '0 = 0', rule: 'q * 0 = 0', adds: [] },
  });
  assert.match(rule, /in `multN0M0`, rule 2 of 2 of `rewrite`/);
  assert.match(rule, /before ⊢ <\/span>q \* 0 = 0/);
  assert.match(rule, /rule <\/span>q \* 0 = 0/);
  assert.match(rule, /after ⊢ <\/span>0 = 0/);
  const arm = cfg.contextHtml({
    type: 'Succ k = Succ k', checked: true, kind: 'proof',
    locals: [{ name: 'k', type: 'Nat' }],
    step: { form: 'arm', description: 'arm 2 of 2, `| Succ k`', kind: 'proof',
      before: 'n = n', after: 'Succ k = Succ k', adds: ['k'] },
  });
  assert.match(arm, /class="h added">\+ <span class="n">k<\/span>/);
  const line = cfg.contextHtml({
    type: 'b = c', checked: true, kind: 'proof', locals: [],
    step: { form: 'calcLine', description: 'line 2 of 2 of `calc`', kind: 'proof',
      before: 'a = b', after: 'b = c', adds: [] },
  });
  assert.match(line, /so far <\/span>a = b/);
  assert.match(line, /line ⊢ <\/span>b = c/);
  const at = cfg.contextHtml({
    type: 'a = c', checked: true, kind: 'proof', locals: [],
    step: { form: 'rewriteRule', description: 'rule 1 of 1 of `rewrite … at h1`', kind: 'proof',
      before: 'a = b', after: 'a = c', rule: 'b = c', target: 'h1', adds: [] },
  });
  assert.match(at, /before h1: <\/span>a = b/);
});

test('goals panel: the hole under the cursor, else the context, else the nearest hole', () => {
  const at = (line, character) => ({ line, character });
  const goal = { range: { start: at(3, 2), end: at(3, 3) }, owner: '`f`', goal: 'g', context: [] };
  const context = { type: 'Nat', checked: true, kind: 'program', locals: [] };
  assert.ok(cfg.goalIsHere(goal, at(3, 2)));
  assert.ok(!cfg.goalIsHere(goal, at(2, 8)));
  assert.ok(!cfg.goalIsHere(null, at(2, 8)));
  assert.match(cfg.panelBody(goal, context, at(3, 3)), /⊢ g/);
  assert.match(cfg.panelBody(goal, context, at(2, 8)), /expected Nat/);
  assert.match(cfg.panelBody(goal, null, at(2, 8)), /⊢ g/);
  assert.strictEqual(cfg.panelBody(null, null, at(2, 8)), null);
});

test('goals panel: no answer keeps the last one, dimmed with a note', () => {
  assert.match(cfg.staleBody(undefined), /No open goal/);
  const kept = cfg.staleBody('<div class="goal">⊢ g</div>');
  assert.match(kept, /class="stale"/);
  assert.match(kept, /Nothing at the cursor/);
  assert.match(kept, /⊢ g/);
});

test('server settings: the values the server reads, nested as it expects, unset ones left out', () => {
  const values = {
    'inlayHints.letTypes': false,
    'codeLens.run': true,
    'proofSearch.enabled': true,
    'proofSearch.timeLimitMs': 2500,
    semanticColours: false,
  };
  assert.deepStrictEqual(cfg.serverSettings((name) => values[name]), {
    inlayHints: { letTypes: false },
    codeLens: { run: true },
    proofSearch: { enabled: true, timeLimitMs: 2500 },
    semanticColours: false,
  });
  assert.deepStrictEqual(cfg.serverSettings(() => undefined), {
    inlayHints: {},
    codeLens: {},
    proofSearch: {},
  });
});

test('package.json declares every setting the client sends, and format on save for .sw', () => {
  const pkg = require('../package.json');
  const props = pkg.contributes.configuration.properties;
  for (const name of [
    'inlayHints.letTypes',
    'codeLens.run',
    'proofSearch.enabled',
    'proofSearch.timeLimitMs',
    'semanticColours',
    'goals.openAutomatically',
  ]) {
    assert.ok(props[`stitchwort.${name}`], name);
    assert.ok(props[`stitchwort.${name}`].description, name);
  }
  assert.strictEqual(props['stitchwort.goals.openAutomatically'].default, false);
  assert.deepStrictEqual(pkg.contributes.configurationDefaults['[stitchwort]'], {
    'editor.formatOnSave': true,
    'editor.defaultFormatter': 'local.stitchwort',
  });
});

test('mentionsGoal: a ? in code, not in a comment or string', () => {
  assert.ok(cfg.mentionsGoal('def f: Nat := ?\n'));
  assert.ok(!cfg.mentionsGoal('-- is it? \ndef f: Text := "why?"\n'));
  assert.ok(cfg.mentionsGoal('def f: Text := "a\\"" ++ ?\n'));
});

test('search for a proof: picks show the proof text, best first; the messages and the staleness rule', () => {
  assert.strictEqual(cfg.SEARCH_PROOF, 'stitchwort.searchProof');
  assert.strictEqual(cfg.SELECT_RANGE, 'stitchwort.selectRange');
  const answer = {
    version: 3,
    range: { start: { line: 1, character: 4 }, end: { line: 1, character: 5 } },
    proofs: [
      { title: 'Replace ? with `Nat.addComm m n` (exact, Std.Nat.addComm)', newText: 'Nat.addComm m n' },
      { title: 'Replace ? with `omega` (closes it alone)', newText: 'omega' },
    ],
  };
  const picks = cfg.proofPicks(answer);
  assert.deepStrictEqual(
    picks.map((p) => [p.label, p.description]),
    [['Nat.addComm m n', 'exact, Std.Nat.addComm'], ['omega', 'closes it alone']],
  );
  assert.strictEqual(picks[0].proof, answer.proofs[0]);
  assert.deepStrictEqual(cfg.proofPicks({ proofs: [] }), []);
  assert.strictEqual(cfg.provedMessage('rfl'), 'Proved by `rfl`');
  assert.ok(cfg.provedMessage('x'.repeat(100)).length < 80);
  assert.strictEqual(cfg.noProofMessage(5000), 'No proof found within 5 s');
  assert.strictEqual(cfg.noProofMessage(1500), 'No proof found within 1.5 s');
  assert.ok(cfg.proofStillApplies(answer, 3, 'x'), 'same version');
  assert.ok(cfg.proofStillApplies(answer, 4, '?'), 'moved version, ? still there');
  assert.ok(!cfg.proofStillApplies(answer, 4, 'n'));
});
