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
  assert.strictEqual(cfg.watchedGlob, '**/stitchwort.yaml');
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
