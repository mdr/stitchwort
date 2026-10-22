'use strict';
// A tiny fake `stitchwort lsp`: LSP over stdio with canned answers, for the
// client tests. Run as `node fake-server.js lsp` (the argument is ignored, as
// the real program is started with `lsp`). Full-text sync: every didOpen /
// didChange publishes one diagnostic carrying the text length, so a test can
// see the text the client sent.
const { createMessageConnection, StreamMessageReader, StreamMessageWriter } = require('vscode-jsonrpc/node');

const conn = createMessageConnection(
  new StreamMessageReader(process.stdin),
  new StreamMessageWriter(process.stdout),
);

const range = (l, c, l2, c2) => ({ start: { line: l, character: c }, end: { line: l2, character: c2 } });
const texts = new Map();

function publish(uri) {
  const text = texts.get(uri);
  conn.sendNotification('textDocument/publishDiagnostics', {
    uri,
    diagnostics: [
      { range: range(0, 0, 0, 1), severity: 1, code: 'E-FAKE', source: 'stitchwort', message: `length ${text.length}` },
    ],
  });
}

conn.onRequest('initialize', () => ({
  capabilities: {
    textDocumentSync: 1, // full
    definitionProvider: true,
    hoverProvider: true,
    referencesProvider: true,
    documentSymbolProvider: true,
  },
  serverInfo: { name: 'fake-stitchwort' },
}));
conn.onNotification('initialized', () => {});
conn.onNotification('textDocument/didOpen', (p) => {
  texts.set(p.textDocument.uri, p.textDocument.text);
  publish(p.textDocument.uri);
});
conn.onNotification('textDocument/didChange', (p) => {
  texts.set(p.textDocument.uri, p.contentChanges[p.contentChanges.length - 1].text);
  publish(p.textDocument.uri);
});
conn.onNotification('textDocument/didClose', (p) => {
  texts.delete(p.textDocument.uri);
  conn.sendNotification('textDocument/publishDiagnostics', { uri: p.textDocument.uri, diagnostics: [] });
});
conn.onRequest('textDocument/definition', (p) => ({ uri: p.textDocument.uri, range: range(2, 4, 2, 7) }));
conn.onRequest('textDocument/hover', () => ({
  contents: { kind: 'markdown', value: '```stitchwort\nNat\n```' },
  range: range(0, 0, 0, 3),
}));
conn.onRequest('textDocument/references', (p) => [
  { uri: p.textDocument.uri, range: range(2, 4, 2, 7) },
  { uri: p.textDocument.uri, range: range(5, 1, 5, 4) },
]);
conn.onRequest('textDocument/documentSymbol', () => [
  {
    name: 'f',
    detail: 'Nat',
    kind: 12,
    range: range(2, 0, 3, 5),
    selectionRange: range(2, 4, 2, 5),
    children: [],
  },
]);
conn.onRequest('shutdown', () => null);
conn.onNotification('exit', () => process.exit(0));
conn.listen();
