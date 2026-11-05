// Prototype (SW-1375, SW-1384): CodeMirror 6 talking to the language server
// in a worker through @codemirror/lsp-client. Build: see lsp.html. With
// `?project=aoc&open=src/…` the page opens that file of a bundled project,
// checked as part of the project.
import { EditorView, keymap, lineNumbers, highlightActiveLine, drawSelection } from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import { defaultKeymap, history, historyKeymap, indentWithTab } from "@codemirror/commands";
import { StreamLanguage, syntaxHighlighting, defaultHighlightStyle, bracketMatching } from "@codemirror/language";
import { lintGutter } from "@codemirror/lint";
import { LSPClient, LSPPlugin, languageServerExtensions } from "@codemirror/lsp-client";

const KEYWORDS = new Set(["def", "theorem", "import", "match", "let", "in", "if", "then", "else", "type", "interface", "instance", "namespace", "test", "ability", "handle", "with", "fn", "where", "pub", "data", "record"]);
const stitchwort = StreamLanguage.define({
  name: "stitchwort",
  token(stream) {
    if (stream.match("--")) { stream.skipToEnd(); return "comment"; }
    if (stream.match(/^"(?:[^"\\]|\\.)*"?/)) return "string";
    if (stream.match(/^\d+(\.\d+)?/)) return "number";
    if (stream.match(/^[A-Za-z_][A-Za-z0-9_']*/)) {
      const w = stream.current();
      return KEYWORDS.has(w) ? "keyword" : /^[A-Z]/.test(w) ? "typeName" : null;
    }
    stream.next();
    return null;
  },
});

// What the probe (web/proto/lsp-check.mjs) reads: a log of the traffic with
// times, and the time each publishDiagnostics arrived.
const log = (window.lspLog = []);
const timing = (window.lspTiming = { ticks: [], received: [], published: [], searched: [], searchesStopped: 0, project: null, ready: null, crashed: null });
const t0 = performance.now();
// The bundle is served from web/dist/; the worker stays beside the trial page.

const worker = new Worker(new URL("../proto/lsp-worker.js", import.meta.url), { type: "module" });
let handlers = [];
const stdWaiting = new Map();
worker.onmessage = ({ data }) => {
  const now = performance.now() - t0;
  if (data.lsp !== undefined) {
    const m = JSON.parse(data.lsp);
    log.push({ t: now, dir: "in", method: m.method, id: m.id, size: data.lsp.length });
    if (m.method === "textDocument/publishDiagnostics") timing.published.push({ t: now, uri: m.params.uri, version: m.params.version, count: m.params.diagnostics.length });
    for (const h of handlers) h(data.lsp);
  } else if (data.tick !== undefined) timing.ticks.push({ t: now, ms: data.tick, published: data.published, startAbs: data.startAbs - t0 });
  else if (data.received !== undefined) timing.received.push({ t: now, ms: data.received, method: data.method });
  else if (data.ready !== undefined) { timing.ready = { t: now, ms: data.ready }; status.textContent = `Server ready in ${data.ready.toFixed(0)} ms`; }
  else if (data.searched !== undefined) timing.searched.push({ t: now, ms: data.searched });
  else if (data.searchStopped !== undefined) timing.searchesStopped++;
  else if (data.searchCrashed !== undefined) timing.crashed = "search: " + data.searchCrashed;
  else if (data.project !== undefined) timing.project = { t: now, name: data.project, files: data.files };
  else if (data.stdSource !== undefined) { stdWaiting.get(data.stdSource)?.(data.text); stdWaiting.delete(data.stdSource); }
  else if (data.crashed !== undefined) { timing.crashed = data.crashed; status.textContent = `The server crashed: ${data.crashed}`; }
};
// Cancellation (docs/proposals/playground-editor.md §5.2.1): with
// cross-origin isolation, a counter in shared memory that this page bumps
// for each edit, which the checker reads while it checks and so stops a
// check the edit has made stale. Without it, a check runs to its end.
const edits = globalThis.crossOriginIsolated ? new Int32Array(new SharedArrayBuffer(4)) : null;
if (edits) worker.postMessage({ edits });
timing.isolated = !!edits;
const STALE = new Set(["textDocument/didChange", "textDocument/didClose"]);

const transport = {
  send(message) {
    const m = JSON.parse(message);
    if (edits && STALE.has(m.method)) Atomics.add(edits, 0, 1);
    log.push({ t: performance.now() - t0, dir: "out", method: m.method, id: m.id, size: message.length });
    worker.postMessage(message);
  },
  subscribe(h) { handlers.push(h); },
  unsubscribe(h) { handlers = handlers.filter((x) => x !== h); },
};

const params = new URLSearchParams(location.search);
const project = params.get("project");
const open = params.get("open");
if (project) worker.postMessage({ project });

const client = new LSPClient({ extensions: languageServerExtensions(), timeout: 30000 }).connect(transport);
window.lspClient = client;

// Code actions: the client has no UI for them, so this is the glue. Mod-.
// asks for the actions at the cursor and applies the first one's edit (the
// plain `changes` form, which the server sends to a client that doesn't
// claim `documentChanges`).
async function codeAction(view) {
  const plugin = LSPPlugin.get(view);
  if (!plugin) return false;
  plugin.client.sync();
  const { from, to } = view.state.selection.main;
  const t = performance.now();
  const actions = await plugin.client.request("textDocument/codeAction", {
    textDocument: { uri: plugin.uri },
    range: { start: plugin.toPosition(from), end: plugin.toPosition(to) },
    context: { diagnostics: [] },
  });
  window.lastCodeAction = { ms: performance.now() - t, titles: (actions ?? []).map((a) => a.title) };
  const edits = actions?.[0]?.edit?.changes?.[plugin.uri];
  if (!edits) return true;
  view.dispatch({ changes: edits.map((e) => ({ from: plugin.fromPosition(e.range.start), to: plugin.fromPosition(e.range.end), insert: e.newText })) });
  return true;
}

const base = [
  lineNumbers(), highlightActiveLine(), drawSelection(), history(), bracketMatching(),
  syntaxHighlighting(defaultHighlightStyle), stitchwort, lintGutter(),
  keymap.of([{ key: "Mod-.", run: (view) => { codeAction(view); return true; } }, ...defaultKeymap, ...historyKeymap, indentWithTab]),
];

// A library file, for go to definition into std: shown read-only beside the
// editor, with its own plugin so hover works there too.
let stdView = null;
client.workspace.displayFile = async (uri) => {
  const known = client.workspace.getFile(uri);
  if (known) return known.getView();
  if (!uri.startsWith("stitchwort-std:")) return null;
  const path = uri.slice("stitchwort-std:".length);
  const text = await new Promise((ok) => { stdWaiting.set(path, ok); worker.postMessage({ stdSource: path }); });
  stdView?.destroy();
  document.getElementById("stdname").textContent = path;
  stdView = new EditorView({
    parent: document.getElementById("std"),
    state: EditorState.create({ doc: text, extensions: [...base, EditorState.readOnly.of(true), client.plugin(uri, "stitchwort")] }),
  });
  window.stdView = stdView;
  return stdView;
};

const status = document.getElementById("status");
(async () => {
  const doc = project
    ? await fetch(new URL(`../pkg/projects/${project}/${open}`, import.meta.url)).then((r) => r.text())
    : document.getElementById("sample").textContent.replace(/^\n/, "");
  const uri = project ? `file:///playground/${project}/${open}` : "file:///playground/main.sw";
  window.view = new EditorView({
    parent: document.getElementById("editor"),
    state: EditorState.create({ doc, extensions: [...base, client.plugin(uri, "stitchwort")] }),
  });
})();
