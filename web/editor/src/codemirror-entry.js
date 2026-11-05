// Prototype (SW-1118, docs/proposals/playground-editor.md): CodeMirror 6 over
// the playground's own worker. Diagnostics from the compiler's index become
// lint marks; hovering a stretch shows the expression type the index records.
// Build: see the comment at the top of codemirror.html.
import { EditorView, keymap, lineNumbers, highlightActiveLine, drawSelection, hoverTooltip } from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import { defaultKeymap, history, historyKeymap, indentWithTab } from "@codemirror/commands";
import { StreamLanguage, syntaxHighlighting, defaultHighlightStyle, indentOnInput, bracketMatching } from "@codemirror/language";
import { linter, lintGutter, forceLinting } from "@codemirror/lint";
import { closeBrackets, closeBracketsKeymap } from "@codemirror/autocomplete";

// A small tokenizer; the real thing would reuse the playground's `colour`.
const KEYWORDS = new Set(["def", "theorem", "import", "match", "let", "in", "if", "then", "else", "type", "interface", "instance", "namespace", "test", "ability", "handle", "with", "fn", "where", "pub"]);
const stitchwort = StreamLanguage.define({
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

// The page's side of the worker protocol (web/playground-worker.js).
const worker = new Worker(new URL("../playground-worker.js", import.meta.url), { type: "module" });
const module = fetch(new URL("../pkg/stitchwort_web_bg.wasm", import.meta.url)).then((r) => r.arrayBuffer()).then((b) => WebAssembly.compile(b));
let nextId = 1;
const pending = new Map();
worker.onmessage = ({ data }) => { const p = pending.get(data.id); if (p && (data.out || data.crashed)) { pending.delete(data.id); p(data); } };
async function ask(action, source) {
  const id = nextId++;
  const reply = new Promise((resolve) => pending.set(id, resolve));
  worker.postMessage({ id, module: await module, action, source });
  return reply;
}

let latest = { exprs: [] };
const offsetOf = (doc, line, ch) => doc.line(Math.min(line + 1, doc.lines)).from + ch;

const lint = linter(async (view) => {
  const doc = view.state.doc;
  const text = doc.toString();
  const reply = await ask("index", text);
  if (view.state.doc.toString() !== text) return []; // stale: a newer lint is coming
  if (reply.crashed) return [{ from: 0, to: 0, severity: "error", message: reply.error }];
  latest = reply.out;
  status.textContent = `${latest.diagnostics.length} diagnostic(s), ${latest.exprs?.length ?? 0} typed expressions`;
  return latest.diagnostics.filter((d) => d.range).map((d) => {
    const [sl, sc, el, ec] = d.range;
    const from = offsetOf(doc, sl, sc);
    const to = Math.max(from, offsetOf(doc, el, ec));
    return {
      from, to,
      severity: d.severity === "goal" ? "info" : d.severity,
      source: d.code,
      message: [d.message, ...d.notes].join("\n"),
    };
  });
}, { delay: 250 });

const types = hoverTooltip((view, pos) => {
  const doc = view.state.doc;
  let best = null;
  for (const [, range, type] of latest.exprs ?? []) {
    const from = offsetOf(doc, range[0], range[1]), to = offsetOf(doc, range[2], range[3]);
    if (from <= pos && pos <= to && (!best || to - from < best.to - best.from)) best = { from, to, type };
  }
  return best && { pos: best.from, end: best.to, create: () => { const dom = document.createElement("div"); dom.className = "tip"; dom.textContent = best.type; return { dom }; } };
});

const status = document.getElementById("status");
new EditorView({
  parent: document.getElementById("editor"),
  state: EditorState.create({
    doc: document.getElementById("sample").textContent.replace(/^\n/, ""),
    extensions: [
      lineNumbers(), highlightActiveLine(), drawSelection(), history(), indentOnInput(), bracketMatching(), closeBrackets(),
      syntaxHighlighting(defaultHighlightStyle), stitchwort, lintGutter(), lint, types,
      keymap.of([...closeBracketsKeymap, ...defaultKeymap, ...historyKeymap, indentWithTab]),
    ],
  }),
});
