// Headless check of the SW-1375 trial page (lsp.html): opens it in Chrome
// over the DevTools protocol, tries each feature through the editor, and
// prints what worked and the timings, with screenshots beside it.
//
//   node web/proto/lsp-check.mjs [OUTDIR]
//
// Serve nothing first: it serves web/ itself. Needs pkg/ (web/build.sh) and
// lsp.bundle.js. Chrome is found as web/tests/browser.mjs finds it.
import { spawn, execFileSync } from "node:child_process";
import { createServer } from "node:http";
import { existsSync, mkdtempSync, readFileSync, statSync, writeFileSync, mkdirSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, extname, join, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, "..");
const out = resolve(process.argv[2] ?? join(tmpdir(), "sw-lsp-check"));
mkdirSync(out, { recursive: true });
const aocDay = readFileSync(resolve(root, "../aoc/src/Aoc/Year2024/Day21/Day21.sw"), "utf8");

const chrome = process.env.CHROME ?? ["/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", "/Applications/Chromium.app/Contents/MacOS/Chromium"].find(existsSync);
const TYPES = { ".html": "text/html; charset=utf-8", ".js": "text/javascript", ".wasm": "application/wasm", ".json": "application/json" };
const server = await new Promise((ok) => {
  const s = createServer((req, res) => {
    const file = resolve(root, "." + decodeURIComponent(new URL(req.url, "http://x").pathname));
    if (!file.startsWith(root + sep) || !existsSync(file) || !statSync(file).isFile()) return res.writeHead(404).end();
    res.writeHead(200, { "content-type": TYPES[extname(file)] ?? "application/octet-stream", "cache-control": "no-store" });
    res.end(readFileSync(file));
  });
  s.listen(0, "127.0.0.1", () => ok(s));
});
const base = `http://127.0.0.1:${server.address().port}/`;

const child = spawn(chrome, ["--headless=new", "--remote-debugging-port=0", `--user-data-dir=${mkdtempSync(join(tmpdir(), "sw-chrome-"))}`,
  "--no-first-run", "--no-default-browser-check", "--window-size=1600,1000", "about:blank"], { stdio: ["ignore", "ignore", "pipe"] });
const wsUrl = await new Promise((ok) => { let e = ""; child.stderr.on("data", (d) => { e += d; const m = /DevTools listening on (ws:\/\/\S+)/.exec(e); if (m) ok(m[1]); }); });
const ws = new WebSocket(wsUrl);
await new Promise((ok) => (ws.onopen = ok));
let next = 0;
const waiting = new Map();
const consoleLines = [];
ws.onmessage = ({ data }) => {
  const m = JSON.parse(data);
  if (m.id !== undefined) { const w = waiting.get(m.id); waiting.delete(m.id); m.error ? w.fail(new Error(m.error.message)) : w.ok(m.result); }
  else if (m.method === "Runtime.consoleAPICalled") consoleLines.push(m.params.args.map((a) => a.value ?? a.description).join(" "));
  else if (m.method === "Runtime.exceptionThrown") consoleLines.push("EXCEPTION " + (m.params.exceptionDetails.exception?.description ?? m.params.exceptionDetails.text));
};
let session;
const send = (method, params = {}) => new Promise((ok, fail) => { const id = ++next; waiting.set(id, { ok, fail }); ws.send(JSON.stringify({ id, method, params, sessionId: session })); });
const { targetId } = await send("Target.createTarget", { url: "about:blank" });
({ sessionId: session } = await send("Target.attachToTarget", { targetId, flatten: true }));
await send("Runtime.enable");
await send("Page.enable");
const ev = async (expression) => {
  const r = await send("Runtime.evaluate", { expression, awaitPromise: true, returnByValue: true });
  if (r.exceptionDetails) throw new Error(r.exceptionDetails.exception?.description ?? r.exceptionDetails.text);
  return r.result.value;
};
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const until = async (expr, ms = 60000) => { const t = Date.now(); for (;;) { const v = await ev(expr); if (v) return v; if (Date.now() - t > ms) throw new Error("timed out: " + expr); await sleep(20); } };
const shot = async (name) => { const { data } = await send("Page.captureScreenshot", { format: "png" }); writeFileSync(join(out, name + ".png"), Buffer.from(data, "base64")); };
const report = {};
const step = async (name, f) => { try { report[name] = await f(); } catch (e) { report[name] = { failed: String(e.message ?? e) }; } console.log(name, JSON.stringify(report[name])); };

// Where `needle` is in the main editor (plus `delta` characters), on screen.
const coords = (needle, delta = 0, which = "view") => ev(`(() => { const v = window.${which}; const i = v.state.doc.toString().indexOf(${JSON.stringify(needle)}) + ${delta};
  v.dispatch({ selection: { anchor: i }, scrollIntoView: true }); const c = v.coordsAtPos(i); return { i, x: (c.left + c.right) / 2 + 2, y: (c.top + c.bottom) / 2 }; })()`);
const key = async (k, code, keyCode, modifiers = 0) => {
  await send("Input.dispatchKeyEvent", { type: "rawKeyDown", key: k, code, windowsVirtualKeyCode: keyCode, modifiers });
  await send("Input.dispatchKeyEvent", { type: "keyUp", key: k, code, windowsVirtualKeyCode: keyCode, modifiers });
};
// The latest publishDiagnostics for main.sw after `since`, and the time it arrived.
// With `version`, only diagnostics for that version of the text or later.
const publishedAfter = (since, version = 0) => until(`window.lspTiming.published.find((p) => p.t > ${since} && p.uri.endsWith("main.sw") && (p.version ?? 0) >= ${version})`);
const MAIN = `window.lspClient.workspace.getFile("file:///playground/main.sw")`;

const t0 = Date.now();
await send("Page.navigate", { url: base + "proto/lsp.html" });

await step("first diagnostics", async () => {
  await until(`window.lspTiming`);
  const p = await publishedAfter(0);
  await until(`document.querySelectorAll(".cm-lintRange").length > 0`);
  const marks = await ev(`[...document.querySelectorAll(".cm-lintRange")].map((e) => e.className.match(/cm-lintRange-(\\w+)/)[1] + ": " + e.textContent)`);
  const ready = await ev(`window.lspTiming.ready`);
  return { serverReadyMs: Math.round(ready.ms), publishedAtMs: Math.round(p.t), count: p.count, marks, wall: Date.now() - t0 };
});
await shot("1-diagnostics");

await step("hover", async () => {
  const c = await coords("double (double n)", 1);
  await send("Input.dispatchMouseEvent", { type: "mouseMoved", x: c.x, y: c.y });
  const text = await until(`document.querySelector(".cm-tooltip-hover")?.innerText`, 5000);
  await shot("2-hover");
  await send("Input.dispatchMouseEvent", { type: "mouseMoved", x: 5, y: 5 });
  return { text };
});

await step("go to definition (same file)", async () => {
  await coords("double (double n)", 1);
  const t = await ev(`performance.now()`);
  await ev(`window.view.focus()`);
  await key("F12", "F12", 123);
  const line = await until(`(() => { const v = window.view, s = v.state.selection.main.head; const l = v.state.doc.lineAt(s); return l.text.startsWith("def double") && { line: l.number, col: s - l.from }; })()`, 5000);
  return { ...line, ms: Math.round((await ev(`performance.now()`)) - t) };
});

await step("go to definition (into std)", async () => {
  await coords(".foldLeft", 2);
  await ev(`window.view.focus()`);
  await key("F12", "F12", 123);
  const at = await until(`window.stdView && (() => { const v = window.stdView, s = v.state.selection.main.head; return { file: document.getElementById("stdname").textContent, line: v.state.doc.lineAt(s).number, text: v.state.doc.lineAt(s).text.trim().slice(0, 80) }; })()`, 5000);
  await shot("3-std-definition");
  return at;
});

await step("hover in std", async () => {
  const head = await ev(`window.stdView.state.selection.main.head`);
  const c = await ev(`(() => { const c = window.stdView.coordsAtPos(${head} + 5); return { x: c.left + 2, y: (c.top + c.bottom) / 2 }; })()`);
  await send("Input.dispatchMouseEvent", { type: "mouseMoved", x: c.x, y: c.y });
  const text = await until(`document.querySelector(".cm-tooltip-hover")?.innerText`, 3000);
  await send("Input.dispatchMouseEvent", { type: "mouseMoved", x: 5, y: 5 });
  return { text: text.slice(0, 200) };
});

await step("format (Shift-Alt-f)", async () => {
  const before = await ev(`window.view.state.doc.toString()`);
  await ev(`window.view.focus()`);
  await key("f", "KeyF", 70, 1 | 8 /* Alt, Shift */);
  const changed = await until(`window.view.state.doc.toString() !== ${JSON.stringify(before)}`, 5000).catch(() => false);
  const line = await ev(`window.view.state.doc.toString().split("\\n").find((l) => l.startsWith("def double"))`);
  return { changed, line };
});

await step("completion (named arguments after '(')", async () => {
  const end = await ev(`window.view.state.doc.length`);
  await ev(`(() => { const add = "\\ndef six : Nat := double "; window.view.dispatch({ changes: { from: ${end}, insert: add }, selection: { anchor: ${end} + add.length } }); window.view.focus(); })()`);
  await send("Input.insertText", { text: "(" });
  const items = await until(`document.querySelector(".cm-tooltip-autocomplete") && [...document.querySelectorAll(".cm-tooltip-autocomplete li")].map((li) => li.innerText)`, 5000);
  await shot("4-completion");
  await key("Escape", "Escape", 27);
  return { items };
});

await step("signature help", async () => {
  const caps = await ev(`window.lspClient.serverCapabilities.signatureHelpProvider ?? null`);
  return { advertised: caps };
});

await step("code action on ? (page glue: Mod-.)", async () => {
  await coords("n + 0 = n := ?", 13);
  await ev(`window.view.focus()`);
  await key(".", "Period", 190, 4 /* Meta */);
  const result = await until(`window.lastCodeAction`, 60000);
  await until(`!window.view.state.doc.toString().includes(":= ?")`, 2000).catch(() => null);
  const line = await ev(`window.view.state.doc.toString().split("\\n").find((l) => l.startsWith("theorem hole"))`);
  await shot("4b-code-action");
  return { ms: Math.round(result.ms), titles: result.titles, after: line };
});

await step("find references (Shift-F12)", async () => {
  await coords("def double", 5);
  await ev(`window.view.focus()`);
  await key("F12", "F12", 123, 8 /* Shift */);
  const refs = await until(`document.querySelector(".cm-lsp-reference-panel") && [...document.querySelectorAll(".cm-lsp-reference")].map((e) => e.innerText.trim())`, 5000);
  await shot("4c-references");
  return { refs };
});

await step("references / format / rename (client has them)", async () => {
  const caps = await ev(`({ references: window.lspClient.serverCapabilities.referencesProvider, formatting: window.lspClient.serverCapabilities.documentFormattingProvider, rename: window.lspClient.serverCapabilities.renameProvider ?? false })`);
  return caps;
});

// Typing: one character at the end of the document, synced at once
// (client.sync() rather than the client's own 500 ms pause), to the
// diagnostics of the new version.
let this_version = 0;
async function typing(label, runs) {
  const times = [];
  for (let i = 0; i < runs; i++) {
    const t = await ev(`(() => { const v = window.view; v.dispatch({ changes: { from: v.state.doc.length, insert: ${JSON.stringify(i % 2 ? "\n" : " ")} } }); const t = performance.now(); window.lspClient.sync(); return { t, version: ${MAIN}.version }; })()`).then(({ t, version }) => { this_version = version; return t; });
    const p = await publishedAfter(t, this_version).catch(() => null);
    // A change that leaves the diagnostics as they were publishes nothing:
    // then the end of the ticks is the answer.
    const quiet = await until(`(() => { const last = window.lspTiming.ticks.at(-1); return last && last.t > ${t} && performance.now() - last.t > 30 && last.t; })()`, 60000);
    times.push(Math.round((p?.t ?? quiet) - t));
  }
  const ticks = await ev(`window.lspTiming.ticks.slice(-40).map((x) => Math.round(x.ms))`);
  const abs = await ev(`window.lspTiming.ticks.slice(-3).map((x) => ({ startAbs: Math.round(x.startAbs - performance.timeOrigin), endPage: Math.round(x.t), ms: Math.round(x.ms) }))`);
  return { label, abs, msToDiagnostics: times, median: [...times].sort((a, b) => a - b)[times.length >> 1], recentTickMs: ticks };
}

await step("typing latency, small file", () => typing("sample", 7));

await step("AoC 2024 day 21 (226 lines): load", async () => {
  const t = await ev(`(() => { const v = window.view; v.dispatch({ changes: { from: 0, to: v.state.doc.length, insert: ${JSON.stringify(aocDay)} } }); const t = performance.now(); window.lspClient.sync(); return { t, version: ${MAIN}.version }; })()`).then(({ t, version }) => { this_version = version; return t; });
  const p = await publishedAfter(t, this_version);
  await sleep(300);
  await shot("5-aoc");
  return { msToDiagnostics: Math.round(p.t - t), count: p.count, diags: await ev(`window.lspLog.length`) };
});
await step("typing latency, AoC day", () => typing("aoc day21", 7));

await step("default client pause (500 ms) end to end", async () => {
  const t = await ev(`(() => { const v = window.view; v.dispatch({ changes: { from: v.state.doc.length, insert: "x" } }); return performance.now(); })()`);
  const p = await publishedAfter(t);
  return { msToDiagnostics: Math.round(p.t - t) };
});

report.crashed = await ev(`window.lspTiming.crashed`);
report.console = consoleLines.slice(0, 20);
writeFileSync(join(out, "report.json"), JSON.stringify(report, null, 2));
console.log("written to", out);
child.kill();
server.close();
process.exit(0);
