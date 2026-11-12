// Browser tests for the playground (web/index.html): headless Chrome, driven
// over the DevTools protocol, against a static server of our own.
//
//   node web/tests/browser.mjs [--dir DIR] [NAME...]
//
// DIR is what to serve: web/ by default (build it first with web/build.sh),
// or a `nix build .#playground` result. NAMEs pick the tests whose names
// contain any of them. Chrome is found from $CHROME, the usual macOS
// application paths, or google-chrome/chromium on the PATH; without it the
// tests are skipped (exit status 0, with a message). See docs/testing.md.
//
// Each test has a fresh tab with empty storage. The server and Chrome listen
// on ports the system picks, and both are stopped at the end.

import { spawn, execFileSync } from "node:child_process";
import { createServer } from "node:http";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, extname, join, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import assert from "node:assert/strict";

const here = dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
let root = resolve(here, "..");
const filters = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === "--dir") root = resolve(args[++i]);
  else filters.push(args[i]);
}

// What the page and its tests are given ------------------------------------

/** How long the page lets a run take: see RUN_SECONDS in index.html. */
const RUN_SECONDS = 15;
const MAX_OUTPUT = 256 * 1024;

const MAIN_INPUT = "Ada\n40\ntwo\n2\n";
const MAIN_OUTPUT = "What's your name?\n" +
  "Hello, Ada! Type numbers to add, one per line, and an empty line to stop.\n" +
  "  total: 40\n\"two\" isn't a number; skipped\n  total: 42\nThe sum is 42. Goodbye, Ada.\n";

/**
 * Prints `tick`, then counts down from a number so large that it never ends.
 * The number depends on the input, as otherwise checking the program would
 * count down too.
 */
const SPIN = `def spin : Nat -> Nat
  | 0      => 0
  | Succ n => spin n

def start : Option Text -> Nat
  | None => 1000000000000
  | Some l  => 1000000000000

def main () : {IO} () :=
  IO.print "tick"
  IO.print (spin (start (IO.readLine ()))).toText
`;

/** Prints `line` `n` times. */
const printMany = (n, line) => `def printMany : Nat -> {IO} ()
  | 0      => ()
  | Succ n =>
    IO.print "${line}"
    printMany n

def main () : {IO} () := printMany ${n}
`;

/** Reads `n` lines, ignoring what it gets. */
const readMany = (n) => `def readMany : Nat -> {IO} ()
  | 0      => ()
  | Succ n =>
    let l := IO.readLine ()
    readMany n

def main () : {IO} () := readMany ${n}
`;

// Finding Chrome -------------------------------------------------------------

function findChrome() {
  if (process.env.CHROME) {
    if (!existsSync(process.env.CHROME)) throw new Error(`$CHROME is ${process.env.CHROME}, which doesn't exist`);
    return process.env.CHROME;
  }
  for (const app of ["/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
                     "/Applications/Chromium.app/Contents/MacOS/Chromium"]) {
    if (existsSync(app)) return app;
  }
  for (const name of ["google-chrome", "google-chrome-stable", "chromium", "chromium-browser"]) {
    try {
      return execFileSync("which", [name], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim();
    } catch {}
  }
  return null;
}

// A static server for the page -----------------------------------------------

const TYPES = { ".html": "text/html; charset=utf-8", ".js": "text/javascript", ".wasm": "application/wasm",
                ".json": "application/json", ".css": "text/css" };

/** Files the server gives in place of the real ones: path → text. */
const overrides = new Map();
/**
 * Whether the server sends COOP/COEP, as the page is served once its service worker
 * (coi-serviceworker.js) has run. Off, a visit starts without isolation and the worker
 * has to provide it (see the test for that).
 */
let isolating = true;
const ISOLATION = { "cross-origin-opener-policy": "same-origin", "cross-origin-embedder-policy": "require-corp" };

function serve(dir) {
  const server = createServer((req, res) => {
    const path = decodeURIComponent(new URL(req.url, "http://x").pathname);
    if (overrides.has(path)) {
      res.writeHead(200, { "content-type": TYPES[extname(path)] ?? "text/plain", "cache-control": "no-store", ...(isolating ? ISOLATION : {}) });
      res.end(overrides.get(path));
      return;
    }
    const file = resolve(dir, "." + path);
    if (!file.startsWith(dir + sep) || !existsSync(file) || !statSync(file).isFile()) {
      res.writeHead(404).end("not found");
      return;
    }
    res.writeHead(200, { "content-type": TYPES[extname(file)] ?? "application/octet-stream", "cache-control": "no-store", ...(isolating ? ISOLATION : {}) });
    res.end(readFileSync(file));
  });
  return new Promise((ok) => server.listen(0, "127.0.0.1", () => ok(server)));
}

// Chrome over the DevTools protocol ------------------------------------------

async function launch(chrome, profile) {
  const child = spawn(chrome, [
    "--headless=new", "--remote-debugging-port=0", `--user-data-dir=${profile}`, "--no-first-run",
    "--no-default-browser-check", "--disable-background-networking", "--disable-extensions",
    "--window-size=1400,900", "about:blank",
  ], { stdio: ["ignore", "ignore", "pipe"] });
  const url = await new Promise((ok, fail) => {
    let err = "";
    const timer = setTimeout(() => fail(new Error("Chrome didn't start:\n" + err)), 30000);
    child.stderr.on("data", (d) => {
      err += d;
      const m = /DevTools listening on (ws:\/\/\S+)/.exec(err);
      if (m) { clearTimeout(timer); ok(m[1]); }
    });
    child.on("exit", (code) => { clearTimeout(timer); fail(new Error(`Chrome exited (${code}):\n${err}`)); });
  });
  child.stderr.resume();
  const ws = new WebSocket(url);
  await new Promise((ok, fail) => { ws.onopen = ok; ws.onerror = () => fail(new Error("can't connect to Chrome")); });
  let next = 0;
  const waiting = new Map();
  const listeners = new Map();
  ws.onmessage = ({ data }) => {
    const msg = JSON.parse(data);
    if (msg.id !== undefined) {
      const w = waiting.get(msg.id);
      waiting.delete(msg.id);
      if (msg.error) w?.fail(new Error(`${w.method}: ${msg.error.message}`));
      else w?.ok(msg.result);
    } else {
      listeners.get(msg.sessionId)?.(msg);
    }
  };
  const send = (method, params = {}, sessionId) => new Promise((ok, fail) => {
    const id = ++next;
    waiting.set(id, { ok, fail, method });
    ws.send(JSON.stringify({ id, method, params, sessionId }));
  });
  return { child, ws, send, listeners };
}

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

/** A tab, and helpers for driving the playground in it. */
class Page {
  constructor(browser, sessionId, targetId, base) {
    Object.assign(this, { browser, sessionId, targetId, base });
    this.console = [];
    this.exceptions = [];
    browser.listeners.set(sessionId, (msg) => {
      if (msg.method === "Runtime.consoleAPICalled") {
        this.console.push(`${msg.params.type}: ` + msg.params.args.map((a) => a.value ?? a.description).join(" "));
      } else if (msg.method === "Runtime.exceptionThrown") {
        const d = msg.params.exceptionDetails;
        this.exceptions.push(d.exception?.description ?? d.text);
      }
    });
  }

  send(method, params) { return this.browser.send(method, params, this.sessionId); }

  /** Evaluates `expression` in the page, awaiting a promise, and returns its value. */
  async ev(expression) {
    const r = await this.send("Runtime.evaluate", { expression, awaitPromise: true, returnByValue: true });
    if (r.exceptionDetails) throw new Error(`in the page: ${r.exceptionDetails.exception?.description ?? r.exceptionDetails.text}\n  evaluating ${expression.slice(0, 200)}`);
    return r.result.value;
  }

  /** Waits until `expression` is truthy in the page, and returns its value. */
  async until(expression, ms = 30000, what = expression) {
    const start = Date.now();
    for (;;) {
      const v = await this.ev(expression);
      if (v) return v;
      if (Date.now() - start > ms) {
        throw new Error(`timed out after ${ms} ms waiting for ${what}\n  status: ${await this.status()}\n  output: ${(await this.output()).slice(0, 600)}`);
      }
      await sleep(50);
    }
  }

  async open({ patch, hash = "" } = {}) {
    if (patch) await this.send("Page.addScriptToEvaluateOnNewDocument", { source: patch });
    await this.send("Page.navigate", { url: this.base + "index.html" + hash });
    await this.until(`document.readyState === "complete"`);
  }

  async reload() {
    await this.send("Page.reload", {});
    await sleep(200);
    await this.until(`document.readyState === "complete"`);
  }

  status() { return this.ev(`document.getElementById("status").textContent`); }
  output() { return this.ev(`document.getElementById("output").innerText`); }
  untilStatus(text, ms) { return this.until(`document.getElementById("status").textContent === ${JSON.stringify(text)}`, ms, `status "${text}"`); }
  untilChecked(ms) { return this.untilStatus("Checked by the kernel", ms); }

  // Changing the source or example first blanks the status, which is only
  // set again once the new source has been checked, so that waiting for a
  // status can't see the old one.
  static #blank = `document.getElementById("status").textContent = "(changed)";`;

  /** Replaces the source, as a paste would. */
  setSource(text) {
    return this.ev(`(() => { ${Page.#blank} window.editor.setText(${JSON.stringify(text)}); })()`);
  }
  pick(id) {
    return this.ev(`(() => { ${Page.#blank} const p = document.getElementById("example"); p.value = ${JSON.stringify(id)};
      p.dispatchEvent(new Event("change")); })()`);
  }
  tab(view) { return this.ev(`document.querySelector('[data-view="${view}"]').click()`); }
  click(selector) { return this.ev(`document.querySelector(${JSON.stringify(selector)}).click()`); }
  runResult() { return this.ev(`document.querySelector(".run-result")?.innerText ?? ""`); }
  printed() { return this.ev(`document.querySelector(".run-result pre.program-output")?.textContent ?? null`); }

  /**
   * Starts a run with the Run button or `start`, and waits for it to end;
   * returns the run's result as text. (In the page, without a worker, it may
   * already have ended when the click returns.)
   */
  async run(ms = 30000, start = () => this.click("#run")) {
    await this.ev(`document.querySelector(".run-result")?.replaceChildren()`);
    await start();
    await this.until(`!document.getElementById("run").disabled &&
      (document.querySelector(".run-result")?.innerText ?? "") !== ""`, ms, "the run to end");
    return this.runResult();
  }
  untilRunEnds(ms = 30000) {
    return this.until(`!document.getElementById("run").disabled`, ms, "the run to end");
  }

  /**
   * Whether what the editor draws is the text: each line it has drawn has the text of its line, and
   * the colouring covers the same characters (its marks, joined, are the text's stretches).
   */
  drawn() {
    return this.ev(`(() => {
      const e = window.editor, doc = e.view.state.doc;
      // Only the view on show: files of the same project stay in the page, hidden.
      const lines = [...e.view.dom.querySelectorAll(".cm-content .cm-line")];
      // The server's inlay hints are drawn in the line but are not its text.
      const text = (l) => { const c = l.cloneNode(true); c.querySelectorAll(".cm-inlay").forEach((h) => h.remove()); return c.textContent; };
      const wrong = lines.filter((l) => text(l) !== doc.lineAt(e.view.posAtDOM(l)).text);
      return { lines: lines.length, wrong: wrong.map((l) => text(l).slice(0, 60)),
               box: (() => { const r = document.querySelector("#editor .cm-editor").getBoundingClientRect(); return [r.width, r.height]; })() };
    })()`);
  }

  async key(key, code, keyCode, { modifiers = 0, commands } = {}) {
    await this.send("Input.dispatchKeyEvent", { type: "rawKeyDown", key, code, windowsVirtualKeyCode: keyCode, modifiers, commands });
    await this.send("Input.dispatchKeyEvent", { type: "keyUp", key, code, windowsVirtualKeyCode: keyCode, modifiers });
  }
  type(text) { return this.send("Input.insertText", { text }); }
}

// The tests --------------------------------------------------------------------

const tests = [];
const test = (name, body, { ms = 60000, exceptions = false } = {}) => tests.push({ name, body, ms, exceptions });

/** Asserts that the editor draws the text it holds. */
async function assertAligned(page, what) {
  const d = await page.drawn();
  assert.ok(d.lines > 0, `${what}: the editor draws lines`);
  assert.deepEqual(d.wrong, [], `${what}: every line drawn is its line of the text`);
}

test("loads and checks the default example", async (page) => {
  await page.open();
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-lists");
  assert.match(await page.output(), /Every definition type-checks/);
  await assertAligned(page, "the default example");
});

test("direct links open the dropdown's entries, and follow it", async (page) => {
  const hash = () => page.ev(`location.hash`);
  const length = () => page.ev(`history.length`);
  const blank = `document.getElementById("status").textContent = "(changed)";`;
  await page.open({ hash: "#aoc/2025/day02" });
  await page.untilStatus(dayStatus(2), 60000);
  assert.equal(await page.ev(`document.getElementById("example").value`), "aoc:1");
  assert.equal(await sourceText(page), await bundled(page, DAY2), "Day 2's program is open");
  assert.equal(await hash(), "#aoc/2025/day02");
  // Picking another entry updates the address bar, without a history entry.
  const before = await length();
  await page.pick("ex-division");
  await page.untilChecked();
  assert.equal(await hash(), "#example/safe-division");
  await page.pick("aoc:2");
  await page.untilStatus(dayStatus(3), 60000);
  assert.equal(await hash(), "#aoc/2025/day03");
  assert.equal(await length(), before, "no history entries are added");
  // Editing the fragment switches the entry.
  await page.ev(`(() => { ${blank} location.hash = "#example/proofs-about-lists"; })()`);
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-lists");
  await page.ev(`(() => { ${blank} location.hash = "#aoc/2025/day01"; })()`);
  await page.untilStatus(dayStatus(1), 60000);
  assert.equal(await page.ev(`document.getElementById("example").value`), "aoc:0");
  await page.ev(`(() => { ${blank} location.hash = "#aoc/2024/day01"; })()`);
  await page.untilStatus(dayStatus(1, 2024), 60000);
  assert.equal(await page.ev(`document.getElementById("example").value`), "aoc:9");
  // An unknown fragment gives the default example, with a notice.
  await page.ev(`(() => { ${blank} location.hash = "#example/nonsense"; })()`);
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-lists");
  assert.match(await page.ev(`document.getElementById("link-notice").textContent`), /No such link/);
  assert.equal(await page.ev(`document.getElementById("link-notice").hidden`), false);
  assert.equal(await hash(), "#example/proofs-about-lists");
});

test("an unknown link at the start gives the default example and a notice", async (page) => {
  await page.open({ hash: "#aoc/2025/day99" });
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-lists");
  assert.match(await page.ev(`document.getElementById("link-notice").textContent`), /No such link/);
  await page.pick("ex-tests");
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("link-notice").hidden`), true);
});

// The language guide (web/guide/) ---------------------------------------------

/** Whether the guide is on show, in place of the editor. */
const guideShown = (page) => page.ev(`!document.getElementById("guide").hidden && document.querySelector("main").hidden`);
/** Waits for the guide's text and examples to be in the page. */
const guideReady = (page) => page.until(`document.querySelectorAll("#guide .guide-code pre").length >= 15`, 30000, "the guide's examples");
/** How far below the top of the window a section starts, in pixels. */
const sectionTop = (page, slug) => page.ev(`Math.round(document.getElementById("guide-${slug}").getBoundingClientRect().top)`);

test("the Guide opens from its button, lists its sections and colours its code", async (page) => {
  await page.open();
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("guide").hidden`), true, "the guide starts hidden");
  await page.click("#guide-button");
  await guideReady(page);
  assert.ok(await guideShown(page), "the guide replaces the editor");
  assert.equal(await page.ev(`location.hash`), "#guide");
  assert.equal(await page.ev(`document.getElementById("guide-button").getAttribute("aria-pressed")`), "true");
  // A contents list with a link for each section, naming its fragment.
  const links = await page.ev(`[...document.querySelectorAll("#guide-contents a")].map((a) => [a.textContent, a.getAttribute("href")])`);
  const sections = await page.ev(`document.querySelectorAll("#guide-article section").length`);
  assert.ok(links.length >= 15 && links.length === sections, JSON.stringify(links));
  assert.ok(links.some(([title, href]) => /Records and variants/.test(title) && href === "#guide/records-and-variants"), JSON.stringify(links));
  // The code is coloured by the editor's tokenizer: its keywords, comments,
  // and names being defined each get their colour.
  const coloured = await page.ev(`(() => {
    const code = document.querySelector("#guide .guide-code pre");
    const colour = (kind) => { const s = code.querySelector("span.hl-" + kind); return s ? getComputedStyle(s).color : null; };
    return { text: code.textContent, base: getComputedStyle(code).color,
             keyword: colour("keyword"), comment: colour("comment"), defined: colour("defined"), number: colour("number"),
             keywords: [...code.querySelectorAll("span.hl-keyword")].map((s) => s.textContent) };
  })()`);
  assert.ok(coloured.text.startsWith("-- A definition names"), coloured.text.slice(0, 40));
  assert.ok(coloured.keywords.includes("def") && coloured.keywords.includes("test"), JSON.stringify(coloured.keywords));
  for (const kind of ["keyword", "comment", "defined", "number"]) {
    assert.ok(coloured[kind] && coloured[kind] !== coloured.base, `${kind} is coloured differently from the plain text: ${JSON.stringify(coloured)}`);
  }
  // The button again goes back to the editor.
  await page.click("#guide-button");
  assert.ok(!(await guideShown(page)));
  assert.equal(await page.ev(`document.querySelector("main").hidden`), false);
  assert.equal(await page.ev(`location.hash`), "#example/proofs-about-lists");
});

test("a link to a guide section opens it there, and the contents follow the address", async (page) => {
  await page.open({ hash: "#guide/proofs" });
  await guideReady(page);
  assert.ok(await guideShown(page));
  await page.until(`Math.abs(document.getElementById("guide-proofs").getBoundingClientRect().top) < 40`, 10000, "the section to scroll into view");
  assert.equal(await page.ev(`location.hash`), "#guide/proofs");
  assert.equal(await page.ev(`document.querySelector('#guide-contents a[aria-current="true"]').textContent`), "Theorems and proofs");
  // Changing the fragment moves to another section; the editor stays behind it.
  await page.ev(`location.hash = "#guide/tests"`);
  await page.until(`Math.abs(document.getElementById("guide-tests").getBoundingClientRect().top) < 40`, 10000, "the tests section");
  assert.ok(await guideShown(page));
  // A contents link does the same, and the failing test's output is there.
  await page.click('#guide-contents a[href="#guide/abilities"]');
  await page.until(`Math.abs(document.getElementById("guide-abilities").getBoundingClientRect().top) < 40`, 10000, "the abilities section");
  assert.match(await page.ev(`document.querySelector("#guide-tests .guide-output").textContent`), /✗ 2023 is wrong on purpose.*\n\s+left:\s+False\n\s+right: True/);
  // An unknown section shows the top of the guide, not the default example.
  await page.ev(`location.hash = "#guide/nonsense"`);
  await page.until(`window.scrollY === 0 && document.querySelectorAll('#guide-contents a[aria-current]').length === 0`, 10000, "the top");
  assert.ok(await guideShown(page));
  // Leaving the guide's fragment for an example's shows the editor with it.
  await page.ev(`(() => { document.getElementById("status").textContent = "(changed)"; location.hash = "#example/safe-division"; })()`);
  await page.untilChecked();
  assert.ok(!(await guideShown(page)));
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-division");
});

test("Open in editor puts a guide example in the editor, ready to run, and coloured there", async (page) => {
  await page.open({ hash: "#guide/records-and-variants" });
  await guideReady(page);
  const file = await page.ev(`fetch("guide/03-data.sw").then((r) => r.text())`);
  await page.ev(`document.getElementById("status").textContent = "(changed)"`);
  await page.click("#guide-records-and-variants .guide-code button");
  await page.until(`document.getElementById("guide").hidden`, 5000, "the guide to close");
  assert.equal(await sourceText(page), file);
  await page.untilChecked();
  assert.equal(await page.ev(`location.hash`), "", "the address no longer names the guide");
  // Its tests, which this one has, are shown (once they've run).
  await page.until(`document.querySelectorAll("ul.tests li").length > 0`, 30000, "the tests");
  assert.match(await page.output(), /area[\s\S]*update[\s\S]*label/);
  assert.equal(await page.ev(`document.getElementById("tab-tests").getAttribute("aria-selected")`), "true");
  // The editor's own colouring covers it, and lines up with the text.
  const keywords = await page.ev(`window.editor.marked().keyword ?? []`);
  assert.ok(keywords.includes("type") && keywords.includes("def") && keywords.includes("test"), JSON.stringify(keywords));
  await assertAligned(page, "a guide example in the editor");
  // Editing it works as with any example, and survives a reload as the draft.
  await page.setSource(file + "\ntest \"extra\" := 1 == 1\n");
  await page.untilChecked();
  await page.reload();
  await page.untilChecked();
  assert.match(await sourceText(page), /test "extra"/);
});

test("every guide example opens, checks, and passes its tests but the failing one", async (page) => {
  await page.open({ hash: "#guide" });
  await guideReady(page);
  const count = await page.ev(`document.querySelectorAll("#guide .guide-code button").length`);
  assert.ok(count >= 15, String(count));
  for (let i = 0; i < count; i++) {
    await page.ev(`location.hash = "#guide"`);
    await page.until(`!document.getElementById("guide").hidden`, 10000, "the guide");
    await page.ev(`document.getElementById("status").textContent = "(changed)"`);
    await page.ev(`document.querySelectorAll("#guide .guide-code button")[${i}].click()`);
    await page.untilStatus("Checked by the kernel", 60000);
    const failing = await page.ev(`window.editor.value.includes("wrong on purpose")`);
    await page.tab("tests");
    await page.until(`document.querySelectorAll("ul.tests li").length > 0 || /No tests/i.test(document.getElementById("output").innerText)`, 30000, "the tests");
    const failures = await page.ev(`document.querySelectorAll("ul.tests li.fail").length`);
    assert.equal(failures, failing ? 1 : 0, `example ${i}: ${await page.output()}`);
  }
}, { ms: 300000 });

test("the Guide on a phone: nothing scrolls sideways, and the contents come first", async (page) => {
  await page.send("Emulation.setDeviceMetricsOverride", { width: 400, height: 860, deviceScaleFactor: 2, mobile: true });
  await page.open({ hash: "#guide" });
  await guideReady(page);
  const l = await page.ev(`(() => {
    const r = (s) => document.querySelector(s).getBoundingClientRect();
    const wide = [...document.querySelectorAll("#guide pre")].filter((p) => p.getBoundingClientRect().right > innerWidth + 1).length;
    return { width: innerWidth, scrollWidth: document.documentElement.scrollWidth,
             contentsBottom: r("#guide-contents").bottom, articleTop: r("#guide-article").top, wide };
  })()`);
  assert.equal(l.width, 400);
  assert.ok(l.scrollWidth <= l.width, `the page scrolls sideways: ${JSON.stringify(l)}`);
  assert.ok(l.articleTop >= l.contentsBottom - 1, `the contents are above the text: ${JSON.stringify(l)}`);
  assert.equal(l.wide, 0, "code blocks stay inside the window (they scroll inside themselves)");
});

// With GUIDE_SHOTS=DIR, saves pictures of the guide (desktop and phone, light
// and dark) there, for looking at; otherwise it checks nothing and passes.
test("pictures of the Guide (only with GUIDE_SHOTS=DIR)", async (page) => {
  const dir = process.env.GUIDE_SHOTS;
  if (!dir) return;
  mkdirSync(dir, { recursive: true });
  for (const [size, mobile] of [[[1280, 900], false], [[400, 860], true]]) {
    for (const scheme of ["light", "dark"]) {
      await page.send("Emulation.setDeviceMetricsOverride", { width: size[0], height: size[1], deviceScaleFactor: 1, mobile });
      await page.send("Emulation.setEmulatedMedia", { features: [{ name: "prefers-color-scheme", value: scheme }] });
      for (const [name, hash] of [["top", "#guide"], ["records", "#guide/records-and-variants"], ["tests", "#guide/tests"], ["export", "#guide/javascript"]]) {
        await page.open({ hash });
        await guideReady(page);
        await sleep(400);
        const { data } = await page.send("Page.captureScreenshot", { format: "png" });
        writeFileSync(join(dir, `guide-${size[0]}-${scheme}-${name}.png`), Buffer.from(data, "base64"));
      }
      await page.open({ hash: "#guide/records-and-variants" });
      await guideReady(page);
      await page.click("#guide-records-and-variants .guide-code button");
      await page.untilChecked();
      await sleep(300);
      const { data } = await page.send("Page.captureScreenshot", { format: "png" });
      writeFileSync(join(dir, `guide-${size[0]}-${scheme}-editor.png`), Buffer.from(data, "base64"));
    }
  }
});

test("the compiler's files are asked for by content hash (pkg/version.json)", async (page) => {
  await page.open();
  await page.untilChecked();
  const version = await page.ev(`fetch("pkg/version.json").then((r) => r.json())`);
  assert.match(version.compiler, /^[0-9a-f]{16}$/);
  assert.match(version.projects, /^[0-9a-f]{16}$/);
  // The compiler's worker starts on the first request for it (the Tests tab,
  // Run); the Check pane is the language server's.
  await page.tab("tests");
  await page.until(`document.getElementById("output").dataset.for === window.editor.value`, 30000, "the tests' results");
  const asked = await page.ev(`performance.getEntriesByType("resource").map((e) => new URL(e.name).pathname.split("/").pop() + new URL(e.name).search)`);
  assert.ok(asked.includes("version.json"), `version.json is fetched: ${asked}`);
  assert.ok(asked.includes(`stitchwort_web_bg.wasm?v=${version.compiler}`), `the WebAssembly: ${asked}`);
  assert.ok(asked.includes(`playground-worker.js?v=${version.compiler}`), `the worker: ${asked}`);
  assert.ok(!asked.some((a) => a.includes("load=")), `no ?load=: ${asked}`);
  await page.pick("aoc:0");
  await page.untilStatus(dayStatus(1), 60000);
  const manifest = await page.ev(`performance.getEntriesByType("resource").map((e) => new URL(e.name).pathname.split("/").pop() + new URL(e.name).search).filter((a) => a.startsWith("manifest.json"))`);
  // One per bundled project: aoc, rogue, sf and book.
  assert.ok(manifest.length === 4 && manifest.every((a) => a === `manifest.json?v=${version.projects}`), `one manifest per bundled project: ${manifest}`);
});

test("every example checks, and passes its tests but the failing one", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.tab("tests");
  const ids = await page.ev(`[...document.querySelectorAll("#example > option")].map((o) => o.value)`);
  assert.ok(ids.length >= 6, `${ids.length} examples`);
  for (const id of ids) {
    await page.pick(id);
    await page.untilChecked();
    // A render of the previous example can still finish after the pick and
    // leave its own "No tests yet" or summary, so wait for results that say
    // they are for this source (`data-for`, set by the page).
    const summary = await page.until(`document.getElementById("output").dataset.for === window.editor.value &&
      (document.querySelector(".summary")?.textContent ||
       document.getElementById("output").textContent.match(/No tests yet/)?.[0])`, 30000, `${id}'s tests`);
    if (id === "ex-tests") {
      assert.match(summary, /^4 tests: 3 passed, 1 failed( \(4 from the cache\))?$/, `${id}: ${summary} / ${await page.output()} / ${await page.ev("window.editor.value.slice(0,80)")} / ${ids}`);
      assert.match(await page.output(), /✗\s*this one fails \(evaluated to False\)/);
    } else if (summary !== "No tests yet") {
      assert.match(summary, /^(\d+) tests: \1 passed, 0 failed( \(\d+ from the cache\))?$/, id);
    }
    await assertAligned(page, id);
  }
});

test("test results are cached, and can be forgotten", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.pick("ex-tests");
  await page.untilChecked();
  await page.tab("tests");
  // Results arrive asynchronously: wait for the ones for this source.
  const results = () => page.until(`(() => {
    const o = document.getElementById("output");
    const summary = o.querySelector(".summary")?.textContent;
    if (!summary || o.dataset.for !== window.editor.value) return false;
    return { rows: [...o.querySelectorAll("ul.tests li")].map((li) => li.textContent), summary };
  })()`, 30000, "the tests for this source");

  const first = await results();
  assert.equal(first.rows.length, 4);
  assert.ok(first.rows.every((row) => row.endsWith("ran")), first.rows.join("\n"));
  assert.doesNotMatch(first.summary, /from the cache/);
  assert.match(first.summary, /^4 tests: 3 passed, 1 failed$/);

  // A harmless edit: the tests' results are still valid, so they're cached.
  const source = await page.ev(`window.editor.value`);
  await page.setSource(source + "\n-- edit\n");
  await page.untilChecked();
  const second = await results();
  assert.ok(second.rows.every((row) => row.endsWith("cached")), second.rows.join("\n"));
  assert.match(second.summary, /^4 tests: 3 passed, 1 failed \(4 from the cache\)$/);

  await page.click("#forget-cache");
  const third = await results();
  assert.ok(third.rows.every((row) => row.endsWith("ran")), third.rows.join("\n"));
  assert.doesNotMatch(third.summary, /from the cache/);
});

test("a failed comparison test shows both sides in the Tests tab", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(`import Std (List)

def part1 (n: Nat): Nat := n + 1

test "part 1 on the example" := part1 1 == 3
test "greater" := 1 > part1 5
test "long value" := List.range 0 1000 == []
test "huge value" := List.range 0 100000 == []
test "not a comparison" := List.all [1, 2, 3] (n => n < 3)
test "second part" := part1 1 == 2 && part1 2 == 4
`);
  await page.untilChecked();
  await page.tab("tests");
  const results = () => page.until(`(() => {
    const o = document.getElementById("output");
    if (!o.querySelector(".summary") || o.dataset.for !== window.editor.value) return false;
    return [...o.querySelectorAll("ul.tests li")].map((li) => ({
      text: li.firstChild.nextSibling.textContent,
      detail: li.querySelector(".detail")?.textContent ?? null }));
  })()`, 30000, "the tests for this source");
  const rows = await results();
  assert.equal(rows.length, 6);
  assert.equal(rows[0].text, "part 1 on the example (`==` is False)");
  assert.equal(rows[0].detail, "left:  2\nright: 3");
  assert.equal(rows[1].text, "greater (`>` is False)");
  assert.equal(rows[1].detail, "left:  1\nright: 6");
  assert.match(rows[2].detail, /^left:  \[0, 1, 2, [^]*, 999\]\nright: \[\]\nfirst difference at \[0\]: [^\n]*\n  left:  \[0, 1, 2, 3, …\]\n  right: \[\]$/);
  assert.equal(rows[3].detail, "left:  … (too large to show)\nright: []");
  assert.equal(rows[4].text, "not a comparison (evaluated to False)");
  assert.equal(rows[4].detail, null);
  // The false part of an `&&`, with its values and where it is (D601).
  assert.equal(rows[5].text, "second part (`==` is False)");
  assert.match(rows[5].detail, /^left:  3\nright: 4\nin: part1 2 == 4  \(\S+:10:39\)$/);
  await shots(page, "sw216-tests-tab");
});

test("errors show in the Check tab", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource("def x : Nat := rfl\n");
  await page.untilStatus("Doesn’t check");
  assert.match(await page.ev(`document.querySelector("pre.errors").textContent`), /E-TYPE-MISMATCH/);
});

/** Checks, with one warning (W-MODULE-NAME): `a` is the module's `a`. */
const WARNED = `def size : List a -> Nat
  | Nil       => 0
  | Cons _ xs => Succ (size xs)

def a : Type := Nat
`;

test("warnings show apart from errors, without stopping anything", async (page) => {
  const shown = () => page.ev(`(() => {
    const text = (s) => document.querySelector(s)?.textContent ?? null;
    const count = document.getElementById("warning-count");
    return { count: count.checkVisibility() ? count.textContent : null, warnings: text("#output pre.warnings"),
             errors: text("#output pre.errors"), output: document.getElementById("output").innerText };
  })()`);
  await page.open();
  await page.untilChecked();
  assert.equal((await shown()).count, null, "no warnings in the example");
  await page.setSource(WARNED);
  await page.untilChecked();
  let s = await shown();
  assert.equal(s.count, "1 warning");
  assert.match(s.output, /Every definition type-checks/);
  assert.match(s.warnings, /^\[W-MODULE-NAME\] `a` in this type/);
  assert.equal(s.errors, null);
  // With an error as well: each in its own box, in its own colour.
  await page.setSource(WARNED + "\ndef bad : Nat := rfl\n");
  await page.untilStatus("Doesn’t check");
  s = await shown();
  assert.equal(s.count, "1 warning");
  assert.match(s.errors, /E-TYPE-MISMATCH/);
  assert.doesNotMatch(s.errors, /W-MODULE-NAME/);
  assert.match(s.warnings, /W-MODULE-NAME/);
  const colours = await page.ev(`["pre.errors", "pre.warnings"].map((s) => getComputedStyle(document.querySelector(s)).color)`);
  assert.notEqual(colours[0], colours[1], "errors and warnings look different");
  // Other tabs show them with the errors, and work as usual once it checks.
  await page.tab("tests");
  await page.until(`document.querySelector("#output pre.warnings")`, 30000, "the warnings in the Tests tab");
  await page.setSource(WARNED + `\ntest "sized" := size [1, 2] <= 2\n`);
  await page.until(`document.querySelector(".summary")?.textContent === "1 test: 1 passed, 0 failed"`);
  assert.equal((await shown()).count, "1 warning");
  // The count goes to the Check tab.
  await page.click("#warning-count");
  await page.until(`document.querySelector("#output pre.warnings")`, 30000, "the Check tab's warnings");
  assert.equal(await page.ev(`document.querySelector('[aria-selected="true"]').dataset.view`), "check");
  // Gone once fixed.
  await page.setSource(WARNED.replace("List a", "[a : Type] -> List a"));
  await page.untilChecked();
  s = await shown();
  assert.equal(s.count, null);
  assert.equal(s.warnings, null);
});

test("a ? program shows its open goals in a Goals section", async (page) => {
  const shown = () => page.ev(`(() => {
    const text = (s) => document.querySelector(s)?.textContent ?? null;
    return { goals: text("#output pre.goals"), errors: text("#output pre.errors"),
             headings: [...document.querySelectorAll("#output h2")].map((h) => h.textContent),
             status: document.getElementById("status").textContent,
             output: document.getElementById("output").innerText };
  })()`);
  await page.open();
  await page.untilChecked();
  assert.equal((await shown()).goals, null, "no goals in the example");
  await page.setSource("def two : Nat := 2\n\ntheorem two_is_two : two = 2 := ?\n");
  await page.untilStatus("1 goal open");
  let s = await shown();
  assert.deepEqual(s.headings, ["Goals (1 open)"]);
  assert.match(s.goals, /^in `two_is_two`\n⊢ two = 2/);
  assert.match(s.goals, /⊢ two = 2/);
  assert.equal(s.errors, null);
  assert.doesNotMatch(s.output, /Every definition type-checks/);
  // A goal with names in scope lists them (the server's message carries the context).
  await page.setSource("theorem plus_zero (n : Nat) : n + 0 = n := ?\n");
  await page.untilStatus("1 goal open");
  assert.match((await shown()).goals, /^in `plus_zero`\nn: Nat\n⊢ /);
  // Beside an error: the goals come first, the errors in their own box.
  await page.setSource("def two : Nat := 2\n\ntheorem two_is_two : two = 2 := ?\n\ndef bad : Nat := rfl\n");
  await page.untilStatus("Doesn’t check");
  s = await shown();
  assert.deepEqual(s.headings, ["Goals (1 open)", "Errors"]);
  assert.match(s.goals, /⊢ two = 2/);
  assert.match(s.errors, /E-TYPE-MISMATCH/);
  assert.doesNotMatch(s.errors, /GOAL/);
  const colours = await page.ev(`["pre.errors", "pre.goals"].map((s) => getComputedStyle(document.querySelector(s)).color)`);
  assert.notEqual(colours[0], colours[1], "errors and goals look different");
  // Gone once filled in.
  await page.setSource("def two : Nat := 2\n\ntheorem two_is_two : two = 2 := rfl\n");
  await page.untilChecked();
  assert.equal((await shown()).goals, null);
});

test("the goals panel shows the goal at the cursor, and follows it", async (page) => {
  const panel = () => page.ev(`(() => { const p = document.getElementById("goalpanel"); return p.hidden ? null : p.innerText; })()`);
  const caretAt = (needle) => page.ev(`(() => { const e = window.editor; e.focus(); const i = e.value.indexOf(${JSON.stringify(needle)}); e.setSelectionRange(i, i); return i; })()`);
  await page.open();
  await page.untilChecked();
  assert.equal(await panel(), null, "no panel for a program without goals");
  const text = "def two : Nat := 2\n\ntheorem two_is_two : two = 2 := ?\n";
  await page.setSource(text);
  await page.untilStatus("1 goal open");
  // On another declaration, where the server has nothing: no panel yet.
  await caretAt("def two");
  await new Promise((r) => setTimeout(r, 1500));
  assert.equal(await panel(), null, "nothing to show before any answer");
  // On the `?`.
  await caretAt("?");
  await page.until(`document.getElementById("goalpanel").innerText.includes("⊢ two = 2")`, 30000, "the goal at the ?");
  assert.match(await panel(), /two_is_two/);
  // Moved to where there is nothing: the last answer stays, marked.
  await caretAt("def two");
  await page.until(`document.getElementById("goalpanel").innerText.includes("Nothing at the cursor")`, 30000, "the last answer to be marked");
  assert.match(await panel(), /⊢ two = 2/);
  // The Check output keeps its Goals list.
  assert.match(await page.ev(`document.querySelector("#output pre.goals")?.textContent ?? ""`), /⊢ two = 2/);
  // Filled in: no goal, no panel.
  await page.setSource("def two : Nat := 2\n\ntheorem two_is_two : two = 2 := rfl\n");
  await page.untilChecked();
  // Filled in, the panel follows the cursor anyway: it still shows the statement's goal at the proof.
  await caretAt("rfl");
  await page.until(`document.getElementById("goalpanel").innerText.includes("two = 2")`, 30000, "the expected type at rfl");
});

test("the book's chapter 2 shows a ?'s goal in the panel", async (page) => {
  await page.open({ hash: "#book/2" });
  await page.until(`document.getElementById("example").value === "book:2" &&
    window.editor.value.includes("theorem noAndAnything")`, 60000, "the book's chapter 2");
  const text = await sourceText(page);
  const line = "theorem noAndAnything (b: Answer): both No b = No := rfl";
  assert.ok(text.includes(line), text.slice(0, 80));
  await page.setSource(text.replace(line, line.slice(0, -"rfl".length) + "?"));
  await caretAt(page, "both No b = No := ?", "both No b = No := ?".length - 1);
  await page.until(`document.getElementById("goalpanel").innerText.includes("⊢ both No b = No")`, 180000, "the goal at the ?");
  const panel = await page.ev(`document.getElementById("goalpanel").innerText`);
  assert.match(panel, /b: Answer/);
  assert.match(panel, /⊢ both No b = No/);
  assert.match(panel, /computes to No = No/);
}, { ms: 240000 });

test("a code action on the book's chapter 2 splits the theorem on b", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.ev(`location.hash = "#book/2"`);
  await page.until(`document.getElementById("example").value === "book:2" &&
    window.editor.value.includes("theorem noAndAnything")`, 60000, "the book's chapter 2");
  const text = await sourceText(page);
  const line = "theorem noAndAnything (b: Answer): both No b = No := rfl";
  assert.ok(text.includes(line), text.slice(0, 80));
  await page.setSource(text.replace(line, line.slice(0, -"rfl".length) + "?"));
  const hole = "both No b = No := ?";
  await caretAt(page, hole, hole.length - 1);
  // The server has checked the file when its goal is on show; from there the
  // list comes from what the check published, with no search (D3529).
  await page.until(`document.getElementById("goalpanel").innerText.includes("⊢ both No b = No")`, 180000, "the goal at the ?");
  const pressed = Date.now();
  await page.key(".", "Period", 190, { modifiers: CMD });
  await page.until(`document.querySelector(".pick-panel") !== null`, 60000, "the code actions");
  const listed = Date.now() - pressed;
  console.log(`  Cmd+. to the list: ${listed} ms`);
  assert.ok(listed < 3000, `the list took ${listed} ms`);
  const titles = await page.ev(`window.editor.lastCodeActions`);
  assert.ok(titles.includes("Split on `b`"), titles.join());
  assert.ok(titles.includes("Search for a proof"), titles.join());
  const picked = Date.now();
  await page.ev(`[...document.querySelectorAll(".pick-item")].find((b) => b.textContent.includes("Split on \`b\`")).click()`);
  await page.until(`window.editor.value.includes("match b with")`, 30000, "the split");
  console.log(`  Split applied in ${Date.now() - picked} ms`);
  assert.ok(Date.now() - picked < 3000, "the split waited for a search");
  assert.match(await sourceText(page),
    /theorem noAndAnything \(b: Answer\): both No b = No := match b with\n  \| Yes => \?\n  \| No => \?\n  \| Unknown => \?/);
  // The caret is on the first new ?, and the panel shows that arm's goal (D3530).
  const caret = await page.ev(`(() => { const e = window.editor; return e.value.slice(e.selectionStart - 7, e.selectionEnd) + "|" + (e.selectionEnd - e.selectionStart); })()`);
  assert.equal(caret, "Yes => ?|1", "the selection is the first ?");
  await page.until(`document.getElementById("goalpanel").innerText.includes("⊢ No = No")`, 60000, "the first arm's goal");
}, { ms: 240000 });

test("a second Cmd+. on the book's chapter 2 waits instead of saying no action", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.ev(`location.hash = "#book/2"`);
  await page.until(`document.getElementById("example").value === "book:2" &&
    window.editor.value.includes("theorem noAndAnything")`, 60000, "the book's chapter 2");
  const text = await sourceText(page);
  const line = "theorem noAndAnything (b: Answer): both No b = No := rfl";
  assert.ok(text.includes(line), text.slice(0, 80));
  await page.setSource(text.replace(line, line.slice(0, -"rfl".length) + "?"));
  const hole = "both No b = No := ?";
  await caretAt(page, hole, hole.length - 1);
  await page.until(`document.getElementById("goalpanel").innerText.includes("⊢ both No b = No")`, 180000, "the goal at the ?");
  // Keep every notice the person would have seen.
  await page.ev(`(() => {
    const notices = window.__notices = [];
    const old = window.editor.options.onNotice;
    window.editor.options.onNotice = (t) => { notices.push(t); old?.(t); };
  })()`);
  // Press before and after the ?, as the person did: the second press comes
  // while the first search is still loading the library for it.
  await caretAt(page, hole, hole.length - 1);
  await page.key("Period", "Period", 190, { modifiers: CMD });
  await caretAt(page, hole, hole.length);
  await page.key("Period", "Period", 190, { modifiers: CMD });
  await page.until(`document.querySelector(".pick-panel") !== null`, 120000, "the code actions");
  const titles = await page.ev(`window.editor.lastCodeActions`);
  assert.ok(titles.includes("Split on `b`"), titles.join());
  assert.ok(titles.includes("Search for a proof"), titles.join());
  const notices = await page.ev(`window.__notices`);
  assert.ok(!notices.includes("No code action here"), JSON.stringify(notices));
}, { ms: 240000 });

test("the goals panel shows the goal at a rewrite step in a proof with no ?", async (page) => {
  const panel = () => page.ev(`document.getElementById("goalpanel").innerText`);
  const caretAt = (needle) => page.ev(`(() => { const e = window.editor; e.focus(); const i = e.value.indexOf(${JSON.stringify(needle)}); e.setSelectionRange(i, i); return i; })()`);
  await page.open();
  await page.untilChecked();
  await page.setSource("theorem swap_eq (a: Nat) (b: Nat) (h: a = b) : b = a :=\n  rewrite h in rfl\n");
  await page.untilChecked();
  assert.equal(await page.ev(`document.querySelector("#output pre.goals")`), null, "the proof has no goals");
  await caretAt("h in rfl");
  await page.until(`document.getElementById("goalpanel").innerText.includes("b = a")`, 60000, "the goal at the rewrite");
  assert.match(await panel(), /a: Nat/);
  assert.match(await panel(), /h: a = b/);
});

test("the settings menu switches the inlay hints off, keeps the choice, and Escape closes it", async (page) => {
  const hints = () => page.ev(`document.querySelectorAll(".cm-inlay").length`);
  await page.open();
  await page.untilChecked();
  await page.setSource("def f (n: Nat): Nat :=\n  let a := n + 1\n  a\n");
  await page.untilChecked();
  await page.until(`document.querySelectorAll(".cm-inlay").length > 0`, 30000, "the let's type hint");
  await page.ev(`document.getElementById("settings-button").click()`);
  assert.equal(await page.ev(`document.getElementById("settings-menu").hidden`), false);
  assert.equal(await page.ev(`document.getElementById("settings-button").getAttribute("aria-expanded")`), "true");
  await page.ev(`document.querySelector("#settings-menu [name=letTypes]").click()`);
  await page.until(`document.querySelectorAll(".cm-inlay").length === 0`, 30000, "the hint to go");
  assert.equal(await hints(), 0);
  assert.equal(JSON.parse(await page.ev(`localStorage.getItem("stitchwort.settings")`)).letTypes, false);
  await page.ev(`document.querySelector("#settings-menu [name=letTypes]").dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true }))`);
  assert.equal(await page.ev(`document.getElementById("settings-menu").hidden`), true);
  assert.equal(await page.ev(`document.getElementById("settings-button").getAttribute("aria-expanded")`), "false");
});

/** The labels of the completion list on show, or null when there is none. */
const completions = (page) => page.ev(`(() => {
  const list = document.querySelector(".cm-tooltip-autocomplete");
  return list ? [...list.querySelectorAll("li .cm-completionLabel")].map((l) => l.textContent) : null;
})()`);

/** Puts the caret at the end of the text, with the editor focused. */
const caretAtEnd = (page) => page.ev(`(() => { const e = window.editor; e.focus(); e.setSelectionRange(e.value.length, e.value.length); })()`);

test("typing a name offers the names in scope, and accepting one inserts it", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource("def helloWorld : Nat := 1\n\ndef other : Nat := 0");
  await page.untilChecked();
  await caretAtEnd(page);
  await page.type(" + hel");
  await page.until(`!!document.querySelector(".cm-tooltip-autocomplete")`, 30000, "the completion list");
  const labels = await completions(page);
  assert.ok(labels.includes("helloWorld"), `offered ${JSON.stringify(labels)}`);
  await sleep(200); // CodeMirror ignores Enter for the first moments of a list
  await page.key("Enter", "Enter", 13);
  await page.until(`window.editor.value.trimEnd().endsWith("def other : Nat := 0 + helloWorld")`, 10000, "the name to be inserted")
    .catch(async (e) => { throw new Error(`${e.message}\n  text: ${JSON.stringify(await page.ev("window.editor.value"))}`); });
  assert.equal(await completions(page), null, "the list closes");
});

test("typing a dot after a List offers its members (through the search worker)", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource("def count (xs : List Nat) : List Nat := xs");
  await page.untilChecked();
  await caretAtEnd(page);
  await page.type(".");
  // The server checks a copy of the file with a dummy in place of the member: a few seconds.
  await page.until(`!!document.querySelector(".cm-tooltip-autocomplete")`, 60000, "the member list");
  const labels = await completions(page);
  // The list shows only the first hundred, the common functions first (shorter names, then theorems).
  assert.ok(labels.includes("map") && labels.includes("length"), `offered ${JSON.stringify(labels.slice(0, 10))}`);
  // Typing more narrows it, and accepting inserts the member.
  await page.type("len");
  await page.until(`(() => { const l = document.querySelector(".cm-tooltip-autocomplete"); return l && l.innerText.includes("length"); })()`, 30000, "the narrowed list");
  const narrowed = await completions(page);
  assert.ok(narrowed[0] === "length", `narrowed to ${JSON.stringify(narrowed.slice(0, 10))}`);
  await sleep(200);
  await page.key("Enter", "Enter", 13);
  await page.until(`window.editor.value.trimEnd().endsWith("xs.length")`, 10000, "the member to be inserted");
}, { ms: 120000 });

test("completing a library name adds its import", async (page) => {
  const head = "namespace Demo\nimport Std (List)\n\ndef f (xs : List Nat) : List Nat := xs\n";
  await page.open();
  await page.untilChecked();
  await page.setSource(head);
  await page.untilChecked();
  await caretAtEnd(page);
  await page.type("\ndef g (xs : List Nat) : List Nat := sortW");
  await page.until(`!!document.querySelector(".cm-tooltip-autocomplete")`, 30000, "the completion list");
  assert.ok((await completions(page)).includes("sortWith"));
  await sleep(200);
  await page.key("Enter", "Enter", 13);
  await page.until(`window.editor.value.includes("sortWith")`, 10000, "the name to be inserted");
  const text = await page.ev(`window.editor.value`);
  assert.match(text, /^namespace Demo\nimport Std \(List\)\nimport Std\.List \(sortWith\)\n/, text);
  assert.match(text, /:= sortWith\s*$/);
});

test("Share puts the program in the link, and opening it keeps the person's own work", async (page) => {
  const snippet = "def three : Nat := 3\n\ntheorem three_is_three : three = 3 := rfl\n";
  const mine = "def mine : Nat := 1\n";
  await page.open();
  await page.untilChecked();
  await page.setSource(snippet);
  await page.click("#share");
  await page.until(`/^#s\\//.test(location.hash)`, 10000, "the link in the address bar");
  const hash = await page.ev(`location.hash`);
  assert.match(await page.ev(`document.getElementById("link-notice").textContent`), /Link copied|address bar/);
  // The person's own work is something else.
  await page.setSource(mine);
  await page.untilChecked();
  // From a blank page: the address is the same one, and a same-document navigation would not load it.
  const openLink = async (link) => { await page.send("Page.navigate", { url: "about:blank" }); await page.open({ hash: link }); };
  await openLink(hash);
  await page.until(`window.editor.value === ${JSON.stringify(snippet)}`, 30000, "the shared text in the editor");
  assert.match(await page.ev(`document.getElementById("banner").innerText`), /shared link/);
  await page.untilChecked();
  // Opening the link did not replace the saved draft.
  assert.equal(await page.ev(`localStorage.getItem("stitchwort.draft")`), mine);
  // Back to it.
  await page.click("#banner button");
  await page.until(`window.editor.value === ${JSON.stringify(mine)}`, 30000, "the person's own text back");
  assert.equal(await page.ev(`document.getElementById("banner").hidden`), true);
  // Editing the shared text takes it over: the draft is replaced and the address no longer names the text.
  await openLink(hash);
  await page.until(`window.editor.value === ${JSON.stringify(snippet)}`, 30000, "the shared text again");
  await page.ev(`(() => { window.editor.focus(); window.editor.setSelectionRange(0, 0); })()`);
  await page.type("-- hi\n");
  await page.until(`localStorage.getItem("stitchwort.draft").startsWith("-- hi")`, 10000, "the edit saved as the draft");
  assert.equal(await page.ev(`location.hash`), "");
  // A damaged link.
  await openLink("#s/AAAA-not-deflate");
  await page.until(`/damaged/.test(document.getElementById("link-notice").textContent)`, 30000, "the notice");
});

test("Share warns about a long link, and a project shares as a link to the day", async (page) => {
  await page.open();
  await page.untilChecked();
  // Text that doesn't compress, so that its link is long.
  let seed = 12345;
  const noise = Array.from({ length: 12000 }, () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return (seed >> 8).toString(36).slice(-1); }).join("");
  await page.setSource(`-- ${noise}\n`);
  await page.click("#share");
  await page.until(`/KB/.test(document.getElementById("link-notice").textContent)`, 10000, "the warning");
  await page.pick("aoc:0");
  await page.until(`!document.getElementById("filebar").hidden`, 30000, "the project");
  await page.click("#share");
  await page.until(`/without your edits/.test(document.getElementById("link-notice").textContent)`, 10000, "the notice");
  assert.match(await page.ev(`location.hash`), /^#aoc\//);
});

test("the Evaluate tab", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.tab("eval");
  const result = await page.until(`document.querySelector(".result")?.textContent`);
  assert.equal(result, "[3, 2, 1]: List Nat");
  await page.ev(`(() => { const i = document.getElementById("eval-input"); i.value = "nope 1";
    i.form.requestSubmit(); })()`);
  assert.match(await page.until(`document.querySelector("#output pre.errors")?.textContent`), /E-UNKNOWN-NAME/);
});

test("the Evaluate tab takes import lines, which accumulate", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.tab("eval");
  await page.until(`document.querySelector(".result")?.textContent`);
  const submit = (text) => page.ev(`(() => { const i = document.getElementById("eval-input"); i.value = ${JSON.stringify(text)};
    i.form.requestSubmit(); })()`);
  // `Text.` is no prefix until it is imported (the example imports only Eq and List).
  await submit("Text.length \"ab\"");
  assert.match(await page.until(`document.querySelector("#output pre.errors")?.textContent`), /E-UNKNOWN-NAME/);
  // A bad import is the usual error, and isn't kept.
  await submit("import Std (Nope)");
  assert.match(await page.until(`document.querySelector("#output pre.errors")?.textContent.includes("E-IMPORT-UNKNOWN") && document.querySelector("#output pre.errors").textContent`), /E-IMPORT-UNKNOWN/);
  assert.equal(await page.ev(`document.getElementById("eval-imports").textContent`), "");
  await submit("import Std (Text)");
  await page.until(`document.getElementById("eval-imports").textContent === "import Std (Text)"`);
  await submit("import Std.Nat (add)");
  await page.until(`document.getElementById("eval-imports").textContent === "import Std (Text)\\nimport Std.Nat (add)"`);
  await submit("Text.length \"ab\" + add 1 2");
  assert.equal(await page.until(`document.querySelector(".result")?.textContent`), "5: Nat");
});

test("the JavaScript tab", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.tab("js");
  await page.until(`document.getElementById("output").textContent.includes("Nothing is exported")`);
  await page.pick("ex-js");
  await page.until(`document.getElementById("output").textContent.includes("ES module")`);
  const out = await page.output();
  assert.match(out, /TypeScript declarations/i);
  assert.match(out, /export declare function applyDiscount/);
  assert.match(out, /export declare function area\(/);
  assert.match(out.slice(out.search(/ES module/i)), /\bapplyDiscount\b/);
});

test("the JavaScript tab shows the declarations and the module in full, and scrolls", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.pick("ex-js");
  await page.untilChecked();
  await page.tab("js");
  await page.until(`document.getElementById("output").textContent.includes("ES module")`);
  const boxes = await page.ev(`(() => {
    const o = document.getElementById("output");
    const pres = [...o.querySelectorAll("pre")].map((p) => ({ lines: p.textContent.trimEnd().split("\\n").length,
      height: p.clientHeight, content: p.scrollHeight, lineHeight: parseFloat(getComputedStyle(p).lineHeight) }));
    return { pres, pane: o.clientHeight, paneContent: o.scrollHeight };
  })()`);
  const what = JSON.stringify(boxes);
  assert.equal(boxes.pres.length, 2, what);
  for (const p of boxes.pres) {
    // All of it shows, with no scrolling of its own.
    assert.ok(p.height >= p.content - 1, `a box scrolls by itself: ${what}`);
    assert.ok(p.height >= p.lines * p.lineHeight - 1, `a box is too short: ${what}`);
  }
  assert.ok(boxes.pres[0].lines >= 5, what);
  // The two are taller than the pane, which scrolls instead.
  assert.ok(boxes.paneContent > boxes.pane, what);
});

test("Run, with scripted input", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.pick("ex-main");
  await page.untilChecked();
  const result = await page.run();
  assert.equal(await page.ev(`document.getElementById("run-input").value`), MAIN_INPUT);
  assert.equal(await page.printed(), MAIN_OUTPUT);
  assert.match(result, /Finished in/);
  // Different input, and Ctrl+Enter from the source.
  await page.ev(`document.getElementById("run-input").value = "Grace\\n1\\n"`);
  await page.ev(`window.editor.focus()`);
  await page.run(30000, () => page.key("Enter", "Enter", 13, { modifiers: 2 }));
  assert.match(await page.printed(), /Hello, Grace!.*\n  total: 1\nThe sum is 1\. Goodbye, Grace\.\n$/s);
});

test("Run, reading all the input at once", async (page) => {
  await page.open();
  await page.untilChecked();
  // `IO.readAll` after a `IO.readLine` gives the rest, verbatim; `IO.readLine` after
  // it gives `None`.
  await page.setSource(`def textOr : Option Text -> Text
  | None => "none"
  | Some t  => t

def main () : {IO} () :=
  IO.print (textOr (IO.readLine ()))
  let rest := IO.readAll ()
  IO.print rest.lines.length.toText
  IO.print rest
  IO.print (textOr (IO.readLine ()))
`);
  await page.untilChecked();
  await page.tab("run");
  await page.ev(`document.getElementById("run-input").value = "first\\nsecond\\nthird"`);
  const result = await page.run();
  assert.match(result, /Finished in/);
  assert.equal(await page.printed(), "first\n2\nsecond\nthird\nnone\n");
});

test("Run, with an unhandled Fail in main", async (page) => {
  await page.open();
  await page.untilChecked();
  // What was printed before the failure stays, and the failure is shown as
  // an error below it, as the command line prints it.
  await page.setSource(`import Std (Fail)

def main(): {IO, Fail} () :=
  IO.print "before"
  Fail.fail "boom"
`);
  await page.untilChecked();
  await page.tab("run");
  const result = await page.run();
  assert.equal(await page.printed(), "before\n");
  assert.match(result, /error: boom/);
  assert.doesNotMatch(result, /Finished in/);
});

test("Run's errors", async (page) => {
  await page.open();
  await page.untilChecked();
  let result = await page.run();
  assert.match(result, /E-NO-MAIN/);
  assert.doesNotMatch(result, /Output/);
  // Too much output: stopped at the cap, with what fits.
  await page.setSource(printMany(1000000, "hello"));
  const started = Date.now();
  result = await page.run();
  const took = Date.now() - started;
  assert.match(result, new RegExp(`E-OUTPUT.*more than ${MAX_OUTPUT} bytes`));
  assert.equal(await page.ev(`document.querySelector(".run-result pre.program-output").textContent.length`), MAX_OUTPUT);
  console.log(`    (${Math.floor(MAX_OUTPUT / 6)} lines up to the output cap: ${took} ms)`);
  // The most lines the cap allows.
  await page.setSource(printMany(1000000, ""));
  const emptyStarted = Date.now();
  result = await page.run();
  assert.match(result, /E-OUTPUT/);
  assert.equal(await page.printed(), "\n".repeat(MAX_OUTPUT));
  console.log(`    (${MAX_OUTPUT} empty lines: ${Date.now() - emptyStarted} ms)`);
  // Reading past the end of the input too often stops at once.
  await page.setSource(readMany(1000000000));
  result = await page.run(RUN_SECONDS * 1000 / 2);
  assert.match(result, /E-INPUT.*read past the end of its input more than 10000 times/);
});

// Effectful `List.map` over 1,000,000 elements, with the page's limits
// (docs/proposals/effect-runtime.md stage 4c, D1163): web/tests/effect-shapes.sw,
// whose shapes crates/web's library tests also run. `ioRead` reads a line
// per element (an `IO` operation each); printing every element would pass
// the output cap, so `io` itself is left to the library tests.
test("effectful List.map runs at a million elements", async (page) => {
  const n = 1000000;
  const sum = n * (n - 1) / 2;
  const shapes = [
    ["ioRead", sum + n * (n + 1) / 2],
    ["checked", sum + n],
    ["asked", sum + 7 * n],
    ["askedChecked", sum + 7 * n],
    ["askedIn", sum + 7 * n],
    ["emitted", sum],
    ["emittedIn", sum],
    ["searched", sum],
    ["counted", 2 * sum],
  ];
  await page.open();
  await page.untilChecked();
  await page.setSource(readFileSync(join(here, "effect-shapes.sw"), "utf8"));
  await page.untilChecked(60000);
  await page.tab("run");
  for (const [name, total] of shapes) {
    const lines = name === "ioRead" ? Array.from({ length: n }, (_, i) => `${i + 1}\n`).join("") : "";
    // As a paste does: the page keeps a large input out of the textarea,
    // whose layout would otherwise freeze the page for minutes.
    await page.ev(`(() => { const t = document.getElementById("run-input");
      t.value = ${JSON.stringify(`${name}\n${n}\n${lines}`)}; t.dispatchEvent(new Event("input")); })()`);
    const started = Date.now();
    const result = await page.run(RUN_SECONDS * 1000 + 15000);
    assert.match(result, /Finished in/, `${name}: ${result.slice(0, 400)}`);
    assert.equal(await page.printed(), `${name} ${n}: ${total}\n`, name);
    console.log(`    (${name}: ${Date.now() - started} ms; ${result.match(/Finished in [^\n]*/)[0]})`);
  }
}, { ms: 300000 });

test("a long run streams its output, and Stop cancels it", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(SPIN);
  await page.untilChecked();
  await page.click("#run");
  // The output appears while it runs.
  await page.until(`document.querySelector(".run-result pre.program-output")?.textContent === "tick\\n"`, 10000, "tick");
  assert.match(await page.runResult(), /Running…/);
  // Checking goes on meanwhile, in its own worker.
  await page.setSource(SPIN + "\ndef bad : Nat := rfl\n");
  await page.untilStatus("Doesn’t check");
  assert.match(await page.runResult(), /Running…/);
  const result = await page.run(5000, () => page.click(".runrow button:nth-child(2)"));
  assert.match(result, /Stopped after/);
  assert.equal(await page.printed(), "tick\n");
  // The next run works.
  await page.pick("ex-main");
  await page.run();
  assert.equal(await page.printed(), MAIN_OUTPUT);
});

// Run in terminal (docs/proposals/playground-live-keys.md): keys pressed in
// the pane reach the running program one at a time, each answered by the
// next frame, which replaces the last.
const LIVE = `document.getElementById("live-screen")`;
const WALK = readFileSync(join(here, "..", "..", "examples", "accept", "terminal-walk.sw"), "utf8");
const liveScreen = (page) => page.ev(`${LIVE}.dataset.text`);
const liveState = (page) => page.ev(`${LIVE}?.dataset.state ?? ""`);
const liveStretches = (page) => page.ev(`Number(${LIVE}?.dataset.stretches ?? 0)`);

/** Presses a key in the pane and waits for the program to answer: waiting again, or over. */
async function liveKey(page, key, code, keyCode, options) {
  const before = await liveStretches(page);
  await page.key(key, code, keyCode, options);
  await page.until(`Number(${LIVE}.dataset.stretches) > ${before} && ${LIVE}.dataset.state !== "running"`, 20000, `an answer to ${key}`);
}

/** Starts terminal-walk in the terminal, and waits for its first frame. */
async function startWalk(page) {
  await page.open();
  await page.untilChecked();
  await page.setSource(WALK);
  await page.untilChecked();
  await page.tab("run");
  await page.click("#run-live");
  await page.until(`${LIVE}?.dataset.state === "waiting"`, 20000, "the first frame");
}

/** The walk's screen with the @ at `column`, `row`. */
const walkRoom = (column, row) => {
  const rows = [0, 1, 2, 3].map((r) => "#" + (r === row ? ".".repeat(column) + "@" + ".".repeat(9 - column) : ".".repeat(10)) + "#");
  return ["############", ...rows, "############", "hjkl or arrows to move, q to stop"].join("\n");
};

test("Run in terminal plays terminal-walk key by key, and ends with q", async (page) => {
  await startWalk(page);
  assert.equal(await liveScreen(page), walkRoom(0, 0));
  await liveKey(page, "l", "KeyL", 76);
  assert.equal(await liveScreen(page), walkRoom(1, 0));
  await liveKey(page, "ArrowDown", "ArrowDown", 40);
  assert.equal(await liveScreen(page), walkRoom(1, 1));
  await liveKey(page, "j", "KeyJ", 74);
  await liveKey(page, "ArrowLeft", "ArrowLeft", 37);
  assert.equal(await liveScreen(page), walkRoom(0, 2));
  await liveKey(page, "q", "KeyQ", 81);
  assert.equal(await liveState(page), "finished");
  // Keys mode ended, so the last words are on the normal screen.
  assert.equal(await liveScreen(page), "The @ stopped at column 0, row 2.");
  assert.equal(await page.ev(`document.getElementById("run").disabled`), false);
});

test("Ctrl-C stops a run in the terminal", async (page) => {
  await startWalk(page);
  await liveKey(page, "l", "KeyL", 76);
  await liveKey(page, "c", "KeyC", 67, { modifiers: 2 });
  assert.equal(await liveState(page), "interrupted");
  assert.match(await page.runResult(), /Stopped by Ctrl-C/);
  // The buttons are free again, and a scripted Run works afterwards.
  assert.equal(await page.ev(`document.getElementById("run").disabled`), false);
  await page.pick("ex-main");
  await page.run();
  assert.equal(await page.printed(), MAIN_OUTPUT);
});

test("Stop ends a run waiting in the terminal", async (page) => {
  await startWalk(page);
  await page.click(".runrow button:nth-child(2)");
  await page.until(`${LIVE}.dataset.state === "stopped"`, 5000, "stopped");
});

/** The text of the cell at `row`, `column` of the pane, and the classes of its span. */
const liveCell = (page, row, column) => page.ev(`(() => {
  const rowEl = ${LIVE}.querySelectorAll(".trow")[${row}];
  const spans = [...rowEl.children];
  const span = spans.filter((s) => Number(s.dataset.col) <= ${column}).pop();
  if (!span) return [" ", ""];
  const at = ${column} - Number(span.dataset.col);
  return at < span.textContent.length ? [span.textContent[at], span.className.replace(/ ?cur/, "")] : [" ", ""];
})()`);

/** Starts `source` in the terminal and waits for it to wait for input. */
async function startLive(page, source) {
  await page.open();
  await page.untilChecked();
  await page.setSource(source);
  await page.untilChecked();
  await page.tab("run");
  await page.click("#run-live");
  await page.until(`${LIVE}?.dataset.state === "waiting"`, 20000, "the program to wait");
}

test("terminal: frames land in the right cells, with colours", async (page) => {
  await startWalk(page);
  // Row 0 is the wall, row 1 the room's first row: # @ . . .
  assert.deepEqual(await liveCell(page, 0, 0), ["#", ""]);
  assert.deepEqual(await liveCell(page, 0, 11), ["#", ""]);
  assert.deepEqual(await liveCell(page, 1, 0), ["#", ""]);
  assert.deepEqual(await liveCell(page, 1, 1), ["@", "f3"]);
  assert.deepEqual(await liveCell(page, 1, 2), [".", ""]);
  assert.deepEqual(await liveCell(page, 1, 11), ["#", ""]);
  assert.deepEqual(await liveCell(page, 5, 0), ["#", ""]);
  assert.deepEqual(await liveCell(page, 6, 0), ["h", ""]);
  assert.deepEqual(await liveCell(page, 7, 0), [" ", ""]);
  // The @ moves with the next frame; the old cell is plain again.
  await liveKey(page, "l", "KeyL", 76);
  assert.deepEqual(await liveCell(page, 1, 1), [".", ""]);
  assert.deepEqual(await liveCell(page, 1, 2), ["@", "f3"]);
  // The grid is 80 columns by 24 rows.
  assert.equal(await page.ev(`${LIVE}.querySelectorAll(".trow").length`), 24);
});

const STYLES = `import Std (Ansi, IO, Terminal, Text)
import Std.Ansi.Colour (Red)

def show (): {Terminal} () :=
  Terminal.draw ["\${Ansi.bold (Ansi.colour Red "hot")} \${Ansi.reverse "inv"}", "plain"]
  match Terminal.readKey () with
    | _ => ()

def main (): {IO} () :=
  IO.print "before"
  Terminal.toIO (() => show ())
  IO.print "after"
`;

test("terminal: colour, bold and reverse make styled spans, and the normal screen comes back", async (page) => {
  await startLive(page, STYLES);
  assert.equal(await page.ev(`${LIVE}.dataset.keys`), "keys");
  assert.equal(await liveScreen(page), "hot inv\nplain");
  assert.deepEqual(await liveCell(page, 0, 0), ["h", "f1 bd"]);
  assert.deepEqual(await liveCell(page, 0, 2), ["t", "f1 bd"]);
  assert.deepEqual(await liveCell(page, 0, 3), [" ", ""]);
  assert.deepEqual(await liveCell(page, 0, 4), ["i", "rv"]);
  assert.deepEqual(await liveCell(page, 1, 0), ["p", ""]);
  // Bold really is bold, and reverse swaps the colours.
  assert.equal(await page.ev(`getComputedStyle(${LIVE}.querySelector(".bd")).fontWeight`), "700");
  const [fg, bg] = await page.ev(`(() => { const s = getComputedStyle(${LIVE}.querySelector(".rv")); return [s.color, s.backgroundColor]; })()`);
  assert.notEqual(fg, bg);
  // A key ends the game; the screen from before it is back, with what came after.
  await liveKey(page, "x", "KeyX", 88);
  assert.equal(await liveState(page), "finished");
  assert.equal(await page.ev(`${LIVE}.dataset.keys`), "line");
  assert.equal(await liveScreen(page), "before\nafter");
});

const GREETER = `import Std (IO, Text)

def main (): {IO} () :=
  match IO.readLine () with
    | Some name => IO.print "hello \${name}"
    | None => IO.print "no input"
`;

/** Types `text` into the focused pane, a key at a time. */
async function liveType(page, text) {
  for (const ch of text) {
    const upper = ch.toUpperCase();
    await page.key(ch, upper >= "A" && upper <= "Z" ? `Key${upper}` : "Digit0", upper.charCodeAt(0));
  }
}

test("terminal: readLine is echoed and edited in the pane, and Enter sends it", async (page) => {
  await startLive(page, GREETER);
  assert.equal(await page.ev(`${LIVE}.dataset.keys`), "line");
  await liveType(page, "Alx");
  await page.key("Backspace", "Backspace", 8);
  await liveType(page, "ice");
  // Echoed, not yet sent: the program is still waiting on its first line.
  await page.until(`${LIVE}.dataset.text === "Alice"`, 5000, "the echo");
  assert.equal(await liveStretches(page), 1);
  await liveKey(page, "Enter", "Enter", 13);
  assert.equal(await liveState(page), "finished");
  assert.equal(await liveScreen(page), "Alice\nhello Alice");
});

test("terminal: Ctrl-D ends the input", async (page) => {
  await startLive(page, GREETER);
  await liveKey(page, "d", "KeyD", 68, { modifiers: 2 });
  assert.equal(await liveState(page), "finished");
  assert.equal(await liveScreen(page), "no input");
});

test("terminal: Esc then Tab leaves the pane, and Tab alone goes to the program", async (page) => {
  await startWalk(page);
  const focused = `document.activeElement === ${LIVE}`;
  assert.equal(await page.ev(focused), true);
  // Tab alone is a key for the program.
  await liveKey(page, "Tab", "Tab", 9);
  assert.equal(await page.ev(focused), true);
  const before = await liveStretches(page);
  await liveKey(page, "Escape", "Escape", 27);
  await page.key("Tab", "Tab", 9);
  assert.equal(await page.ev(focused), false, "focus left the pane");
  assert.equal(await liveStretches(page), before + 1, "the Tab was not sent on");
  assert.match(await page.runResult(), /Esc then Tab/);
});

test("a runaway run is stopped by the timeout, with its output", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(SPIN);
  await page.untilChecked();
  const started = Date.now();
  const result = await page.run((RUN_SECONDS + 15) * 1000);
  const took = (Date.now() - started) / 1000;
  assert.ok(took >= RUN_SECONDS - 0.5 && took < RUN_SECONDS + 10, `stopped after ${took} s`);
  assert.match(result, new RegExp(`Stopped after ${RUN_SECONDS} s`));
  assert.equal(await page.printed(), "tick\n");
}, { ms: (RUN_SECONDS + 30) * 1000 });

// The machine keeps a program's recursion in its own memory, not on the
// browser's stack: this sum is a million calls deep and not a tail call.
// (The reference evaluator, which also keeps its pending work on the heap,
// managed this too; the test guards the machine.)
test("a deep recursion runs", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(`def sumTo : Nat -> Nat
  | 0      => 0
  | Succ n => (n + 1) + sumTo n

def main () : {IO} () :=
  IO.print (sumTo 1000000).toText
`);
  await page.untilChecked();
  const result = await page.run(30000);
  assert.match(result, /Finished in/);
  assert.equal(await page.printed(), "500000500000\n");
});

// SW-62: a list literal was a `Cons` chain as deep as it was long, which
// stopped at about 120 elements under the build's small stack guard. A long
// one is now cut into short chains joined by `append`s. (100,000 elements
// check and run in the build too, but the page then spends most of a minute
// colouring and indexing the text, so the test uses a fifth of that.)
test("a long list literal checks and runs", async (page) => {
  const n = 20000;
  const rows = Array.from({ length: n / 50 }, () => Array(50).fill("1").join(", "));
  await page.open();
  await page.untilChecked();
  await page.setSource(`import Std (List)
def xs: List Nat := [${rows.join(",\n  ")}]
def main(): {IO} () := IO.print "\${List.length xs}"
`);
  await page.untilChecked(60000);
  const result = await page.run(60000);
  assert.match(result, /Finished in/);
  assert.equal(await page.printed(), `${n}\n`);
}, { ms: 150000 });

// No program is known to crash the compiler any more: its depth guards stop
// deep programs with E-RESOURCE first. So this test serves a worker that
// runs the tests of a program containing CRASH with the engine's stack almost used up,
// which overflows it inside the WebAssembly, as a deep program once did.
const CRASH = "-- crash the engine's stack";
const crashing = (worker) => {
  const tests = 'test: () => b.test(data.source, data.known ?? ""),';
  assert.ok(worker.includes(tests), "the worker tests with b.test(data.source, …)");
  return worker.replace(tests, `test: () => data.source.includes(${JSON.stringify(CRASH)})
      ? withoutStack(() => b.test(data.source, "")) : b.test(data.source, data.known ?? ""),`) + `
// For the browser tests: runs f with only a little of the stack left, so
// that the stack runs out inside the WebAssembly. It recurses until the
// stack runs out, then calls f a few frames up while unwinding. If only
// JavaScript ran out there (f's glue, before the WebAssembly was entered),
// nothing in the instance was interrupted, so it tries again a frame higher,
// until f either finishes or runs out of stack with WebAssembly on it.
// (Measuring the depth with one function, then descending most of the way
// with another, left a varying amount of stack: their frame sizes vary with
// how the engine has compiled each, so sometimes f had room to finish.)
function withoutStack(f) {
  f();
  for (let frames = 1; ; frames++) {
    let up = 0;
    const go = () => {
      try {
        go();
      } catch (e) {
        if (!(e instanceof RangeError) || ++up < frames) throw e;
        let done;
        try { done = { value: f() }; } catch (error) { done = { error }; }
        // Thrown as a plain object, which the frames above pass on.
        throw done;
      }
    };
    const limit = Error.stackTraceLimit;
    Error.stackTraceLimit = 1000;
    let done;
    try { go(); } catch (thrown) { done = thrown; } finally { Error.stackTraceLimit = limit; }
    if (done instanceof Error) throw done;
    if (!("error" in done)) return done.value;
    if (!(done.error instanceof RangeError) || /wasm:\\/\\//.test(done.error.stack)) throw done.error;
  }
}
`;
};

test("after a crash, the next request starts a fresh compiler", async (page) => {
  overrides.set("/playground-worker.js", crashing(readFileSync(join(root, "playground-worker.js"), "utf8")));
  await page.open();
  await page.untilChecked();
  await page.setSource("def x : Nat := 1\n" + CRASH + "\n");
  await page.tab("tests");
  await page.untilStatus("The compiler crashed");
  assert.match(await page.output(), /The compiler crashed \(RangeError: Maximum call stack size exceeded\)/);
  assert.match(await page.output(), /It has been restarted/);
  await page.setSource("def x : Nat := 1\n");
  await page.untilChecked();
  await page.pick("ex-main");
  await page.run();
  assert.equal(await page.printed(), MAIN_OUTPUT);
}, { ms: 120000 });

for (const [how, patch] of [
  ["the Worker constructor throws", `window.Worker = function () { throw new Error("workers are blocked"); };`],
  ["the worker script is missing", `{ const W = window.Worker; window.Worker = function (url, opts) { return new W("missing-worker.js", opts); }; }`],
]) {
  test(`the compiler runs in the page when ${how}`, async (page) => {
    await page.open({ patch });
    await page.untilChecked();
    assert.ok(page.console.some((m) => m.startsWith("warning: The playground's worker didn't start")), page.console.join("\n"));
    await page.pick("ex-tests");
    await page.tab("tests");
    await page.until(`/^4 tests: 3 passed, 1 failed( \\(4 from the cache\\))?$/.test(document.querySelector(".summary")?.textContent ?? "")`);
    await page.pick("ex-main");
    await page.run();
    assert.equal(await page.printed(), MAIN_OUTPUT);
  });
}

test("syntax colouring stays aligned with the text", async (page) => {
  await page.open();
  await page.untilChecked();
  // A long program, scrolled both ways.
  const main = await page.ev(`document.getElementById("ex-main").textContent`);
  let long = "";
  while (long.split("\n").length < 1500) long += main;
  long += "longLine = " + "\"a long string\" ++ ".repeat(60) + "\"end\"\n";
  await page.setSource(long);
  await assertAligned(page, "a long program");
  for (const [top, left] of [[0.5, 0], [1, 0], [1, 1]]) {
    await page.ev(`(() => { const s = window.editor.view.scrollDOM;
      s.scrollTop = (s.scrollHeight - s.clientHeight) * ${top}; s.scrollLeft = (s.scrollWidth - s.clientWidth) * ${left}; })()`);
    await sleep(100);
    assert.ok(await page.ev(`window.editor.scrollTop > 0`), "it scrolled");
    await assertAligned(page, `scrolled to ${top}, ${left}`);
  }
  // Typing at the end.
  await page.ev(`(() => { const s = window.editor; s.focus(); s.setSelectionRange(s.value.length, s.value.length); })()`);
  await page.type("\n\n-- typed <b>&amp; \"str\\\"ing\" 'x' 42");
  await sleep(100);
  await assertAligned(page, "after typing at the end");
  assert.ok(await page.ev(`window.editor.marked().comment.includes(${JSON.stringify("-- typed <b>&amp; \"str\\\"ing\" 'x' 42")})`), "the typed comment is coloured");
});

test("interpolation is coloured as code inside a string", async (page) => {
  await page.open();
  await page.untilChecked();
  const source = 'def world : Text := "w"\n' +
    'test "t" := "a ${ 1 + 2 } b ${"x ${world} y"} \\${z}" == "x"';
  await page.setSource(source);
  await sleep(100);
  const marked = await page.ev(`(() => {
    const m = window.editor.marked();
    return { string: m.string ?? [], interp: m.interp ?? [], number: m.number ?? [] };
  })()`);
  assert.deepEqual(marked.number, ["1", "2"], JSON.stringify(marked.number));
  assert.deepEqual(marked.interp, ["${", "}", "${", "${", "}", "}"], JSON.stringify(marked.interp));
  for (const piece of ['"w"', '"t"', '"a ', " b ", '"x ', ' y"']) {
    assert.ok(marked.string.includes(piece), `${JSON.stringify(piece)} is a string piece: ${JSON.stringify(marked.string)}`);
  }
  assert.ok(marked.string.includes(' \\${z}"'), `the escaped dollar stays a string: ${JSON.stringify(marked.string)}`);
  assert.ok(!marked.string.some((s) => s.includes("world")), `world in the interpolation isn't string-coloured: ${JSON.stringify(marked.string)}`);
});

test("a text block is coloured as one string over its lines", async (page) => {
  await page.open();
  await page.untilChecked();
  const source = 'test "t" := """\n  say "hi" ${1 + 2}\n  more \\"""\n  """ == "x"\n';
  await page.setSource(source);
  await sleep(100);
  const marked = await page.ev(`(() => {
    const m = window.editor.marked();
    return { string: m.string ?? [], interp: m.interp ?? [], number: m.number ?? [] };
  })()`);
  assert.deepEqual(marked.number, ["1", "2"], JSON.stringify(marked.number));
  assert.deepEqual(marked.interp, ["${", "}"], JSON.stringify(marked.interp));
  assert.ok(marked.string.includes('"""\n  say "hi" '), JSON.stringify(marked.string));
  assert.ok(marked.string.includes('\n  more \\"""\n  """'), JSON.stringify(marked.string));
  assert.ok(marked.string.includes('"x"'), JSON.stringify(marked.string));
});

test("`|>` is coloured as one operator", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource("def n : Nat := [1, 2]\n  |> .sum\n");
  await sleep(100);
  const operators = await page.ev(`window.editor.marked().operator`);
  assert.ok(operators.includes("|>"), JSON.stringify(operators));
});

test("the draft, input and tab are kept across a reload", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.pick("ex-main");
  await page.untilChecked();
  await page.ev(`(() => { const s = window.editor; s.focus(); s.setSelectionRange(0, 0); })()`);
  await page.type("-- a draft\n");
  await page.tab("run");
  await page.ev(`(() => { const i = document.getElementById("run-input"); i.value = "Bo\\n"; i.dispatchEvent(new Event("input")); })()`);
  await page.tab("tests");
  const draft = await page.ev(`window.editor.value`);
  assert.ok(draft.startsWith("-- a draft\n-- A program"));
  await page.reload();
  await page.until(`document.querySelector(".summary")`);
  assert.equal(await page.ev(`window.editor.value`), draft);
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-main");
  assert.equal(await page.ev(`document.querySelector('[aria-selected="true"]').dataset.view`), "tests");
  await assertAligned(page, "the restored draft");
  await page.tab("run");
  assert.equal(await page.ev(`document.getElementById("run-input").value`), "Bo\n");
});

test("Tab indents, and undo still undoes earlier typing", async (page) => {
  await page.open();
  await page.untilChecked();
  const original = await page.ev(`window.editor.value`);
  await page.ev(`(() => { const s = window.editor; s.focus(); s.setSelectionRange(s.value.length, s.value.length); })()`);
  await page.type("x : Nat");
  await page.key("Tab", "Tab", 9);
  await page.type("-- after a tab");
  await sleep(50);
  const value = () => page.ev(`window.editor.value`);
  assert.equal(await value(), original + "x : Nat  -- after a tab");
  assert.ok(await page.ev(`document.activeElement.closest("#editor") !== null`), "the editor keeps the focus");
  await assertAligned(page, "after Tab");
  // Undo goes back through these, in order (the browser decides which
  // edits it merges into one step), to the start; redo comes back.
  const states = ["x : Nat  -- after a tab", "x : Nat  ", "x : Nat", ""].map((s) => original + s);
  const modifier = process.platform === "darwin" ? 4 : 2;
  const step = async (command, modifiers) => {
    const before = await value();
    await page.key("z", "KeyZ", 90, { modifiers, commands: [command] });
    const after = await value();
    assert.ok(after !== before, `${command} changed nothing`);
    await assertAligned(page, `after ${command}`);
    assert.equal(await page.ev(`localStorage.getItem("stitchwort.draft")`), after, "the draft is what's shown");
    return after;
  };
  const seen = [];
  while (seen.at(-1) !== original && seen.length < states.length) {
    const now = await step("undo", modifier);
    assert.ok(states.indexOf(now) > states.indexOf(seen.at(-1) ?? states[0]), `undo went to ${JSON.stringify(now.slice(original.length))}`);
    seen.push(now);
  }
  assert.equal(seen.at(-1), original, "undo reached the start");
  while ((await value()) !== states[0] && seen.length < 2 * states.length) seen.push(await step("redo", modifier | 8));
  assert.equal(await value(), states[0], "redo came back");
  console.log(`    (undo went back through ${seen.length / 2} steps)`);
});

test("Format rewrites the text, undo restores it, and a syntax error leaves it alone", async (page) => {
  await page.open();
  await page.untilChecked();
  const value = () => page.ev(`window.editor.value`);
  const modifier = process.platform === "darwin" ? 4 : 2;
  // Typed (not assigned), so that the browser has it in its undo history.
  const typeSource = async (text) => {
    await page.ev(`(() => { const s = window.editor; s.focus(); s.select(); })()`);
    await page.type(text);
    await sleep(50);
    assert.equal(await value(), text);
  };
  const messy = "def   x :  Nat :=   5\n\n\n\ndef y : Nat :=\n        x\n";
  await typeSource(messy);
  // The caret is at the end of `x`'s line, after the last token.
  await page.click("#format");
  await page.until(`window.editor.value !== ${JSON.stringify(messy)}`, 10000, "the formatted text");
  const formatted = await value();
  assert.equal(formatted, "def x: Nat := 5\n\ndef y: Nat :=\n  x\n");
  assert.equal(await page.ev(`localStorage.getItem("stitchwort.draft")`), formatted, "the draft is the formatted text");
  await assertAligned(page, "after Format");
  // The caret was at the end of the text, and is still there.
  assert.equal(await page.ev(`window.editor.selectionStart`), formatted.length);
  // One undo step takes it back, then redo brings it again.
  await page.key("z", "KeyZ", 90, { modifiers: modifier, commands: ["undo"] });
  await sleep(100);
  assert.equal(await value(), messy, "undo restored the original text");
  await page.key("z", "KeyZ", 90, { modifiers: modifier | 8, commands: ["redo"] });
  await sleep(100);
  assert.equal(await value(), formatted, "redo formatted it again");
  // Shift+Alt+F does the same; the text is already formatted, so nothing changes.
  await page.key("F", "KeyF", 70, { modifiers: 9 });
  await sleep(300);
  assert.equal(await value(), formatted);

  // Shift+Alt+F formats a messy file...
  await typeSource(messy);
  await page.key("F", "KeyF", 70, { modifiers: 9 });
  await page.until(`window.editor.value === ${JSON.stringify(formatted)}`, 10000, "Shift+Alt+F to format");

  // ...and a file with a syntax error is left as it is, its error underlined.
  const broken = "def   x :  Nat :=\n";
  await typeSource(broken);
  await page.click("#format");
  await sleep(1500);
  assert.equal(await value(), broken, "a refused file is unchanged");
  await page.until(`!!document.querySelector("#editor .cm-lint-marker-error")`, 30000, "the syntax error marked");
});

test("the page fills the window, and long results scroll in their pane", async (page) => {
  const geometry = () => page.ev(`(() => {
    const s = document.querySelector("#editor .cm-editor").getBoundingClientRect();
    const o = document.getElementById("output");
    return { page: document.documentElement.scrollHeight, window: innerHeight, editorBottom: Math.round(s.bottom),
             outputBottom: Math.round(o.getBoundingClientRect().bottom) };
  })()`);
  await page.open();
  await page.untilChecked();
  const empty = await geometry();
  assert.ok(empty.editorBottom <= empty.window, JSON.stringify(empty));
  assert.equal(empty.outputBottom, empty.editorBottom, "the panes end together");
  await page.pick("ex-js");
  await page.tab("js");
  await page.until(`document.getElementById("output").textContent.includes("ES module")`);
  assert.deepEqual(await geometry(), empty);
});

test("on a phone, the panes stack and nothing scrolls sideways", async (page) => {
  // A phone-sized screen. Without a viewport tag, a mobile browser would lay
  // the page out 980 px wide and shrink it.
  await page.send("Emulation.setDeviceMetricsOverride", { width: 400, height: 860, deviceScaleFactor: 2, mobile: true });
  await page.open();
  await page.untilChecked();
  const layout = () => page.ev(`(() => {
    const box = (s) => { const r = document.querySelector(s).getBoundingClientRect();
                         return { left: r.left, right: r.right, top: r.top, bottom: r.bottom, width: r.width }; };
    return { width: innerWidth, scrollWidth: document.documentElement.scrollWidth,
             source: box("#editor .cm-editor"), results: box('[aria-label="Results"]'), output: box("#output"),
             fontSize: parseFloat(getComputedStyle(document.querySelector("#editor .cm-editor")).fontSize) };
  })()`);
  for (const [example, view] of [["ex-lists", "check"], ["ex-js", "js"], ["ex-tests", "tests"], ["ex-main", "run"]]) {
    await page.pick(example);
    await page.untilChecked();
    await page.tab(view);
    await sleep(300);
    const l = await layout();
    const what = `${example}, ${view}: ${JSON.stringify(l)}`;
    assert.equal(l.width, 400, what);
    assert.ok(l.scrollWidth <= l.width, `the page scrolls sideways: ${what}`);
    // The results are below the source, and both are nearly the full width.
    assert.ok(l.results.top >= l.source.bottom, what);
    for (const b of [l.source, l.output]) assert.ok(b.left >= 0 && b.right <= l.width && b.width >= l.width - 50, what);
    // Big enough that a phone doesn't zoom in when it's focused.
    assert.ok(l.fontSize >= 16, what);
  }
  // Typing still works, and the editor still draws the text.
  await page.ev(`(() => { const s = window.editor; s.focus(); s.setSelectionRange(s.value.length, s.value.length); })()`);
  await page.type("\n-- typed on a phone, with a line long enough that the editor has to scroll sideways");
  await sleep(100);
  assert.match(await page.ev(`window.editor.value`), /typed on a phone/);
  await assertAligned(page, "on a phone");
  assert.ok((await layout()).scrollWidth <= 400, "the page doesn't scroll sideways after a long line");
});

test("dragging the editor's corner resizes it", async (page) => {
  await page.open();
  await page.untilChecked();
  const box = () => page.ev(`(() => { const s = document.querySelector("#editor .cm-editor");
    s.scrollIntoView({ block: "end" }); const r = s.getBoundingClientRect();
    return { x: r.right, y: r.bottom, height: r.height }; })()`);
  const drag = async (dy) => {
    const before = await box();
    const [x, y] = [before.x - 4, before.y - 4];
    await page.send("Input.dispatchMouseEvent", { type: "mouseMoved", x, y });
    await page.send("Input.dispatchMouseEvent", { type: "mousePressed", x, y, button: "left", clickCount: 1 });
    for (let i = 1; i <= 10; i++) {
      await page.send("Input.dispatchMouseEvent", { type: "mouseMoved", x, y: y + (dy * i) / 10, button: "left", buttons: 1 });
    }
    await page.send("Input.dispatchMouseEvent", { type: "mouseReleased", x, y: y + dy, button: "left", clickCount: 1 });
    await sleep(100);
    return { before: before.height, after: (await box()).height };
  };
  const taller = await drag(300);
  assert.ok(Math.abs(taller.after - taller.before - 300) <= 2, `taller: ${JSON.stringify(taller)}`);
  await assertAligned(page, "after making it taller");
  const shorter = await drag(-150);
  assert.ok(Math.abs(shorter.before - shorter.after - 150) <= 2, `shorter: ${JSON.stringify(shorter)}`);
  await assertAligned(page, "after making it shorter");
});

// The AoC project (docs/proposals/playground-projects.md) -----------------------

/** The days in the dropdown's order (2025, then 2024), with what each prints for its example input and for
 *  its real input (the CLI's answers). */
const answers = (part1, part2) => `Part 1: ${part1}\nPart 2: ${part2}\n`;
const AOC_DAYS = [
  { year: 2025, day: 1, example: answers(3, 6), puzzle: answers(1076, 6379) },
  { year: 2025, day: 2, example: answers(1227775554, 4174379265), puzzle: answers(16793817782, 27469417404) },
  { year: 2025, day: 3, example: answers(357, 3121910778619), puzzle: answers(17263, 170731717900423) },
  { year: 2025, day: 4, example: answers(13, 43), puzzle: answers(1397, 8758) },
  { year: 2025, day: 5, example: answers(3, 14), puzzle: answers(525, 333892124923577) },
  { year: 2025, day: 6, example: answers(4277556, 3263827), puzzle: answers(4722948564882, 9581313737063) },
  { year: 2025, day: 7, example: answers(21, 40), puzzle: answers(1594, 15650261281478) },
  { year: 2025, day: 8, example: answers(20, 25272), puzzle: answers(42315, 8079278220) },
  { year: 2025, day: 9, example: answers(50, 24), puzzle: answers(4756718172, 1665679194) },
  { year: 2024, day: 1, example: answers(11, 31), puzzle: answers(2066446, 24931009) }
];
/** Every day has proofs. */
const dayStatus = (day, year = 2025) => `${year} / Day ${day} and its proofs checked by the kernel`;
const DAY2 = "src/Aoc/Year2025/Day02/Day02.sw";
/** Day 2's own files, which come first among its tabs; then the files of the namespaces it uses (all of
 *  Aoc.Common, so more as other days add to it), then the spec. */
const DAY2_OWN_TABS = ["Day02.sw", "Tests/BruteForce.sw", "Tests/Examples.sw", "Tests/Input.sw", "Proofs/Part1.sw", "Proofs/Part2.sw", "Proofs/Repeated.sw", "Proofs/Templates.sw"];
const DAY2_TABS_READY = `[...document.querySelectorAll("#filetabs button")].some((b) => b.firstChild.textContent === "Spec/Spec.sw")`;

/** The labels of the file tabs. */
const fileTabs = (page) => page.ev(`[...document.querySelectorAll("#filetabs button")].map((b) => b.firstChild.textContent)`);
/** Opens the dropdown's `index`th day, day `day` of its year, and waits for it to check; its tabs are those of
 *  its namespaces. */
async function openEntry(page, index, day, year) {
  await page.pick(`aoc:${index}`);
  await page.untilStatus(dayStatus(day, year), 60000);
}
/** The text the closed picker shows. */
const pickerLabel = (page) => page.ev(`document.getElementById("example").selectedOptions[0].textContent`);
/** Opens a day of 2025. */
const openDay = (page, day) => openEntry(page, day - 1, day);
const openTab = (page, label) => page.ev(`[...document.querySelectorAll("#filetabs button")].find((b) => b.firstChild.textContent === ${JSON.stringify(label)}).click()`);
const sourceText = (page) => page.ev(`window.editor.value`);
/** The bundled text of a file, fetched as the page does. */
const bundled = (page, path) => page.ev(`fetch("pkg/projects/aoc/${path}").then((r) => r.text())`);
/** Sets the source (the open file), as typing would, and waits for the checked status to be blank first. */
const edit = (page, text) => page.setSource(text);
/** Waits for a stored edit of `path` to be saved. */
const savedEdit = (page, path) => page.until(`localStorage.getItem(${JSON.stringify("stitchwort.project.aoc.file." + path)})`, 10000, `a saved edit of ${path}`);
/** The AoC groups as the page bundles them: the day folders under `pkg/projects/aoc/src/Aoc`, the source
 *  `bundle-projects.sh` builds the dropdown's days from. Newest year first, days in order. */
function bundledAocGroups() {
  const aoc = join(root, "pkg", "projects", "aoc", "src", "Aoc");
  const byYear = new Map();
  for (const yearFolder of readdirSync(aoc)) {
    const year = /^Year(\d{4})$/.exec(yearFolder)?.[1];
    if (!year) continue;
    const days = [];
    for (const dayFolder of readdirSync(join(aoc, yearFolder))) {
      const day = /^Day(\d{2})$/.exec(dayFolder)?.[1];
      if (day && existsSync(join(aoc, yearFolder, dayFolder, `${dayFolder}.sw`))) days.push(Number(day));
    }
    if (days.length) byYear.set(year, days.sort((a, b) => a - b));
  }
  return [...byYear.keys()].sort().reverse().map((year) => ({
    label: `Advent of Code ${year}`,
    days: byYear.get(year).map((day) => `${year} / Day ${day}`)
  }));
}

test("the AoC days are listed, and a day opens its program with its files as tabs", async (page) => {
  await page.open();
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("filebar").hidden`), true, "no file tabs for a single file");
  const years = await page.until(`(() => { const groups = [...document.querySelectorAll("#example optgroup")]
    .filter((g) => g.label.startsWith("Advent of Code"));
    return groups.length > 0 && groups.map((g) => ({ label: g.label, days: [...g.children].map((o) => o.textContent) })); })()`,
    10000, "the AoC groups");
  assert.deepEqual(years, bundledAocGroups());
  // The closed picker and the status name the year.
  await openEntry(page, 9, 1, 2024);
  assert.equal(await pickerLabel(page), "2024 / Day 1");
  assert.equal(await page.status(), "2024 / Day 1 and its proofs checked by the kernel");
  await shots(page, "year-label-2024");
  await openDay(page, 2);
  assert.equal(await pickerLabel(page), "2025 / Day 2");
  assert.equal(await page.status(), "2025 / Day 2 and its proofs checked by the kernel");
  assert.equal(await page.ev(`document.getElementById("filebar").hidden`), false);
  await page.until(DAY2_TABS_READY, 10000, "day 2's tabs");
  const tabs = await fileTabs(page);
  assert.deepEqual(tabs.slice(0, DAY2_OWN_TABS.length), DAY2_OWN_TABS);
  for (const used of ["Common/Range.sw", "Common/Proofs/Range.sw", "Spec/Spec.sw"]) assert.ok(tabs.includes(used), `${used} in ${tabs}`);
  assert.equal(await sourceText(page), await bundled(page, DAY2));
  assert.match(await page.output(), /Every definition type-checks/);
  await assertAligned(page, "day 2");
  // Switching tabs shows another file of the day.
  await openTab(page, "Proofs/Part1.sw");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Proofs/Part1.sw"`);
  assert.equal(await sourceText(page), await bundled(page, "src/Aoc/Year2025/Day02/Proofs/Part1.sw"));
  assert.equal(await page.status(), dayStatus(2), "still checked");
  await assertAligned(page, "day 2 proofs tab");
  // Another day has its own files as tabs.
  await openDay(page, 4);
  await page.until(`document.querySelectorAll("#filetabs button")[0]?.firstChild.textContent === "Day04.sw"`);
  const day4 = await fileTabs(page);
  assert.ok(day4.includes("Proofs/Part1.sw") && day4.includes("Tests/Spec.sw"), `day 4's tabs: ${day4}`);
}, { ms: 120000 });

test("every day checks, with its proofs, and runs on its example and on its puzzle input", async (page) => {
  await page.open();
  await page.untilChecked();
  for (const [index, { year, day, example, puzzle }] of AOC_DAYS.entries()) {
    const name = `${year} day ${day}`;
    const file = `${year}/day0${day}.txt`;
    await openEntry(page, index, day, year);
    const input = await page.until(`document.getElementById("run-input")?.value || (document.getElementById("run").click(), false)`, 10000, "the input");
    assert.equal(input, await page.ev(`fetch("pkg/projects/aoc/examples/${file}").then((r) => r.text())`), `${name}: the input box has the example`);
    assert.equal(await page.ev(`document.getElementById("run").title`), `Run Aoc.Year${year}.Day0${day}.main (Ctrl+Enter)`);
    await page.run(30000);
    assert.equal(await page.printed(), example, `${name} on its example`);
    // The puzzle input, chosen next to the example.
    await page.ev(`(() => { const s = document.getElementById("input-choice"); s.value = "inputs/${file}";
      s.dispatchEvent(new Event("change")); })()`);
    const puzzleInput = await page.ev(`fetch("pkg/projects/aoc/inputs/${file}").then((r) => r.text())`);
    await page.until(`document.getElementById("run-input").value === ${JSON.stringify(puzzleInput)}`, 10000, "the puzzle input");
    await page.run(60000);
    assert.equal(await page.printed(), puzzle, `${name} on its puzzle input`);  }
}, { ms: 360000 });

test("the AoC tests are grouped by namespace, and cached on the next visit", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 3);
  await page.tab("tests");
  const results = () => page.until(`(() => {
    const o = document.getElementById("output");
    const summary = o.querySelector(".summary")?.textContent;
    if (!summary || !o.querySelector("ul.tests")) return false;
    return { groups: [...o.querySelectorAll("ul.tests")].map((l) => l.dataset.namespace), summary,
             rows: [...o.querySelectorAll("ul.tests li")].map((li) => li.textContent) };
  })()`, 60000, "the tests");
  const first = await results();
  assert.equal(first.groups[0], "Aoc.Year2025.Day03.Tests");
  assert.ok(first.rows.length >= 2 && first.rows.every((r) => r.startsWith("✓")), first.rows.join("\n"));
  assert.doesNotMatch(first.summary, /failed, [1-9]|[1-9]\d* failed/);
  // `Tests/Input.sw` reads the bundled puzzle input through `include` (SW-187).
  assert.ok(first.rows.some((r) => r.includes("real input")), first.rows.join("\n"));
  await page.reload();
  await page.until(`document.getElementById("status").textContent === ${JSON.stringify(dayStatus(3))}`, 60000);
  const second = await results();
  assert.ok(second.rows.every((r) => r.endsWith("cached")), second.rows.join("\n"));
}, { ms: 120000 });

test("the real-input tests of AoC days 8 and 9 finish well within the compiler limit (D1138)", async (page) => {
  await page.open();
  await page.untilChecked();
  for (const day of [8, 9]) {
    await openDay(page, day);
    await page.tab("tests");
    const started = Date.now();
    const results = await page.until(`(() => {
      const o = document.getElementById("output");
      const summary = o.querySelector(".summary")?.textContent;
      if (!summary || !o.querySelector("ul.tests")) return false;
      return { summary, rows: [...o.querySelectorAll("ul.tests li")].map((li) => li.textContent) };
    })()`, 30000, `the Day ${day} tests`);
    console.log(`  Day ${day} tests finished in ${Date.now() - started} ms`);
    assert.ok(results.rows.some((r) => r.includes("real input")), results.rows.join("\n"));
    assert.ok(results.rows.every((r) => r.startsWith("✓")), results.rows.join("\n"));
    assert.doesNotMatch(results.summary, /failed, [1-9]|[1-9]\d* failed/);
  }
}, { ms: 120000 });

test("an error in a shared file shows in the Check tab, marks its tab, and links to its line", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.until(DAY2_TABS_READY);
  await openTab(page, "Common/Range.sw");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`);
  const range = await sourceText(page);
  await edit(page, range + "\ndef broken: Nat := rfl\n");
  await page.untilStatus("Doesn’t check", 60000);
  const shown = await page.ev(`({
    errors: [...document.querySelectorAll("#output pre.errors")].map((p) => p.textContent),
    marked: [...document.querySelectorAll("#filetabs button[data-errors]")].map((b) => b.firstChild.textContent),
    jumps: [...document.querySelectorAll("#output button.jump")].map((b) => b.textContent) })`);
  assert.ok(shown.errors.length >= 1, shown.errors.join("\n"));
  assert.match(shown.errors[0], /E-TYPE-MISMATCH/);
  // Day 2 doesn't use `broken`, so it's checked as usual (D3524).
  assert.ok(!shown.errors.some((e) => /E-NAMESPACE-FAILED|E-USES-FAILED/.test(e)), shown.errors.join("\n"));
  assert.ok(shown.marked.includes("Common/Range.sw"));
  const line = range.split("\n").length + 1;
  assert.match(shown.jumps[0], new RegExp(`^src/Aoc/Common/Range\\.sw:${line}:`));
  // Going to the other file's error, and back by the link.
  await openTab(page, "Day02.sw");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Day02.sw"`);
  await page.click("#output button.jump");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`);
  const caretLine = await page.ev(`(() => { const s = window.editor;
    return s.value.slice(0, s.selectionStart).split("\\n").length; })()`);
  assert.equal(caretLine, line, "the caret is on the error's line");
}, { ms: 120000 });

test("a saved edit survives a reload, shows on its tab, and can be reset", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  const original = await sourceText(page);
  await edit(page, original + "\n-- my edit\n");
  await savedEdit(page, DAY2);
  assert.equal(await page.ev(`document.querySelectorAll("#filetabs button[data-edited]").length`), 1);
  await page.reload();
  await page.until(`document.getElementById("status").textContent === ${JSON.stringify(dayStatus(2))}`, 60000);
  assert.equal(await sourceText(page), original + "\n-- my edit\n");
  assert.equal(await page.ev(`document.querySelector("#filetabs button[data-edited]")?.firstChild.textContent`), "Day02.sw");
  // The edit is on every day that uses the file, and the page remembers which file was open.
  await openDay(page, 5);
  await page.until(`document.querySelectorAll("#filetabs button").length >= 2`);
  assert.equal(await page.ev(`document.querySelectorAll("#filetabs button[data-edited]").length`), 0, "day 5 doesn't show day 2's file");
  await openDay(page, 2);
  assert.equal(await sourceText(page), original + "\n-- my edit\n");
  await page.pick("aoc:1");
  await page.click("#reset-file");
  await page.until(`window.editor.value === ${JSON.stringify(original)}`);
  assert.equal(await page.ev(`localStorage.getItem("stitchwort.project.aoc.file.${DAY2}")`), null, "the saved edit is gone");
  assert.equal(await page.ev(`document.querySelectorAll("#filetabs button[data-edited]").length`), 0);
  // Resetting the whole project asks first.
  await edit(page, original + "\n-- again\n");
  await savedEdit(page, DAY2);
  await page.click("#reset-project");
  assert.equal(await page.ev(`document.getElementById("reset-confirm").hidden`), false);
  assert.equal(await sourceText(page), original + "\n-- again\n", "nothing is reset before it's confirmed");
  await page.click("#reset-yes");
  await page.until(`window.editor.value === ${JSON.stringify(original)}`);
  assert.equal(await page.ev(`localStorage.getItem("stitchwort.project.aoc.file.${DAY2}")`), null);
}, { ms: 120000 });

test("when the bundled file changes under a saved edit, the edit is kept and a banner asks", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  const original = await sourceText(page);
  const mine = original + "\n-- mine\n";
  await edit(page, mine);
  await savedEdit(page, DAY2);
  const newer = original + "\n-- the new bundled version\n";
  overrides.set("/pkg/projects/aoc/" + DAY2, newer);
  await page.reload();
  await page.until(`document.getElementById("status").textContent === ${JSON.stringify(dayStatus(2))}`, 60000);
  assert.equal(await sourceText(page), mine, "the edit is kept");
  assert.match(await page.ev(`document.getElementById("banner").textContent`), /Day02\.sw has changed since you edited it/);
  // "Keep mine": the banner goes, and stays gone after a reload.
  await page.click("#keep-mine");
  assert.equal(await page.ev(`document.getElementById("banner").hidden`), true);
  assert.equal(await sourceText(page), mine);
  await page.reload();
  await page.until(`document.getElementById("status").textContent === ${JSON.stringify(dayStatus(2))}`, 60000);
  assert.equal(await page.ev(`document.getElementById("banner").hidden`), true, "no banner after keeping mine");
  assert.equal(await sourceText(page), mine);
  // Change the bundle again: "Use the new version" drops the edit.
  const newest = original + "\n-- the newest\n";
  overrides.set("/pkg/projects/aoc/" + DAY2, newest);
  await page.reload();
  await page.until(`document.getElementById("banner").textContent.includes("has changed")`, 60000);
  await page.click("#use-new");
  await page.until(`window.editor.value === ${JSON.stringify(newest)}`);
  assert.equal(await page.ev(`document.getElementById("banner").hidden`), true);
  assert.equal(await page.ev(`localStorage.getItem("stitchwort.project.aoc.file.${DAY2}")`), null);
}, { ms: 120000 });

test("F2 renames a function in every file of a project, including files that are not open", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  const text = await sourceText(page);
  // The caret on the definition of `parseRanges`, which two other files of the day use.
  await page.ev(`(() => { const e = window.editor; e.focus(); const i = e.value.indexOf("def parseRanges") + 6; e.setSelectionRange(i, i); })()`);
  // The server answers only once the whole project is checked: F2 is tried until it does.
  let prompt = false;
  for (let i = 0; i < 240 && !prompt; i++) {
    await page.key("F2", "F2", 113);
    prompt = await page.ev(`!!document.querySelector(".rename-panel input")`).catch(() => false);
    if (!prompt) await sleep(1000);
  }
  assert.ok(prompt, `F2 opens the name prompt once the project is checked (notice: ${await page.ev(`document.getElementById("link-notice").textContent`)}; focus: ${await page.ev(`document.activeElement?.className`)})`);
  assert.equal(await page.ev(`document.querySelector(".rename-panel input").value`), "parseRanges");
  await page.ev(`(() => { const i = document.querySelector(".rename-panel input"); i.value = "parseIdRanges"; i.form.requestSubmit(); })()`);
  await page.until(`!document.querySelector(".rename-panel") || !document.querySelector(".rename-problems").hidden && !document.querySelector(".rename-problems.busy")`, 420000, "the rename to finish")
    .catch(async (e) => { throw new Error(`${e.message}\n  log: ${await page.ev(`JSON.stringify(window.editor.stats.log.slice(-8))`)}`); });
  assert.equal(await page.ev(`document.querySelector(".rename-panel")?.innerText ?? ""`), "", "the prompt closes without a refusal");
  assert.equal(await sourceText(page), text.replaceAll("parseRanges", "parseIdRanges"), "the open file is edited");
  // Files that are not open changed too: the page keeps them as the project's edits.
  for (const file of ["Tests/Examples.sw", "Tests/Input.sw"]) {
    const path = `src/Aoc/Year2025/Day02/${file}`;
    const stored = await savedEdit(page, path).catch(() => null);
    assert.ok(stored, `${file} is a saved edit`);
    assert.match(stored, /parseIdRanges/);
    assert.doesNotMatch(stored, /parseRanges/);
  }
  // And the project still checks.
  await page.untilStatus(dayStatus(2), 120000);
}, { ms: 900000 });

test("Evaluate takes full names in a project", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.tab("eval");
  assert.equal(await page.until(`document.getElementById("eval-input")?.value`, 10000), "Aoc.Year2025.Day02.Tests.exampleRanges.map Aoc.Year2025.Day02.solvePart1");
  await page.until(`document.querySelector(".result")?.textContent.startsWith("Ok 1227775554")`, 30000, "the value");
  // A short name isn't in scope.
  await page.ev(`(() => { const i = document.getElementById("eval-input"); i.value = "solvePart1";
    i.form.dispatchEvent(new Event("submit", { cancelable: true })); })()`);
  await page.until(`document.querySelector("#output pre.errors")?.textContent.includes("E-UNKNOWN-NAME")`, 30000, "an unknown name");
  // An import of the project's namespace gives it.
  const submit = (text) => page.ev(`(() => { const i = document.getElementById("eval-input"); i.value = ${JSON.stringify(text)};
    i.form.requestSubmit(); })()`);
  await submit("import Aoc.Year2025.Day02 (solvePart1)");
  await page.until(`document.getElementById("eval-imports").textContent === "import Aoc.Year2025.Day02 (solvePart1)"`, 30000, "the import");
  await submit("Aoc.Year2025.Day02.Tests.exampleRanges.map solvePart1");
  await page.until(`document.querySelector(".result")?.textContent.startsWith("Ok 1227775554")`, 30000, "the value through an import");
}, { ms: 120000 });

// The roguelike (games/rogue), bundled as a second project ---------------------

test("the roguelike is a second project: it checks with its proofs, plays on keys typed in the input box, and tests", async (page) => {
  await page.open();
  await page.untilChecked();
  const groups = await page.until(`[...document.querySelectorAll("#example optgroup")].some((g) => g.label === "Roguelike") &&
    [...document.querySelectorAll("#example optgroup")].map((g) => [g.label, [...g.children].map((o) => o.value + "=" + o.textContent)])`, 10000, "every group");
  assert.deepEqual(groups.find(([label]) => label === "Roguelike"), ["Roguelike", ["rogue:0=Play", "rogue:1=Play (scripted)"]]);
  // The bundle is the sources alone.
  const manifest = await page.ev(`fetch("pkg/projects/rogue/manifest.json").then((r) => r.json())`);
  assert.ok(manifest.files.length > 15 && manifest.files.every((p) => /^src\/.*\.sw$/.test(p)), manifest.files.join());
  assert.equal(await page.ev(`fetch("pkg/projects/rogue/stitchwort.yaml").then((r) => r.status)`), 404);
  await page.pick("rogue:1");
  await page.until(`document.getElementById("status").textContent.endsWith("checked by the kernel") || document.getElementById("status").textContent === "Checked by the kernel"`, 120000, "the roguelike to check");
  assert.equal(await page.ev(`document.getElementById("filebar").hidden`), false);
  assert.ok((await fileTabs(page)).includes("Rogue.sw") && (await fileTabs(page)).includes("Proofs/Step.sw"));
  assert.equal(await page.ev(`location.hash`), "#rogue/play-scripted");
  assert.equal(await page.ev(`document.getElementById("run").title`), "Run Rogue.main (Ctrl+Enter)");
  // The hint says how to play, and the input starts as a key script.
  await page.tab("run");
  assert.match(await page.ev(`[...document.querySelectorAll(".hint")].map((e) => e.textContent).join(" ")`), /q quits/);
  assert.equal(await page.until(`document.getElementById("run-input").value`, 10000, "the key script"), "lllj.q");
  // Play: keys, then q. Each turn prints a frame, and the end is the quit line.
  await page.ev(`(() => { const i = document.getElementById("run-input"); i.value = "lllj.q"; i.dispatchEvent(new Event("input")); })()`);
  await page.run(60000);
  const printed = await page.printed();
  const frames = printed.split("\n");
  assert.match(frames.slice(0, 12).join("\n"), /#[.#]+/, "the first frame draws walls and floor");
  assert.ok(frames.some((line) => line.includes("@")), "the player is drawn");
  assert.match(frames.at(-2) ?? "", /^You gave up on level 1, on turn \d+\.$/);
  // The end of the input quits too.
  await page.ev(`(() => { const i = document.getElementById("run-input"); i.value = "l"; i.dispatchEvent(new Event("input")); })()`);
  await page.run(60000);
  assert.match(await page.printed(), /You gave up on level 1, on turn \d+\.\n$/);
  // The tests run in the playground.
  await page.tab("tests");
  const summary = await page.until(`(() => { const o = document.getElementById("output");
    return o.querySelector("ul.tests") && o.querySelector(".summary")?.textContent; })()`, 120000, "the tests");
  assert.doesNotMatch(summary, /[1-9]\d* failed/);
}, { ms: 400000 });

// The roguelike played live (docs/proposals/playground-live-keys.md, lane 4).
// The random seed comes from `IO.randomSeed ()`, which the page can't set, so
// these tests pin it the cheap way: they edit the open Rogue.sw so that main
// uses a fixed seed. The moves are still checked against the grid they find,
// not against a hard-coded dungeon.

/** Opens the live roguelike with the seed fixed to `seed`, and waits for its first frame. */
async function startRogue(page, seed) {
  await page.open({ hash: "#rogue/play" });
  await page.until(`document.getElementById("status").textContent.endsWith("checked by the kernel")`, 120000, "the roguelike to check");
  const text = await page.ev(`window.editor.value`);
  assert.match(text, /IO\.randomSeed\(\) % 2147483648/);
  await page.setSource(text.replace("IO.randomSeed() % 2147483648", String(seed)));
  await page.untilStatus("Play and its proofs checked by the kernel", 120000);
  await page.tab("run");
  assert.equal(await page.ev(`document.getElementById("run-input").hidden`), true, "a live day has no input box");
  await page.click("#run");
  await page.until(`${LIVE}?.dataset.state === "waiting"`, 60000, "the first frame");
}

/** The cells of the level (the rows above the status line), as arrays of characters. */
const rogueRows = async (page) => (await liveScreen(page)).split("\n");
const rogueAt = async (page) => {
  const rows = await rogueRows(page);
  const row = rows.findIndex((line) => line.includes("@"));
  assert.ok(row >= 0, "the @ is drawn:\n" + rows.join("\n"));
  return { row, column: rows[row].indexOf("@") };
};
const rogueTurn = async (page) => Number((await liveScreen(page)).match(/Turn (\d+)/)?.[1]);

const ROGUE_KEYS = [["l", "KeyL", 76, 0, 1], ["h", "KeyH", 72, 0, -1], ["j", "KeyJ", 74, 1, 0], ["k", "KeyK", 75, -1, 0],
                    ["ArrowRight", "ArrowRight", 39, 0, 1], ["ArrowLeft", "ArrowLeft", 37, 0, -1],
                    ["ArrowDown", "ArrowDown", 40, 1, 0], ["ArrowUp", "ArrowUp", 38, -1, 0]];

test("the roguelike plays live: keys move the @, the status line counts turns, and q restores the normal screen", async (page) => {
  await startRogue(page, 7);
  assert.equal(await page.ev(`${LIVE}.dataset.keys`), "keys");
  const first = await liveScreen(page);
  assert.match(first, /Level 1\/3 +HP \d+\/\d+ +Potions \d+ +Blows 2-\d+ +Turn 0/);
  assert.match(first, /arrows, h\/j\/k\/l/);
  // The @ is a bold yellow cell.
  const start = await rogueAt(page);
  assert.deepEqual(await liveCell(page, start.row, start.column), ["@", "f3 bd"]);
  // A wait takes a turn and leaves the @ where it is.
  await liveKey(page, ".", "Period", 190);
  assert.equal(await rogueTurn(page), 1);
  assert.deepEqual(await rogueAt(page), start);
  // Each move key moves the @ one cell its way, or (into a wall) not at all;
  // either way the turn count only goes up when a turn was taken.
  let position = start;
  let moved = 0;
  for (const [key, code, keyCode, dRow, dColumn] of [...ROGUE_KEYS, ...ROGUE_KEYS]) {
    await liveKey(page, key, code, keyCode);
    if (await liveState(page) !== "waiting") break;
    const now = await rogueAt(page);
    if (now.row !== position.row || now.column !== position.column) {
      assert.deepEqual(now, { row: position.row + dRow, column: position.column + dColumn }, `${key} moved the @ one cell`);
      moved++;
    }
    position = now;
  }
  assert.ok(moved >= 4, `the @ moved ${moved} times`);
  if (await liveState(page) === "waiting") {
    // The screen is the game's: 24 rows, the level then the status line.
    assert.equal(await page.ev(`${LIVE}.querySelectorAll(".trow").length`), 24);
    await liveKey(page, "q", "KeyQ", 81);
  }
  assert.equal(await liveState(page), "finished");
  // The game's screen is gone and the last words are on the normal one.
  assert.equal(await page.ev(`${LIVE}.dataset.keys`), "line");
  assert.match(await liveScreen(page), /^You (gave up|died) on level 1, on turn \d+\.$/);
  assert.equal(await page.ev(`document.getElementById("run").disabled`), false);
}, { ms: 400000 });

test("the roguelike survives a long game on live keys: no time or output cap ends it", async (page) => {
  await startRogue(page, 7);
  const keys = 300;
  const timings = [];
  const draws = [];
  let sent = 0;
  const waits = ["l", "h", "."];
  const codes = { l: ["KeyL", 76], h: ["KeyH", 72], ".": ["Period", 190] };
  for (; sent < keys; sent++) {
    const key = waits[sent % waits.length];
    const before = await liveStretches(page);
    await page.key(key, codes[key][0], codes[key][1]);
    await page.until(`Number(${LIVE}.dataset.stretches) > ${before} && ${LIVE}.dataset.state !== "running"`, 20000, `an answer to key ${sent}`);
    timings.push(Number(await page.ev(`${LIVE}.dataset.frameMs`)));
    draws.push(Number(await page.ev(`${LIVE}.dataset.drawMs`)));
    if (await liveState(page) !== "waiting") break;
  }
  const state = await liveState(page);
  // The game may end on its own (a monster can win), but never by a limit.
  assert.ok(state === "waiting" || state === "finished", `the run ended as ${state} after ${sent} keys`);
  if (state === "finished") assert.match(await liveScreen(page), /^You (died|won) on level \d, on turn \d+\.$/);
  else {
    assert.equal(sent, keys);
    assert.ok((await rogueTurn(page)) >= keys / 2, "turns went by");
    await liveKey(page, "q", "KeyQ", 81);
    assert.equal(await liveState(page), "finished");
  }
  timings.sort((a, b) => a - b);
  draws.sort((a, b) => a - b);
  const pct = (xs, p) => xs[Math.min(xs.length - 1, Math.floor(xs.length * p))];
  console.log(`      ${sent} keys: key-to-frame (in page, sent to drawn) median ${pct(timings, 0.5).toFixed(1)} ms, p95 ${pct(timings, 0.95).toFixed(1)} ms, max ${timings.at(-1).toFixed(1)} ms; ` +
              `grid render median ${pct(draws, 0.5).toFixed(2)} ms, max ${draws.at(-1).toFixed(2)} ms`);
  assert.ok(pct(timings, 0.95) < 250, "keys are answered promptly");
}, { ms: 400000 });

test("Ctrl-C stops the roguelike", async (page) => {
  await startRogue(page, 7);
  await liveKey(page, ".", "Period", 190);
  await liveKey(page, "c", "KeyC", 67, { modifiers: 2 });
  assert.equal(await liveState(page), "interrupted");
  assert.equal(await page.ev(`document.getElementById("run").disabled`), false);
}, { ms: 400000 });

// The Software Foundations port (sf/), bundled with chapters as its entries -------

test("sf/ is a project with a chapter per entry, opens by link, and shows open goals as goals", async (page) => {
  await page.open({ hash: "#sf/induction" });
  const groups = await page.until(`[...document.querySelectorAll("#example optgroup")].some((g) => g.label === "Software Foundations (port)") &&
    [...document.querySelectorAll("#example optgroup")].map((g) => [g.label, [...g.children].map((o) => o.value + "=" + o.textContent)])`, 10000, "every group");
  assert.deepEqual(groups.find(([label]) => label === "Software Foundations (port)"),
    ["Software Foundations (port)", ["sf:0=Basics", "sf:1=Induction", "sf:2=Lists", "sf:3=Poly"]]);
  const manifest = await page.ev(`fetch("pkg/projects/sf/manifest.json").then((r) => r.json())`);
  assert.equal(manifest.openGoals, "warn");
  assert.ok(manifest.files.every((p) => /^src\/.*\.sw$/.test(p)), manifest.files.join());
  assert.equal(await page.ev(`fetch("pkg/projects/sf/stitchwort.yaml").then((r) => r.status)`), 404);
  // The exercises are open goals, which are not errors.
  await page.until(`/ goals? open$/.test(document.getElementById("status").textContent)`, 120000, "Induction's goals");
  assert.equal(await page.ev(`document.getElementById("example").value`), "sf:1");
  assert.equal(await page.ev(`location.hash`), "#sf/induction");
  assert.ok((await fileTabs(page)).includes("Induction.sw"));
}, { ms: 200000 });

test("a chapter's Run is disabled and says chapters are checked, not run, until an AoC day is picked", async (page) => {
  await page.open({ hash: "#book/2" });
  const title = await page.until(`document.getElementById("example").value === "book:2" &&
    (() => { const b = document.getElementById("run"); return b.disabled && b.title; })()`, 120000, "the chapter's Run button to be disabled");
  assert.match(title, /checked, not run/);
  assert.match(title, /Tests tab/);
  // Let the chapter's check finish before switching: it is the server's, and a
  // check still running would put the next project behind it.
  await page.until(`(() => { const s = document.getElementById("status").textContent;
    return s !== "Loading the compiler…" && s !== "(changed)"; })()`, 180000, "the chapter to check");
  // The chapters' manifests mark them so; the days' project has programs to run.
  const flags = await page.ev(`Promise.all(["book", "sf", "aoc"].map((name) =>
    fetch("pkg/projects/" + name + "/manifest.json").then((r) => r.json()).then((m) => !!m.noRun)))`);
  assert.deepEqual(flags, [true, true, false]);
  // An AoC day has a main, so Run comes back.
  await openDay(page, 2);
  assert.equal(await page.ev(`document.getElementById("run").disabled`), false);
  assert.match(await page.ev(`document.getElementById("run").title`), /^Run Aoc\.Year2025\.Day02\.main /);
}, { ms: 200000 });

test("only the listed folders are bundled: sources, examples and puzzle inputs", async (page) => {
  await page.open();
  await page.untilChecked();
  const manifest = await page.ev(`fetch("pkg/projects/aoc/manifest.json").then((r) => r.json())`);
  const listed = [...manifest.files, ...manifest.data, ...manifest.days.flatMap((d) => d.inputs.map((i) => i.path))];
  assert.ok(listed.length > 15);
  for (const path of listed) {
    assert.match(path, /^(src\/.*\.sw|examples\/\d{4}\/[^/]*\.txt|inputs\/\d{4}\/[^/]*\.txt)$/, path);
  }
  for (const path of listed) assert.equal(await page.ev(`fetch("pkg/projects/aoc/${path}").then((r) => r.status)`), 200, path);
  // The project's config and anything else of aoc/ isn't served.
  for (const path of ["stitchwort.yaml", "../../../aoc/stitchwort.yaml", "board/tickets.json"]) {
    assert.equal(await page.ev(`fetch("pkg/projects/aoc/${path}").then((r) => r.status)`), 404, path);
  }
  // Every URL the page fetches is relative.
  const html = readFileSync(join(root, "index.html"), "utf8");
  assert.doesNotMatch(html, /127\.0\.0\.1|localhost/);
  assert.doesNotMatch(html, /(?:fetch|URL)\(\s*["'`]\//);
});

test("on a phone, a project's file tabs scroll inside themselves", async (page) => {
  await page.send("Emulation.setDeviceMetricsOverride", { width: 400, height: 860, deviceScaleFactor: 2, mobile: true });
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.until(DAY2_TABS_READY);
  const l = await page.ev(`(() => { const t = document.getElementById("filetabs");
    return { width: innerWidth, scrollWidth: document.documentElement.scrollWidth,
             tabs: { client: t.clientWidth, scroll: t.scrollWidth, overflow: getComputedStyle(t).overflowX } }; })()`);
  assert.equal(l.width, 400);
  assert.ok(l.scrollWidth <= l.width, `the page scrolls sideways: ${JSON.stringify(l)}`);
  assert.ok(l.tabs.scroll > l.tabs.client && l.tabs.overflow === "auto", `the tabs scroll inside themselves: ${JSON.stringify(l)}`);
}, { ms: 120000 });

// The language server in the editor (docs/proposals/playground-editor.md) --------------

const NAV_SOURCE = `import Std (List, Text)

def double (n: Nat) : Nat := n + n

def quad (n: Nat) : Nat := double (double n)

def lengths (xs: List Nat) : Nat := List.length xs

def tricky (ys: List Nat) : Nat := if Text.isEmpty "😀😀" then 0 else List.length ys
`;

const CMD = 4;

/** Saves a screenshot, light and dark, under $NAV_SHOTS (if set): for looking at, not asserting. */
async function shots(page, name) {
  const dir = process.env.NAV_SHOTS;
  if (!dir) return;
  mkdirSync(dir, { recursive: true });
  for (const scheme of ["light", "dark"]) {
    await page.send("Emulation.setEmulatedMedia", { features: [{ name: "prefers-color-scheme", value: scheme }] });
    await new Promise((r) => setTimeout(r, 300));
    const { data } = await page.send("Page.captureScreenshot", { format: "png" });
    writeFileSync(join(dir, `${name}-${scheme}.png`), Buffer.from(data, "base64"));
  }
  await page.send("Emulation.setEmulatedMedia", { features: [] });
}

/** The error a helper throws when the editor's text lacks `needle`. */
const missingText = (helper, needle) => `${helper}: the editor's text does not contain ${JSON.stringify(needle)}`;

/** Where the text `delta` characters into the first `needle` is drawn, after scrolling it into view. */
function whereIs(page, needle, delta = 0) {
  return page.ev(`new Promise((done, fail) => {
    const e = window.editor, i = e.value.indexOf(${JSON.stringify(needle)});
    if (i < 0) { fail(new Error(${JSON.stringify(missingText("whereIs", needle))})); return; }
    const at = i + ${delta};
    e.scrollTo(at);
    requestAnimationFrame(() => requestAnimationFrame(() => done(e.coords(at))));
  })`);
}
const mouse = (page, { x, y }, modifiers = 0) => page.send("Input.dispatchMouseEvent", { type: "mouseMoved", x, y, modifiers });
async function cmdClick(page, { x, y }) {
  await mouse(page, { x, y }, CMD);
  await page.send("Input.dispatchMouseEvent", { type: "mousePressed", x, y, button: "left", clickCount: 1, modifiers: CMD });
  await page.send("Input.dispatchMouseEvent", { type: "mouseReleased", x, y, button: "left", clickCount: 1, modifiers: CMD });
}
/** What the editor has selected, and where. */
const selected = (page) => page.ev(`(() => { const e = window.editor;
  return { text: e.value.slice(e.selectionStart, e.selectionEnd), line: e.value.slice(0, e.selectionStart).split("\\n").length,
           readOnly: e.readOnly, inStd: e.inStd }; })()`);
const hoverText = (page) => page.ev(`document.querySelector(".cm-tooltip-hover")?.innerText ?? null`);

/** Waits for the server's diagnostics for `uri` (a part of it) to have arrived `n` times. */
const untilPublished = (page, uri, n = 1, ms = 60000) =>
  page.until(`window.editor.stats.published.filter((p) => p.uri.includes(${JSON.stringify(uri)})).length >= ${n}`, ms, `diagnostics for ${uri}`);
/**
 * Waits until the server has published an error on the line with `needle` in `name`, and scrolls that line
 * into view: CodeMirror draws only the lines near the viewport, so its lint mark can be missing until then.
 */
const untilErrorInView = (page, name, needle, ms = 60000) =>
  page.until(`(() => {
    const e = window.editor;
    const uri = [...e.published.keys()].find((u) => u.endsWith(${JSON.stringify(name)}));
    const diagnostics = (uri && e.diagnosticsOf(uri)) ?? [];
    for (const d of diagnostics) {
      if (d.severity !== 1) continue;
      const line = e.view.state.doc.line(d.range.start.line + 1);
      if (!line.text.includes(${JSON.stringify(needle)})) continue;
      e.reveal(line.from + d.range.start.character, line.from + d.range.end.character);
      return true;
    }
    return false;
  })()`, ms, `the error on the line with ${needle} in ${name}, in view`);
const tooltips = (page) => page.ev(`[...document.querySelectorAll(".cm-tooltip")].map((t) => t.innerText)`);
const underlined = (page) => page.ev(`document.querySelectorAll("#editor .cm-lintRange-error").length`);
/** Puts the caret `delta` characters into the first `needle`. */
const caretAt = (page, needle, delta = 0) => page.ev(`(() => { const e = window.editor; e.focus();
  const i = e.value.indexOf(${JSON.stringify(needle)});
  if (i < 0) throw new Error(${JSON.stringify(missingText("caretAt", needle))});
  const at = i + ${delta}; e.setSelectionRange(at, at); })()`);
/** Waits until the selection is `text`, or (given `line`) the caret is on that line. */
const untilCaret = (page, ms, what, test) => page.until(`(() => { const e = window.editor; const t = e.value.slice(0, e.selectionStart).split("\\n").length; return ${test}; })()`, ms, what);

test("whereIs and caretAt name a missing needle instead of returning a wrong position", async (page) => {
  await page.open();
  await page.untilChecked();
  const needle = "text the editor does not have";
  await assert.rejects(whereIs(page, needle), new RegExp(`whereIs: the editor's text does not contain "${needle}"`));
  await assert.rejects(caretAt(page, needle), new RegExp(`caretAt: the editor's text does not contain "${needle}"`));
});

test("an error is underlined, its message shows on hover, and the underline goes when it is fixed", async (page) => {
  await page.open();
  await page.untilChecked();
  assert.equal(await page.ev(`window.editor.stats.isolated`), true, "the page is cross-origin isolated, so edits can cancel a stale check");
  const t = Date.now();
  await page.setSource(NAV_SOURCE + `\ndef bad : Nat := "oops"\n`);
  await page.until(`!!document.querySelector("#editor .cm-lintRange-error")`, 60000, "the error underlined");
  console.log(`    (first diagnostics ${Math.round(await page.ev(`window.editor.stats.firstDiagnostics`))} ms after the editor started; the error underlined ${Date.now() - t} ms after the edit)`);
  assert.equal(await underlined(page), 1);
  assert.equal(await page.ev(`document.querySelector("#editor .cm-lintRange-error").textContent`), `"oops"`, "the underline covers the text at fault");
  await mouse(page, await whereIs(page, `"oops"`, 2));
  await page.until(`!!document.querySelector(".cm-tooltip-lint")`, 10000, "the message");
  assert.match((await tooltips(page)).join("\n"), /type mismatch\s+expected `Nat`, but this has type `Text`/);
  // Fixing it clears the underline.
  await page.setSource(NAV_SOURCE + `\ndef bad : Nat := 5\n`);
  await page.until(`document.querySelectorAll("#editor .cm-lintRange-error").length === 0`, 30000, "the underline to go");
});

test("hovering a name shows its declaration and its documentation", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(`import Std (List)\n\n--| Twice \`n\`. Not shown.\n--|\n--| Nor this paragraph.\ndef double (n: Nat) : Nat := n + n\n\ndef quad (n: Nat) : Nat := double (double n)\n\ndef lengths (xs: List Nat) : Nat := List.length xs\n`);
  await untilPublished(page, "main.sw", 2);
  await sleep(500);
  await mouse(page, await whereIs(page, "double (double n)", 1));
  await page.until(`!!document.querySelector(".cm-tooltip-hover")`, 30000, "the tooltip of a documented declaration");
  const tip = (await tooltips(page)).join("\n");
  assert.match(tip, /^def Main\.double \(n: Nat\): Nat\s+Twice n\. Not shown\.\s+Nor this paragraph\.$/);
  // A library function: its qualified name, its type, and what its documentation says.
  await mouse(page, await whereIs(page, "List.length xs", 6));
  await page.until(`document.querySelector(".cm-tooltip-hover")?.innerText.includes("Std.List.length")`, 30000, "the library function's tooltip");
  assert.match((await tooltips(page)).join("\n"), /def Std\.List\.length \[a: Type\] \(xs: List a\): Nat/);
  // Off a name, there is none.
  await mouse(page, await whereIs(page, "def double", 1));
  await page.until(`!document.querySelector(".cm-tooltip-hover")`, 5000, "the tooltip to go");
}, { ms: 90000 });

test("F12 and Cmd-click go to the definition, in the file; Cmd+[ comes back", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await untilPublished(page, "main.sw", 2);
  await sleep(500);
  await caretAt(page, "(double n)", 3);
  await page.key("F12", "F12", 123);
  await untilCaret(page, 30000, "the jump", `t === 3`);
  // Cmd-click on a local goes to its binder, after astral characters on the line.
  await cmdClick(page, await whereIs(page, "else List.length ys", 17));
  await untilCaret(page, 30000, "the binder", `e.selectionStart === e.value.indexOf("ys:")`);
  // And back, by Cmd+[ (twice: to the call of `double`, then to where the caret began).
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await untilCaret(page, 10000, "the way back", `e.selectionStart !== e.value.indexOf("ys:") && t === 9`);
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await untilCaret(page, 10000, "the way back to the start", `t === 5`);
}, { ms: 90000 });

test("Cmd-click on a library function shows the library's text, read-only, with a way back", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await untilPublished(page, "main.sw", 2);
  await sleep(500);
  await cmdClick(page, await whereIs(page, "List.length xs", 6));
  await page.until(`window.editor.inStd`, 30000, "the library file");
  assert.equal(await page.ev(`document.getElementById("stdbar").hidden`), false);
  assert.match(await page.ev(`document.getElementById("std-name").textContent`), /\.sw$/);
  assert.deepEqual({ ...(await selected(page)), line: 0 }, { text: "", line: 0, readOnly: true, inStd: true });
  assert.match(await page.ev(`window.editor.view.state.doc.lineAt(window.editor.selectionStart).text`), /^def List\.length/);
  // The user's own text is kept, and typing in the library file changes nothing.
  assert.equal(await sourceText(page), NAV_SOURCE);
  await page.type("garbage");
  assert.equal(await page.ev(`window.editor.view.state.doc.toString().includes("garbage")`), false, "read-only");
  assert.equal(await page.ev(`document.querySelectorAll("#editor .cm-lintRange-error").length`), 0);
  // Hover works there too.
  await mouse(page, await page.ev(`window.editor.coords(window.editor.selectionStart + 4)`));
  await page.until(`!!document.querySelector(".cm-tooltip-hover")`, 30000, "a tooltip in the library file");
  // Escape goes back.
  await page.key("Escape", "Escape", 27);
  await page.until(`!window.editor.inStd`, 10000, "the way back");
  assert.equal(await page.ev(`document.getElementById("stdbar").hidden`), true);
  assert.equal(await sourceText(page), NAV_SOURCE);
  // The Back button too, and editing after it works.
  await cmdClick(page, await whereIs(page, "List.length xs", 6));
  await page.until(`window.editor.inStd`, 30000, "the library file again");
  await page.click("#std-back");
  await page.until(`!window.editor.inStd`, 10000, "the Back button");
  await page.setSource(NAV_SOURCE + "-- edited\n");
  assert.equal(await sourceText(page), NAV_SOURCE + "-- edited\n");
}, { ms: 90000 });

test("Shift+F12 lists the uses of a name, and clicking one goes there", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await untilPublished(page, "main.sw", 2);
  await sleep(500);
  await caretAt(page, "double (double n)", 2);
  await page.key("F12", "F12", 123, { modifiers: 8 });
  await page.until(`!!document.querySelector(".cm-lsp-reference-panel")`, 30000, "the references panel");
  const rows = await page.ev(`[...document.querySelectorAll(".cm-lsp-reference")].map((r) => r.textContent.trim())`);
  assert.ok(rows.some((r) => r.startsWith("3:") && r.includes("def double")), JSON.stringify(rows));
  assert.ok(rows.filter((r) => r.startsWith("5:")).length >= 1 && rows.every((r) => /^\d+:/.test(r)), JSON.stringify(rows));
  await page.ev(`document.querySelector(".cm-lsp-reference-panel .cm-lsp-reference").click()`);
  await untilCaret(page, 10000, "the first use", `t === 3`);
});

test("in a project, go to definition opens the other file and Cmd+[ comes back; an edit is checked", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.until(DAY2_TABS_READY);
  // The server checks the project as a whole before its first marks (tens of seconds: no check cache here).
  const t = Date.now();
  await untilPublished(page, "Day02.sw", 1, 150000);
  console.log(`    (the day's first diagnostics ${Math.round((Date.now() - t) / 100) / 10} s after its page check)`);
  const own = await sourceText(page);
  const at = own.indexOf("Range");
  await page.ev(`(() => { const e = window.editor; e.focus(); e.setSelectionRange(${at + 1}, ${at + 1}); })()`);
  await page.key("F12", "F12", 123);
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`, 60000, "the other file");
  assert.equal(await sourceText(page), await bundled(page, "src/Aoc/Common/Range.sw"));
  await untilCaret(page, 10000, "the declaration", `window.editor.value.slice(window.editor.selectionStart).startsWith("Range")`);
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Day02.sw"`, 10000, "the way back");
  assert.equal(await sourceText(page), own);
  // An edit of the day's program is checked (the server went on working after the other file was opened).
  const before = await page.ev(`window.editor.stats.publishedTotal`);
  const t2 = Date.now();
  await page.setSource(own + "\n-- an edit\n");
  await page.until(`window.editor.stats.published.some((p) => p.n > ${before} && p.uri.includes("Day02.sw"))`, 60000, "diagnostics for the edit");
  console.log(`    (an edit of the day checked after ${Date.now() - t2} ms)`);
  assert.equal(await page.ev(`window.editor.stats.restarts`), 0, "the server didn't crash");
}, { ms: 280000 });

// The server's background check of the rest of the project goes through Aoc.Year2021.Day11.Proofs, whose
// noted types are deep: with a file of Aoc.Common open, printing them could overflow V8's stack (SW-1430).
test("in a project, after a jump into another file and the whole project's check, an error in the day is underlined", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.until(DAY2_TABS_READY);
  await untilPublished(page, "Day02.sw", 1, 150000);
  const own = await sourceText(page);
  const at = own.indexOf("Range");
  await page.ev(`(() => { const e = window.editor; e.focus(); e.setSelectionRange(${at + 1}, ${at + 1}); })()`);
  await page.key("F12", "F12", 123);
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`, 60000, "the other file");
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Day02.sw"`, 10000, "the way back");
  let t = Date.now();
  await page.until(`window.editor.stats.idle || window.editor.stats.restarts > 0`, 240000, "the project's check to finish");
  console.log(`    (the rest of the project checked ${Math.round((Date.now() - t) / 100) / 10} s after the jump)`);
  assert.equal(await page.ev(`window.editor.stats.restarts`), 0, `the server didn't crash: ${await page.ev(`window.editor.stats.crashed`)}`);
  // `published` keeps only the last few hundred, which the project's check has filled: those after the edit.
  const since = await page.ev(`performance.now() - window.editor.t0`);
  t = Date.now();
  await page.setSource(own + "\ndef broken: Nat := rfl\n");
  try {
    await page.until(`window.editor.stats.published.some((p) => p.t > ${since} && p.uri.endsWith("Day02.sw") && p.count > 0)`, 60000, "the error published");
  } catch (e) {
    console.log("    DUMP", JSON.stringify(await page.ev(`(() => { const s = window.editor.stats; return { n: s.published.length, idle: s.idle, ticks: s.ticks,
      published: s.published.filter((p) => p.t > ${since} - 1000), log: (s.log ?? []).filter((l) => l.t > ${since} - 1000).slice(-30) }; })()`)));
    throw e;
  }
  // The editor draws only the lines near its viewport, and the way back kept the scrolling at the top.
  await untilErrorInView(page, "Day02.sw", "broken");
  await page.until(`!!document.querySelector("#editor .cm-lintRange-error")`, 10000, "the error underlined");
  console.log(`    (underlined ${Date.now() - t} ms after the edit)`);
  assert.equal(await page.ev(`window.editor.stats.restarts`), 0, "the server didn't crash");
}, { ms: 480000 });

test("in a project, an error in the day's program is underlined", async (page) => {
  await page.open();
  await page.untilChecked();
  const opened = Date.now();
  await openDay(page, 2);
  await page.until(DAY2_TABS_READY);
  await untilPublished(page, "Day02.sw", 1, 150000);
  // With the library's check cache (pkg/std.cache.gz) the first marks come in seconds.
  console.log(`    (first diagnostics ${Date.now() - opened} ms after opening the day; library cache: ${await page.ev(`window.editor.stats.libraryCache`)})`);
  console.log(`    (stats: ${JSON.stringify(await page.ev(`(({ ready, libraryCacheMs, longestTick, ticks }) => ({ ready, libraryCacheMs, longestTick, ticks }))(window.editor.stats)`))})`);
  assert.equal(await page.ev(`window.editor.stats.libraryCache`), true, "the library's check cache was read");
  const t = Date.now();
  await page.setSource((await sourceText(page)) + "\ndef broken: Nat := rfl\n");
  await untilErrorInView(page, "Day02.sw", "broken");
  await page.until(`!!document.querySelector("#editor .cm-lintRange-error")`, 10000, "the error underlined");
  console.log(`    (underlined ${Date.now() - t} ms after the edit)`);
  assert.equal(await page.ev(`window.editor.stats.restarts`), 0, "the server didn't crash");
}, { ms: 280000 });

test("the roguelike's files open without false errors", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.pick("rogue:1");
  await page.until(`document.getElementById("status").textContent.endsWith("checked by the kernel")`, 120000, "the roguelike to check");
  await untilPublished(page, "/rogue/", 1, 150000);
  await sleep(1000);
  assert.equal(await underlined(page), 0, "no underlined errors");
  assert.equal(await page.ev(`window.editor.stats.restarts`), 0);
}, { ms: 280000 });

test("a code action on a ? offers a proof search, and the proof picked fills it in", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource("def two : Nat := 2\n\ntheorem two_is_two : two = 2 := ?\n");
  await untilPublished(page, "main.sw", 2);
  await sleep(500);
  await caretAt(page, "?");
  await page.key(".", "Period", 190, { modifiers: CMD });
  // The list comes at once, without a search having run.
  await page.until(`document.querySelector(".pick-panel") !== null`, 20000, "the code actions");
  assert.ok((await page.ev(`window.editor.lastCodeActions`)).includes("Search for a proof"));
  assert.ok(!(await page.ev(`window.editor.lastCodeActions`)).some((t) => t.startsWith("Replace ? with")));
  await page.ev(`[...document.querySelectorAll(".pick-item")].find((b) => b.textContent.includes("Search for a proof")).click()`);
  await page.until(`document.querySelector(".pick-panel [role=option]") !== null && document.querySelector(".pick-panel").getAttribute("aria-label").startsWith("Replace")`, 100000, "the proofs");
  await page.ev(`document.querySelector(".pick-panel .pick-item").click()`);
  await page.until(`!window.editor.value.includes("?")`, 20000, "the proof");
  assert.match(await sourceText(page), /two = 2 := (rfl|omega|cases|Std\.byDecision)\n$/);
}, { ms: 120000 });

test("a proof search in the book's chapter 2 shows progress, and a second one doesn't load the library again", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.ev(`location.hash = "#book/2"`);
  await page.until(`document.getElementById("example").value === "book:2" &&
    window.editor.value.includes("theorem noAndAnything")`, 60000, "the book's chapter 2");
  const text = await sourceText(page);
  const line = "theorem noAndAnything (b: Answer): both No b = No := rfl";
  await page.setSource(text.replace(line, line.slice(0, -"rfl".length) + "?"));
  const hole = "both No b = No := ?";
  await caretAt(page, hole, hole.length - 1);
  await page.until(`document.getElementById("goalpanel").innerText.includes("⊢ both No b = No")`, 180000, "the goal at the ?");
  await page.ev(`(() => {
    const notices = window.__notices = [];
    const old = window.editor.options.onNotice;
    window.editor.options.onNotice = (t) => { notices.push(t); old?.(t); };
  })()`);
  const search = async (label) => {
    await caretAt(page, hole, hole.length - 1);
    await page.key(".", "Period", 190, { modifiers: CMD });
    await page.until(`document.querySelector(".pick-panel") !== null`, 20000, "the code actions");
    const began = Date.now();
    await page.ev(`[...document.querySelectorAll(".pick-item")].find((b) => b.textContent.includes("Search for a proof")).click()`);
    await page.until(`document.querySelector(".pick-panel") !== null && document.querySelector(".pick-panel").getAttribute("aria-label").startsWith("Replace")`, 150000, "the proofs");
    const took = Date.now() - began;
    console.log(`  ${label} search: ${took} ms`);
    await page.ev(`document.querySelector(".pick-panel")?.remove()`);
    return took;
  };
  await search("first");
  const notices = await page.ev(`window.__notices`);
  assert.ok(notices.some((n) => n.startsWith("Searching for a proof")), JSON.stringify(notices));
  const second = await search("second");
  assert.ok(second < 8000, `the second search took ${second} ms`);
}, { ms: 400000 });

test("a let without a type shows its type after the name, and the drawn text is still the document", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource("def f (n : Nat) : Nat :=\n  let a := n + 1\n  a + a\n");
  await page.until(`[...document.querySelectorAll("#editor .cm-inlay")].some((h) => h.textContent === ": Nat")`, 60000, "the let's type");
  await assertAligned(page, "a let with its hint");
  // The hint is not text: the document is as typed.
  assert.equal(await sourceText(page), "def f (n : Nat) : Nat :=\n  let a := n + 1\n  a + a\n");
});

test("without COOP/COEP headers, the service worker isolates the page, and the server gets a shared counter", async (page) => {
  isolating = false;
  await page.open();
  // The first visit registers the worker and reloads (coi-serviceworker.js).
  await page.until(`window.crossOriginIsolated === true && !!window.editor`, 30000, "isolation from the service worker");
  await page.untilChecked();
  assert.equal(await page.ev(`window.editor.stats.isolated`), true);
  await page.setSource(NAV_SOURCE + `\ndef bad : Nat := "oops"\n`);
  await page.until(`!!document.querySelector("#editor .cm-lintRange-error")`, 60000, "the error underlined");
  await page.ev(`navigator.serviceWorker.getRegistrations().then((rs) => Promise.all(rs.map((r) => r.unregister())))`);
}, { ms: 120000 });

// Running them -------------------------------------------------------------------

async function main() {
  if (!existsSync(join(root, "pkg", "stitchwort_web_bg.wasm"))) {
    console.error(`${join(root, "pkg")} isn't built: run web/build.sh first, or pass --dir with a built playground.`);
    return 1;
  }
  const chrome = findChrome();
  if (!chrome) {
    console.log("SKIPPED: the browser tests need Chrome or Chromium, and none was found. Set CHROME to its executable.");
    return 0;
  }
  const chosen = tests.filter((t) => filters.length === 0 || filters.some((f) => t.name.includes(f)));
  const server = await serve(root);
  const base = `http://127.0.0.1:${server.address().port}/`;
  const profile = mkdtempSync(join(tmpdir(), "stitchwort-chrome-"));
  let browser;
  // However this process ends (even by an error, or output to a closed
  // pipe), the Chrome it started ends too.
  const stop = () => { if (browser?.child.exitCode === null) browser.child.kill("SIGKILL"); };
  process.on("exit", () => { stop(); rmSync(profile, { recursive: true, force: true }); });
  process.on("SIGINT", () => process.exit(130));
  process.on("SIGTERM", () => process.exit(143));
  process.on("SIGHUP", () => process.exit(129));
  let failed = 0;
  try {
    browser = await launch(chrome, profile);
    console.log(`Chrome: ${(await browser.send("Browser.getVersion")).product}; serving ${root} at ${base}`);
    for (const t of chosen) {
      const started = Date.now();
      const { targetId } = await browser.send("Target.createTarget", { url: "about:blank" });
      const { sessionId } = await browser.send("Target.attachToTarget", { targetId, flatten: true });
      const page = new Page(browser, sessionId, targetId, base);
      await page.send("Runtime.enable");
      await page.send("Page.enable");
      await page.send("Storage.clearDataForOrigin", { origin: base.slice(0, -1), storageTypes: "all" });
      try {
        let timer;
        await Promise.race([
          t.body(page),
          new Promise((_, fail) => { timer = setTimeout(() => fail(new Error(`took longer than ${t.ms / 1000} s`)), t.ms); }),
        ]).finally(() => clearTimeout(timer));
        if (!t.exceptions && page.exceptions.length) throw new Error("uncaught in the page:\n" + page.exceptions.join("\n"));
        console.log(`ok   ${t.name} (${((Date.now() - started) / 1000).toFixed(1)} s)`);
      } catch (e) {
        failed++;
        console.log(`FAIL ${t.name}\n  ${String(e.stack ?? e).replaceAll("\n", "\n  ")}`);
        if (page.console.length) console.log("  console:\n    " + page.console.join("\n    "));
      } finally {
        overrides.clear();
        isolating = true;
      }
      browser.listeners.delete(sessionId);
      await browser.send("Target.closeTarget", { targetId }).catch(() => {});
    }
  } finally {
    await browser?.send("Browser.close").catch(() => {});
    if (browser?.child.exitCode === null) {
      await Promise.race([new Promise((r) => browser.child.once("exit", r)), sleep(5000)]);
      stop();
    }
    server.close();
  }
  console.log(`${chosen.length - failed} of ${chosen.length} browser tests passed`);
  return failed ? 1 : 0;
}

process.exitCode = await main();
