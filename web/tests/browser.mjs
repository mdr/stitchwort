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
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
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

function serve(dir) {
  const server = createServer((req, res) => {
    const path = decodeURIComponent(new URL(req.url, "http://x").pathname);
    if (overrides.has(path)) {
      res.writeHead(200, { "content-type": TYPES[extname(path)] ?? "text/plain", "cache-control": "no-store" });
      res.end(overrides.get(path));
      return;
    }
    const file = resolve(dir, "." + path);
    if (!file.startsWith(dir + sep) || !existsSync(file) || !statSync(file).isFile()) {
      res.writeHead(404).end("not found");
      return;
    }
    res.writeHead(200, { "content-type": TYPES[extname(file)] ?? "application/octet-stream", "cache-control": "no-store" });
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

  async open({ patch } = {}) {
    if (patch) await this.send("Page.addScriptToEvaluateOnNewDocument", { source: patch });
    await this.send("Page.navigate", { url: this.base + "index.html" });
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
    return this.ev(`(() => { ${Page.#blank} const s = document.getElementById("source"); s.value = ${JSON.stringify(text)};
      s.dispatchEvent(new Event("input")); })()`);
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

  /** The editor's two layers: the textarea and the coloured copy under it. */
  layers() {
    return this.ev(`(() => {
      const s = document.getElementById("source"), h = document.getElementById("highlight");
      const box = (e) => { const r = e.getBoundingClientRect(); return [r.x, r.y, r.width, r.height].map(Math.round); };
      return { sameText: h.textContent === s.value + "\\n",
               ta: { box: box(s), bars: [s.offsetWidth - s.clientWidth - 2 * s.clientLeft, s.offsetHeight - s.clientHeight - 2 * s.clientTop], scroll: [s.scrollTop, s.scrollLeft] },
               pre: { box: box(h), scroll: [h.scrollTop, h.scrollLeft] },
               client: [s.clientWidth, s.clientHeight, h.clientWidth, h.clientHeight] };
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

/** Asserts that the layers of the editor line up. */
async function assertAligned(page, what) {
  const l = await page.layers();
  assert.ok(l.sameText, `${what}: the coloured copy has the textarea's text`);
  // The copy covers the textarea less its scrollbars (it has none of its own,
  // and the textarea's sit over nothing it draws), so its box is that smaller.
  const [x, y, w, h] = l.ta.box;
  assert.deepEqual(l.pre.box, [x, y, w - l.ta.bars[0], h - l.ta.bars[1]], `${what}: the coloured copy covers the textarea less its scrollbars`);
  assert.deepEqual(l.pre.scroll, l.ta.scroll, `${what}: the coloured copy scrolls with the textarea`);
  assert.deepEqual(l.client.slice(2), l.client.slice(0, 2), `${what}: the visible areas are the same size`);
}

test("loads and checks the default example", async (page) => {
  await page.open();
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-lists");
  assert.match(await page.output(), /Every definition type-checks/);
  await assertAligned(page, "the default example");
});

test("the compiler's files are asked for by content hash (pkg/version.json)", async (page) => {
  await page.open();
  await page.untilChecked();
  const version = await page.ev(`fetch("pkg/version.json").then((r) => r.json())`);
  assert.match(version.compiler, /^[0-9a-f]{16}$/);
  assert.match(version.projects, /^[0-9a-f]{16}$/);
  const asked = await page.ev(`performance.getEntriesByType("resource").map((e) => new URL(e.name).pathname.split("/").pop() + new URL(e.name).search)`);
  assert.ok(asked.includes("version.json"), `version.json is fetched: ${asked}`);
  assert.ok(asked.includes(`stitchwort_web_bg.wasm?v=${version.compiler}`), `the WebAssembly: ${asked}`);
  assert.ok(asked.includes(`playground-worker.js?v=${version.compiler}`), `the worker: ${asked}`);
  assert.ok(!asked.some((a) => a.includes("load=")), `no ?load=: ${asked}`);
  await page.pick("aoc:0");
  await page.untilStatus(dayStatus(1), 60000);
  const manifest = await page.ev(`performance.getEntriesByType("resource").map((e) => new URL(e.name).pathname.split("/").pop() + new URL(e.name).search).filter((a) => a.startsWith("manifest.json"))`);
  assert.deepEqual(manifest, [`manifest.json?v=${version.projects}`]);
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
    const summary = await page.until(`document.getElementById("output").dataset.for === document.getElementById("source").value &&
      (document.querySelector(".summary")?.textContent ||
       document.getElementById("output").textContent.match(/No tests yet/)?.[0])`, 30000, `${id}'s tests`);
    if (id === "ex-tests") {
      assert.match(summary, /^4 tests: 3 passed, 1 failed( \(4 from the cache\))?$/, `${id}: ${summary} / ${await page.output()} / ${await page.ev("document.getElementById(\"source\").value.slice(0,80)")} / ${ids}`);
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
    if (!summary || o.dataset.for !== document.getElementById("source").value) return false;
    return { rows: [...o.querySelectorAll("ul.tests li")].map((li) => li.textContent), summary };
  })()`, 30000, "the tests for this source");

  const first = await results();
  assert.equal(first.rows.length, 4);
  assert.ok(first.rows.every((row) => row.endsWith("ran")), first.rows.join("\n"));
  assert.doesNotMatch(first.summary, /from the cache/);
  assert.match(first.summary, /^4 tests: 3 passed, 1 failed$/);

  // A harmless edit: the tests' results are still valid, so they're cached.
  const source = await page.ev(`document.getElementById("source").value`);
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
test "long value" := List.range 1000 == []
test "huge value" := List.range 100000 == []
test "not a comparison" := part1 1 == 2 && part1 2 == 4
`);
  await page.untilChecked();
  await page.tab("tests");
  const results = () => page.until(`(() => {
    const o = document.getElementById("output");
    if (!o.querySelector(".summary") || o.dataset.for !== document.getElementById("source").value) return false;
    return [...o.querySelectorAll("ul.tests li")].map((li) => ({
      text: li.firstChild.nextSibling.textContent,
      detail: li.querySelector(".detail")?.textContent ?? null }));
  })()`, 30000, "the tests for this source");
  const rows = await results();
  assert.equal(rows.length, 5);
  assert.equal(rows[0].text, "part 1 on the example (`==` is False)");
  assert.equal(rows[0].detail, "left:  2\nright: 3");
  assert.equal(rows[1].text, "greater (`>` is False)");
  assert.equal(rows[1].detail, "left:  1\nright: 6");
  assert.match(rows[2].detail, /^left:  \[0, 1, 2, [^]*…\nright: \[\]$/);
  assert.ok(rows[2].detail.length < 300, rows[2].detail.length);
  assert.equal(rows[3].detail, "left:  … (too large to show)\nright: []");
  assert.equal(rows[4].text, "not a comparison (evaluated to False)");
  assert.equal(rows[4].detail, null);
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
  assert.match(s.warnings, /^\[W-MODULE-NAME\] Warning:/);
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
  await page.pick("ex-main");
  await page.untilChecked();
  const result = await page.run();
  assert.equal(await page.ev(`document.getElementById("run-input").value`), MAIN_INPUT);
  assert.equal(await page.printed(), MAIN_OUTPUT);
  assert.match(result, /Finished in/);
  // Different input, and Ctrl+Enter from the source.
  await page.ev(`document.getElementById("run-input").value = "Grace\\n1\\n"`);
  await page.ev(`document.getElementById("source").focus()`);
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
  // The most lines the cap allows, each sent from the worker on its own.
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

// No program is known to crash the compiler any more: its depth guards stop
// deep programs with E-RESOURCE first. So this test serves a worker that
// checks a program containing CRASH with the engine's stack almost used up,
// which overflows it inside the WebAssembly, as a deep program once did.
const CRASH = "-- crash the engine's stack";
const crashing = (worker) => {
  const check = "check: () => b.check(data.source),";
  assert.ok(worker.includes(check), "the worker checks with b.check(data.source)");
  return worker.replace(check, `check: () => data.source.includes(${JSON.stringify(CRASH)})
      ? withoutStack(() => b.check(data.source)) : b.check(data.source),`) + `
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

for (const [how, patch] of [["highlights", null], ["spans", "delete window.Highlight;"]]) {
  test(`syntax colouring stays aligned (${how})`, async (page) => {
    await page.open({ patch });
    await page.untilChecked();
    const spans = await page.ev(`document.querySelectorAll("#highlight span").length`);
    assert.ok(how === "spans" ? spans > 0 : spans === 0, `${spans} spans`);
    // A long program, scrolled both ways.
    const main = await page.ev(`document.getElementById("ex-main").textContent`);
    let long = "";
    while (long.split("\n").length < 1500) long += main;
    long += "longLine = " + "\"a long string\" ++ ".repeat(60) + "\"end\"\n";
    await page.setSource(long);
    await assertAligned(page, "a long program");
    for (const [top, left] of [[0.5, 0], [1, 0], [1, 1]]) {
      await page.ev(`(() => { const s = document.getElementById("source");
        s.scrollTop = (s.scrollHeight - s.clientHeight) * ${top}; s.scrollLeft = (s.scrollWidth - s.clientWidth) * ${left}; })()`);
      await sleep(100);
      const l = await page.layers();
      assert.ok(l.ta.scroll[0] > 0, "it scrolled");
      await assertAligned(page, `scrolled to ${top}, ${left}`);
    }
    // Typing at the end.
    await page.ev(`(() => { const s = document.getElementById("source"); s.focus(); s.setSelectionRange(s.value.length, s.value.length); })()`);
    await page.type("\n\n-- typed <b>&amp; \"str\\\"ing\" 'x' 42");
    await sleep(100);
    await assertAligned(page, "after typing at the end");
  });
}

test("interpolation is coloured as code inside a string", async (page) => {
  await page.open();
  await page.untilChecked();
  const source = 'def world : Text := "w"\n' +
    'test "t" := "a ${ 1 + 2 } b ${"x ${world} y"} \\${z}" == "x"';
  await page.setSource(source);
  await sleep(100);
  const marked = await page.ev(`(() => {
    const text = document.getElementById("source").value;
    const pieces = (kind) => Array.from(CSS.highlights.get("hl-" + kind) ?? [],
      (r) => text.slice(r.startOffset, r.endOffset));
    return { string: pieces("string"), interp: pieces("interp"), number: pieces("number") };
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
    const text = document.getElementById("source").value;
    const pieces = (kind) => Array.from(CSS.highlights.get("hl-" + kind) ?? [],
      (r) => text.slice(r.startOffset, r.endOffset));
    return { string: pieces("string"), interp: pieces("interp"), number: pieces("number") };
  })()`);
  assert.deepEqual(marked.number, ["1", "2"], JSON.stringify(marked.number));
  assert.deepEqual(marked.interp, ["${", "}"], JSON.stringify(marked.interp));
  assert.ok(marked.string.includes('"""\n  say "hi" '), JSON.stringify(marked.string));
  assert.ok(marked.string.includes('\n  more \\"""\n  """'), JSON.stringify(marked.string));
  assert.ok(marked.string.includes('"x"'), JSON.stringify(marked.string));
});

test("`|>` is coloured as one operator", async (page) => {
  await page.open({ patch: "delete window.Highlight;" });
  await page.untilChecked();
  await page.setSource("def n : Nat := [1, 2]\n  |> .sum\n");
  await sleep(100);
  const operators = await page.ev(`[...document.querySelectorAll("#highlight span.hl-operator")].map((s) => s.textContent)`);
  assert.ok(operators.includes("|>"), JSON.stringify(operators));
});

test("the draft, input and tab are kept across a reload", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.pick("ex-main");
  await page.untilChecked();
  await page.ev(`(() => { const s = document.getElementById("source"); s.focus(); s.setSelectionRange(0, 0); })()`);
  await page.type("-- a draft\n");
  await page.tab("run");
  await page.ev(`(() => { const i = document.getElementById("run-input"); i.value = "Bo\\n"; i.dispatchEvent(new Event("input")); })()`);
  await page.tab("tests");
  const draft = await page.ev(`document.getElementById("source").value`);
  assert.ok(draft.startsWith("-- a draft\n-- A program"));
  await page.reload();
  await page.until(`document.querySelector(".summary")`);
  assert.equal(await page.ev(`document.getElementById("source").value`), draft);
  assert.equal(await page.ev(`document.getElementById("example").value`), "ex-main");
  assert.equal(await page.ev(`document.querySelector('[aria-selected="true"]').dataset.view`), "tests");
  await assertAligned(page, "the restored draft");
  await page.tab("run");
  assert.equal(await page.ev(`document.getElementById("run-input").value`), "Bo\n");
});

test("Tab indents, and undo still undoes earlier typing", async (page) => {
  await page.open();
  await page.untilChecked();
  const original = await page.ev(`document.getElementById("source").value`);
  await page.ev(`(() => { const s = document.getElementById("source"); s.focus(); s.setSelectionRange(s.value.length, s.value.length); })()`);
  await page.type("x : Nat");
  await page.key("Tab", "Tab", 9);
  await page.type("-- after a tab");
  await sleep(50);
  const value = () => page.ev(`document.getElementById("source").value`);
  assert.equal(await value(), original + "x : Nat  -- after a tab");
  assert.equal(await page.ev(`document.activeElement.id`), "source");
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

test("the page fills the window, and long results scroll in their pane", async (page) => {
  const geometry = () => page.ev(`(() => {
    const s = document.getElementById("source").getBoundingClientRect();
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
             source: box("#source"), results: box('[aria-label="Results"]'), output: box("#output"),
             fontSize: parseFloat(getComputedStyle(document.getElementById("source")).fontSize) };
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
  // Typing still works, and the colouring stays aligned.
  await page.ev(`(() => { const s = document.getElementById("source"); s.focus(); s.setSelectionRange(s.value.length, s.value.length); })()`);
  await page.type("\n-- typed on a phone, with a line long enough that the editor has to scroll sideways");
  await sleep(100);
  assert.match(await page.ev(`document.getElementById("source").value`), /typed on a phone/);
  await assertAligned(page, "on a phone");
  assert.ok((await layout()).scrollWidth <= 400, "the page doesn't scroll sideways after a long line");
});

test("dragging the editor's corner resizes it", async (page) => {
  await page.open();
  await page.untilChecked();
  const box = () => page.ev(`(() => { const s = document.getElementById("source");
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

/** What each day prints for its example input, and for its real input (the CLI's answers). */
const AOC_EXAMPLE = ["Part 1: 3\nPart 2: 6\n", "Part 1: 1227775554\nPart 2: 4174379265\n", "Part 1: 357\nPart 2: 3121910778619\n",
                     "Part 1: 13\nPart 2: 43\n", "Part 1: 3\nPart 2: 14\n", "Part 1: 4277556\nPart 2: 3263827\n",
                     "Part 1: 21\nPart 2: 40\n"];
const AOC_PUZZLE = ["Part 1: 1076\nPart 2: 6379\n", "Part 1: 16793817782\nPart 2: 27469417404\n",
                    "Part 1: 17263\nPart 2: 170731717900423\n", "Part 1: 1397\nPart 2: 8758\n",
                    "Part 1: 525\nPart 2: 333892124923577\n", "Part 1: 4722948564882\nPart 2: 9581313737063\n",
                    "Part 1: 1594\nPart 2: 15650261281478\n"];
/** Every day has proofs. */
const dayStatus = (day) => `Day ${day} and its proofs checked by the kernel`;
const DAY2 = "src/Aoc/Day02/Day02.sw";
const DAY2_TABS = ["Day02.sw", "Tests/BruteForce.sw", "Tests/Examples.sw", "Tests/Input.sw", "Proofs/Part1.sw", "Proofs/Part2.sw", "Proofs/Repeated.sw", "Common/Proofs/Range.sw", "Common/Range.sw"];

/** The labels of the file tabs. */
const fileTabs = (page) => page.ev(`[...document.querySelectorAll("#filetabs button")].map((b) => b.firstChild.textContent)`);
/** Opens a day and waits for it to check; its tabs are those of its namespaces. */
async function openDay(page, day) {
  await page.pick(`aoc:${day - 1}`);
  await page.untilStatus(dayStatus(day), 60000);
}
const openTab = (page, label) => page.ev(`[...document.querySelectorAll("#filetabs button")].find((b) => b.firstChild.textContent === ${JSON.stringify(label)}).click()`);
const sourceText = (page) => page.ev(`document.getElementById("source").value`);
/** The bundled text of a file, fetched as the page does. */
const bundled = (page, path) => page.ev(`fetch("pkg/projects/aoc/${path}").then((r) => r.text())`);
/** Sets the source (the open file), as typing would, and waits for the checked status to be blank first. */
const edit = (page, text) => page.setSource(text);
/** Waits for a stored edit of `path` to be saved. */
const savedEdit = (page, path) => page.until(`localStorage.getItem(${JSON.stringify("stitchwort.project.aoc.file." + path)})`, 10000, `a saved edit of ${path}`);

test("the AoC days are listed, and a day opens its program with its files as tabs", async (page) => {
  await page.open();
  await page.untilChecked();
  assert.equal(await page.ev(`document.getElementById("filebar").hidden`), true, "no file tabs for a single file");
  const days = await page.until(`(() => { const g = document.querySelector("#example optgroup"); return g && { label: g.label,
    days: [...g.children].map((o) => o.textContent) }; })()`, 10000, "the AoC group");
  assert.deepEqual(days, { label: "Advent of Code 2025", days: ["Day 1", "Day 2", "Day 3", "Day 4", "Day 5", "Day 6", "Day 7"] });
  await openDay(page, 2);
  assert.equal(await page.ev(`document.getElementById("filebar").hidden`), false);
  await page.until(`document.querySelectorAll("#filetabs button").length === ${DAY2_TABS.length}`, 10000, "day 2's tabs");
  assert.deepEqual(await fileTabs(page), DAY2_TABS);
  assert.equal(await sourceText(page), await bundled(page, DAY2));
  assert.match(await page.output(), /Every definition type-checks/);
  await assertAligned(page, "day 2");
  // Switching tabs shows another file of the day.
  await openTab(page, "Proofs/Part1.sw");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Proofs/Part1.sw"`);
  assert.equal(await sourceText(page), await bundled(page, "src/Aoc/Day02/Proofs/Part1.sw"));
  assert.equal(await page.status(), dayStatus(2), "still checked");
  await assertAligned(page, "day 2 proofs tab");
  // Another day has its own files as tabs.
  await openDay(page, 4);
  await page.until(`document.querySelectorAll("#filetabs button")[0]?.firstChild.textContent === "Day04.sw"`);
  const day4 = await fileTabs(page);
  assert.ok(day4.includes("Proofs/Part1.sw") && day4.includes("Proofs/Spec.sw"), `day 4's tabs: ${day4}`);
}, { ms: 120000 });

test("every day checks, with its proofs, and runs on its example and on its puzzle input", async (page) => {
  await page.open();
  await page.untilChecked();
  for (let day = 1; day <= 7; day++) {
    await openDay(page, day);
    const input = await page.until(`document.getElementById("run-input")?.value || (document.getElementById("run").click(), false)`, 10000, "the input");
    assert.equal(input, await page.ev(`fetch("pkg/projects/aoc/examples/day0${day}.txt").then((r) => r.text())`), `day ${day}: the input box has the example`);
    assert.equal(await page.ev(`document.getElementById("run").title`), `Run Aoc.Day0${day}.main (Ctrl+Enter)`);
    await page.run(30000);
    assert.equal(await page.printed(), AOC_EXAMPLE[day - 1], `day ${day} on its example`);
    // The puzzle input, chosen next to the example.
    await page.ev(`(() => { const s = document.getElementById("input-choice"); s.value = "inputs/day0${day}.txt";
      s.dispatchEvent(new Event("change")); })()`);
    const puzzle = await page.ev(`fetch("pkg/projects/aoc/inputs/day0${day}.txt").then((r) => r.text())`);
    await page.until(`document.getElementById("run-input").value === ${JSON.stringify(puzzle)}`, 10000, "the puzzle input");
    await page.run(60000);
    assert.equal(await page.printed(), AOC_PUZZLE[day - 1], `day ${day} on its puzzle input`);
  }
}, { ms: 240000 });

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
  assert.equal(first.groups[0], "Aoc.Day03.Tests");
  assert.ok(first.rows.length >= 2 && first.rows.every((r) => r.startsWith("✓")), first.rows.join("\n"));
  assert.doesNotMatch(first.summary, /failed, [1-9]|[1-9]\d* failed/);
  // `Tests/Input.sw` reads the bundled puzzle input through `include` (SW-187).
  assert.ok(first.rows.some((r) => r.includes("real input")), first.rows.join("\n"));
  await page.reload();
  await page.until(`document.getElementById("status").textContent === ${JSON.stringify(dayStatus(3))}`, 60000);
  const second = await results();
  assert.ok(second.rows.every((r) => r.endsWith("cached")), second.rows.join("\n"));
}, { ms: 120000 });

test("an error in a shared file shows in the Check tab, marks its tab, and links to its line", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.until(`document.querySelectorAll("#filetabs button").length === ${DAY2_TABS.length}`);
  await openTab(page, "Common/Range.sw");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`);
  const range = await sourceText(page);
  await edit(page, range + "\ndef broken: Nat := rfl\n");
  await page.untilStatus("Doesn’t check", 60000);
  const shown = await page.ev(`({
    errors: [...document.querySelectorAll("#output pre.errors")].map((p) => p.textContent),
    marked: [...document.querySelectorAll("#filetabs button[data-errors]")].map((b) => b.firstChild.textContent),
    jumps: [...document.querySelectorAll("#output button.jump")].map((b) => b.textContent) })`);
  assert.ok(shown.errors.length >= 2, shown.errors.join("\n"));
  assert.match(shown.errors[0], /E-TYPE-MISMATCH/);
  assert.match(shown.errors[1], /E-NAMESPACE-FAILED/, "listed after the error that caused it");
  assert.ok(shown.marked.includes("Common/Range.sw"));
  const line = range.split("\n").length + 1;
  assert.match(shown.jumps[0], new RegExp(`^src/Aoc/Common/Range\\.sw:${line}:`));
  // Going to the other file's error, and back by the link.
  await openTab(page, "Day02.sw");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Day02.sw"`);
  await page.click("#output button.jump");
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`);
  const caretLine = await page.ev(`(() => { const s = document.getElementById("source");
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
  await page.until(`document.getElementById("source").value === ${JSON.stringify(original)}`);
  assert.equal(await page.ev(`localStorage.getItem("stitchwort.project.aoc.file.${DAY2}")`), null, "the saved edit is gone");
  assert.equal(await page.ev(`document.querySelectorAll("#filetabs button[data-edited]").length`), 0);
  // Resetting the whole project asks first.
  await edit(page, original + "\n-- again\n");
  await savedEdit(page, DAY2);
  await page.click("#reset-project");
  assert.equal(await page.ev(`document.getElementById("reset-confirm").hidden`), false);
  assert.equal(await sourceText(page), original + "\n-- again\n", "nothing is reset before it's confirmed");
  await page.click("#reset-yes");
  await page.until(`document.getElementById("source").value === ${JSON.stringify(original)}`);
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
  await page.until(`document.getElementById("source").value === ${JSON.stringify(newest)}`);
  assert.equal(await page.ev(`document.getElementById("banner").hidden`), true);
  assert.equal(await page.ev(`localStorage.getItem("stitchwort.project.aoc.file.${DAY2}")`), null);
}, { ms: 120000 });

test("Evaluate takes full names in a project", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.tab("eval");
  assert.equal(await page.until(`document.getElementById("eval-input")?.value`, 10000), "Aoc.Day02.solvePart1 Aoc.Day02.Tests.exampleRanges");
  await page.until(`document.querySelector(".result")?.textContent.startsWith("1227775554")`, 30000, "the value");
  // A short name isn't in scope.
  await page.ev(`(() => { const i = document.getElementById("eval-input"); i.value = "solvePart1";
    i.form.dispatchEvent(new Event("submit", { cancelable: true })); })()`);
  await page.until(`document.querySelector("#output pre.errors")?.textContent.includes("E-UNKNOWN-NAME")`, 30000, "an unknown name");
  // An import of the project's namespace gives it.
  const submit = (text) => page.ev(`(() => { const i = document.getElementById("eval-input"); i.value = ${JSON.stringify(text)};
    i.form.requestSubmit(); })()`);
  await submit("import Aoc.Day02 (solvePart1)");
  await page.until(`document.getElementById("eval-imports").textContent === "import Aoc.Day02 (solvePart1)"`, 30000, "the import");
  await submit("solvePart1 Aoc.Day02.Tests.exampleRanges");
  await page.until(`document.querySelector(".result")?.textContent.startsWith("1227775554")`, 30000, "the value through an import");
}, { ms: 120000 });

test("only the listed folders are bundled: sources, examples and puzzle inputs", async (page) => {
  await page.open();
  await page.untilChecked();
  const manifest = await page.ev(`fetch("pkg/projects/aoc/manifest.json").then((r) => r.json())`);
  const listed = [...manifest.files, ...manifest.data, ...manifest.days.flatMap((d) => d.inputs.map((i) => i.path))];
  assert.ok(listed.length > 15);
  for (const path of listed) {
    assert.match(path, /^(src\/.*\.sw|examples\/[^/]*\.txt|inputs\/[^/]*\.txt)$/, path);
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
  await page.until(`document.querySelectorAll("#filetabs button").length === ${DAY2_TABS.length}`);
  const l = await page.ev(`(() => { const t = document.getElementById("filetabs");
    return { width: innerWidth, scrollWidth: document.documentElement.scrollWidth,
             tabs: { client: t.clientWidth, scroll: t.scrollWidth, overflow: getComputedStyle(t).overflowX } }; })()`);
  assert.equal(l.width, 400);
  assert.ok(l.scrollWidth <= l.width, `the page scrolls sideways: ${JSON.stringify(l)}`);
  assert.ok(l.tabs.scroll > l.tabs.client && l.tabs.overflow === "auto", `the tabs scroll inside themselves: ${JSON.stringify(l)}`);
}, { ms: 120000 });

// Code navigation (docs/proposals/code-navigation.md) ------------------------------

const NAV_SOURCE = `import Std (List, Text)

def double (n: Nat) : Nat := n + n

def quad (n: Nat) : Nat := double (double n)

def lengths (xs: List Nat) : Nat := List.length xs

def tricky (ys: List Nat) : Nat := if Text.isEmpty "😀😀" then 0 else List.length ys
`;

const CMD = 4;

/**
 * The centre, in the viewport, of the text `len` characters long at `delta` into the
 * first `needle` of the editor's text (after scrolling its line into view), where the
 * browser drew it in the coloured copy.
 */
function whereIs(page, needle, delta = 0, len = 1) {
  return page.ev(`new Promise((done) => {
    const s = document.getElementById("source"), h = document.getElementById("highlight");
    const i = s.value.indexOf(${JSON.stringify(needle)}) + ${delta};
    const line = s.value.slice(0, i).split("\\n").length - 1;
    const css = getComputedStyle(s), lh = parseFloat(css.lineHeight);
    const y = parseFloat(css.paddingTop) + line * lh;
    if (y < s.scrollTop || y + lh > s.scrollTop + s.clientHeight) s.scrollTop = Math.max(0, y - s.clientHeight / 3);
    s.dispatchEvent(new Event("scroll"));
    requestAnimationFrame(() => {
      // The coloured copy is split into spans: find the text nodes of the offsets.
      const point = (o) => { const w = document.createTreeWalker(h, NodeFilter.SHOW_TEXT); let at = 0;
        for (let n = w.nextNode(); n; n = w.nextNode()) { if (o <= at + n.length) return [n, o - at]; at += n.length; } };
      const range = document.createRange();
      range.setStart(...point(i));
      range.setEnd(...point(i + ${len}));
      const r = range.getBoundingClientRect();
      done({ x: r.left + r.width / 2, y: r.top + r.height / 2 });
    });
  })`);
}
const hoverAt = (page, { x, y }, modifiers = 0) => page.send("Input.dispatchMouseEvent", { type: "mouseMoved", x, y, modifiers });
async function cmdClick(page, { x, y }) {
  await hoverAt(page, { x, y }, CMD);
  await page.send("Input.dispatchMouseEvent", { type: "mousePressed", x, y, button: "left", clickCount: 1, modifiers: CMD });
  await page.send("Input.dispatchMouseEvent", { type: "mouseReleased", x, y, button: "left", clickCount: 1, modifiers: CMD });
}
const tooltip = (page) => page.ev(`(() => { const t = document.getElementById("navtip"); return t.hidden ? null : t.textContent; })()`);
/** Waits for the tooltip to show (the index is computed, and the pointer has rested). */
const untilTooltip = (page) => page.until(`!document.getElementById("navtip").hidden && document.getElementById("navtip").textContent`, 30000, "the tooltip");
/** What the editor has selected, and where. */
const selected = (page) => page.ev(`(() => { const s = document.getElementById("source");
  return { text: s.value.slice(s.selectionStart, s.selectionEnd), line: s.value.slice(0, s.selectionStart).split("\\n").length,
           readOnly: s.readOnly }; })()`);

test("hovering a name shows its type: a local, a declaration, a library function", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  // A parameter, used in the body.
  await hoverAt(page, await whereIs(page, "length xs", 7, 2));
  assert.match(await untilTooltip(page), /^xs local\n: List Nat$/);
  // A library function: its qualified name and its type.
  await hoverAt(page, await whereIs(page, "List.length xs", 5, 6));
  await page.until(`document.getElementById("navtip").textContent.includes("Std.List.length")`, 10000, "the library function's tooltip");
  assert.match(await tooltip(page), /^Std.List.length def\n: .*List .*Nat/s);
  // A parameter after astral characters on its line.
  await hoverAt(page, await whereIs(page, "else List.length ys", 17, 2));
  await page.until(`document.getElementById("navtip").textContent.startsWith("ys")`, 10000, "the tooltip of a name after astral characters");
  assert.match(await tooltip(page), /^ys local\n: List Nat$/);
  // A declaration of the program.
  await hoverAt(page, await whereIs(page, "double (double n)", 0, 6));
  await page.until(`document.getElementById("navtip").textContent.startsWith("Main.double")`, 10000, "the tooltip of a declaration");
  assert.match(await tooltip(page), /^Main.double def\n: Nat -> Nat$/);
  // Off a name, there is none.
  await hoverAt(page, await whereIs(page, "def double", 1, 1));
  await page.until(`document.getElementById("navtip").hidden`, 5000, "the tooltip to go");
}, { ms: 90000 });

test("with Cmd held, the name under the pointer is underlined, and a click goes to its definition in the same file", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  const at = await whereIs(page, "(double n)", 1, 3);
  await hoverAt(page, at, CMD);
  await page.until(`(() => { const l = document.getElementById("navlink"); return !l.hidden && l.getBoundingClientRect().width > 10; })()`, 30000, "the underline");
  assert.equal(await page.ev(`document.getElementById("source").style.cursor`), "pointer");
  await hoverAt(page, at, 0);
  await page.until(`document.getElementById("navlink").hidden`, 5000, "the underline to go without Cmd");
  await cmdClick(page, at);
  await page.until(`document.getElementById("source").selectionEnd > document.getElementById("source").selectionStart`, 10000, "a selection at the definition");
  assert.deepEqual(await selected(page), { text: "double", line: 3, readOnly: false });
  // Cmd-click on a local goes to its binder, after astral characters on the line.
  await cmdClick(page, await whereIs(page, "else List.length ys", 17, 2));
  await page.until(`document.getElementById("source").selectionStart === document.getElementById("source").value.indexOf("ys:")`, 10000, "the binder");
  assert.deepEqual(await selected(page), { text: "ys", line: 9, readOnly: false });
  // And back, by Cmd+[.
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.getElementById("source").selectionStart !== document.getElementById("source").value.indexOf("ys:")`, 10000, "the way back");
}, { ms: 90000 });

test("F12 goes to the definition of the name at the caret", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  await page.ev(`(() => { const s = document.getElementById("source"); s.focus();
    const i = s.value.indexOf("(double n)") + 3; s.setSelectionRange(i, i); })()`);
  await page.key("F12", "F12", 123);
  await page.until(`document.getElementById("source").selectionEnd > document.getElementById("source").selectionStart`, 30000, "the jump");
  assert.deepEqual(await selected(page), { text: "double", line: 3, readOnly: false });
}, { ms: 90000 });

test("Cmd-click on a library function shows the library's text, read-only, at its definition, with a way back", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  await cmdClick(page, await whereIs(page, "List.length xs", 5, 6));
  await page.until(`!document.getElementById("stdbar").hidden`, 30000, "the library's text");
  assert.match(await page.ev(`document.getElementById("std-name").textContent`), /\.sw$/);
  const there = await selected(page);
  assert.equal(there.text, "length");
  assert.equal(there.readOnly, true);
  // The line is the library's: the text shown has `length` defined there, and it's in view.
  const view = await page.ev(`(() => { const s = document.getElementById("source"), css = getComputedStyle(s);
    const line = s.value.slice(0, s.selectionStart).split("\\n").length - 1, text = s.value.split("\\n")[line];
    const y = parseFloat(css.paddingTop) + line * parseFloat(css.lineHeight);
    return { text, visible: y >= s.scrollTop && y < s.scrollTop + s.clientHeight, aligned: document.getElementById("highlight").textContent === s.value + "\\n" }; })()`);
  assert.match(view.text, /\bdef List\.length\b/);
  assert.ok(view.visible, "the line is scrolled into view");
  assert.ok(view.aligned, "the coloured copy shows the library's text");
  assert.equal(await page.status(), "Checked by the kernel", "the check is not disturbed");
  // The way back restores the editor, and it can be edited again.
  await page.click("#std-back");
  assert.equal(await page.ev(`document.getElementById("stdbar").hidden`), true);
  assert.equal(await sourceText(page), NAV_SOURCE);
  assert.equal((await selected(page)).readOnly, false);
  // Again, left with Escape.
  await cmdClick(page, await whereIs(page, "List.length xs", 5, 6));
  await page.until(`!document.getElementById("stdbar").hidden`, 30000, "the library's text again");
  await page.key("Escape", "Escape", 27);
  await page.until(`document.getElementById("stdbar").hidden`, 5000, "Escape to go back");
  assert.equal(await sourceText(page), NAV_SOURCE);
}, { ms: 90000 });

const STD_SOURCE = `import Std (List)

def lengths (xs: List Nat) : Nat := List.length xs

def total (xs: List Nat) : Nat := List.sum xs
`;

/** Selects `len` characters at `delta` into the first `needle` of the editor, as a keyboard or a phone's handles would. */
const selectText = (page, needle, delta, len) => page.ev(`(() => { const s = document.getElementById("source");
  const i = s.value.indexOf(${JSON.stringify(needle)}) + ${delta};
  s.focus({ preventScroll: true }); s.setSelectionRange(i, i + ${len}); })()`);
const selectionStatus = (page) => page.ev(`(() => { const t = document.getElementById("seltype"); return t.hidden ? null : t.textContent; })()`);
const untilSelectionStatus = (page, text) => page.until(`(() => { const t = document.getElementById("seltype"); return !t.hidden && t.textContent === ${JSON.stringify(text)}; })()`, 30000, `the selection's type ${text}`);

test("selecting an expression shows its type in the status line, and in the tooltip when the pointer is over the selection", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  // The whole call: the index is computed on demand.
  await selectText(page, "double (double n)", 0, 17);
  await untilSelectionStatus(page, "selection: Nat");
  await hoverAt(page, await whereIs(page, "double (double n)", 9, 3));
  await page.until(`!document.getElementById("navtip").hidden && document.getElementById("navtip").textContent.startsWith("selection")`, 10000, "the selection's tooltip");
  assert.equal(await tooltip(page), "selection\n: Nat");
  await shots(page, "selection-type");
  // The argument: the name under the pointer gives way to the selection.
  await selectText(page, "double (double n)", 8, 8);
  await untilSelectionStatus(page, "selection: Nat");
  await hoverAt(page, await whereIs(page, "double (double n)", 14, 1));
  await page.until(`document.getElementById("navtip").textContent === "selection\\n: Nat"`, 10000, "the argument's tooltip");
  // Whitespace at the ends is trimmed, and parentheses may or may not be in.
  await selectText(page, "length xs", 6, 4);
  await untilSelectionStatus(page, "selection: List Nat");
  await selectText(page, "(double n)", 0, 10);
  await untilSelectionStatus(page, "selection: Nat");
  await selectText(page, "double n)", 0, 8);
  await untilSelectionStatus(page, "selection: Nat");
  // A selection no expression covers (a keyword and a name) has no type.
  await selectText(page, "def quad", 0, 8);
  await page.until(`document.getElementById("seltype").hidden`, 10000, "the status to clear");
  // Pointer outside the selection: the ordinary hover.
  await selectText(page, "double (double n)", 8, 8);
  await untilSelectionStatus(page, "selection: Nat");
  await hoverAt(page, await whereIs(page, "length xs", 7, 2));
  await page.until(`document.getElementById("navtip").textContent.startsWith("xs")`, 10000, "the name's tooltip");
  // Collapsed, the status goes.
  await page.ev(`(() => { const s = document.getElementById("source"); s.setSelectionRange(3, 3); })()`);
  await page.until(`document.getElementById("seltype").hidden`, 10000, "the status to clear");
}, { ms: 120000 });

const stdName = (page) => page.ev(`document.getElementById("stdbar").hidden ? null : document.getElementById("std-name").textContent`);
const untilStd = (page, name, what) => page.until(`!document.getElementById("stdbar").hidden && document.getElementById("std-name").textContent === ${JSON.stringify(name)}`, 30000, what);
const textAtCaret = (page) => page.ev(`(() => { const s = document.getElementById("source");
  return s.value.split("\\n")[s.value.slice(0, s.selectionStart).split("\\n").length - 1]; })()`);
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

test("Inside a library file: hover, Cmd-click, F12, find references and the menu work, across library files, and Back walks the chain", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(STD_SOURCE);
  await page.untilChecked();
  // Program -> List.length in core/Data.sw.
  await cmdClick(page, await whereIs(page, "List.length xs", 5, 6));
  await untilStd(page, "core/Data.sw", "core/Data.sw");
  assert.match(await textAtCaret(page), /^def List\.length\b/);
  // Hover in the library file: a name in its type, then a constructor in its body.
  await hoverAt(page, await whereIs(page, "List a -> Nat\n  | Nil       => 0", 10, 3));
  await page.until(`document.getElementById("navtip").textContent.startsWith("Std.Nat")`, 30000, "the tooltip in the library file");
  assert.match(await tooltip(page), /^Std.Nat data\n: Type$/);
  await hoverAt(page, await whereIs(page, "Succ (List.length xs)", 0, 4));
  await page.until(`document.getElementById("navtip").textContent.startsWith("Std.Nat.Succ") || document.getElementById("navtip").textContent.startsWith("Succ")`, 10000, "the tooltip of a constructor");
  // With Cmd held the name is underlined, and the cursor says it's a link.
  const nat = await whereIs(page, "List a -> Nat\n  | Nil       => 0", 10, 3);
  await hoverAt(page, nat, CMD);
  await page.until(`(() => { const l = document.getElementById("navlink"); return !l.hidden && l.getBoundingClientRect().width > 10; })()`, 10000, "the underline in the library file");
  assert.equal(await page.ev(`document.getElementById("source").style.cursor`), "pointer");
  await shots(page, "std-hover-underline");
  // Cmd-click: to the definition of Nat, in core/Data.sw again (a second hop).
  await cmdClick(page, nat);
  await page.until(`document.getElementById("source").value.slice(document.getElementById("source").selectionStart, document.getElementById("source").selectionEnd) === "Nat" && document.getElementById("source").value.slice(0, document.getElementById("source").selectionStart).split("\\n").length < 40`, 10000, "the jump to Nat's definition");
  assert.match(await textAtCaret(page), /^type Nat\b/);
  assert.equal(await stdName(page), "core/Data.sw");
  assert.equal((await selected(page)).readOnly, true);
  // Back, once: to List.length in core/Data.sw; twice: to the program, editable again.
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.getElementById("source").value.slice(0, document.getElementById("source").selectionStart).split("\\n").length > 40`, 10000, "back to List.length");
  assert.match(await textAtCaret(page), /^def List\.length\b/);
  assert.equal(await stdName(page), "core/Data.sw");
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.getElementById("stdbar").hidden`, 10000, "back to the program");
  assert.equal(await sourceText(page), STD_SOURCE);
  assert.equal((await selected(page)).readOnly, false);

  // Program -> List.sum in List/Toolkit.sw -> Add.add in core/AddMul.sw: another library file, then Back twice.
  await cmdClick(page, await whereIs(page, "List.sum xs", 5, 3));
  await untilStd(page, "List/Toolkit.sw", "List/Toolkit.sw");
  assert.match(await textAtCaret(page), /^def List\.sum\b/);
  // F12 at the caret in the library file: go to the definition of the name.
  await page.ev(`(() => { const s = document.getElementById("source"); s.focus();
    const i = s.value.indexOf("Add.add Add.zero") + 1; s.setSelectionRange(i, i); })()`);
  await page.key("F12", "F12", 123);
  await untilStd(page, "core/AddMul.sw", "core/AddMul.sw from the toolkit");
  assert.match(await textAtCaret(page), /Add\b|add\b/);
  await shots(page, "std-after-jump");
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await untilStd(page, "List/Toolkit.sw", "back to the toolkit");
  assert.match(await textAtCaret(page), /^def List\.sum\b/);

  // Shift+F12 in the library file lists the declaration and uses; a row jumps there.
  await findReferencesAt(page, "def List.sum", 10);
  const panel = await refRows(page);
  assert.match(panel.title, /^Std\.List\.sum def: \d+ uses?/);
  assert.equal(panel.rows[0][2], true);
  assert.match(panel.rows[0][0], /^List\/Toolkit\.sw:/);
  assert.ok(panel.rows.some(([where, text]) => /^line 5$/.test(where) && /List\.sum xs/.test(text)), JSON.stringify(panel));
  await shots(page, "std-references");
  // The right-click menu on a name there, with its two lookups.
  await page.key("Escape", "Escape", 27);
  const menuAt = await whereIs(page, "Add.add Add.zero", 0, 3);
  await page.send("Input.dispatchMouseEvent", { type: "mouseMoved", x: menuAt.x, y: menuAt.y });
  await page.send("Input.dispatchMouseEvent", { type: "mousePressed", x: menuAt.x, y: menuAt.y, button: "right", clickCount: 1 });
  await page.send("Input.dispatchMouseEvent", { type: "mouseReleased", x: menuAt.x, y: menuAt.y, button: "right", clickCount: 1 });
  await page.until(`!document.getElementById("navmenu").hidden`, 10000, "the menu in the library file");
  assert.deepEqual(await page.ev(`[...document.querySelectorAll("#navmenu button")].map((b) => b.textContent)`), ["Go to definitionF12", "Find references⇧F12"]);
  await shots(page, "std-menu");
  await page.key("Escape", "Escape", 27);
  // Back to the program, the editor as it was.
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.getElementById("stdbar").hidden`, 10000, "back to the program");
  assert.equal(await sourceText(page), STD_SOURCE);
}, { ms: 180000 });

test("Cmd-click in a project goes to the definition in another file, and a library name shows a tooltip", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.until(`document.querySelectorAll("#filetabs button").length === ${DAY2_TABS.length}`, 10000, "day 2's tabs");
  const own = await sourceText(page);
  // `Range` is defined in Common/Range.sw.
  await cmdClick(page, await whereIs(page, "def solvePart1 (ranges: List Range)", 29, 5));
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`, 60000, "the other file");
  const there = await selected(page);
  assert.equal(there.text, "Range");
  assert.equal(await sourceText(page), await bundled(page, "src/Aoc/Common/Range.sw"));
  assert.match(await page.ev(`(() => { const s = document.getElementById("source");
    return s.value.split("\\n")[s.value.slice(0, s.selectionStart).split("\\n").length - 1]; })()`), /Range/);
  // The way back is the file we came from.
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Day02.sw"`, 10000, "the way back");
  assert.equal(await sourceText(page), own);
  // Hovering a library name in a project.
  await hoverAt(page, await whereIs(page, "List.rangeFrom size 1", 5, 9));
  await page.until(`document.getElementById("navtip").textContent.includes("Std.List.rangeFrom")`, 30000, "a library name's tooltip");
}, { ms: 180000 });

// Find references -------------------------------------------------------------------

const SHIFT = 8;
/** The panel's rows: [where, snippet text], or null while it is hidden. */
const refRows = (page) => page.ev(`(() => { const p = document.getElementById("navrefs"); if (p.hidden) return null;
  return { title: p.querySelector("header .title").textContent,
           rows: [...p.querySelectorAll("li button")].map((b) => [b.querySelector(".where").textContent, b.querySelector(".snippet").textContent,
                                                                    b.classList.contains("decl")]) }; })()`);
// Find references may first build the index, including the library (all of the core), in its
// worker; under load that took over 30 s three times on 21-22 Oct 2026, so allow 90 s.
const untilRefs = (page) => page.until(`!document.getElementById("navrefs").hidden`, 90000, "the references panel");
/** Puts the caret `delta` into the first `needle`, and presses Shift+F12. */
async function findReferencesAt(page, needle, delta) {
  await page.ev(`(() => { const s = document.getElementById("source"); s.focus();
    const i = s.value.indexOf(${JSON.stringify(needle)}) + ${delta}; s.setSelectionRange(i, i); })()`);
  await page.key("F12", "F12", 123, { modifiers: SHIFT });
  await untilRefs(page);
}

test("Shift+F12 lists the uses of a name in the file, with its declaration; clicking one goes there, and Cmd+[ comes back", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  assert.equal(await refRows(page), null);
  await findReferencesAt(page, "(double n)", 3);
  const panel = await refRows(page);
  assert.match(panel.title, /^Main.double def: 2 uses$/);
  assert.deepEqual(panel.rows, [
    ["line 3", "def double (n: Nat) : Nat := n + n", true],
    ["line 5", "def quad (n: Nat) : Nat := double (double n)", false],
    ["line 5", "def quad (n: Nat) : Nat := double (double n)", false],
  ]);
  // The name is marked in each snippet, and the first use has the focus.
  assert.deepEqual(await page.ev(`[...document.querySelectorAll("#navrefs li button .snippet mark")].map((m) => m.textContent)`), ["double", "double", "double"]);
  assert.equal(await page.ev(`document.activeElement === document.querySelectorAll("#navrefs li button")[1]`), true);
  // Go to the second use (the inner one).
  await page.ev(`document.querySelectorAll("#navrefs li button")[2].click()`);
  assert.equal(await page.ev(`document.getElementById("navrefs").hidden`), true);
  assert.deepEqual(await selected(page), { text: "double", line: 5, readOnly: false });
  assert.equal(await page.ev(`document.getElementById("source").selectionStart`),
               (await sourceText(page)).lastIndexOf("double"));
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.getElementById("source").selectionStart === document.getElementById("source").value.indexOf("(double n)") + 3`, 10000, "the way back");
}, { ms: 90000 });

test("references of a local variable and of a library function; the declaration's own name works too; Escape closes", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  // A parameter, from its binder: the binder, then its uses.
  await findReferencesAt(page, "(ys: List Nat)", 2);
  const local = await refRows(page);
  assert.match(local.title, /^ys local: 1 use$/);
  assert.equal(local.rows.length, 2);
  assert.match(local.rows[0][1], /^def tricky \(ys: List Nat\)/);
  assert.match(local.rows[1][1], /else List.length ys$/);
  await page.key("Escape", "Escape", 27);
  assert.equal(await page.ev(`document.getElementById("navrefs").hidden`), true);
  assert.equal(await page.ev(`document.activeElement === document.getElementById("source")`), true);
  // A library function: the uses in the program, the declaration in the library, and its other uses counted.
  await findReferencesAt(page, "List.length xs", 5);
  const lib = await refRows(page);
  assert.match(lib.title, /^Std.List.length def: 2 uses/);
  assert.deepEqual(lib.rows.map((r) => r[0]).slice(1), ["line 7", "line 9"]);
  assert.match(lib.rows[0][0], /\.sw:\d+ \(declaration\)|\.sw:\d+/);
  assert.match(lib.rows[0][1], /def List\.length/);
  await page.key("Escape", "Escape", 27);
  // Off a name, nothing opens.
  await page.ev(`(() => { const s = document.getElementById("source"); s.focus(); s.setSelectionRange(1, 1); })()`);
  await page.key("F12", "F12", 123, { modifiers: SHIFT });
  await sleep(1500);
  assert.equal(await page.ev(`document.getElementById("navrefs").hidden`), true);
}, { ms: 90000 });

test("the right-click menu on a name offers go to definition and find references", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.setSource(NAV_SOURCE);
  await page.untilChecked();
  const at = await whereIs(page, "(double n)", 1, 3);
  await hoverAt(page, at);
  await untilTooltip(page); // the index is ready
  const menu = () => page.ev(`(() => { const m = document.getElementById("navmenu"); return m.hidden ? null : [...m.querySelectorAll("button")].map((b) => b.textContent); })()`);
  const contextMenu = (p) => page.ev(`document.getElementById("source").dispatchEvent(new MouseEvent("contextmenu", { clientX: ${p.x}, clientY: ${p.y}, bubbles: true, cancelable: true }))`);
  // The browser's own menu is left alone off a name (the event isn't cancelled).
  assert.equal(await contextMenu(await whereIs(page, "def double", 1, 1)), true);
  assert.equal(await menu(), null);
  assert.equal(await contextMenu(at), false);
  assert.deepEqual(await menu(), ["Go to definitionF12", "Find references⇧F12"]);
  await page.ev(`document.querySelectorAll("#navmenu button")[1].click()`);
  await untilRefs(page);
  assert.equal(await menu(), null);
  assert.equal((await refRows(page)).rows.length, 3);
}, { ms: 90000 });

test("references in a project include other files; clicking one opens that file", async (page) => {
  await page.open();
  await page.untilChecked();
  await openDay(page, 2);
  await page.until(`document.querySelectorAll("#filetabs button").length === ${DAY2_TABS.length}`, 10000, "day 2's tabs");
  await page.ev(`document.getElementById("source").focus()`);
  await findReferencesAt(page, "def solvePart1 (ranges: List Range)", 30);
  const panel = await refRows(page);
  assert.match(panel.title, /^Aoc\.Common\.Range record: \d+ uses?$/);
  const labels = panel.rows.map((r) => r[0].replace(/:\d+( \(declaration\))?$/, ""));
  assert.ok(labels.includes("Common/Range.sw"), `rows: ${labels}`);
  assert.ok(labels.includes("Day02.sw"), `rows: ${labels}`);
  // The declaration is in Common/Range.sw: go to it from the panel.
  const decl = panel.rows.findIndex((r) => r[2]);
  assert.match(panel.rows[decl][0], /^Common\/Range\.sw:/);
  await page.ev(`document.querySelectorAll("#navrefs li button")[${decl}].click()`);
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Common/Range.sw"`, 60000, "the other file");
  assert.equal((await selected(page)).text, "Range");
  assert.equal(await sourceText(page), await bundled(page, "src/Aoc/Common/Range.sw"));
  // Back to where it was asked from.
  await page.key("[", "BracketLeft", 219, { modifiers: CMD });
  await page.until(`document.querySelector('#filetabs [aria-selected="true"]').firstChild.textContent === "Day02.sw"`, 10000, "the way back");
}, { ms: 180000 });

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
