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
import { existsSync, mkdtempSync, readFileSync, rmSync, statSync } from "node:fs";
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

def start : Maybe Text -> Nat
  | Nothing => 1000000000000
  | Just l  => 1000000000000

def main () : {IO} () :=
  print "tick"
  print (Nat.toText (spin (start (readLine ()))))
`;

/** Prints `line` `n` times. */
const printMany = (n, line) => `def printMany : Nat -> {IO} ()
  | 0      => ()
  | Succ n =>
    print "${line}"
    printMany n

def main () : {IO} () := printMany ${n}
`;

/** Reads `n` lines, ignoring what it gets. */
const readMany = (n) => `def readMany : Nat -> {IO} ()
  | 0      => ()
  | Succ n =>
    let l := readLine ()
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
      res.writeHead(200, { "content-type": TYPES[extname(path)], "cache-control": "no-store" });
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

test("every example checks, and passes its tests but the failing one", async (page) => {
  await page.open();
  await page.untilChecked();
  await page.tab("tests");
  const ids = await page.ev(`[...document.getElementById("example").options].map((o) => o.value)`);
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
      assert.match(summary, /^4 tests: 3 passed, 1 failed$/, `${id}: ${summary} / ${await page.output()} / ${await page.ev("document.getElementById(\"source\").value.slice(0,80)")} / ${ids}`);
      assert.match(await page.output(), /✗\s*this one fails \(evaluated to False\)/);
    } else if (summary !== "No tests yet") {
      assert.match(summary, /^(\d+) tests: \1 passed, 0 failed$/, id);
    }
    await assertAligned(page, id);
  }
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
  await page.setSource(WARNED + `\ntest "sized" := Nat.leq (size [1, 2]) 2\n`);
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
  assert.equal(result, "[3, 2, 1] : List Nat");
  await page.ev(`(() => { const i = document.getElementById("eval-input"); i.value = "nope 1";
    i.form.requestSubmit(); })()`);
  assert.match(await page.until(`document.querySelector("#output pre.errors")?.textContent`), /E-UNKNOWN-NAME/);
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

// No program is known to crash the compiler any more: its depth guards stop
// deep programs with E-RESOURCE first. So this test serves a worker that
// checks a program containing CRASH with the engine's stack almost used up,
// which overflows it inside the WebAssembly, as a deep program once did.
const CRASH = "-- crash the engine's stack";
const crashing = (worker) => {
  const check = "check: () => check(data.source),";
  assert.ok(worker.includes(check), "the worker checks with check(data.source)");
  return worker.replace(check, `check: () => data.source.includes(${JSON.stringify(CRASH)})
      ? withoutStack(() => check(data.source)) : check(data.source),`) + `
// For the browser tests: runs f with only a little of the stack left.
function withoutStack(f) {
  let depth = 0;
  const measure = () => { depth++; measure(); };
  try { measure(); } catch {}
  const at = (n) => n === 0 ? f() : at(n - 1) + 0;
  return at(depth - 100);
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
    await page.until(`document.querySelector(".summary")?.textContent === "4 tests: 3 passed, 1 failed"`);
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

test("`|>` is coloured as one operator", async (page) => {
  await page.open({ patch: "delete window.Highlight;" });
  await page.untilChecked();
  await page.setSource("def n : Nat := [1, 2]\n  |> List.sum\n");
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
