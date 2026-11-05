// The language server in a worker: crates/lsp, compiled into the
// playground's WebAssembly (crates/web/src/lsp.rs). The page posts
// JSON-RPC text; the worker posts back {lsp: text} for each message the
// server sends. Between messages it runs the server's background work a
// piece at a time (one namespace's check), so a new edit is read before the
// next piece.
//
// Proof searches (code actions on `?`) take seconds, so they run in a
// second worker (lsp-search-worker.js), one at a time, and the checker goes
// on meanwhile. A search the server answers itself meanwhile (with null:
// the document was edited, or a newer request superseded it) is stale: a
// queued one is dropped, and a running one is stopped by terminating that
// worker and starting another.
//
// The page may post {edits: Int32Array} first, a counter in shared memory
// that it bumps for each didChange and didClose: the server then stops a
// check as soon as the counter is ahead of the edits read (cancellation,
// docs/proposals/playground-editor.md §5.2.1).
//
// The page may post {project: name} first: the bundled project
// pkg/projects/NAME/ is then read from memory at /playground/NAME, for
// documents opened as file:///playground/NAME/src/….
import init, { load_std, std_source, LanguageServer } from "../pkg/stitchwort_web.js";

let server = null;
let module = null;
let bundle = null;
const projects = [];
const ready = (async () => {
  const t0 = performance.now();
  module = await WebAssembly.compileStreaming(fetch(new URL("../pkg/stitchwort_web_bg.wasm", import.meta.url)));
  await init({ module_or_path: module });
  bundle = new Uint8Array(await fetch(new URL("../pkg/std.bundle", import.meta.url)).then((r) => r.arrayBuffer()));
  load_std(bundle);
  server = new LanguageServer();
  postMessage({ ready: performance.now() - t0 });
})().catch((e) => postMessage({ crashed: String(e) }));

// ---- searches --------------------------------------------------------------

let searcher = null;
let running = null; // { key, id, t }
const queue = []; // [{ key, id, search }]
const key = (id) => JSON.stringify(id);

function startSearcher() {
  searcher = new Worker(new URL("./lsp-search-worker.js", import.meta.url), { type: "module" });
  searcher.postMessage({ module, bundle, projects });
  searcher.onmessage = ({ data }) => {
    if (data.result !== undefined && running) {
      const done = running;
      running = null;
      postMessage({ searched: performance.now() - done.t });
      send(server.searched(done.key, data.result));
      nextSearch();
    } else if (data.crashed !== undefined) {
      // Its instance may be broken: the search is answered with nothing,
      // and the next runs in a new worker.
      postMessage({ searchCrashed: data.crashed });
      const done = running;
      searcher.terminate();
      searcher = null;
      running = null;
      if (done) send(server.searched(done.key, "null"));
      nextSearch();
    }
  };
}

function nextSearch() {
  if (running || queue.length === 0) return;
  if (!searcher) startSearcher();
  const job = queue.shift();
  running = { key: job.key, id: job.id, t: performance.now() };
  searcher.postMessage({ job: JSON.stringify(job.search) });
}

function takeSearches() {
  for (const job of JSON.parse(server.take_searches())) queue.push({ ...job, key: key(job.id) });
  nextSearch();
}

// A response the server sent for a search handed out: it is stale.
function answered(k) {
  const i = queue.findIndex((j) => j.key === k);
  if (i >= 0) queue.splice(i, 1);
  if (running?.key === k) {
    searcher.terminate();
    searcher = null;
    running = null;
    postMessage({ searchStopped: k });
    nextSearch();
  }
}

// ---- messages ----------------------------------------------------------------

function send(array) {
  for (const message of JSON.parse(array)) {
    if (message.id !== undefined && message.method === undefined) answered(key(message.id));
    postMessage({ lsp: JSON.stringify(message) });
  }
}

let scheduled = false;
function schedule() {
  if (scheduled) return;
  scheduled = true;
  setTimeout(tick, 0);
}

function tick() {
  scheduled = false;
  const t = performance.now();
  let answer;
  try {
    answer = JSON.parse(server.tick());
  } catch (e) {
    postMessage({ crashed: String(e) });
    return;
  }
  const ms = performance.now() - t;
  send(JSON.stringify(answer.sent));
  takeSearches();
  postMessage({ tick: ms, published: answer.sent.length, startAbs: performance.timeOrigin + t });
  if (answer.more) schedule();
}

async function loadProject(name) {
  const base = new URL(`../pkg/projects/${name}/`, import.meta.url);
  const manifest = await fetch(new URL("manifest.json", base)).then((r) => r.json());
  const paths = [...manifest.files, ...manifest.data];
  const texts = await Promise.all(paths.map((p) => fetch(new URL(p, base)).then((r) => r.text())));
  const project = { root: `/playground/${name}`, sources: ["src"], paths, texts };
  projects.push(project);
  server.add_project(project.root, project.sources, paths, texts);
  searcher?.postMessage({ project });
  postMessage({ project: name, files: paths.length });
}

// Edits the page has sent (in `edits`) against those read here.
let editsSent = null;
let editsRead = 0;
const STALE = new Set(["textDocument/didChange", "textDocument/didClose"]);
globalThis.stitchwortEditsWaiting = () => editsSent !== null && Atomics.load(editsSent, 0) !== editsRead;

async function handle(data) {
  if (data.edits !== undefined) {
    editsSent = data.edits;
    server.watch_edits();
    return;
  }
  if (data.stdSource !== undefined) {
    postMessage({ stdSource: data.stdSource, text: std_source(data.stdSource) });
    return;
  }
  if (data.project !== undefined) {
    await loadProject(data.project);
    return;
  }
  const t = performance.now();
  const method = JSON.parse(data).method;
  if (STALE.has(method)) editsRead++;
  try {
    send(server.receive(data));
    takeSearches();
  } catch (e) {
    postMessage({ crashed: String(e) });
    return;
  }
  postMessage({ received: performance.now() - t, method });
  schedule();
}

// One message at a time, in order, each after the server is ready.
let chain = ready;
onmessage = ({ data }) => {
  chain = chain.then(() => handle(data)).catch((e) => postMessage({ crashed: String(e) }));
};
