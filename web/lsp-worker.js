// The language server in a worker: crates/lsp, compiled into the
// playground's WebAssembly (crates/web/src/lsp.rs). The page (the editor,
// web/editor/src/editor-entry.js) first posts {init: {module, load}}: the
// compiled WebAssembly, and the query string (`?v=HASH`) for the files this
// worker fetches. Then it posts JSON-RPC text, and the worker posts back
// {lsp: text} for each message the server sends. Between messages it runs the server's background work a
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
// that it bumps for each didOpen, didChange and didClose: the server then
// stops a check as soon as the counter is ahead of the edits read
// (cancellation, docs/proposals/playground-editor.md §5.2.1). A didOpen of
// another document stops the check too, so that the new document's check
// isn't queued behind a long one already running.
//
// The page may post {project: {root, sources, paths, texts}}: that project
// is then read from memory (`LanguageServer::add_project`), for documents
// opened under its root, as file:///playground/aoc/src/…. {setFile: {root,
// path, text}} gives one of its files other text (`set_project_file`).
import init, { checking_namespace, load_std, stack_reached, std_source, LanguageServer } from "./pkg/stitchwort_web.js";

let server = null;
let module = null;
let load = "";
let bundle = null;
const projects = [];
let begin;
// Whether the library's check cache was read (false: no cache, or another
// build's), once it has been fetched: a project waits for it.
let libraryCache = null;
const started = new Promise((ok) => { begin = ok; });
const ready = (async () => {
  const first = await started;
  ({ module, load } = first);
  const t0 = performance.now();
  await init({ module_or_path: module });
  const cache = fetch(new URL(`./pkg/std.cache.gz${load}`, import.meta.url))
    .then((r) => (r.ok ? new Response(r.body.pipeThrough(new DecompressionStream("gzip"))).arrayBuffer() : null))
    .catch(() => null);
  bundle = new Uint8Array(await fetch(new URL(`./pkg/std.bundle${load}`, import.meta.url)).then((r) => r.arrayBuffer()));
  load_std(bundle);
  server = new LanguageServer();
  // The library checked when the page was built (web/bundle-std-cache.mjs),
  // several megabytes: a program on its own doesn't wait for it, a project
  // does. Without it each project checks the library again on its first
  // load, which takes tens of seconds.
  libraryCache = cache.then((bytes) => {
    const read = bytes !== null && server.load_library_cache(new Uint8Array(bytes));
    postMessage({ libraryCache: read, after: performance.now() - t0 });
    return read;
  });
  postMessage({ ready: performance.now() - t0 });
})().catch((e) => postMessage({ crashed: String(e) }));

// ---- searches --------------------------------------------------------------

let searcher = null;
let searcherLoaded = false;
let running = null; // { key, id, t }
const queue = []; // [{ key, id, search }]
const key = (id) => JSON.stringify(id);
// Whether the server has checked a document: until then its first check
// shouldn't compete with the search worker's library load.
let checked = false;
let warmed = false;

/**
 * Starts the search worker before a search needs it, once the first check is
 * done and there is a project to search in: the rest of a project's check
 * goes on while the library loads.
 */
function warmSearcher() {
  if (warmed || !checked || projects.length === 0) return;
  warmed = true;
  if (!searcher) startSearcher();
}

function startSearcher() {
  searcherLoaded = false;
  searcher = new Worker(new URL("./lsp-search-worker.js", import.meta.url), { type: "module" });
  searcher.postMessage({ module, bundle, projects, load });
  searcher.onmessage = ({ data }) => {
    if (data.ready !== undefined) {
      searcherLoaded = true;
      nextSearch();
    } else if (data.warmed !== undefined) {
      postMessage({ searchWorker: { ...data.warmed, at: performance.now() } });
    } else if (data.result !== undefined && running) {
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
      searcherLoaded = false;
      running = null;
      if (done) send(server.searched(done.key, "null"));
      nextSearch();
    }
  };
}

function nextSearch() {
  if (running || queue.length === 0) return;
  if (!searcher) startSearcher();
  // Its init may not be done yet; the ready message starts the search. Its
  // library load may still be running after that, and this worker's message
  // chain makes the search wait for it rather than start a second load.
  if (!searcherLoaded) return;
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
    searcherLoaded = false;
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

// For a crash's report: the namespace being checked, and how deep the
// WebAssembly stack got (in a build with STITCHWORT_STACK_PROBE). Never
// throws, so the crash itself is always reported.
function crashInfo() {
  try {
    return { stack: Array.from(stack_reached()), checking: checking_namespace() };
  } catch {
    return {};
  }
}

let scheduled = false;
function schedule() {
  if (scheduled) return;
  scheduled = true;
  setTimeout(tick, 0);
}

// Where a re-check's time goes (SW-3113): the page sums these in `stats.phases`.
let lastTickEnd = null;
function tick() {
  scheduled = false;
  const t = performance.now();
  const gap = lastTickEnd === null ? 0 : t - lastTickEnd;
  let answer;
  try {
    answer = JSON.parse(server.tick());
  } catch (e) {
    postMessage({ crashed: String(e) + "\n" + (e?.stack ?? "").split("\n").slice(0, 12).join("\n"), ...crashInfo() });
    return;
  }
  const ms = performance.now() - t;
  const t1 = performance.now();
  send(JSON.stringify(answer.sent));
  takeSearches();
  const sendMs = performance.now() - t1;
  postMessage({ tick: ms, sendMs, gap, published: answer.sent.length, startAbs: performance.timeOrigin + t, more: answer.more });
  lastTickEnd = performance.now();
  if (!checked && answer.sent.some((m) => m.method === "stitchwort/checked")) {
    checked = true;
    warmSearcher();
  }
  if (answer.more) schedule();
  // `stack`: the WebAssembly stack the work reached, in a build with STITCHWORT_STACK_PROBE.
  else postMessage({ phases: { ...JSON.parse(server.phases()), stack: Array.from(stack_reached()) } });
}

function loadProject(project) {
  projects.push(project);
  server.add_project(project.root, project.sources, project.paths, project.texts);
  searcher?.postMessage({ project });
  warmSearcher();
  postMessage({ project: project.root, files: project.paths.length });
}

// Edits the page has sent (in `edits`) against those read here.
let editsSent = null;
let editsRead = 0;
const STALE = new Set(["textDocument/didOpen", "textDocument/didChange", "textDocument/didClose"]);
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
    await libraryCache;
    loadProject(data.project);
    return;
  }
  if (data.setFile !== undefined) {
    // A rename changed a file of a project that the editor hasn't opened.
    const { root, path, text } = data.setFile;
    await libraryCache;
    server.set_project_file(root, path, text);
    const project = projects.find((p) => p.root === root);
    const at = project?.paths.indexOf(path) ?? -1;
    if (at >= 0) project.texts[at] = text;
    searcher?.postMessage({ setFile: data.setFile });
    return;
  }
  const t = performance.now();
  const method = JSON.parse(data).method;
  if (STALE.has(method)) editsRead++;
  try {
    send(server.receive(data));
    takeSearches();
  } catch (e) {
    postMessage({ crashed: String(e) + "\n" + (e?.stack ?? "").split("\n").slice(0, 12).join("\n"), ...crashInfo() });
    return;
  }
  postMessage({ received: performance.now() - t, method });
  lastTickEnd = null;
  schedule();
}

// One message at a time, in order, each after the server is ready.
let chain = ready;
onmessage = ({ data }) => {
  if (data.init !== undefined) {
    begin(data.init);
    return;
  }
  chain = chain.then(() => handle(data)).catch((e) => postMessage({ crashed: String(e) }));
};
