// The language server's proof searches, in a worker of their own
// (started by lsp-worker.js): a second instance of the playground's
// WebAssembly, from the module the checker's worker compiled, with the same
// library and projects, and the library's check cache (pkg/std.cache.gz,
// fetched here as the other workers do; the browser's HTTP cache serves the
// file again), so that a search doesn't check the library first. Each {job}
// is a search the server handed out; the answer is {result}, the search's
// result as JSON. A stale search is stopped by terminating this worker.
import init, { load_std, SearchWorker } from "./pkg/stitchwort_web.js";

const started = performance.now();
let searcher = null;
let wasm = null;
let warmed = false;

/**
 * Loads the library a project's searches keep, once there is a project to
 * search in. A check of a file on its own doesn't need it, so the worker
 * doesn't hold its quick searches (the `.` member list) for it.
 */
function warm() {
  if (warmed) return;
  warmed = true;
  const t = performance.now();
  searcher.warm();
  postMessage({ warmed: { warm: performance.now() - t, memory: wasm.memory.buffer.byteLength, at: performance.now() - started } });
}

function handle(data) {
  if (data.module !== undefined) {
    return init({ module_or_path: data.module }).then(async (instance) => {
      wasm = instance;
      load_std(data.bundle);
      searcher = new SearchWorker();
      const cache = await fetch(new URL(`./pkg/std.cache.gz${data.load}`, import.meta.url))
        .then((r) => (r.ok ? new Response(r.body.pipeThrough(new DecompressionStream("gzip"))).arrayBuffer() : null))
        .catch(() => null);
      if (cache) searcher.load_library_cache(new Uint8Array(cache));
      for (const p of data.projects) searcher.add_project(p.root, p.sources, p.paths, p.texts);
      // The page starts this worker before the first search, so the library
      // loads while it is still being read; any search posted meanwhile waits
      // in this worker's message chain.
      postMessage({ ready: performance.now() - started });
      if (data.projects.length > 0) warm();
    });
  }
  if (data.project !== undefined) {
    const p = data.project;
    searcher.add_project(p.root, p.sources, p.paths, p.texts);
    warm();
  } else if (data.setFile !== undefined) {
    searcher.set_project_file(data.setFile.root, data.setFile.path, data.setFile.text);
  } else if (data.job !== undefined) {
    postMessage({ result: searcher.run(data.job) });
  }
}

let chain = Promise.resolve();
onmessage = ({ data }) => {
  chain = chain.then(() => handle(data)).catch((e) => postMessage({ crashed: String(e) }));
};
