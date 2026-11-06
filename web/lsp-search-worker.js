// The language server's proof searches, in a worker of their own
// (started by lsp-worker.js): a second instance of the playground's
// WebAssembly, from the module the checker's worker compiled, with the same
// library and projects, and the library's check cache (pkg/std.cache.gz,
// fetched here as the other workers do; the browser's HTTP cache serves the
// file again), so that a search doesn't check the library first. Each {job}
// is a search the server handed out; the answer is {result}, the search's
// result as JSON. A stale search is stopped by terminating this worker.
import init, { load_std, SearchWorker } from "./pkg/stitchwort_web.js";

let searcher = null;

function handle(data) {
  if (data.module !== undefined) {
    return init({ module_or_path: data.module }).then(async () => {
      load_std(data.bundle);
      searcher = new SearchWorker();
      const cache = await fetch(new URL(`./pkg/std.cache.gz${data.load}`, import.meta.url))
        .then((r) => (r.ok ? new Response(r.body.pipeThrough(new DecompressionStream("gzip"))).arrayBuffer() : null))
        .catch(() => null);
      if (cache) searcher.load_library_cache(new Uint8Array(cache));
      for (const p of data.projects) searcher.add_project(p.root, p.sources, p.paths, p.texts);
    });
  }
  if (data.project !== undefined) {
    const p = data.project;
    searcher.add_project(p.root, p.sources, p.paths, p.texts);
  } else if (data.job !== undefined) {
    postMessage({ result: searcher.run(data.job) });
  }
}

let chain = Promise.resolve();
onmessage = ({ data }) => {
  chain = chain.then(() => handle(data)).catch((e) => postMessage({ crashed: String(e) }));
};
