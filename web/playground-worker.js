// The playground's compiler, in a worker of its own (see index.html). The
// page discards this worker after a crash (a trap, or the engine's stack
// running out), because the WebAssembly instance's state isn't restored
// afterwards, and terminates it to stop a request that runs too long.
//
// Each request is { id, module, action, ... }, where `module` is the compiled
// WebAssembly module (compiled once by the page, so a fresh worker starts
// quickly). The reply is { id, out } with the compiler's parsed JSON, or
// { id, crashed: true, error }. While a run is going, what it prints is sent
// as { id, output } messages: the run may be stopped at any time, and the
// worker can't send anything later, being busy until the run ends. A message
// per line costs far more than the printing (hundreds of thousands of
// messages queue up in the page), so a burst of lines goes in one message;
// see `outputSink`.

// The bindings are imported with the worker's own `?v=…`, so they always
// come from the same page load as the worker (see index.html). They're
// imported in the handler: `onmessage` must be set before the first message
// arrives, which a top-level `await` would delay.
let bindings = null;
let ready = null;
// The standard library's files, fetched beside the WebAssembly (pkg/std.bundle,
// with the worker's `?v=…`) and given to the compiler before its first use,
// and the library as the build checked it (pkg/std.cache, the same file the
// language server's worker reads), so that tests, runs and evaluations replay
// the library instead of checking it again. A cache that is missing or
// another build's leaves them checking it, as before.
let stdLoaded = null;

// A live run (docs/proposals/playground-live-keys.md): the run stays here,
// paused, between keys. Its requests, each answered with { id, out } after
// the output it caused ({ id, output }), where `out` is { state } with the
// state "waiting", "finished", "interrupted", "ended", "stopped" or
// "failed" (and then `errors`):
//   live-start  { source } or { paths, texts, name }: start and run to the
//               first wait
//   live-keys   { keys: [[byte, ...], ...], close }: push each key as one
//               read (Ctrl-C is [3]), close the input if asked, and run on
//   live-stop   drop the run
let live = null;

// The most a message holds before it's sent, and the quiet time after which
// the next print is sent at once. The worker is busy while a run goes on and
// has no timer to flush with, so text printed in a burst waits until the next
// print after that interval, or until the request ends.
const OUTPUT_BATCH = 64 * 1024;
const OUTPUT_QUIET_MS = 16;

/**
 * The run's `sink`: a `write(text)` that batches, and a `flush()` that must
 * be called before the request's reply, so the output stays ahead of it (and
 * of the error or the wait for input that ends the run).
 */
function outputSink(id) {
  let buffered = "";
  let lastSent = performance.now();
  const flush = () => {
    if (buffered) self.postMessage({ id, output: buffered });
    buffered = "";
    lastSent = performance.now();
  };
  return {
    write(text) {
      buffered += text;
      if (buffered.length >= OUTPUT_BATCH || performance.now() - lastSent >= OUTPUT_QUIET_MS) flush();
    },
    flush,
  };
}

function liveRequest(b, data, sink) {
  const done = () => { live?.free(); live = null; };
  if (data.action === "live-stop") {
    done();
    return { state: "stopped" };
  }
  if (data.action === "live-start") {
    done();
    try {
      live = data.paths ? b.start_live_project(data.project, data.paths, data.texts, data.name) : b.start_live(data.source);
    } catch (failure) {
      return { state: "failed", errors: JSON.parse(failure).errors };
    }
  } else if (live) {
    for (const key of data.keys ?? []) live.push(Uint8Array.from(key));
    if (data.close) live.close();
  } else {
    return { state: "ended" };
  }
  const out = JSON.parse(live.advance(sink));
  if (out.state !== "waiting") done();
  return out;
}

self.onmessage = async ({ data }) => {
  try {
    bindings ??= import(`./pkg/stitchwort_web.js${self.location.search}`);
    const b = await bindings;
    ready ??= b.default({ module_or_path: data.module });
    await ready;
    stdLoaded ??= fetch(`./pkg/std.bundle${self.location.search}`)
      .then((r) => { if (!r.ok) throw new Error(`std.bundle: HTTP ${r.status}`); return r.arrayBuffer(); })
      .then(async (bytes) => {
        b.load_std(new Uint8Array(bytes));
        const cache = await fetch(`./pkg/std.cache${self.location.search}`)
          .then((r) => (r.ok ? r.arrayBuffer() : null))
          .catch(() => null);
        if (cache) b.load_library_cache(new Uint8Array(cache));
      });
    await stdLoaded;
    const sink = outputSink(data.id);
    if (data.action.startsWith("live-")) {
      let out;
      try {
        out = liveRequest(b, data, sink);
      } finally {
        sink.flush();
      }
      self.postMessage({ id: data.id, out });
      return;
    }
    // A request with `paths` is for a project: the files are `paths` and
    // `texts`, and `targets` are the namespaces to check.
    // The library's text (for navigation): the one answer that isn't JSON.
    if (data.action === "stdsource") {
      self.postMessage({ id: data.id, out: { text: b.std_source(data.path) } });
      return;
    }
    const answer = data.paths ? {
      outline: () => b.outline_project(data.project, data.paths, data.texts),
      check: () => b.check_project(data.project, data.paths, data.texts, data.targets),
      checkall: () => b.check_project(data.project, data.paths, data.texts, ""),
      test: () => b.test_project(data.project, data.paths, data.texts, data.targets, data.known ?? ""),
      evaluate: () => b.evaluate_project(data.project, data.paths, data.texts, data.targets, data.imports ?? "", data.expr),
      extract: () => b.extract_project(data.project, data.paths, data.texts, data.namespace),
      // Formats the open file only: `source` is its text.
      format: () => b.format(data.source),
      run: () => b.run_project_streaming(data.project, data.paths, data.texts, data.name, data.input, data.maxOutput, sink),
    }[data.action] : {
      check: () => b.check(data.source),
      test: () => b.test(data.source, data.known ?? ""),
      evaluate: () => b.evaluate(data.source, data.imports ?? "", data.expr),
      extract: () => b.extract(data.source),
      format: () => b.format(data.source),
      run: () => b.run_streaming(data.source, data.input, data.maxOutput, sink),
    }[data.action];
    let out;
    try {
      out = JSON.parse(answer());
    } finally {
      sink.flush();
    }
    self.postMessage({ id: data.id, out });
  } catch (e) {
    self.postMessage({ id: data.id, crashed: true, error: `${e?.name ?? "Error"}: ${e?.message ?? e}` });
  }
};
