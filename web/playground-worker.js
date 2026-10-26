// The playground's compiler, in a worker of its own (see index.html). The
// page discards this worker after a crash (a trap, or the engine's stack
// running out), because the WebAssembly instance's state isn't restored
// afterwards, and terminates it to stop a request that runs too long.
//
// Each request is { id, module, action, ... }, where `module` is the compiled
// WebAssembly module (compiled once by the page, so a fresh worker starts
// quickly). The reply is { id, out } with the compiler's parsed JSON, or
// { id, crashed: true, error }. While a run is going, each line it prints is
// sent as { id, output } as soon as it's printed: the run may be stopped at
// any time, and the worker can't send anything later, being busy until the
// run ends.

// The bindings are imported with the worker's own `?v=…`, so they always
// come from the same page load as the worker (see index.html). They're
// imported in the handler: `onmessage` must be set before the first message
// arrives, which a top-level `await` would delay.
let bindings = null;
let ready = null;

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
    const sink = { write: (output) => self.postMessage({ id: data.id, output }) };
    if (data.action.startsWith("live-")) {
      self.postMessage({ id: data.id, out: liveRequest(b, data, sink) });
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
      index: () => b.check_index_project(data.project, data.paths, data.texts, data.targets),
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
      index: () => b.check_index(data.source),
      check: () => b.check(data.source),
      test: () => b.test(data.source, data.known ?? ""),
      evaluate: () => b.evaluate(data.source, data.imports ?? "", data.expr),
      extract: () => b.extract(data.source),
      format: () => b.format(data.source),
      run: () => b.run_streaming(data.source, data.input, data.maxOutput, sink),
    }[data.action];
    self.postMessage({ id: data.id, out: JSON.parse(answer()) });
  } catch (e) {
    self.postMessage({ id: data.id, crashed: true, error: `${e?.name ?? "Error"}: ${e?.message ?? e}` });
  }
};
