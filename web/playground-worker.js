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

self.onmessage = async ({ data }) => {
  try {
    bindings ??= import(`./pkg/stitchwort_web.js${self.location.search}`);
    const b = await bindings;
    ready ??= b.default({ module_or_path: data.module });
    await ready;
    const sink = { write: (output) => self.postMessage({ id: data.id, output }) };
    // A request with `paths` is for a project: the files are `paths` and
    // `texts`, and `targets` are the namespaces to check.
    // The library's text (for navigation): the one answer that isn't JSON.
    if (data.action === "stdsource") {
      self.postMessage({ id: data.id, out: { text: b.std_source(data.path) } });
      return;
    }
    const answer = data.paths ? {
      index: () => b.check_index_project(data.paths, data.texts, data.targets),
      outline: () => b.outline_project(data.paths, data.texts),
      check: () => b.check_project(data.paths, data.texts, data.targets),
      checkall: () => b.check_project(data.paths, data.texts, ""),
      test: () => b.test_project(data.paths, data.texts, data.targets, data.known ?? ""),
      evaluate: () => b.evaluate_project(data.paths, data.texts, data.targets, data.imports ?? "", data.expr),
      extract: () => b.extract_project(data.paths, data.texts, data.namespace),
      run: () => b.run_project_streaming(data.paths, data.texts, data.name, data.input, data.maxOutput, sink),
    }[data.action] : {
      index: () => b.check_index(data.source),
      check: () => b.check(data.source),
      test: () => b.test(data.source, data.known ?? ""),
      evaluate: () => b.evaluate(data.source, data.imports ?? "", data.expr),
      extract: () => b.extract(data.source),
      run: () => b.run_streaming(data.source, data.input, data.maxOutput, sink),
    }[data.action];
    self.postMessage({ id: data.id, out: JSON.parse(answer()) });
  } catch (e) {
    self.postMessage({ id: data.id, crashed: true, error: `${e?.name ?? "Error"}: ${e?.message ?? e}` });
  }
};
