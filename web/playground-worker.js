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

import init, { check, evaluate, extract, run_streaming, test } from "./pkg/stitchwort_web.js";

let ready = null;

self.onmessage = async ({ data }) => {
  try {
    ready ??= init({ module_or_path: data.module });
    await ready;
    const sink = { write: (output) => self.postMessage({ id: data.id, output }) };
    const answer = {
      check: () => check(data.source),
      test: () => test(data.source),
      evaluate: () => evaluate(data.source, data.expr),
      extract: () => extract(data.source),
      run: () => run_streaming(data.source, data.input, data.maxOutput, sink),
    }[data.action];
    self.postMessage({ id: data.id, out: JSON.parse(answer()) });
  } catch (e) {
    self.postMessage({ id: data.id, crashed: true, error: `${e?.name ?? "Error"}: ${e?.message ?? e}` });
  }
};
