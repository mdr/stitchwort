// Runs one request against the compiler, in its own worker, so that a crash
// (a trap, or the engine's stack running out) can't leave the page's
// WebAssembly instance in a broken state, and a runaway case can be stopped
// by terminating the worker. See stress.html.

import init, { check, evaluate, limits, test } from "./pkg/stitchwort_web.js";

let wasm;

self.onmessage = async ({ data }) => {
  const started = performance.now();
  const memory = () => wasm?.memory?.buffer.byteLength ?? null;
  try {
    wasm ??= await init();
    const run = {
      check: () => check(data.source),
      test: () => test(data.source),
      evaluate: () => evaluate(data.source, "", data.expr),
      limits: () => limits(),
    }[data.action];
    const out = JSON.parse(run());
    self.postMessage({ crashed: false, out, ms: performance.now() - started, memory: memory() });
  } catch (e) {
    self.postMessage({
      crashed: true,
      error: `${e?.name ?? "Error"}: ${e?.message ?? e}`,
      ms: performance.now() - started,
      memory: memory(),
    });
  }
};
