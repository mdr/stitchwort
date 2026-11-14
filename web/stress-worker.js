// Runs one request against the compiler, in its own worker, so that a crash
// (a trap, or the engine's stack running out) can't leave the page's
// WebAssembly instance in a broken state, and a runaway case can be stopped
// by terminating the worker. See stress.html.

import init, { check, evaluate, limits, load_library_cache, load_std, stack_reached, test } from "./pkg/stitchwort_web.js";

let wasm;
// Enough frames in a crash's trace to see which recursion overflowed.
Error.stackTraceLimit = 200;

self.onmessage = async ({ data }) => {
  const started = performance.now();
  const memory = () => wasm?.memory?.buffer.byteLength ?? null;
  // Bytes of WebAssembly stack the run reached, in a build with
  // STITCHWORT_STACK_PROBE (0 otherwise): read after a crash too, since it is
  // kept in linear memory.
  const reached = () => { try { return stack_reached(); } catch { return null; } };
  try {
    if (!wasm) {
      wasm = await init();
      load_std(new Uint8Array(await (await fetch(new URL("./pkg/std.bundle", import.meta.url))).arrayBuffer()));
      // The library as the build checked it, as the playground's workers read it.
      const cache = await fetch(new URL("./pkg/std.cache.gz", import.meta.url))
        .then((r) => (r.ok ? new Response(r.body.pipeThrough(new DecompressionStream("gzip"))).arrayBuffer() : null))
        .catch(() => null);
      if (cache) load_library_cache(new Uint8Array(cache));
    }
    reached();
    const run = {
      check: () => check(data.source),
      test: () => test(data.source),
      evaluate: () => evaluate(data.source, "", data.expr),
      limits: () => limits(),
    }[data.action];
    const out = JSON.parse(run());
    self.postMessage({ crashed: false, out, ms: performance.now() - started, memory: memory(), stack: reached() });
  } catch (e) {
    self.postMessage({
      crashed: true,
      error: `${e?.name ?? "Error"}: ${e?.message ?? e}`,
      ms: performance.now() - started,
      memory: memory(),
      stack: reached(),
      trace: e?.stack ?? null,
    });
  }
};
