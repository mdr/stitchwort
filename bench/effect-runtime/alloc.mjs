// Allocation and garbage collection inside one call of an export of a built
// module (docs/proposals/effect-runtime.md, stage 4f). Usage:
//
//   node --expose-gc bench/effect-runtime/alloc.mjs OUT/shapes.js searchedIn 1000000 [RUNS]
//
// Each run builds the input, collects garbage, then measures only the call:
// its time; the bytes it allocated (heap in use at the end, minus at the
// start, plus what every collection during the call freed, from
// `v8.GCProfiler`); the time spent collecting, and how often; the most heap
// in use after a collection during the call (what the run keeps alive); and
// the heap the result keeps alive once the call is over (a full collection
// with the result still referenced). Prints the median of RUNS (default 5)
// runs in the same process, after one warm-up run of the same size.
// `failsLast` and `countedChecked` get the size as their limit.
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import v8 from "node:v8";

const [file, name, size, runsArg] = process.argv.slice(2);
const runs = Number(runsArg ?? 5);
const m = await import(pathToFileURL(resolve(file)).href);
const n = Number(size);
const withLimit = new Set(["failsLast", "countedChecked"]);
if (typeof gc !== "function") throw new Error("run node with --expose-gc");
const used = () => v8.getHeapStatistics().used_heap_size;

const once = () => {
  const xs = Array.from({ length: n }, (_, i) => BigInt(i));
  gc();
  gc();
  const profiler = new v8.GCProfiler();
  const before = used();
  profiler.start();
  const start = performance.now();
  let result = withLimit.has(name) ? m[name](BigInt(n), xs) : m[name](xs);
  const ms = performance.now() - start;
  const end = used();
  const { statistics } = profiler.stop();
  let freed = 0, gcMs = 0, peak = before, scavenges = 0, fulls = 0;
  for (const s of statistics) {
    const b = s.beforeGC.heapStatistics.usedHeapSize;
    const a = s.afterGC.heapStatistics.usedHeapSize;
    freed += b - a;
    gcMs += s.cost / 1000;
    peak = Math.max(peak, a);
    if (s.gcType === "Scavenge") scavenges++; else fulls++;
  }
  gc();
  gc();
  const kept = used() - before;
  const alive = result !== undefined;
  result = undefined;
  return {
    ms,
    allocated: end - before + freed,
    gcMs,
    scavenges,
    fulls,
    peak: peak - before,
    kept,
    alive,
  };
};

// COLD=1 skips the warm-up: with RUNS=1, the call is the process's first.
if (!process.env.COLD) once();
const results = [];
for (let i = 0; i < runs; i++) results.push(once());
const median = (key) => {
  const v = results.map((r) => r[key]).sort((a, b) => a - b);
  return v[Math.floor(v.length / 2)];
};
const mb = (x) => (x / 1e6).toFixed(0);
console.log(
  [
    name,
    n,
    `${median("ms").toFixed(0)} ms`,
    `alloc ${mb(median("allocated"))} MB (${(median("allocated") / n).toFixed(0)} B/elem)`,
    `gc ${median("gcMs").toFixed(0)} ms (${median("scavenges")} scavenges, ${median("fulls")} full)`,
    `peak live ${mb(median("peak"))} MB`,
    `kept ${mb(median("kept"))} MB`,
  ].join("\t"),
);
