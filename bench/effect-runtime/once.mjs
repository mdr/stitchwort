// Calls one export of a built module once, for profiling with Node's flags
// (docs/proposals/effect-runtime-review.md). Usage:
//
//   node --trace-gc bench/effect-runtime/once.mjs OUT/map-loop.js checked 1024000
//
// Prints the time and the heap in use after the call. `failsLast` and
// `countedChecked` get the size as their limit.
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const [file, name, size] = process.argv.slice(2);
const m = await import(pathToFileURL(resolve(file)).href);
const n = Number(size);
const xs = Array.from({ length: n }, (_, i) => BigInt(i));
const withLimit = new Set(["failsLast", "countedChecked"]);
const start = performance.now();
const result = withLimit.has(name) ? m[name](BigInt(n), xs) : m[name](xs);
const ms = performance.now() - start;
const heap = process.memoryUsage().heapUsed / 1e6;
console.log(`${name} ${n}: ${ms.toFixed(1)} ms, heap after ${heap.toFixed(0)} MB, result ${typeof result}`);
