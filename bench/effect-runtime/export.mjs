// The exported functions of bench/effect-runtime/map.sw, called from Node on
// its default stack, as a library user or the playground would call them
// (docs/proposals/effect-runtime.md). Usage:
//
//   stitchwort build --js bench/effect-runtime/map.sw -o OUT
//   node bench/effect-runtime/export.mjs OUT/map.js [MAX_SECONDS]
//
// For each function, the size doubles from 1,000 until the call throws (a
// stack overflow shows as the module's resource error) or takes longer than
// MAX_SECONDS (default 20). Each size is timed once after one warm-up call at
// 1,000 elements, so the times include the boundary's decoding and encoding.
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const file = resolve(process.argv[2] ?? "map.js");
const maxSeconds = Number(process.argv[3] ?? 20);
const m = await import(pathToFileURL(file).href);

const functions = {
  plain: (xs) => m.plain(xs),
  pureMapIn: (xs) => m.pureMapIn(xs),
  checked: (xs) => m.checked(xs),
  failsLast: (xs) => m.failsLast(BigInt(xs.length), xs),
  counted: (xs) => m.counted(xs),
  countedChecked: (xs) => m.countedChecked(BigInt(xs.length), xs),
};

const list = (n) => Array.from({ length: n }, (_, i) => BigInt(i));

for (const [name, f] of Object.entries(functions)) {
  f(list(1000));
  for (let n = 1000; n <= 1_048_576_000; n *= 2) {
    const xs = list(n);
    const start = performance.now();
    let outcome = "ok";
    try {
      f(xs);
    } catch (e) {
      outcome = `error: ${String(e.message ?? e).split("\n")[0].slice(0, 80)}`;
    }
    const ms = performance.now() - start;
    console.log(`${name}\t${n}\t${ms.toFixed(1)} ms\t${outcome}`);
    if (outcome !== "ok" || ms > maxSeconds * 1000 || n >= 1_000_000) break;
  }
}
