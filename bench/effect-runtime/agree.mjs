// Checks that two builds of bench/effect-runtime/map.sw give the same results
// (docs/proposals/effect-runtime.md): the generated module, and the module
// patched by prototype.mjs. Usage:
//
//   node bench/effect-runtime/agree.mjs OUT/map.js OUT/map-loop.js
//
// Small inputs only, so the generated module doesn't run out of stack.
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { isDeepStrictEqual } from "node:util";

const load = (file) => import(pathToFileURL(resolve(file)).href);
const [a, b] = await Promise.all(process.argv.slice(2, 4).map(load));
const list = (n) => Array.from({ length: n }, (_, i) => BigInt(i));

const cases = [];
for (const n of [0, 1, 2, 5, 100, 500]) {
  const xs = list(n);
  cases.push([`plain ${n}`, (m) => m.plain(xs)]);
  cases.push([`pureMapIn ${n}`, (m) => m.pureMapIn(xs)]);
  cases.push([`counted ${n}`, (m) => m.counted(xs)]);
  cases.push([`checked ${n}`, (m) => m.checked(xs)]);
  cases.push([`failsLast ${n}`, (m) => m.failsLast(BigInt(n), xs)]);
  for (const limit of [0n, 1n, BigInt(n), BigInt(n) + 1n]) {
    cases.push([`countedChecked ${limit} ${n}`, (m) => m.countedChecked(limit, xs)]);
  }
}
for (const n of [0, 1, 2, 3, 8, 12]) {
  cases.push([`choices ${n}`, (m) => m.choices(list(n))]);
}

let failed = 0;
for (const [name, run] of cases) {
  const left = run(a);
  const right = run(b);
  if (!isDeepStrictEqual(left, right)) {
    failed++;
    console.log(`DIFFERENT: ${name}`);
  }
}
console.log(`${cases.length - failed} of ${cases.length} cases agree`);
process.exit(failed === 0 ? 0 : 1);
