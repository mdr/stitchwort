// Runs the exports of bench/effect-runtime/shapes.sw from Node on its default
// stack (docs/proposals/effect-runtime-review.md), for each module given:
// the size doubles from 1,000 until the call throws, takes longer than 10 s,
// or reaches 1,024,000. Also checks that every module gives the first
// module's answers at sizes 0 to 300. Usage:
//
//   node bench/effect-runtime/shapes.mjs OUT/shapes.js OUT/shapes-loop.js ...
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { isDeepStrictEqual } from "node:util";

const files = process.argv.slice(2);
const modules = await Promise.all(files.map((f) => import(pathToFileURL(resolve(f)).href)));
const list = (n) => Array.from({ length: n }, (_, i) => BigInt(i));
const names = ["asked", "emitted", "askedChecked", "searched", "askedIn", "emittedIn", "searchedIn"];

let disagree = 0;
for (const name of names) {
  for (const n of [0, 1, 2, 7, 300]) {
    const want = modules[0][name](list(n));
    for (let i = 1; i < modules.length; i++) {
      if (!isDeepStrictEqual(want, modules[i][name](list(n)))) {
        disagree++;
        console.log(`DIFFERENT: ${files[i]} ${name} ${n}`);
      }
    }
  }
}
console.log(disagree === 0 ? "all modules agree" : `${disagree} disagreements`);

for (let i = 0; i < modules.length; i++) {
  console.log(`=== ${files[i]}`);
  for (const name of names) {
    const f = modules[i][name];
    f(list(1000));
    for (let n = 1000; n <= 1_024_000; n *= 2) {
      const xs = list(n);
      const start = performance.now();
      let outcome = "ok";
      try {
        f(xs);
      } catch (e) {
        outcome = `error: ${String(e.message ?? e).split("\n")[0].slice(0, 70)}`;
      }
      const ms = performance.now() - start;
      console.log(`${name}\t${n}\t${ms.toFixed(1)} ms\t${outcome}`);
      if (outcome !== "ok" || ms > 10000) break;
    }
  }
}
