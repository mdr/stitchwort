// Float on the WebAssembly kernel (docs/proposals/float.md §3.4, §7.4): runs
// the kernel gate and prints the kernel's float results, from the
// playground's bundle, in Node.
//
//   node web/tests/float-wasm.mjs gate          the gate; exits 1 if a check fails
//   node web/tests/float-wasm.mjs eval FILE     for each line `name expr` of FILE,
//                                               prints `name <hex bits>` of `expr.bits`
//
// Needs web/pkg (web/build.sh, or the wasm-bindgen step of it); PKG=dir
// points elsewhere. Run inside `nix develop`.
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const pkg = process.env.PKG ?? join(here, "..", "pkg");
const web = await import(join(pkg, "stitchwort_web.js"));
web.initSync({ module: readFileSync(join(pkg, "stitchwort_web_bg.wasm")) });

const [command, file] = process.argv.slice(2);
if (command === "gate") {
  const report = web.float_gate();
  process.stdout.write(report);
  const failed = report.split("\n").filter((l) => l.startsWith("FAIL"));
  const passed = report.split("\n").filter((l) => l.startsWith("PASS"));
  console.log(`${passed.length} passed, ${failed.length} failed`);
  process.exit(failed.length === 0 && passed.length > 0 ? 0 : 1);
} else if (command === "eval") {
  for (const line of readFileSync(file, "utf8").split("\n")) {
    if (!line.trim()) continue;
    const space = line.indexOf(" ");
    const [name, expr] = [line.slice(0, space), line.slice(space + 1)];
    const answer = JSON.parse(web.evaluate("import Std (Float)\n", "", `(${expr}).bits`));
    if (!answer.ok) {
      console.log(`${name} ERROR ${JSON.stringify(answer)}`);
      continue;
    }
    console.log(`${name} ${BigInt(answer.value).toString(16).padStart(16, "0")}`);
  }
} else {
  console.error("usage: float-wasm.mjs gate | eval FILE");
  process.exit(2);
}
