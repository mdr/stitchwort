// Float on the WebAssembly kernel (docs/proposals/float.md §3.4, §7.4), from
// the playground's bundle, in Node:
//
//   node web/tests/float-wasm.mjs fingerprint
//       the fingerprint of the sources the bundle was built from, which the
//       tests compare with their own to tell a stale bundle
//   node web/tests/float-wasm.mjs gate
//       the kernel gate (§3.4): every check, with natives on and with the
//       float natives off; exits 1 if one fails
//   node web/tests/float-wasm.mjs evaluate FILE EXPR
//       loads the program in FILE and prints the value of EXPR, as the
//       playground's Evaluate tab does (the WebAssembly kernel's path of
//       crates/cli/tests/float_paths.rs)
//
// Needs web/pkg (web/build.sh, or its cargo and wasm-bindgen steps); PKG=dir
// points elsewhere. Run inside `nix develop`.
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const pkg = process.env.PKG ?? join(here, "..", "pkg");
const web = await import(join(pkg, "stitchwort_web.js"));
web.initSync({ module: readFileSync(join(pkg, "stitchwort_web_bg.wasm")) });

const [command, file, expr] = process.argv.slice(2);
if (command === "fingerprint") {
  // The sources the bundle was built from (absent in a bundle older than this).
  console.log(web.source_fingerprint ? web.source_fingerprint() : "none");
} else if (command === "gate") {
  const report = web.float_gate();
  process.stdout.write(report);
  const lines = report.split("\n");
  const failed = lines.filter((l) => l.startsWith("FAIL")).length;
  const passed = lines.filter((l) => l.startsWith("PASS")).length;
  console.log(`${passed} passed, ${failed} failed`);
  // `exitCode`, not `exit()`: into a pipe, `exit()` can cut off the report.
  process.exitCode = failed === 0 && passed > 0 ? 0 : 1;
} else if (command === "evaluate") {
  const answer = JSON.parse(web.evaluate(readFileSync(file, "utf8"), "", expr));
  if (!answer.ok) {
    console.error(JSON.stringify(answer));
    process.exit(1);
  }
  console.log(answer.value);
} else {
  console.error("usage: float-wasm.mjs gate | evaluate FILE EXPR");
  process.exit(2);
}
