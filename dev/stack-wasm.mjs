// One check of a namespace in the playground's WebAssembly, run by dev/stack-wasm
// (SW-4869); run under `node --stack-size=N` to give the engine that much stack.
//
//   node [--stack-size=N] dev/stack-wasm.mjs SITE cache CACHE_FILE
//   node [--stack-size=N] dev/stack-wasm.mjs SITE check CACHE_FILE PROJECT NAMESPACE
//
// SITE holds stitchwort_web.js, stitchwort_web_bg.wasm, std.bundle and
// projects/PROJECT/. `cache` writes the checked library to CACHE_FILE; `check`
// replays it (as the playground does) and checks the namespace the way the
// language server does, with navigation on, and prints one JSON line:
// {kind: ok | error | crash, reachedKiB, ms, ...}. For a crash (the engine's
// stack ran out), TRACE=FILE writes each WebAssembly frame on the stack at the
// overflow as `function index<TAB>name`, innermost first.
import fs from "node:fs";
import path from "node:path";

Error.stackTraceLimit = Infinity;
const [site, mode, cacheFile, project, ns] = process.argv.slice(2);
const W = await import(path.join(site, "stitchwort_web.js"));
W.initSync({ module: fs.readFileSync(path.join(site, "stitchwort_web_bg.wasm")) });
W.load_std(new Uint8Array(fs.readFileSync(path.join(site, "std.bundle"))));
try {
  W.stack_reached();
} catch {}
if (mode === "cache") {
  const bytes = W.build_library_cache();
  fs.writeFileSync(cacheFile, bytes);
  console.log(JSON.stringify({ kind: "cache", bytes: bytes.length, reachedKiB: Math.round(W.stack_reached()[0] / 1024) }));
  process.exit(0);
}
if (!W.load_library_cache(new Uint8Array(fs.readFileSync(cacheFile)))) throw new Error("cache refused");
const base = path.join(site, "projects", project);
const manifest = JSON.parse(fs.readFileSync(path.join(base, "manifest.json"), "utf8"));
const paths = [...manifest.files, ...manifest.data];
const texts = paths.map((p) => fs.readFileSync(path.join(base, p), "utf8"));
try {
  W.stack_reached();
} catch {}
const t = Date.now();
let out;
let err = null;
try {
  out = JSON.parse(W.check_project(project, paths, texts, ns));
} catch (e) {
  err = e;
}
const reachedKiB = Math.round(W.stack_reached()[0] / 1024);
const ms = Date.now() - t;
if (err) {
  const lines = String(err.stack).split("\n").filter((l) => l.includes("wasm"));
  console.log(JSON.stringify({ kind: "crash", err: String(err.message), reachedKiB, frames: lines.length, ms }));
  if (process.env.TRACE) {
    const name = (l) => l.replace(/^\s*at /, "").replace(/ \(wasm:.*$/, "").replace(/::h[0-9a-f]{16}$/, "");
    const index = (l) => (l.match(/wasm-function\[(\d+)\]/) || [0, -1])[1];
    fs.writeFileSync(process.env.TRACE, lines.map((l) => index(l) + "\t" + name(l)).join("\n"));
  }
} else {
  console.log(JSON.stringify({ kind: out.ok ? "ok" : "error", detail: out.ok ? "" : String(out.errors).slice(0, 300), reachedKiB, ms }));
}
