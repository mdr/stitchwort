// Writes the standard library's check cache for the playground's language
// server (docs/proposals/playground-editor.md §5.2.4):
//   node web/bundle-std-cache.mjs PKG_DIR
// checks the library with PKG_DIR's WebAssembly and std.bundle, as the
// server's projects load it in the worker (`build_library_cache`), and
// writes PKG_DIR/std.cache.gz. The page's workers load it, so a project's
// library files are replayed rather than checked on every visit. It is
// compressed here rather than left to the host: GitHub Pages compresses only
// the file types it knows, and has no `.cache`. The workers decompress it
// with DecompressionStream. The cache
// is only read by the WebAssembly that made it: its keys cover the
// compiler build, the limits and the library's text. Run by web/build.sh
// after the WebAssembly and std.bundle are written.
import { readFileSync, writeFileSync } from "node:fs";
import { gzipSync } from "node:zlib";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

const pkg = resolve(process.argv[2] ?? "web/pkg");
const web = await import(pathToFileURL(join(pkg, "stitchwort_web.js")).href);
web.initSync({ module: readFileSync(join(pkg, "stitchwort_web_bg.wasm")) });
web.load_std(new Uint8Array(readFileSync(join(pkg, "std.bundle"))));
const t0 = performance.now();
const bytes = web.build_library_cache();
const packed = gzipSync(bytes, { level: 9 });
writeFileSync(join(pkg, "std.cache.gz"), packed);
const seconds = ((performance.now() - t0) / 1000).toFixed(1);
console.log(`std.cache.gz: ${packed.length} bytes (${bytes.length} unpacked) in ${seconds} s; ${web.describe_library_cache(bytes)}`);
