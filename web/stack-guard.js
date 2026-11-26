// The stack guard the playground's WebAssembly runs with, chosen by engine
// (SW-4852, D3749). crates/web/build.rs sets the build's own guard, 320 KiB,
// which Chrome and Firefox have room for. WebKit's workers overflow sooner,
// so they get a smaller one, and their own check cache: the guard is part of
// the cache's keys, so the library checked at 320 KiB would not replay.
//
// Every place that starts the WebAssembly calls `applyStackGuard(wasm)` right
// after `init`, before it makes a session or server or loads a cache, and
// fetches `libraryCacheFile()`.

// Bytes. Measured with `f (f (… 0))` nested applications checked against a
// known type (SW-4849, 26 Nov 2026): Safari 27.2 overflows at 92 levels, about
// 297 KiB of stack; Chrome 158 at about 510 KiB and Firefox 160 at about
// 1.5 MiB. 192 KiB is about 1.5 times under Safari's figure, the margin
// Chrome's 320 KiB has under its own.
export const WEBKIT_GUARD = 192 * 1024;

// Whether the engine is WebKit's. Every browser on iOS is (Chrome's CriOS,
// Firefox's FxiOS), and Chromium-based browsers on other systems say
// `AppleWebKit` too, but also `Chrome/` (Edge and Opera included).
export function isWebKit(userAgent = globalThis.navigator?.userAgent ?? "") {
  return userAgent.includes("AppleWebKit") && !userAgent.includes("Chrome/");
}

// The guard to set, or null to keep the build's.
export function stackGuard(userAgent) {
  return isWebKit(userAgent) ? WEBKIT_GUARD : null;
}

// The check cache made for that guard (web/bundle-std-cache.mjs).
export function libraryCacheFile(userAgent) {
  return isWebKit(userAgent) ? "std.cache.webkit.gz" : "std.cache.gz";
}

// Sets the guard on the initialised WebAssembly module's bindings `wasm`.
export function applyStackGuard(wasm, userAgent) {
  const guard = stackGuard(userAgent);
  if (guard !== null && !wasm.set_stack_guard(guard)) {
    throw new Error("the stack guard was set after the first session");
  }
}
