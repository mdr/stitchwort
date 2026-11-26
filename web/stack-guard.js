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

// ---- When the engine's own stack runs out (SW-4862, D3750) ------------------
//
// The guard above counts the WebAssembly's stack, but the engine has a native
// stack of its own, with less room in some tiers and engines than the guard
// assumes (Chrome overflowed checking Aoc.Year2020.Day05.Proofs at 268 KiB of
// wasm stack, under a 320 KiB guard). The error the engine throws then is a
// RangeError ("Maximum call stack size exceeded" in Chrome and Safari), or in
// Firefox's older releases an InternalError ("too much recursion"). The
// instance can't be used afterwards (its Rust state was left borrowed: later
// calls fail with "recursive use of an object"), so each worker catches
// this, reports a resource error instead of a crash, and is replaced by a
// fresh one.

// Whether `e`, thrown from a call into the WebAssembly, is the engine's stack
// running out. Matched by name and by the words of each engine's message, since
// none of these is standardised.
export function isStackOverflow(e) {
  if (!e || (e.name !== "RangeError" && e.name !== "InternalError")) return false;
  return /call stack|too much recursion|stack (size|overflow)|recursion/i.test(String(e.message ?? ""));
}

// The message shown where a check overflowed, worded as the checker's own
// `E-RESOURCE` errors are (crates/core/src/budget.rs).
export const OVERFLOW_MESSAGE =
  "ran out of resources: the browser's stack ran out while checking this (E-RESOURCE)";
