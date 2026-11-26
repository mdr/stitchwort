# SW-4870: the JSPI chain of stacks, prototyped

Measured 26 Nov 2026 (Opus lane), on `lane/SW-4870` (483e0c48f, from `main` at 41bc5a7bc): headless
Chrome 158 and Firefox 160 on macOS, at a load average of 15 to 35 (other lanes building). Safari can't be
run here: nothing below is measured in WebKit. Follows [SW-4863](SW-4863-playground-stack-end-state.md)
§2.6 and option c2 (D3752: "Prototype it to see what you think").

## Verdict

**Worth adopting as the browser's end state for nesting, but only as a sweep that covers every recursive
pass, and only after Safari has been tried by hand.** Not worth it as the handful of wrapped sites this
prototype has.

- **It works, and it is cheap.** With the chain on, the engine's stack stops being the limit in Chrome and
  Firefox, for every pass that goes through the switch: nested applications went from 200 levels (Chrome)
  and 400 (Firefox) before the engine overflowed to whatever the guard on the WebAssembly's own stack
  allows, and past it the check stops with a clean `E-RESOURCE`. The cost on ordinary checks is about 3%
  in a microbenchmark and nothing measurable on an AoC project's check.
- **It is not "one call in `Budget::nesting`'s slow path".** A check can't move the frames already on the
  engine's stack; only a call can run on a new one. So the switch wraps the *rest* of a recursion in a
  closure (`stack::grow(|| body)`, as `stacker::maybe_grow` does), at a call site in every recursion.
  One recursion without one keeps today's engine limit (about 200 levels in Chrome), and with the guard
  raised to get the benefit, that recursion crashes instead of reporting `E-RESOURCE` (the SW-4862
  restart still catches it). I wrapped 9 sites, the ones nested applications go through, found one at a
  time from the overflow traces; the code base has 69 `Budget::nesting` sites, 4 parser `deeper` sites,
  the lowering's guards and the unguarded recursions (`Drop`, printers). Adopting it means making the
  guard and the switch one call (`budget.nested(PASS, || …)`) at every site, and a test that every
  recursive pass's shape goes deep in a browser.
- **It relies on behaviour the engines didn't design for**, and one engine limit that isn't documented:
  how many stacks may be alive at once (Chrome about 780, Firefox between 271 and over 400 depending on
  the pass). The prototype keeps at most 200 alive, and past that every guard reports the stack used up,
  so hitting the limit is a clean `E-RESOURCE` in both browsers (measured). If an engine lowers its
  limit, the SW-4862 overflow recovery is the backstop, as it is today.

What it buys the user: the playground's depth limit becomes a number we choose, as natively, instead of
an engine's stack that differs by browser and by tier (SW-4857, SW-4849, SW-4863). Programs that check
with `stitchwort check` would check in the browser, given the same guard. Whether any real program needs
that once SW-4863's steps 1 to 5 are in is open: SW-4863 found that the six failing namespaces fail on
the printer and on chains made by computing, not on nesting people write (53 levels at most in the
repo). So: sequence it after those steps, and adopt it when it is the remaining gap, or when the
per-browser guards and caches become the larger cost.

## What was built

- `stitchwort_syntax::stack::grow(f)` (crates/syntax/src/stack.rs): natively, and in the browser unless
  the page turned the chain on and the call came through `promising`, it is `f()` (`#[inline(always)]`;
  the code is under `cfg(target_family = "wasm")`). With the chain on, it counts the guarded levels and
  switches once 64 KiB of WebAssembly stack, or 64 guarded levels, have been used since the last switch.
  The levels rule is for passes whose frames hardly touch linear memory (the parser); in the checks
  measured, the bytes rule made nearly all the switches.
- The switch: the Rust import `stitchwort_stack_grow` (module `../stack-chain.js`) is a
  `WebAssembly.Suspending` whose JavaScript calls the export `stitchwort_stack_resume` through
  `WebAssembly.promising`, with the address of the job (`&mut dyn FnMut()`). wasm-bindgen passes a raw
  `#[link(wasm_import_module)]` import through as `import * as … from "../stack-chain.js"`, so the
  WebAssembly imports the `Suspending` object directly, with no glue frame between (which JSPI refuses).
  The stack in linear memory stays one contiguous stack, so the guard measures it as before.
- The entry: wasm-bindgen's glue can't call an export through `promising` (it needs the answer
  synchronously), so the worker's checking calls are three: a glue method stores the job
  (`receive_later`, `tick_later`, `check_later`), `runLater` in web/stack-chain.js runs
  `stitchwort_run_pending` through `promising` (or directly, without JSPI), and `take_answer` reads the
  answer. web/lsp-worker.js's `receive` and `tick` go this way; the other workers (playground, search,
  stress) call as before, and the chain is off in them.
- At most 200 stacks alive: past that, `stack::position()` reads as 0 until a switch returns, so every
  guard (the budget's and the parser's) reports the stack used up.
- `STITCHWORT_WASM_STACK` (crates/web/build.rs) sets the linear stack, for the experiments below.
- web/stack-chain.js is shipped beside web/stack-guard.js (flake.nix, write-version.sh, the Taskfile's
  sources).

Wrapped: the parser's `expr`, lowering's `expr`, the elaborator's `with_span` (`check`, `infer`,
`infer_unrun`), the kernel's `check` and `infer`, `Term::map_vars_with` and `Term::rewrite_up`, the
termination walker's `walk`, and `may_perform_at`. The shipped guard is unchanged (320 KiB), so the
default build behaves as today apart from the switches.

## Measurements

All measured unless marked. "Nested" is `def f (n : Nat) : Nat := n` and `def y : Nat := f (f (… 0))`,
checked by the free `check` in a fresh worker per try, with the library replayed from a cache built for
the same guard (scripts and logs in the lane's scratch folder, `probe/`).

**Depth, nested applications.**

| Build | Chrome 158 | Firefox 160 |
|---|---|---|
| Shipped today: 8 MiB stack, 320 KiB guard, no chain | 99 levels, then E-RESOURCE (SW-4849) | same |
| 8 MiB stack, 7 MiB guard, no chain | 200 ok; 300 the engine overflows (crash) | 400 ok; 800 crash |
| 8 MiB stack, 7 MiB guard, chain | **2,000 ok (1.9 s); 2,500 E-RESOURCE** (from the guard) | **2,000 ok (2.3 s); 2,500 E-RESOURCE** |
| 64 MiB stack, 60 MiB guard, chain | 8,000 ok (21 s); 14,000 ok (63 s, 700 stacks); 24,000 over 120 s | 8,000 ok (38 s, 400 stacks); 11,000 E-RESOURCE (200 stacks, the cap) |

So the chain takes nesting from the engine's limit to the guard's, about 10 times the shipped depth
with a 7 MiB guard. Past about 8,000 levels the elaborator's own time (roughly quadratic here) is the
limit, not the stack. 64 MiB of linear stack is reserved memory the page would then always have.

**Stacks alive at once** (forced with small switch intervals, before the cap of 200 was added): Chrome
751 worked and 779 failed (`RangeError: Maximum call stack size exceeded`); Firefox failed at 271 in the
parser (`InternalError: too much recursion`) but allowed 400 in the elaborator, so its limit isn't a
plain count. Both failures are what `isStackOverflow` matches, so the SW-4862 recovery would report them.
With the cap, the same runs ended in `E-RESOURCE: the program is nested too deeply to parse`, in both.

**Time on ordinary checks.**

- Three accept examples (quot-protomap, omega-certificates, nested-data-induction; 747 lines), checked
  in one instance with the chain on and off alternately, 64 KiB interval, 27,139 switches a round:
  Chrome median 1,445 ms on against 1,406 off (+3%, 7 rounds after a warm-up); Firefox 1,626 against
  1,609 over the last 4 rounds, its earlier rounds dominated by its tiering (+1%, noisy). About 1.5 µs a
  switch in Chrome. A 16 KiB interval (56,000 switches) cost about 4% in Chrome.
- An AoC project's first check in the language server (the browser test "after the stack runs out in a
  project …", 2025 day 2's project): 109.9 s on `main`'s build, 109.6 s on the chain's. One run each,
  under load, so equal within noise.
- Native: `nested_applications_stack_per_level` measures 7.75 KiB a level (7.8 recorded by SW-4849),
  so the wrappers compile away.

## What breaks, and what doesn't

- **Asynchrony doesn't leak into request handling.** Every promise in the chain settles in microtasks,
  so no message or timer runs while a check is suspended: a hover sent during a check waits for the
  tick to end, as it does today with a synchronous tick. `runLater` throws if a second check ever
  started during one; the whole browser suite never tripped it (see Tests). The worker's `tick` and
  `handle` became `async` functions; nothing else changed in its message order.
- **Cancellation** reads the shared edit counter from inside the check (`stitchwortEditsWaiting`), a
  plain import call, so it works unchanged on any stack of the chain.
- **The overflow recovery (SW-4862, SW-4871)** works through the chain: an engine overflow on an inner
  stack rejects each `promising` call in turn and reaches `runLater` as the same `RangeError`. Both
  browser tests pass.
- **Unsafe code**: the job crosses the import as an address, and `receive_later` and `tick_later` keep a
  raw pointer to the server between the glue's calls, outside wasm-bindgen's borrow flag. Sound only
  while nothing calls the server during a job, which the microtask argument above gives and `runLater`
  checks for its own calls, but not for the glue's other methods.
- **One browser test changed result**: "an error is underlined, its message shows on hover …" failed on
  the chain's build three times out of three (in the suite and twice alone) and passed on `main`'s twice.
  The hover request is never sent: the worker's trace shows no `textDocument/hover`, and the semantic
  tokens' answer lands after the test's mouse move on the chain's build and before it on `main`'s, so the
  redraw seems to swallow the hover. With 3 s between the underline and the mouse move it passes. So the
  test races the editor's redraw, and something in the chain's build moves that answer later; I didn't
  find what (each request's `runLater` takes 0 to 2 ms in the trace). To settle before adopting.
- **The guard's cache**: the guard is part of the check cache's keys, so a raised guard for JSPI
  browsers needs a third library cache (about 5 MB, a minute of build) beside `std.cache.gz` and
  `std.cache.webkit.gz`, chosen by `stack-guard.js` as today.

## Risks

1. **Coverage**: one pass left unwrapped is a crash at the raised guard. Needs the fused API and a
   test per recursion shape (nesting.rs's shapes, run in the browser), and new passes must use it.
2. **Engine behaviour**: nobody documents JSPI for depth (no prior art found, SW-4863). The live-stack
   limits are unspecified and differ (Firefox's depends on the pass). V8 calls its stacks fixed-size
   today; growable stacks would only help. A browser that removes or limits this degrades to the SW-4862
   restart, not to wrong answers.
3. **Safari**: unmeasured. Safari 27 is said to ship JSPI; its stacks and limits are unknown, and WebKit
   already has the smallest engine stack.
4. **Unsafe code at the boundary** (above), small and local.
5. **Memory**: each live stack is an engine stack (about 1 MB in Chrome, SW-4863); 200 is a
   few hundred MB of address space at worst (estimated, not measured).

## For Matt to try in Safari, by hand

The probe site is in `/Users/Shared/SW-4870-site` (the lane's 64 MiB-stack build, guard 60 MiB, with the
cap of 200 stacks). In that folder run `nix run nixpkgs#nodejs -- server.mjs` (it serves port 8765 and
prints one `REPORT` line for each try), then open in Safari
`http://127.0.0.1:8765/probe.html?plan=PLAN` with each PLAN below:

1. `[{"n":50,"chain":{"bytes":65536,"levels":64}}]`: does `hasJspi` say true, and does a small check
   pass with the chain on (`"chain":true`, and `counts` above 0)?
2. `[{"n":60},{"n":90},{"n":120}]`: without the chain, where Safari's engine overflows (`"kind":"crash"`;
   92 levels in SW-4849).
3. `[{"n":500,"chain":{"bytes":65536,"levels":64}},{"n":2000,"chain":{"bytes":65536,"levels":64}}]`:
   does the chain take Safari past that (`"kind":"ok"`)?
4. `[{"n":1000,"chain":{"bytes":4096,"levels":4}}]`: many small stacks: `"kind":"resource"` means the
   cap of 200 held; `"crash"` means Safari allows fewer than 200 stacks alive.

If step 1 says `"chain":false`, Safari has no JSPI in workers and falls back to today's guard.

## What adopting it would take (estimated)

1. A fused guard: `Budget::nested(pass, || body)` and the parser's and lowering's equivalents, swept
   over every guard site; a lint (SW-1966's) that a recursive function goes through it.
2. The chain in the other workers (playground's Check, Tests and Evaluate; the search worker).
3. A raised guard where JSPI is on, its library cache, and `stack-guard.js` choosing it; today's guards
   where it isn't.
4. Browser tests: each nesting.rs shape past today's guard, in the browser, ending in `E-RESOURCE`.

## Tests run

- Browser, on the chain's build (shipped guard): the whole suite once, 104 of 105 passed (the hover
  test above); "the engine's stack running out in the language server is reported as E-RESOURCE …" and
  "after the stack runs out in a project …" also alone, both passed.
- Native: `nesting::{nested_applications, nested_applications_stack_per_level,
  nested_applications_under_the_playground_guard, nested_functions_and_function_types,
  nested_parentheses, long_sums}` (driver, `elaboration`) and the syntax crate's tests matching
  `deep|nest|stack` (7), all passed.
- The probe runs above, from the lane's scratch folder (`probe/`, `variant.sh`, `names.sh`).
