# The JSPI chain of stacks: a way to lift the playground's depth limit, not yet

*SW-4893, Sonnet paper lane, 26 Nov 2026. Research note: nothing built or run. It
records Matt's decision D3753 (26 Nov 2026): write the idea up and conclude "not yet". It
draws only on two reviews, cited by name; the figures are theirs.*

Sources: [SW-4863](../reviews/SW-4863-playground-stack-end-state.md) (the problem, the
options, the search for prior art) and
[SW-4870](../reviews/SW-4870-jspi-stack-chain.md) (the prototype, its measurements and
risks). Labels as in the rest of `docs/research/`: **[cited]** from those reviews or the
pages they link, **[inferred]** reasoning from them.

**Result in two lines.** The chain works in Chrome and Firefox and costs about 3%, but
adopting it means touching every recursion in the code base, relies on engine behaviour
nobody documents, and is untried in Safari. The proofs that motivated it now fit without it.

## 1. The problem

The playground runs the checker as WebAssembly in the browser. The browser gives that code
a fixed call stack (its size differs by browser), so the program can only nest so deeply
before the engine overflows. Natively the limit is a number we choose; in the browser it is
the engine's. To stay clear of a crash, the checker counts the stack it has used and stops
with a clean `E-RESOURCE` at a guard (320 KiB of WebAssembly stack today) **[cited,
SW-4863]**. Nested applications `f (f (f … 0))` reach only 99 levels in Chrome before the
guard stops them, and an engine stack that differs by browser and by tier (SW-4857,
SW-4849) means each browser needs its own guard and its own library cache **[cited,
SW-4870]**.

## 2. The idea

JSPI (JavaScript Promise Integration) lets WebAssembly suspend while JavaScript runs and
resume afterwards. Each call into a function wrapped in `WebAssembly.promising` runs on a
stack of its own. The trick is to use that for depth rather than for waiting: deep in a
recursion, call an import marked `WebAssembly.Suspending` whose JavaScript calls back into
WebAssembly through `promising`. The rest of the recursion then runs on a fresh engine
stack, and the caller resumes when it returns. Natively this is Rust's
`stacker::maybe_grow`; here it is built from JSPI **[cited, SW-4863 §2.6]**.

A check can't move frames already on the stack, so the switch has to wrap the rest of a
recursion in a closure (`stack::grow(|| body)`) at a call site in every recursion. Do it
once the code has used 64 KiB of stack, and the engine's stack stops being the limit: the
guard becomes a policy number again **[cited, SW-4870]**.

Prior art: none found using JSPI for depth. Pyodide and WordPress Playground use JSPI only
to wait on asynchronous work **[cited, SW-4863]**.

## 3. What the prototype showed

SW-4870 built it on `lane/SW-4870` (commit 483e0c48f) and measured headless Chrome 158 and
Firefox 160 **[cited, SW-4870]**:

| Nested applications | Chrome 158 | Firefox 160 |
|---|---|---|
| Today: 8 MiB stack, 320 KiB guard | 99 levels, then `E-RESOURCE` | same |
| Raised guard (7 MiB), no chain | 200 ok, 300 crashes the engine | 400 ok, 800 crashes |
| Same, with the chain | 2,000 ok; 2,500 `E-RESOURCE` from the guard | 2,000 ok; 2,500 `E-RESOURCE` |
| 64 MiB stack, 60 MiB guard, chain | 8,000 ok (21 s); 14,000 ok (63 s) | 8,000 ok (38 s); 11,000 `E-RESOURCE` (the cap on live stacks) |

- **Cost:** about 3% on ordinary checks in Chrome (about 1.5 µs a switch), about 1% in
  Firefox (noisy), and no measurable change on an AoC project's first check.
- **Recovery still works:** an engine overflow on an inner stack rejects each `promising`
  call in turn and reaches the SW-4862 recovery as the same `RangeError`; both browser
  tests pass. Cancellation and request order are unchanged.
- **Safari was not measured.** It can't be run headless here.

## 4. Why not yet

1. **It is a sweep, not a patch.** The prototype wrapped 9 sites. The code base has about
   70 `Budget::nesting` sites, 4 parser `deeper` sites, the lowering's guards, and
   unguarded recursions (`Drop`, the printers). One recursion left unwrapped keeps the
   engine's limit, and with the guard raised that recursion crashes instead of reporting
   `E-RESOURCE` (the SW-4862 restart still catches it). New passes would have to remember
   it too **[cited, SW-4870]**.
2. **It leans on undocumented behaviour.** How many stacks may be alive at once is not
   specified: Chrome failed at 779, Firefox at 271 in the parser but not at 400 in the
   elaborator. The prototype caps itself at 200. V8 calls its JSPI stacks fixed-size today
   **[cited, SW-4870, SW-4863]**.
3. **Safari is unmeasured.** Safari 27 is said to ship JSPI; its stacks and limits are
   unknown, and WebKit already has the smallest engine stack **[cited, SW-4870]**.
4. **The need has gone.** SW-4863 found the failing proofs overflowed on printing and on
   chains made by computing, not on nesting people write. After SW-4863, SW-4865 and
   SW-4868 every measured AoC proof fits the guard (Day05 73, Day22 96, Day11 126 KiB), and
   the deepest real nesting in the repo is 53 levels **[cited: SW-4863 §1 and its table for Day05 and Day22;
   Day11 from SW-4865, docs/worklog/2026-11-26.md]**.
5. **Depth has another ceiling.** Past about 8,000 levels the elaborator's roughly
   quadratic time is the limit, not the stack (SW-4885, being fixed by SW-4891 and
   SW-4892) **[cited: SW-4870; SW-4885, docs/proposals/effects-prepass-cost.md]**.
6. **Loose ends:** a browser test about hover text failed three times out of three on the
   chain's build and not on `main`'s (a race with the editor's redraw that the chain moved;
   cause not found); and a raised guard needs a third library cache, about 5 MB and a
   minute of build **[cited, SW-4870]**.

## 5. What would change the answer

- A real program needs more depth than the guard allows.
- Per-browser guards and caches become the larger cost.
- Safari is confirmed working (Matt's four probe steps are in SW-4870).
- And the design to do it right is settled: a fused `budget.nested(PASS, || …)` that is
  the guard and the switch in one call, swept over every guard site with a lint that a
  recursive function uses it; a browser test per recursion shape (nesting.rs's, run past
  today's guard, ending in `E-RESOURCE`); the chain in the other workers; and a third
  library cache for the raised guard **[cited, SW-4870]**.

## 6. Where the prototype is

- Branch `lane/SW-4870` (tip `581dfa400` as of 26 Nov 2026; the review names `483e0c48f`
  as the measured commit): the stack switch in `crates/syntax/src/stack.rs`,
  `web/stack-chain.js`, the worker's `runLater` entry, and the `STITCHWORT_WASM_STACK`
  build option.
- The Safari probe: `/Users/Shared/SW-4870-site` (64 MiB stack, guard 60 MiB, cap of 200
  stacks; run `nix run nixpkgs#nodejs -- server.mjs` there and open
  `probe.html?plan=…` with the plans in SW-4870's "For Matt to try in Safari"). It is
  outside the repo and may go.
