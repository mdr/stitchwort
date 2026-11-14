# SW-3113: why the playground's re-check takes 27-36 s

Measured 13 Nov 2026 (Sonnet lane). Browser: headless Chrome 157, test "in a project, after a jump into another file and the whole project's check, an error in the day is underlined", three runs.

## Browser, per phase (re-check after an edit of Year2025/Day02; wall 27.3-29.0 s)

| Phase | Time |
|---|---|
| `server.tick()` in wasm (289-291 ticks) | 25.8-26.8 s |
| gap between ticks (`setTimeout(0)`, about 5 ms each) | 1.4-1.6 s |
| sending/serialising output, page message handling | under 5 ms |

So scheduling, message passing and the page are not the cause. Inside the ticks (server-side `live::phases`): 280 namespaces replayed from the store took 1.9 s in all; `LiveProject::answers` (4 calls) 2.1 s; **6 namespaces re-elaborated, "elaborated, not cached", took 20 s** (Year2024 Day13.Proofs 9.1 s, Day22.Proofs 6.3 s, Day11.Proofs 2.1 s, Day16.Proofs 1.9 s, Day02 0.45 s, Day06.Proofs 0.16 s).

## Cause

The playground's session has a stack budget of 512 KiB (`STITCHWORT_GUARD` 256 KiB + 256 KiB, `crates/web/build.rs`, chosen to keep V8's own call stack from overflowing, SW-1430). Namespaces whose proofs recurse more deeply than that fail with "ran out of resources: it recursed more deeply than allowed" (an Error), so `elaborate_namespace_cached` never writes an entry for them (`ok` is false) and each re-check elaborates them again from scratch.

Reproduced natively: `Options::new(512 KiB)` in the LSP profile test (`crates/lsp/tests/it/profile.rs`, `SW3113_STACK=524288`) gives 121 uncached namespaces and a 27.8-29.0 s re-check (against 5 s with 256 MiB), the browser's number. First reasons seen: "recursed more deeply than allowed" (Day23/22/04.Proofs of 2024, Day08.Proofs 2021, ...), "nested too deeply for the type checker" (2020 Day07.Proofs), and dependants "has an error, so ... can't be checked".
(Which namespaces overflow differs between wasm and the native emulation because frame sizes differ; in the browser it was 6 namespaces, 20 of the 23 s. The mechanism in the browser itself was not confirmed by a diagnostic dump: the reason strings were added after the last browser run.)

It also means the playground reports false "ran out of resources" errors on those proofs.

## Options

1. A bigger guard (design: V8's call-stack limit, web/stress.html, SW-1430).
2. Make the deep recursions iterative or cheaper in stack per level (kernel/elaborator work).
3. Cache an entry for a namespace that hit a stack error? No: the result depends on the stack, so it would be wrong.
4. Don't re-elaborate what the edit can't affect: already replayed; the cost is the uncacheable ones.

## Instrumentation kept

`window.editor.stats.phases` (tick, send, gap, page times since `editor.resetPhases()`), `stats.phaseLog` (the server's per-idle `live::phases`: totals, 12 slowest steps with how each was checked), printed by the browser test above.
