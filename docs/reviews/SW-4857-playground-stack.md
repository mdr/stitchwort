# SW-4857: the playground's stack guard against real proofs

> **Note (26 Nov 2026):** [SW-4863](SW-4863-playground-stack-end-state.md) found that the Day05 and
> Day22 rows below measured the hover-text printer (navigation), not checking, and that this note's
> 192 KiB guard proposal for Chrome is not the path taken.

Measured 26 Nov 2026 (Sonnet lane), headless Chrome 158 and Firefox 160 on macOS. Safari could not be run
headless here, so WebKit has only the nested-applications figure (SW-4849).

## Finding that changes the picture

The language server's project check (`LiveProject::step`, which calls `Session::check_project_namespace`)
and `check_project` ran without a `Budget::operation`, so the 320 KiB guard never applied to them: the
crash at 268 KiB in the browser test is the engine overflowing with no guard in the way (SW-4856 fixes
this). The "unguarded" figures below are therefore what the language server really does today. The
guard counts from the start of the operation, so after SW-4856 the guard will see about what is listed
under "wasm KiB the check needs" here; rerun the rows marked * once it is in.

## Method

A wasm build with the stack probe (`STITCHWORT_STACK_PROBE=1`) and the guard lifted
(`STITCHWORT_GUARD=6000000`), run in a fresh worker per workload, as the language server runs: open one
file of the namespace, tick `LanguageServer` until the namespace is checked (the library check cache
built first, as the playground replays it). `phases().deepestKiB` gives the deepest wasm stack of each
namespace's step; on a RangeError, `stack_reached()` (kept in linear memory) gives the wasm stack at the
overflow. The harness (a page, two workers and a server) is in the lane's scratch folder, not the repo.
Chrome ran twice: its default tiering and `--js-flags=--liftoff-only` (baseline compiler only, larger
native frames). `--js-flags=--stack-size=` has no effect on Chrome's workers, so a workload that
fits cannot be forced to overflow: its row is a lower bound.

## Table: wasm KiB when the engine overflows (or the most a check needed)

| Workload | wasm KiB the check needs | Chrome default | Chrome liftoff-only | Firefox |
|---|---|---|---|---|
| Nested applications (SW-4849) | n/a | overflow at 510 | not measured | overflow at 1536 (Safari: 297) |
| 2020 Day05.Proofs | 314 | fits (>= 314) | overflow at 298 (0.58x nested) | fits |
| 2020 Day05.Proofs, the real page (SW-4854) | about 268+ | overflow at 268 (0.53x) | | |
| 2024 Day22.Proofs | 604 (Firefox ran it) | overflow at 331 (0.65x) | overflow at 301 (0.59x) | fits (604, >= 0.39x) |
| 2021 Day11.Proofs | 317 | fits | fits | fits |
| 2024 Day16.Proofs | 156 | fits | fits | fits |
| 2024 Day13.Proofs | 131 | fits | fits | fits |
| 2021 Day06.Proofs | 120 | fits | fits | fits |

Native peaks do not predict wasm ones: Day05 244 KiB native, 314 wasm; Day13 245 native (older figure,
SW-3174), 131 wasm; Day22 155 native (older), 604 wasm. So a guard cannot be chosen from native peaks;
the AoC proofs not measured here are unknown. Day05's native frame table (SW-4854) shows `check_tree`
at 2,800 B a level times 22 levels, 22% of the peak; Day22's wasm figure is mostly a different
recursion that native reports small, which is the point: bytes of wasm stack per engine byte depends on
the function.

Same-engine variation is itself large: Day05 overflowed Chrome at 268 (real page), 298 (liftoff-only)
and did not overflow at 314 (default tiering in my harness). The engine's room is a function of which
tier compiled the hot functions, so no single figure is exact; allow about 15% either way.

## Proposal

Chrome's worst case so far is 268 KiB (the real page); for a 1.25x margin the guard is 268 / 1.25 = 214,
say **192 KiB, as WebKit already has** (Safari's 297 gives 238; Chrome's 268 gives 214). Firefox's worst
case, 1.5 MiB (nested applications), would allow about 1.2 MiB, but there is no reason to raise it above
the 320 KiB it has: no measured proof gets near.

What 192 KiB would refuse in Chrome and WebKit, by the wasm figures above: Day05.Proofs (314),
2021 Day11.Proofs (317), 2024 Day22.Proofs (604), each with E-RESOURCE instead of a crash. Day13, Day16
and 2021 Day06 pass. This is an estimate from six namespaces; whether other AoC proofs exceed 192 KiB
in wasm is unknown, and a whole-AoC browser run (the verifier's or Overmind's job) would list them.
Firefox at 320 KiB refuses Day22.Proofs (604) too, and passes the rest of the six.

Order of work: SW-4856 first (without it the guard does nothing for the language server), then rerun
the Day05 row in the real page and the table's guarded rows, then set the Chrome guard.

## Alternatives

- **Make the proofs fit the engine.** Day05, Day11 and Day22 at 314-604 KiB need shrinking by half to
  fit 192 KiB. `check_tree` (2.8 KiB a frame native) is 22% of Day05; cutting its frame by a third gains
  about 7%. Not enough alone; Day22's 604 is a different recursion that has not been profiled in wasm.
- **Count frames, not bytes.** Nested-application depth in Chrome (160 levels at 510 KiB) and Day05's 22
  `check_tree` levels at 14 KiB a level show bytes per level varies 5x between recursions, so a frame
  count is no more faithful across recursions than bytes, and each recursion would need its own limit.
  Bytes of wasm stack at least are what the probe reads. No evidence found for it beating bytes.
- **Run the engine's own check.** The engine knows its stack exactly: catch the RangeError in the
  worker (the playground already restarts the worker) and report E-RESOURCE for that namespace. The
  language server's crash path (`crashed`, restart) would become a diagnostic, not a restart loop.
  This is faithful whatever the tier and recursion, and removes the guess; the cost is the restart and
  re-check. Cheap to prototype, not done here.
- **Make the wasm frames smaller.** Chrome's overflow figures move 10-15% with tier; a build with
  `-C opt-level=3` or `-Zinline-threshold` changes would shift them too. Not tried.
