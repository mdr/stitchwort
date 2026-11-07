# Open decisions, 7 November 2026

Every D question still waiting for you, on one page (SW-2085). It was put
together at 12:00 on 7 Nov from three sources, with nothing built or run:
the ticket bodies in `board/tickets.json`, the design notes and reviews
merged on 6-7 Nov, and `docs/proposals/README.md`.

**The counts.** 155 questions are open: 146 from D2556 on, D2273-D2277
(asked 3 Nov, raised again today by the SW-1163 review), and 4 older ones
still on backlog tickets. Of those, 3 are plain duplicates (D2635, D2690,
D2853), 4 pairs overlap and are best answered together (D2633 with D2940,
D2701 with D2743, D2556 with D2910, D2610 with D2830), and 3 were asked
twice under the same number (D2680, D2711, D2733). On top of that, 8 calls
the orchestrator took for you overnight are listed for ratifying. 29
numbers are answered, withdrawn or overtaken; they're listed at the end so
the filtering can be checked. Questions before D2554 were all answered or
deliberately deferred on 6 Nov (you deferred D2519, D2529 and D2533), so
they aren't repeated here.

**How to answer.** Most notes recommend "yes" to every question they ask.
"D2610-D2614 yes" settles a note. At the end is a list you can answer with
"accept these" in one go.

Contents: [The 10 that unblock the most](#the-10-that-unblock-the-most) ·
[By epic](#by-epic) · [Safe to accept in bulk](#safe-to-accept-as-recommended-in-bulk) ·
[Answered or no longer open](#answered-or-no-longer-open)

## The 10 that unblock the most

Each one can be answered with one word. "Blocks" counts the backlog
tickets that can't start until it's answered.

| # | Questions | Say | What it unblocks |
|---|---|---|---|
| 1 | **D2610-D2614**, bounded read-back's remaining plan: start `rewrite f` now, the last two limits that choose go, `omega`/`ring` compare atoms folded first, per-candidate limits allowed in searches, programs that relied on a limit are rewritten by the lane that removes it | yes | SW-1830, SW-1631, SW-1832, SW-1837 now, then the chain to SW-1839/SW-1840 (6a/6b). That is the Goals as written epic, and the top gap in the AoC friction synthesis (35+ days). |
| 2 | **D2760-D2763**, the merge gate for kernel and core-language lanes: lanes run the ~75 s corpus check themselves, D2507 is retired, a per-day step baseline later, "merge-ready" needs no further question | yes | SW-1958, SW-1962. After this, kernel lanes merge without waiting on a D question; record eta waited 4.5 h for one. |
| 3 | **D2620-D2623**, stuck values record what they wait on: fix stale stuck calls by design rather than site by site, the folded read-back re-runs them too, waiting checks not now, an 80 s bench run before and after | as recommended | SW-1865, SW-1866. SW-1842-SW-1844 are no longer needed, and SW-1846-SW-1848 close when stage 1 fixes them (7 tickets in all). |
| 4 | **D2630, D2631, D2634** (+ duplicate D2635), record eta: stage 2' is tests, examples and guide text, the record sweep runs now, SW-1755 closes | yes | SW-1643, SW-1645, SW-1755; SW-1859 folds into SW-1643. |
| 5 | **D2273-D2277, D2590-D2592**, in-place reuse after the fresh-eyes review: extend `code.rs` in stages, the report first and in the shipped binary, inlining when the data says so, the projection hoist only when a program needs it, no `Array.pop` change | as recommended | SW-1809, SW-1810, SW-1811, SW-1813, SW-1815, SW-1816 now; SW-1812, SW-1814 on data (8 tickets). |
| 6 | **D2770-D2773**, internal error kinds: a `kind` beside the public code, swallowed limits become a compiler bug, notes keep keying on the code, `CannotInfer` may split later | yes | SW-1972-SW-1978 (7 tickets). |
| 7 | **D2670** (= D2690), **D2691**, **D2780-D2785**, parse recovery: a lexical error costs only its declaration, a byte-order mark is skipped, Design B (keep the signature, a hole where the text breaks) | yes | SW-1873, SW-1982-SW-1986 (6 tickets). The editor's most common annoyance while typing. |
| 8 | **D2711, D2790, D2791**, what the backends trust: native code only for programs lowered in-process, shape checks on field reads (if ≤ 2%), every stale pin refuses to load | yes | SW-1989, SW-1990, SW-1991, SW-1992; closes SW-1586. Turns the last silent-fallback paths into errors. |
| 9 | **D2800-D2802, D2680**, what the check cache trusts: the three-part replay contract, key M1 on the core text, a `--verify-cache` flag in the full tier, dev and release builds keep sharing entries | yes | SW-1919, SW-1995, SW-1996; SW-1925 (running) asserts D2800's refusal count. |
| 10 | **D2577-D2580**, syntax ids for the dot-call caches: copies get a new id, ids only on dot calls, drop the guards they replace, stage 1 on Opus | yes | SW-1803, the last fix for the varying dot-cache results. |

Next in line: D2930-D2932 (postponement, SW-2064, SW-2065), D2701 with
D2743, D2744 and D2733 (the language server's remaining stages, SW-1979,
SW-1950), and D2595-D2601 (a faster `Map`, SW-1824-SW-1827).

## By epic

Each line is a number, the question, the recommendation, what can't start
without it, and where it was asked. A **dup** or **replaces** mark says
which question to answer instead. Paths are under `docs/`.

### Goals as written

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2610 | Start `rewrite f` (stage R) now, beside 0c and 1c, instead of after stages 4 and 5? Amends D2545. | yes | SW-1631 | proposals/bounded-readback-remaining.md |
| D2611 | The two limits that choose (instance search's `SCAN_LIMIT`, the unifier's) go; the reader answers exactly or fails with `E-RESOURCE`. | yes | SW-1832 (via SW-1830's counts) | bounded-readback-remaining.md |
| D2612 | `omega` and `ring` identify atoms folded first, then by conversion, not by the unfolded read-back. | yes | SW-1837 | bounded-readback-remaining.md |
| D2613 | "Limits fail" (D2543) covers questions with one answer, not a search's per-candidate limits, which may skip a candidate if they say so. | yes | SW-1832 | bounded-readback-remaining.md |
| D2614 | A program that relied on a limit choosing is rewritten by the lane that removes the limit; the lane stops if more than five need it. | yes | SW-1832 | bounded-readback-remaining.md |
| D2830 | Do stages 6a/6b (rewrite and match on the goal as written) before the remaining read-back output sites (1c)? Reorders the plan in D2610. | yes | SW-1839, SW-1840 ordering vs SW-1831 | research/aoc-friction-synthesis.md |
| D2957 | Close SW-556 (the 100k-node read-back cap), superseded by bounded read-back? | yes | nothing (tidy-up) | SW-556, proposals/README.md |

### Record eta

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2566 | Keep `p.field` as a call of the accessor (not `Proj`); measure at stage 3 and switch accessor bodies to `Proj` only if it costs. | yes | SW-1851's brief; SW-1766 waits in review | proposals/record-eta.md §6.4 |
| D2630 | Stage 2 is mostly built: make it a short lane of tests, examples, guide and `syntax.md` text, not a unifier change. | yes | SW-1643 | proposals/record-eta-remaining.md |
| D2631 | Split the sweep: the records part now, the pairs part after stage 3. Amends D2505's order. | yes | SW-1645 | record-eta-remaining.md |
| D2632 | Stage 3 gives eta by shape to every qualifying type (`Pair`, `Text`, `Char`, …), with a stop point if one makes checks much slower. | yes | SW-1851 | record-eta-remaining.md |
| D2633 | Stage 3 starts after 0c merges, without waiting for 6b, and may run whole AoC and the roguelike twice (eta on and off, 6 min cap each). Amended by D2940. | yes | SW-1851 | record-eta-remaining.md |
| D2634 | Close SW-1755 as done by SW-1667, once the snapshot is confirmed. | yes | SW-1755 | record-eta-remaining.md |
| D2635 | **dup of D2630.** Record eta docs now, not after the sweep. | yes | SW-1859 | SW-1850 (reviews/SW-1850-guide-accuracy.md) |
| D2850 | Keep the hand-written workarounds for the unifier eta gaps until SW-1998 lands. | yes | nothing | SW-1998 |
| D2940 | Hold stage 3 until SW-1914, SW-1998 and SW-1999 have landed. **Amends D2633's start; answer the two together.** | yes | SW-1644, SW-1851 | reviews/record-eta-as-merged.md |
| D2941 | One background `fuzz:soundness` run (a few minutes) as lane 2's check. | yes | SW-2077 | record-eta-as-merged.md |

### Elaborator and kernel

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2568 | Reopen D2448 (glued closed types, parked "until a real proof hits it")? 2024 day 22 spends 5.5 s of kernel time there. | yes | SW-1788 | proposals/closed-type-values.md |
| D2569 | Direction: the kernel evaluates a statement afresh, glued, in each check; the kept type value becomes glued for the elaborator and tools. | yes (§4, options 3 and 4) | SW-1788 | closed-type-values.md |
| D2577 | A copy of syntax gets a new id rather than keeping its source's. | yes | SW-1803 | proposals/syntax-node-ids.md |
| D2578 | Ids only on dot-call syntax for now (~10 sites, not ~1,600). | yes | SW-1803 | syntax-node-ids.md |
| D2579 | In the same stage, drop what only guarded against address reuse. | yes | SW-1803 | syntax-node-ids.md |
| D2580 | Stage 1 as an Opus lane, determinism tests run by name. | yes | SW-1803 | syntax-node-ids.md |
| D2620 | Fix stale stuck calls by design (record the blocker), instead of the per-site tickets. Replaces D2603. | yes | SW-1865, SW-1866; drops SW-1842-SW-1844 | proposals/stuck-blockers.md |
| D2621 | The folded read-back also re-runs a stale bare stuck call, so a goal never shows `pickHead [True] 5` for `5`. | yes | SW-1866 | stuck-blockers.md |
| D2622 | Waiting checks (`.field`, record literals) also wait on a stuck type's unknown? | not now (backlog) | SW-1868 stays parked | stuck-blockers.md |
| D2623 | Stage 1's lane may run `task bench -- --no-time` (~80 s) before and after. | yes | SW-1866 | stuck-blockers.md |
| D2641 | The kernel closes its last public mutable state (`apart_sets`, caches, a token for trusted admission). | yes | SW-1888 | reviews/code-review-core.md |
| D2651 | Run debug-only invariant checks in the lane and merge tiers, through an `invariants` feature, keeping only those under 1%. | yes | SW-1903 | reviews/code-review-elab-checking.md |
| D2652 | Split `check.rs`, `lib.rs`, `unify.rs` one at a time, when no lane touches the file, `check.rs` first. | yes | SW-1904, SW-1905, SW-1906, SW-1935 | code-review-elab-checking.md |
| D2720 | A library file that fails to check fails every later request for it, with its original errors. | yes | SW-1931 | reviews/code-review-elab-rest.md |
| D2721 | A derive failure the deriver should have ruled out is `E-INTERNAL` on the type. | yes | SW-1930 | code-review-elab-rest.md |
| D2770 | Error kinds, design A: an internal `kind` beside the public code. | yes | SW-1972-SW-1976 | proposals/error-kinds.md |
| D2771 | A declaration that succeeds after hitting a resource limit is a compiler bug (asserted in tests, `E-INTERNAL` in release). | yes | SW-1977 | error-kinds.md |
| D2772 | Notes and rewordings keep keying on the public code. | yes | nothing extra | error-kinds.md |
| D2773 | `CannotInfer` may later split finer than its code, with no new user-visible code. | yes | nothing extra | error-kinds.md |
| D2800 | §1's three-part argument is the contract for check-cache replay; a refusal is a bug, asserted zero. | yes | SW-1925 (running) | proposals/check-cache-trust.md |
| D2801 | Key a custom-prelude session on the core text it elaborated, rather than refusing to cache it. | yes | SW-1919 | check-cache-trust.md |
| D2802 | Add `stitchwort check --verify-cache` (user-visible), run in the full tier; no sampled kernel recheck in daily. | yes | SW-1996 | check-cache-trust.md |
| D2680 | Dev and release builds keep sharing check-cache entries, with the reason written in `check_cache.rs`. (Asked in two places under one number.) | yes | SW-1919 | reviews/code-review-driver.md, check-cache-trust.md |
| D2930 | Postponement: a failed search waits on any unknown only where no enclosing try-and-undo would act on its failure (design B). | yes | SW-2064 | proposals/postpone-fixed-point.md |
| D2931 | Before stage 1 merges, one corpus check (whole AoC `--no-cache`, rogue, examples, snapshots) as a test-budget exception. | yes | SW-2065 | postpone-fixed-point.md |
| D2932 | Accept B's limit: a search inside a region that may retry still fails as today (no re-elaboration as in Agda and Lean). | yes | nothing extra | postpone-fixed-point.md |

### Editor and playground

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2583 | A long randomised kept-session check (~30 s) in daily, a 10-step one in the lane tier. | yes | SW-1823 | reviews/SW-1808-kept-search-session.md |
| D2701 | When a search comparison panics, fail the request and rebuild the kept session (remove the per-comparison catch). | yes | SW-1979 | reviews/code-review-elab-tactics.md |
| D2743 | The same rule for the CLI's `stitchwort search`. **Pairs with D2701; answer together.** | yes | SW-1979 | proposals/lsp-failure-policy.md |
| D2744 | An unreadable `stitchwort.yaml` shows an error in the open files, not only in the log. | yes | SW-1950 | lsp-failure-policy.md |
| D2733 | Drop a project's session a minute after its last file closes (restated in the policy note as 60 s). | yes | SW-1950 | reviews/code-review-cli-lsp-web-fmt.md, lsp-failure-policy.md |
| D2753 | Check in a child process so any abort restarts only the checker? | not now | nothing | proposals/deep-input.md |
| D2840 | Long chains: lists and texts are done; blocks get loops only if a measurement shows a block limit under 300 lines; left-nested operators stay guarded. Replaces D2751. | yes | SW-2018, SW-2021 | proposals/long-chains.md |
| D2841 | A fixed-size `let` split for long literals, so a literal's hash doesn't depend on the stack. | yes | SW-2019 | long-chains.md |
| D2842 | The playground's block length: no fixed number ("limited by memory"), 100,000 lines as the test. | yes | SW-2021 | long-chains.md |
| D2843 | A compact `Term::List` in the kernel? | not now | nothing | long-chains.md |
| D2844 | Long `+ - *` chains stay guarded, with an error note pointing at `[…].sum`. | yes | SW-2020 | long-chains.md |

### Error messages and goal printing

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2731 | `stitchwort fmt DIR` skips hidden folders and doesn't follow symlinked folders. | yes | SW-1951 | reviews/code-review-cli-lsp-web-fmt.md |
| D2732 | Every `--json` mode prints exactly one JSON object, with `ok` true exactly when the exit status is 0. | yes | SW-1952, SW-1692 | code-review-cli-lsp-web-fmt.md |
| D2832 | A check that runs past its budget fails, naming the declaration and what it was unfolding. | yes | SW-2009 | research/aoc-friction-synthesis.md |

### Syntax and language

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2670 | A lexical error (unclosed `"`, a tab, `café`) costs only its declaration, not the whole file. | yes | SW-1873 | reviews/code-review-syntax.md |
| D2690 | **dup of D2670** (the Opus syntax review's wording). | yes | SW-1873 | reviews/code-review-syntax-opus.md |
| D2691 | Skip a byte-order mark at the start of a file silently, as Rust and Go do. | yes | part of SW-1873 | code-review-syntax-opus.md |
| D2671 | Write a grammar chapter (EBNF plus the layout rules), after the parser split. | yes, after the split | SW-1880 | code-review-syntax.md |
| D2780 | Recover inside a declaration by keeping its signature and putting a hole where the text breaks (Design B). | B | SW-1982, SW-1983, SW-1984 | proposals/parse-recovery.md |
| D2781 | A recovered hole counts as an error; its goal shows in the editor, not in `check`'s output. | yes | SW-1983 | parse-recovery.md |
| D2782 | No recovery inside `type`, `interface` and `ability`. | yes | nothing extra | parse-recovery.md |
| D2783 | The formatter keeps refusing a file with a syntax error. | yes, for now | nothing extra | parse-recovery.md |
| D2784 | An unclosed `"""` ends at the next column-0 declaration keyword. | yes | SW-1873 | parse-recovery.md |
| D2785 | Importers of a namespace with syntax errors stay skipped. | yes, for now | nothing extra | parse-recovery.md |
| D2833 | Keep `a != b` beside `=` in a statement reading as `≠` (today's rule). | keep | nothing | research/aoc-friction-synthesis.md |
| D2970 | Warn on bidi direction controls in comments and text literals (Trojan Source), with an escape for a text that needs one. | yes, a warning | SW-2084 | reviews/SW-2080-merges-7-nov.md |

### Effects, partial functions and native binaries

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2660 | A run that uses too much memory: charge growing text natives in the counterexample search only, for now. | (a) | SW-1897 | reviews/code-review-rt.md |
| D2661 | A pending over-application counts as a frame, so the machine and the reference evaluator hit the same limit. | yes | SW-1898 | code-review-rt.md |
| D2711 | Native compilation accepts only programs lowered in the same process (a type only lowering makes). Asked again in backend-trust.md. | yes | SW-1989 | reviews/code-review-js-native.md, proposals/backend-trust.md |
| D2790 | Native code checks a value's shape at every field read: on in release if the bench shows ≤ 2%. | yes | SW-1990 | backend-trust.md |
| D2791 | Every pin that goes stale refuses to load (`E-BUILTIN`), for kernel, runtime, effect natives and backend rewrites. Covers D2710. | yes | SW-1991, SW-1992, SW-1586 | backend-trust.md |
| D2810 | SW-1581 (more row settling sites): an experiment only, closed if it helps no program. | yes | SW-1581 | proposals/row-settling-order.md |
| D2811 | When a call can't settle early, quietly fall back to the old behaviour rather than error. | fall back | SW-1926 | row-settling-order.md |
| D2960 | Ratify SW-424's `Effect.widenIn` decisions (D1150-D1152), which the orchestrator took for you on 24 Oct. | yes | SW-2075, SW-2071's extra fixes | reviews/SW-2072-widen-in-prototype.md |

### Speed

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2273 | In-place reuse: extend `code.rs`'s design in stages, not a new ownership pass. | yes | SW-1813 | reviews/SW-1163-in-place-reuse-fresh-eyes.md |
| D2274 | Start with a per-site reuse report, in the changed form D2590 gives it. | yes | SW-1809, SW-1810 | SW-1163 review |
| D2275 | Then inlining for reuse, if the report shows `Map` among the top missed sites. | yes, on data | SW-1811, SW-1812 | SW-1163 review |
| D2276 | Borrowed parameters only as a design note, only if read-only increments exceed ~20%. | yes | nothing | SW-1163 review |
| D2277 | The report and inlining now; effect-node reuse after SW-593. | yes | nothing extra | SW-1163 review |
| D2590 | Put the reuse report in the shipped binary (copy note names sites; columns under `run --profile`). | yes | SW-1809, SW-1810 | SW-1163 review |
| D2591 | The projection hoist only once a program shows it's needed. | yes, conditional | SW-1814 | SW-1163 review |
| D2592 | An always-give-back `Array.pop` in std now? | no | nothing | SW-1163 review |
| D2595 | A `NatMap` type? Or speed up `Map` itself, or nothing. | (c) speed up `Map` | SW-1824 | proposals/nat-map.md |
| D2596 | A measurement stage first, with a go/no-go rule. | yes | SW-1824 | nat-map.md |
| D2597 | `Map` gets faster by native walks over the existing tree values, not a new native map type. | walks | SW-1825 | nat-map.md |
| D2598 | Which key orders use the natives: base instances and derived `Ord` over them. | yes | SW-1825 | nat-map.md |
| D2599 | A lost native binding falls back quietly, with a binding test per native. | quiet fallback | SW-1825 | nat-map.md |
| D2600 | Native JS walks in stage 2, measured on `get` and `insertWith` first. | stage 2 | SW-1826 | nat-map.md |
| D2601 | Keep the trie as a conditional stage 3, and close SW-1603. | yes | SW-1827 | nat-map.md |
| D2880 | Computed record fields are the answer to "compute this once", the kernel seeing a plain definition. | yes | SW-2024, SW-2025, SW-2026 | proposals/compute-once.md |
| D2881 | Syntax: `computed table: … := …` inside the type's braces, not an attribute on a separate `def`. | in the braces | SW-2024 | compute-once.md |
| D2882 | Computed when the record is built (eager), not on first read. | eager | SW-2025 | compute-once.md |
| D2883 | Also hoist small invariant values out of lambdas automatically, as a later stage. | yes | SW-2027 | compute-once.md |
| D2884 | Computed fields stay out of the type's hash. | yes | SW-2024 | compute-once.md |
| D2885 | Rule out a user-written `implemented_by` and identity-keyed memoisation. | yes | nothing | compute-once.md |
| D2900 | An explicit `ghost` mark is the answer to "data only proofs use": erased at run time, seen by the kernel. | yes | SW-2041-SW-2044 | proposals/erase-proof-data.md |
| D2901 | Syntax: the keyword `ghost`, not `@[erased]` or a quantity. | `ghost` | SW-2042 | erase-proof-data.md |
| D2902 | The ghost check lives in the kernel. | kernel | SW-2041 | erase-proof-data.md |
| D2903 | Stage 1 has no ghost lambda parameters or ghost arrows. | yes | SW-2041 | erase-proof-data.md |
| D2904 | Rule out inferred erasure (keep only a `--profile` hint) and Lean's `Erased`. | yes | SW-2045 | erase-proof-data.md |
| D2905 | Only if D2900 is no: make `Graph.states` a thunk. | only then | nothing | erase-proof-data.md |

### Proof automation and function equations

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2700 | The counterexample search on a failing theorem stops by count of inputs, not time, so its note is the same everywhere. | yes | SW-1937 | reviews/code-review-elab-tactics.md |
| D2860 | Add `within P` to a `rewrite` rule: replace only inside parts of the goal matching `P`. | yes | SW-2033, SW-2035 | proposals/rewrite-occurrence.md |
| D2861 | No occurrence numbers (`nth_rewrite`, `at 2`) for now. | yes | nothing | rewrite-occurrence.md |
| D2862 | A failure note for "the `_` matched only one instance", no "rewrite every instance" form. | yes | SW-2034 | rewrite-occurrence.md |
| D2863 | The word is `within`, contextual (not reserved). | yes | SW-2033 | rewrite-occurrence.md |
| D2864 | A pattern's `_` matches afresh at each instance, unlike a rule's `_`. | yes | SW-2033 | rewrite-occurrence.md |
| D2870 | In a `decreasing` definition, a `match` or `if` gives a recursive call under it its fact automatically. | yes | SW-2029 | proposals/decreasing-with-hypothesis.md |
| D2871 | Document the result-record pattern now; no `ensures` clause until a third day needs it. | yes | SW-2031 | decreasing-with-hypothesis.md |
| D2872 | Then move 2024 day 23, 2021 day 16 and `Graph.searchFrom` off their workarounds. | yes | SW-2032 | decreasing-with-hypothesis.md |

### Standard library

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2820 | Does "full API docs" (D2351) cover theorems? Document one only when its statement doesn't say it all; no sweep. | no | nothing | reviews/code-review-std.md |
| D2821 | Extend effectful `{e}` callbacks to `Array`, `Map`, `Set`, `Option`. | yes | SW-2002 | code-review-std.md |
| D2822 | One name per operation (`getOr`, `Text.foldRight`, `Set.intersection`, …), no aliases kept. | yes | SW-2006 | code-review-std.md |
| D2834 | "The number of …" in specs: document the distinct-list idiom now; `Set.card` only if needed. | document | nothing | research/aoc-friction-synthesis.md |
| D2890 | Hide std's helpers with `@[internal]` (out of completion, `doc`, `search`), not an enforced `private`. | yes | SW-2037-SW-2040 | proposals/private-helpers.md |
| D2891 | "Internal" means a user never needs to write it, even in a proof; accumulator forms stay public. | yes | SW-2038 | private-helpers.md |
| D2892 | User programs may use `@[internal]` too. | yes | SW-2037 | private-helpers.md |
| D2893 | Construction privacy (SW-1065) stays a separate, enforced feature. | yes | SW-1065 (and D2171) | private-helpers.md |

### AoC shared library

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2831 | Every AoC lane ends by moving the generic lemmas it wrote to std or `Aoc.Common`. | yes | nothing (a workflow rule) | research/aoc-friction-synthesis.md |

### Test infrastructure and audit

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2750 | Adopt the deep-input policy: loops where depth comes from length, guards elsewhere, every entry point inside an operation, no `stacker`. | yes | SW-1966-SW-1970 | proposals/deep-input.md |
| D2752 | Let users raise the nesting limit? | no | nothing | deep-input.md |
| D2754 | Which tier runs the deep-input corpus: a small subset in merge (if under 5 s), the full table in daily. | as stated | SW-1965 | deep-input.md |
| D2910 | Restate the daily tier's budget from one quiet measured run, rather than cut 75% of it to reach 5 minutes. Overlaps D2556. | yes | SW-1095, SW-2048 | reviews/code-review-tests.md |
| D2911 | The verifier's sample moves with each batch (offset by the merge hash, logged). | yes | nothing extra | code-review-tests.md |
| D2912 | The fixed core's AoC day checks its proofs too; AoC's own tests in daily if under a minute. | yes | SW-2051 | code-review-tests.md |
| D2913 | Lanes 3 and 4 may run a few slow daily-tier tests by name, one at a time in the background. | yes | SW-2048, SW-2049 | code-review-tests.md |
| D2920 | Adopt the mutation check as designed (source mutants, one rewound session). Replaces D2169. | yes | SW-2056-SW-2058 | proposals/mutation-check.md |
| D2921 | A mutant killed only by a test: report both, headline the share killed by a theorem. | report both | SW-2056 | mutation-check.md |
| D2922 | Advisory now; decide on a gate after the first full AoC run. | advisory | nothing | mutation-check.md |
| D2923 | Mutate the spec too, later, and std against its lemmas. | yes, later | nothing | mutation-check.md |
| D2924 | The full AoC mutation run on the old 16 GB laptop, weekly. | yes | SW-2059, SW-2060 | mutation-check.md |
| D2853 | **dup of D2924** (SW-2060 runs overnight on the laptop). | yes | SW-2060 | SW-2060 |

### Developer loop speed

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2556 | One daily-tier run on a quiet machine to measure the overnight savings. Overlaps D2910. | yes | SW-1804, SW-1734 (in review) | dev/overnight-2026-11-06.md, SW-1804 |
| D2565 | Accept three edits per new elab unit test (and no IDE run icon on them) for ~20 s off a clean build? | yes only if a `build.rs` makes the table | SW-1776 (in review) | SW-1776 |
| D2574 | CLAUDE.md rule: never `rm` a path built from a variable. | yes (implied) | SW-1805 | SW-1805 |
| D2576 | CLAUDE.md rule: stop processes with `dev/stop-mine`, never `pkill`/`killall`. | yes (implied) | SW-1805 | SW-1805, dev/overnight-2026-11-06.md |
| D2735 | Check AoC days in parallel (~70 s on one core → ~15 s). | yes | SW-1964 | SW-1964, proposals/kernel-merge-gate.md |
| D2760 | Kernel and core-language lanes run the ~75 s corpus gate themselves, with no approval needed. | yes | SW-1958 | proposals/kernel-merge-gate.md |
| D2761 | A lane that passed the gate needs no whole-AoC run after merging; D2507 retires. | yes | nothing extra | kernel-merge-gate.md |
| D2762 | A per-day step baseline with a 3× ceiling (after stage 1 has run a few times). | yes | SW-1962 | kernel-merge-gate.md |
| D2763 | "Merge-ready" means meeting the gate; such a lane merges with no further question. | yes | SW-1958 | kernel-merge-gate.md |
| D2961 | A commit marked PROTOTYPE or "not for merging" blocks a merge until the message says how each caveat was met. | yes | nothing (one line in workflow.md) | reviews/SW-2072-widen-in-prototype.md |

### Tutorials and docs

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2636 | A 5-20 s profiled run to requote the guide's chapter 11 profile. | yes | SW-1855 | SW-1850 |
| D2952 | Fix the 20 stale status lines in `docs/proposals`. | yes | SW-2071 | SW-2071, proposals/README.md |
| D2950, D2951, D2953, D2954 | **The text of these isn't recorded** on any ticket, note or commit: SW-2069 cites "D2950-D2955" and stops. They're probably the proposals index's archive and merge suggestions ("Notes to merge or archive"). Ask the orchestrator to restate them. | ? | nothing found | SW-2069 |

### Older questions still on backlog tickets

| D | Question | Rec | Blocks | Source |
|---|---|---|---|---|
| D2166 | When a definition fails termination, try likely measures under a work limit and suggest one that checks. | yes | SW-1062 | SW-1062 |
| D2168 | Custom input generators for the counterexample search. | yes, after SW-1029 | SW-1063 | SW-1063 |
| D2170 | The productivity report's human-editor features get no tickets, noted as "no agent evidence". | yes | nothing | SW-1065 |
| D2171 | Construction privacy, as an Opus design note later. D2893 says how it relates to `@[internal]`. | later | SW-1065 | SW-1065 |

## Safe to accept as recommended in bulk

Each of these is low-risk and easy to reverse: an internal fix, a test
or tier change, a "not now", a tidy-up, or a call the orchestrator has
already taken. None changes the kernel's trusted rules, a syntax users
write, or what a proof means. Answer "accept these" and they're all taken
as recommended.

- **Ratify the orchestrator's calls:** D2560, D2561, D2562 (check-cache
  key: build SW-1741, one key, no shared cache), D2563, D2564 (don't split
  elab; a feature for unit tests), D2567 (SW-1779's fix 1), D2570 (cached
  unfoldings record their modes, built), D2571 (cache sweeps left as they
  are), D2960 (`Effect.widenIn`).
- **Tidy-ups and records:** D2566, D2634, D2635, D2850, D2952, D2957.
- **Internal fixes and hardening:** D2577-D2580, D2620, D2621, D2641,
  D2652, D2661, D2680, D2700, D2701, D2720, D2721, D2743, D2770-D2773,
  D2800, D2801, D2811, D2841.
- **Editor and CLI behaviour:** D2691, D2731, D2732, D2733, D2744, D2970.
- **"Not now" or "no":** D2591, D2592, D2622, D2752, D2753, D2820, D2833,
  D2834, D2843, D2844, D2905.
- **Tests and tiers:** D2583, D2596, D2601, D2651, D2660, D2735, D2750,
  D2754, D2810, D2910, D2911, D2961.
- **Short test runs:** D2623 (bench counts, ~80 s), D2636 (one 5-20 s
  run), D2941 (one fuzz run, a few minutes).

That is 70 numbers (62 open questions and the 8 calls to ratify). The rest need a real look: directions (D2568,
D2569, D2610-D2614, D2632, D2633, D2940, D2830), user-visible language
features (D2860-D2864, D2870-D2872, D2880-D2885, D2890-D2893,
D2900-D2904, D2821, D2822), trust boundaries (D2711, D2790, D2791,
D2802), process rules (D2760-D2763, D2565, D2574, D2576, D2831), and the
longer runs that are test-budget exceptions (D2556, D2913, D2931, D2633).

## Answered or no longer open

Listed so the filtering can be checked.

**Answered by you (ticket or commit records it):** D2555 (usage stop at
94%), D2573, D2581, D2582, D2585, D2672, D2693, D2734 ("parallel design
work", SW-1957), D2740, D2741, D2742, D2792, D2852 ("Yes, push."), D2855
("Proceed with those 3"), D2856 ("proceed"). Answered by the same "Proceed
with those 3": D2640 (Nat natives pinned, built in SW-1885) and D2584 (a
search panic answers "no result", built in SW-1820).

**Withdrawn, moot or overtaken:**

- D2575: withdrawn (D2507 already covered the run).
- D2586: moot (SW-1829 found the fix; no revert).
- D2603: replaced by D2620.
- D2730: replaced by D2740, which you answered.
- D2751: replaced by D2840.
- D2653, D2692, D2823: each asked for a design note. The notes were
  written (error-kinds.md, parse-recovery.md, private-helpers.md), and
  their own questions replace them.
- D2650: keep the search's per-candidate panic catch. Its recommendation
  is the opposite of D2701's and D2743's, which came later and are the
  policy now.
- D2710: folded into D2791 (effect natives pinned like every other pin;
  SW-1885 moved that half to SW-1991).
- D2955: done (the SW-2072 review ran).
- D2169: replaced by D2920.

The numbers between these (D2557-D2559, D2572, D2587-D2589 and so on) were
never used: each note took a block of ten.
