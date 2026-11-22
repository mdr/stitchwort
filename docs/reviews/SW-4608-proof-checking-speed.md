# Proof-checking speed: where the time goes, and how we compare (SW-4608)

**Status:** Opus lane SW-4608, 22 November 2026, for D3716. Measurement only: no checker code
changed. Raw data, small, in [`SW-4608/`](SW-4608/).

Marks: **[measured]** timed or counted today; **[estimated]** my judgement from the measurements;
**[inferred]** read from the code, not timed.

## In plain words

**The question.** We have tuned run time but never looked hard at type and proof checking. Is
there cheap speed there, and how far are we from Lean and Rocq?

**Where the time goes.** A cold check of all of `tools/fmt` takes **252 s** on one core
**[measured]**. Nearly all of it is the elaborator: 84% elaboration, 16% kernel by the
checker's own clock; parsing is 0.3% and hashing 0.5% of the profile. Inside elaboration, the
biggest single thing is **reading values back into terms** (37% of the profile, 54% of
evaluation steps). The time is very concentrated: **63 declarations (0.5%) take half of it**,
and one proof, `standsEachFile`, takes 12.5% alone.

**Cheap wins found.** Two are small, general and safe:

1. **Naming `match` helpers in diagnostics costs 14% of the `tools/fmt` check** (5% of AoC 2021
   day 16, 2.5% of 2020 day 18). Every diagnostic, including ones never shown, is searched for
   the name of every `match` helper lifted so far in the whole run. Estimated saving **10-14%**
   of a large project check, about 25-35 s on `tools/fmt`; no kernel or hash change.
2. **`check --timings=all` spends 125 s of a 387 s run printing its tables** (sys time, one
   write per padding character to unbuffered standard error). Not checking time, but it is the
   command the workflow tells us to time with, so every timing run of a big project pays it.

The bigger, harder wins are read-back (six `tools/fmt` proofs each read back the same
1.1-million-node term and cost 54 s together) and allocation (27-31% of the profile is
`malloc`, `free`, `drop` and `clone` of values). And the check is single-threaded on a
10-core machine.

**Against Lean and Rocq.** On the three AoC days ported to Lean (SW-2294), with library loading
subtracted, we take **2.9x, 7.9x and 3.2x** Lean's time **[measured]**. With loading counted,
a cold `--no-cache` check is **7-24x** slower, because Lean's library comes precompiled and ours
is rechecked (an AoC day's `--no-cache` check is 87-98% standard library). On the 31 sampled
slice 1 formatter theorems (SW-4537), the per-theorem times are of the same order as Lean's
per-file times and a few times Rocq's, but that comparison is loose (section 4). The
resolution is "a few times slower than Lean, more than that behind Rocq", not a number.

## 1. Method

- **Machine:** Speedwell, Apple M1 Pro, 10 cores, 32 GB, macOS 27.2.1. Other agents were using
  it: the 5-minute load was 4-15 during the runs (each run's load is in the notes below).
  Wall times on a loaded machine move by 10-30%.
- **Build:** `lane/SW-4608` at `4a07c90fc`, `cargo build --release -p stitchwort-cli --features
  stitchwort-cli/dev` with `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only` (symbols for the
  profiler; same code).
- **tools/fmt cold check:** from `tools/fmt`, `STITCHWORT_STEP_PHASES=1 /usr/bin/time -l
  stitchwort check --no-cache --timings=all` (run 1, timings), then `samply record --save-only
  --unstable-presymbolicate -r 250 -- stitchwort check --no-cache` (run 3, the profile, no
  timings). Run 2 was lost: samply refuses to profile `/usr/bin/time`, a system binary, and
  ran it unprofiled.
- **AoC days:** from `aoc/`, `check --no-cache Aoc.YearYYYY.DayDD{,.Spec,.Proofs,.Tests}`, once
  with `--timings=all` and `/usr/bin/time -l`, once plain, once under samply at 1 kHz.
- **Profiles:** samply 0.13.1 from nixpkgs; summarised by
  [`samply_summary.py`](SW-4608/samply_summary.py) (self and inclusive share per function over
  the checking thread). Timings tables parsed by [`parse_timings.py`](SW-4608/parse_timings.py).
- **Lean against AoC:** `nix develop .#compare -c python3 -I bench/compare/proofs.py --sw
  target/release/stitchwort --runs 3` (what `task bench:compare:proofs` runs, with 3 runs
  instead of 5), Lean 4.34.1 from the flake.
- **Lean and Rocq against slice 1:** `hyperfine -N --warmup 1 --runs 5` on `lean F.lean` and
  `rocq compile -R <stdlib>/lib/coq/9.1/user-contrib/Stdlib Stdlib F.v` for each SW-4537 file,
  as their headers say, plus an empty file each for the load. Lean 4.35.0, Rocq 9.1.1 (OCaml
  4.14.4) with rocq-stdlib 9.0.0, all from nixpkgs (`lean --version`, `rocq --version`).
  Lean's `.olean` loading of `Init` happens on every `lean` call; there is no separate
  "library build" for core-only files.

## 2. Part 1: where our checking time goes

### 2.1 The whole of tools/fmt, cold

| | value | mark |
|---|---:|---|
| namespaces | 150 project + 72 library files | measured |
| declarations timed | 13,103 rows (36,037 kernel declarations) | measured |
| wall, plain check | 252 s (under samply) | measured |
| wall, `--timings=all` | 387 s; the checker's own clock 262 s | measured |
| user / sys (`--timings=all` run) | 250 s / 123 s | measured |
| peak memory | 3.25 GB RSS, 3.69 GB peak footprint | measured |
| CPU used | one core: user + sys = 96% of wall | measured |

**By phase** (the checker's own clock and the profile):

| phase | time or share | source |
|---|---:|---|
| elaboration | 218.6 s (84% of declaration time) | timings, measured |
| kernel (`define`/`declare` calls) | 40.7 s (16%) | timings, measured |
| library files (std, checked cold) | 23.8 s (9%) | timings, measured |
| outside units: parsing, core load | 1.4 s | timings, measured |
| parsing (`parse_module_and_tree`) | 0.3% | profile, measured |
| hashing (`shape_hash`) | 0.5% | profile, measured |
| read-back (`quote_as_until`, inclusive) | 37.1% | profile, measured |
| evaluation (`value::run`, inclusive) | 36.9% | profile, measured |
| kernel check (`core::check::check`, inclusive) | 15.9% | profile, measured |
| unification (`unify::run`, inclusive) | 10.1% | profile, measured |
| conversion (`conv_with`, inclusive) | 10.2% | profile, measured |
| diagnostics: `explain_lifted` (inclusive) | **14.2%** | profile, measured |
| malloc, free, drop, clone (self, summed) | 27% | profile, measured |
| cache read/write | none (`--no-cache`) | |

Inclusive shares overlap (read-back runs evaluation, the kernel converts), so they don't sum.
**Steps by phase** (`STITCHWORT_STEP_PHASES=1`, 2.92 billion steps): read-back 53.9%, other
32.3%, unify 10.0%, apply 3.5%, walk 0.3% **[measured]**.

**Concentration** (declaration total time, elaboration plus kernel) **[measured]**:

| slowest | share of time |
|---|---:|
| 1 declaration | 12.5% |
| 10 | 32.0% |
| 63 (0.5%) | 50% |
| 131 (1%) | 57.1% |
| 655 (5%) | 73.8% |
| 2,634 (20%) | 90% |
| the 10,056 under 10 ms | 21.5 s (8%) |

So yes: 5% of declarations take three quarters of the time. Fixed per-declaration costs are
not the problem; a few proofs are.

**The top 20** (ms; `fmt-decls-top200.csv` has 200):

| declaration | elab | kernel | total | steps | largest read-back (nodes) |
|---|---:|---:|---:|---:|---:|
| `Fmt.SettleOutputProofs.standsEachFile` | 32,461 | 5 | 32,465 | 475 M | 1,130,523 |
| `Syntax.ReadBackHungTop.readsBackHungListExample` | 267 | 10,783 | 11,050 | 147 M | 43 |
| `Fmt.FileLexProofs.printedFinish1` | 10,803 | 26 | 10,829 | 121 M | 1,130,000 |
| `Syntax.ReadBackHungTop.readsBackHungSignExample` | 226 | 7,022 | 7,249 | 95 M | 43 |
| `Fmt.SettleOutputProofs.standsDecl` | 5,775 | 5 | 5,780 | 93 M | 1,130,000 |
| `Syntax.ReadBackHungAtoms.atomHung` | 4,394 | 38 | 4,433 | 56 M | 274,000 |
| `Syntax.FollowsDeclData.followsFieldsAt` | 4,121 | 4 | 4,125 | 50 M | 4,210 |
| `Syntax.FollowsFormsBlocks.followsExprKeyword` | 1,674 | 800 | 2,474 | 29 M | 53,500 |
| `Fmt.GroupSlots.printedSplitParts` | 2,343 | 3 | 2,346 | 47 M | 1,030,000 |
| `Syntax.FollowsDeclData.followsConstructorStep` | 2,227 | 4 | 2,231 | 29 M | 4,210 |
| `Syntax.ReadBackHungApp.unaryHung` | 2,156 | 67 | 2,223 | 30 M | 573,000 |
| `Syntax.FollowsDeclHeaders.followsHeaderGroupColon` | 2,088 | 15 | 2,104 | 28 M | 5,350 |
| `Fmt.DeclHangProofs.doc1Hangs` | 1,645 | 115 | 1,760 | 26 M | 8,220 |
| `Fmt.SettleOutputProofs.standsRest` | 1,717 | 2 | 1,718 | 28 M | 1,130,000 |
| `Syntax.FollowsDeclData.followsDataDeclOn` | 1,551 | 4 | 1,555 | 19 M | 3,390 |
| `Fmt.OutputStatements.holdsOnSigns` | 753 | 746 | 1,499 | 38 M | 3 |
| `Syntax.ReadBackHungInline.arrowHung` | 1,237 | 235 | 1,472 | 16 M | 92,300 |
| `Syntax.ReadBackHungChains.cmpHung` | 1,307 | 123 | 1,429 | 20 M | 61,600 |
| the `Syntax.Group, Syntax.Row, …` data group | 1,099 | 234 | 1,333 | 19 M | 10,000 |
| `Fmt.FileLexProofs.printedStart1` | 1,327 | 4 | 1,330 | 23 M | 1,030,000 |

Six of these (`standsEachFile`, `printedFinish1`, `standsDecl`, `printedSplitParts`,
`standsRest`, `printedStart1`) each read back a term of 1.03-1.13 million nodes and together
take **54.5 s, 21% of the declaration time** **[measured]**; in `standsEachFile`, 395 M of its
475 M steps are read-back. The two hung examples are kernel time, the re-lexing SW-4536 left.

**Hot functions** (self time, tools/fmt profile; `profile-fmt-self.txt`) **[measured]**:

| self | function |
|---:|---|
| 11.0% | `core::str::pattern::StrSearcher::new` (from `explain_lifted`, below) |
| 9.3% | `stitchwort_core::value::run` (the evaluator) |
| 4.1% | `Value::clone` |
| 3.9% / 3.7% | `mi_free` / `mi_malloc_aligned` |
| 3.3% | `Vec<Value>` from iterator |
| 3.1% | `value::detach` |
| 3.0% | `Term::for_each_child` (subterms) |
| 2.5% | `value::quote_as_until` (read-back) |
| 2.4% | `Rc<[Value]>::from_iter_exact` (spine copies) |
| 2.4% | `drop_glue::<Value>` |
| 2.3% | `value::resume` |
| 2.1% | `value::free_iteratively` |

**Who calls read-back** (share of the whole profile): `matching::blocker` 6.6%, the kernel's
`Rebuild::substitute_in` through `quote_folded` 4.7%, the elaborator's `check::quote_folded`
4.1%+, `matching::generalised_now` 3.2%, `unify::value_forms` 1.2%, the rest under 1.1% each.

### 2.2 The two AoC days, cold

| | 2021 day 16 | 2020 day 18 | mark |
|---|---:|---:|---|
| wall, plain `check --no-cache` | 18.0 s | 12.2-12.7 s | measured |
| wall with `--timings=all` | 26.6 s (sys 8.7 s) | 26.3 s (sys 2.8 s) | measured |
| peak RSS | 440 MB | 284 MB | measured |
| declarations timed | 4,787 | 3,145 | measured |
| standard library's share of the declaration time | **87%** (14.9 of 17.1 s) | **98%** (22.4 of 23.0 s) | measured |
| the day's own namespaces (with `Aoc.Common` for day 16) | 2.1 s | 0.5 s | measured |
| top 1% of declarations | 45.8% | 52.5% | measured |
| read-back, inclusive | 36.0% | 37.3% | measured |
| kernel check, inclusive | 15.5% | 17.3% | measured |
| unification, inclusive | 12.1% | 12.5% | measured |
| `explain_lifted`, inclusive | 5.2% | 2.5% | measured |
| parsing | 1.0% | 2.1% | measured |
| malloc/free/drop/clone, self | 30% | 31% | measured |

A `--no-cache` check of a day is a check of the standard library with the day on top. The
slowest declarations of both runs are std's parser lemmas (`Std.Parse.runFromLabelWholeFromOkTree`
1.2-1.5 s, `runFromOptionalFromOk2Tree` up to 1.5 s, `runFromOptionalLabelWholeNone` 0.9 s).
With the cache, as in normal use, the day pays only its own 0.5-2 s **[inferred from the unit
table]**. The 14 s once recorded for day 16 was mostly std.

The day 18 `--timings` wall times moved between 11.7 and 23.5 s across three runs while other
agents' load rose to 15: treat the day 18 figures as loose. Shares from the profiles are less
sensitive to load than wall time.

### 2.3 Candidate wins, ranked

| # | what | evidence | estimated saving | risk | proposed ticket |
|---|---|---|---|---|---|
| 1 | `explain_lifted` runs a substring search of every diagnostic's message, labels and notes for the name of **every `match` helper lifted so far in the run** (`tables.lifted`, which only grows), and builds and sorts that whole list again per diagnostic. Diagnostics go through it before anyone decides whether to show them (library warnings, which programs never see, included **[inferred]**). Skip the search when the text has no `%` (every generated helper's name has one: `%match1`, `%go` **[inferred]**), build the sorted list once per namespace, or explain only diagnostics that will be printed. | 14.2% inclusive of the tools/fmt profile (11% in `StrSearcher::new` alone); 5.2% and 2.5% of the days; its share rises through the run (3% in the first tenth, up to 35% later) as the table grows | **10-14% of a large project's cold check** (25-35 s of 252 s on tools/fmt), 2-5% of an AoC day **[estimated]** | low: diagnostics only; messages must stay identical (snapshot tests catch a change); no kernel, term or hash change | "Name lifted `match` helpers in diagnostics without searching for all of them (`explain_lifted`, 14% of the tools/fmt check)" (sonnet), small |
| 2 | `--timings=all` writes its three tables with `eprintln!`, one row at a time, padded to the longest name; one row names a whole mutual group (thousands of characters), so every row is padded to it, and unbuffered standard error writes each padding character separately | 62 MB of stderr for tools/fmt; 125 s of 387 s outside the checker's clock; sys 123 s against 0.2 s for a run without timings; day 16 +8.5 s | **125 s per tools/fmt timing run, 8 s per AoC day timing run** **[measured, cause inferred]** | none: output only | "`check --timings`: buffer the tables and cap the name column (125 s of a tools/fmt timing run is printing)" (deepseek), small |
| 3 | The `standsEachFile` family reads back the same ~1.1 M-node term: six proofs, 54.5 s, 21% of tools/fmt's declaration time | timings' largest read-back column; read-back 395 M of `standsEachFile`'s 475 M steps | up to 20% of tools/fmt **[estimated]**, if the read-back can be avoided or shared (a proof change, `byComputing` on a smaller goal, or the elaborator not reading the value back where it only needs its head) | medium: elaborator only if read-back is skipped; proofs may need reshaping | "Profile the `standsEachFile` family's 1.1 M-node read-back and remove it (21% of the tools/fmt check)" (opus), medium; profile first |
| 4 | `matching::blocker` reads back values to find what blocks a `match`; 6.6% of the profile is its read-back | callers of `quote_as_until` | 3-5% **[estimated]** if it looks at the value's head instead of the read-back term | medium: elaborator's match compilation; terms unchanged if it only changes how the blocker is found | "Find a `match`'s blocker without reading the scrutinee back (6.6% of the tools/fmt check)" (opus), small to medium |
| 5 | Allocation: `malloc`/`free`/`drop`/`clone` of `Value`s and `Rc<[Value]>` spine copies (`from_iter_exact` over a chain: appending to a spine copies it) | 27-31% self in all three profiles | 5-15% **[estimated]**, from persistent spines or fewer clones in `value::run` | **high: `crates/core/src/value.rs` is the kernel's evaluator**; a kernel review lane | "Measure spine copying and value clones in `value::run` and propose a cheaper spine (kernel evaluator; design note first)" (opus, with a fable review), large |
| 6 | One core: the check runs namespaces one after another (user + sys = 96% of wall) | `/usr/bin/time` | 2-5x wall on 10 cores for a large cold check **[estimated, depends on the namespace graph's critical path, not measured]** | high: values are `Rc`, not `Send`; a design | "Design note: check independent namespaces in parallel (measure the critical path first)" (opus), large; Matt's call on direction |
| 7 | Std's parser lemmas (`Std.Parse.runFrom…Tree`) take 0.7-1.5 s each and dominate every `--no-cache` std check | top of both day tables | 3-5 s of each cold std check **[estimated]**; nothing in normal (cached) use | low: proofs only | "Speed up std's `Parse.runFrom…Tree` lemmas (1-1.5 s each in every cold std check)" (sonnet), small |

Items 1 and 2 are the cheap, general, safe ones. 3 and 4 are the next tier: one proof family
and one elaborator path that the profile names. 5 and 6 are large and touch the kernel or the
architecture.

Also seen: `check --only` is not a cheap way to recheck one theorem when the project cache is
off. `--no-project-cache --only` of the 3 Pilot theorems loaded 50 namespaces and checked 55
theorems in 41 s; batch C's 13 loaded 140 namespaces in 207 s **[measured]**. With the cache
on, the dependencies come from it, so this matters only for timing; but it means "check just
these theorems cold" isn't something we can measure with `--only`.

## 3. Part 2a: three AoC days against Lean (SW-2294's ports)

`bench/compare/proofs.py`, 3 runs each, medians, load 7-10 during the run **[measured]**:

| day | theorems | sw check | sw load | sw net | lean file | lean load | lean net | sw net / lean net | lake build, cold |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 17 | 2.69 s | 2.40 s | 289 ms | 360 ms | 261 ms | 99 ms | **2.9x** | 891 ms |
| 2020 day 18 | 23 | 11.03 s | 9.46 s | 1.57 s | 459 ms | 261 ms | 199 ms | **7.9x** | 995 ms |
| 2021 day 15 | 41 | 7.38 s | 5.85 s | 1.53 s | 734 ms | 261 ms | 473 ms | **3.2x** | 1.21 s |

- **Net of loading, we are 3-8x slower than Lean on the same theorems** **[measured]**, worst
  on the parser day. That is the "kernel plus elaborator" gap.
- **Loading is the bigger gap.** "sw load" is `check --no-cache` of a file importing what the day
  imports: 2.4-9.5 s, because we recheck the library from source; Lean maps precompiled
  `.olean` files in 0.26 s. In normal use our check cache plays the `.olean` part, so a fairer
  "sw load" would be a cached check of the import file, not measured here. With loading counted
  as the bench does, a cold check is 7x (day 2), 24x (day 18) and 10x (day 15) Lean's time.
- The day 18 port leaves out 26 of 49 theorems (the ones about `Std.Parse`'s `Reads`/`Runs`);
  ours checks only the 23 in common, plus what they need (`--only`).
- The proposal's other rows (warm, one edit, kernel time alone) were not run.

## 4. Part 2b: the slice 1 sample against Lean and Rocq (SW-4537's ports)

Lean and Rocq, `hyperfine` 5 runs, mean wall **[measured]**; "net" subtracts the empty file
(Lean 247 ms: `Init` only, as the files import nothing; Rocq 154 ms with the `Require` line
four of the five files use). Ours is the sum of the sampled theorems' own elaboration plus kernel time
in the cold tools/fmt run (2.1), which leaves out everything they use **[measured]**.

| file (theorems) | Lean | Lean net | Rocq | Rocq net | ours, the theorems alone | ours / Lean net | ours / Rocq net |
|---|---:|---:|---:|---:|---:|---:|---:|
| Pilot (3) | 452 ms | 205 ms | 236 ms | 82 ms | 85 ms | 0.4 | 1.0 |
| Batch A (7) | 1,021 ms | 774 ms | 377 ms | 223 ms | 2,308 ms | 3.0 | 10 |
| Batch B (7) | 1,695 ms | 1,448 ms | 415 ms | 261 ms | 395 ms | 0.3 | 1.5 |
| Batch C (13) | 4,735 ms | 4,488 ms | 454 ms | 300 ms | 475 ms | 0.1 | 1.6 |
| Reserve (1) | 350 ms | 103 ms | 179 ms | 25 ms | 51 ms | 0.5 | 2.0 |
| all 31 | 8,253 ms | 7,018 ms | 1,661 ms | 891 ms | 3,314 ms | **0.5** | **3.7** |

Batch A's figure is mostly one theorem, `unaryHung` (2,223 ms); without it ours is 1,091 ms for
the other 30. Lean's batch C (4.7 s) is mostly its automation (`simp_all`, `decide`) on cut-down
definitions **[inferred, not profiled]**.

**What is and isn't comparable.** This table is loose, and leans in our favour:

- **Their files are self-contained.** Each defines a cut-down parser or printer and states the
  lemmas our proofs use as `axiom`s (Lean batch A has 123 `axiom` lines, batch C 283; Rocq
  89 and 219 `Parameter`/`Axiom`). So the files check the counted theorems plus small
  definitions, and never prove the support. "Net" still includes those definitions.
- **Ours is the theorems alone** inside a full check: the definitions they're about, the lemmas
  they use and std are checked elsewhere and not counted. A file-for-file comparison on our side
  (`check --no-project-cache --only` the theorems) checks their whole dependency cone: 41 s,
  71 s, 89 s, 207 s and 7.5 s for the five files **[measured]**, which compares 50-140 namespaces
  with one file and says nothing useful.
- **Automation differs.** SW-4537's rules kept proof structure close, but the ports use
  `simp_all`, `omega`, `cases <;>`, `inversion`, which cost time where our explicit case arms
  cost lines.
- **Startup differs:** Lean loads `Init` on every call (0.25 s); Rocq loads its Stdlib modules
  (0.15 s); ours is inside a running check.
- **Versions:** Lean 4.35.0 here, 4.34.1 in the AoC bench.

Read it as: on these theorems we are **not orders of magnitude behind Lean, and a few times
behind Rocq**; the AoC bench (section 3) is the firmer number, at 3-8x behind Lean net of
loading.

**A fairer comparison, if wanted:** port one whole small namespace both ways, definitions and
lemmas included (no axioms), and check the same dependency cone cold on each side, with our
std cached and Lean's core prebuilt. Each port in SW-4537 took about an agent-hour per batch;
a namespace of 30-50 declarations is perhaps 1-2 agent-hours per prover **[estimated]**. The
AoC bench already does this for three days, so adding `tools/fmt`'s lexer or `Std.Doc.Proofs`
would be the next step.

## 5. What I'd measure next

- **The critical path of the namespace graph** in a cold tools/fmt check: how much a parallel
  check could save (item 6) before anyone designs one.
- **How many diagnostics `explain_lifted` sees, and how many are printed** (one counter), to
  confirm item 1's fix is "explain only what's shown".
- **The `standsEachFile` read-back**: which call reads back the 1.1 M-node term and how often
  (`STITCHWORT_BIG_READBACK=1000000` gives the backtraces).
- **A cached "sw load"** for the AoC bench (a cached check of the import file), so the load column
  compares our cache with Lean's `.olean`s; and the bench's missing rows (warm, one edit).
- **Allocation counts** per value operation (mimalloc stats) before any spine redesign.

## 6. Notes on the runs

- tools/fmt run 1 (`--timings=all`): started 11:38, 5-minute load 13.7 falling to 4. Run 3
  (profile): 11:54-11:58, load 4.
- AoC days: 12:00-12:04, load 4-17 (rising during day 18's reruns).
- AoC Lean bench: 12:05-12:10, load 7-10.
- Lean/Rocq slice 1 files: 11:37, load about 8.
- Our `--only` runs: 12:16-12:23, load 3-6.
