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

## Rerun, 22 Nov afternoon (SW-4616)

The same bench (`bench/compare/proofs.py`, 3 runs each, medians) on `lane/SW-4616` at
`main` as of cad2a2900, which includes SW-4609, SW-4624 and SW-4629 and the other checking-speed
changes since section 3. Two changes to the bench: "sw load" is now also measured as a **cached**
check of the import file (the check cache warmed by hyperfine's untimed warmup run, so it is our
counterpart of Lean's precompiled `.olean`), and the table gains three columns from it.
"sw load" (the `--no-cache` one) and "sw check" (`--no-cache`) are measured as before; **the
headline stays "sw net / lean net"**, so it compares with section 3, and the new
"sw net + cached load / lean file" is the fair whole-run figure (our time for the day's theorems
plus a warm library, against Lean's whole file with a prebuilt Lib). **[measured]**

| day | theorems | sw check | sw load (no cache) | sw net | lean file | lean load | lean net | sw net / lean net | sw load (cached) | sw net + cached load | that / lean file | lake build, cold |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 17 | 2.55 s | 2.25 s | 304 ms | 405 ms | 262 ms | 143 ms | **2.12x** | 432 ms | 736 ms | 1.8x | 895 ms |
| 2020 day 18 | 23 | 10.32 s | 9.38 s | 943 ms | 450 ms | 262 ms | 189 ms | **5.00x** | 489 ms | 1.43 s | 3.2x | 995 ms |
| 2021 day 15 | 41 | 6.77 s | 4.76 s | 2.01 s | 861 ms | 262 ms | 599 ms | **3.35x** | 487 ms | 2.50 s | 2.9x | 1.41 s |

Old against new, "sw net / lean net":

| day | section 3 | now | sw net, then | sw net, now |
|---|---:|---:|---:|---:|
| 2024 day 2 | 2.9x | 2.12x | 289 ms | 304 ms |
| 2020 day 18 | 7.9x | 5.00x | 1.57 s | 943 ms |
| 2021 day 15 | 3.2x | 3.35x | 1.53 s | 2.01 s |

- **A cached library load is 0.43-0.49 s**, against 2.3-9.4 s uncached and Lean's 0.26 s. So
  with the cache as our `.olean`, the load gap is about 1.7-1.9x, not 9-36x.
- **Counting a warm library load, a day's whole check is 1.8-3.2x Lean's file time**, against
  7-24x in section 3's "load counted" reading.
- Net of loading the picture is mixed: day 18 improved (7.9x to 5.0x), day 2 changed little
  (the ratio moved because Lean's own time did: 99 ms then, 143 ms now), day 15 is slightly worse.
  **I would not read the day 15 change, or the day 2 one, as real**: `sw net` is a difference of two
  medians of 3 runs each, so it carries both runs' noise, and day 15's "sw load" fell by 1.1 s
  between the two measurements (5.85 s to 4.76 s) while its "sw check" fell only 0.6 s.
- Lean's file times also moved between runs (day 2: 360 to 405 ms; day 15: 734 to 861 ms), a
  guide to the noise from load.

Caveats:

- **Load was high and uneven.** The 5-minute load was 16-19 at the start of the timing (the
  brief's bar is under 15; it fell to 15.2 while waiting and then rose to 19 as the bench began, from
  other lanes) and 7.5-13 at the end. Section 3 ran at load 7-10. Both sides are slowed by
  load but the Stitchwort side, which is longer, picks up more noise.
- 3 runs per median (as SW-4608), so a figure's error is easily 10-20%. Treat the ratios as
  to one significant figure.
- The "sw check" figure is still `--no-cache`: a cached check of the day's own theorems would
  measure the cache, not the checker, so it is not run. The fair whole-run reading is the
  "sw net + cached load" column, which assumes the library part and the day's own part add.
- **Lean version**: the `.#compare` shell's Lean is still 4.34.1. `flake.lock` pins nixpkgs at
  `7fd4004d` (lastModified 1791734076), which has `lean4` 4.34.1; current nixpkgs has 4.35.0.
  Matching it means updating the flake's nixpkgs input, which moves every other tool in the
  dev shell, for a comparison that a minor Lean version barely changes. Not done; section 3's
  run was on 4.34.1 as well (the README's "Lean 4.34.1"), and so is this one.

## Rerun, 25 Nov (SW-4806)

Sonnet lane SW-4806, 25 November 2026, 11:40-12:00, for Matt's "it would be quite interesting
to see how we compare now". `lane/SW-4806` at `main` as of `9375ccb14` (after the read-back
fixes, SW-4609 and the parallel check of D3742). Measurement only, same method as sections 3
and 4 and the 22 Nov rerun. Marks as above. "Then" is 22 Nov (section 2.1, the rerun section),
"now" is today. Raw data, small, in [`SW-4608/`](SW-4608/) (`*-2511.csv`).

### In plain words

**Where we stand.** On the one thing we can compare like for like, **we are now level with
Rocq and a long way ahead of the Lean files** *on the 31 sampled slice 1 formatter theorems*:
their elaboration plus kernel time is 838 ms, against 6.7 s for Lean's net time and 0.9 s for
Rocq's, so 0.13x Lean and 0.94x Rocq, where on 22 Nov it was 0.5x and 3.7x **[measured]**.
That table counts only our theorems' own time inside a whole check, while the Lean and Rocq
files are self-contained ports with the supporting lemmas as `axiom`s (their cost is partly
the cut-down definitions), so it flatters us: **do not read it as "faster than Lean"**. What
it does show is that the slow proofs it was sampling (`unaryHung` 2.2 s to 0.26 s, batch A
2.3 s to 0.30 s) are no longer slow. The whole formatter, cold, is **107 s on one worker
(252 s on 22 Nov) and 39 s with the default workers** **[measured]**, 2.4x and 6.5x faster.

**The firmer comparison has not moved.** Against Lean on the three AoC days, net of loading,
we are **3.2x, 5.4x and 3.1x** Lean's time (22 Nov: 2.1x, 5.0x, 3.4x; 21 Nov: 2.9x, 7.9x,
3.2x), and with a warm library counted a day's whole check is **2.2-3.8x** Lean's file time
(1.8-3.2x on 22 Nov) **[measured]**. These are within the noise of the earlier runs (3 runs
per median). So: **on proofs like Lean's own (small, explicit, AoC-sized) we are still about 3-5x
behind, and nothing since 22 Nov has changed that**; what changed is the very large proofs
of the formatter and the use of several cores. The AoC runs are one job (the bench uses
`--only`), so they can't show the parallel gain, and the read-back fixes target the 1-million-node
terms, which AoC days don't have.

**What this does and doesn't cover.** It covers three small AoC days and 31 formatter
theorems, one machine, three or five runs each. It does not cover a hand-written, idiomatic
Lean or Rocq development of the formatter (the ports copy our proof structure; automation
costs them time that explicit case arms cost us in lines); it counts our time for the
sampled theorems alone, not the definitions and lemmas they need; and the whole-formatter
number has no Lean or Rocq counterpart at all, since nobody has ported or checked the whole
slice there. Lean's and Rocq's libraries are precompiled, ours is rechecked from source on a
cold check (a cold formatter check is about 15 s library and 94 s the project's own, one worker).
Honest summary **[estimated]**: about 3-5x behind Lean on ordinary small proofs, roughly
level with Rocq on the formatter sample, and no longer far behind on the big ones; nothing
here shows us ahead of either on equal work.

### Method and machine

Same machine (Speedwell, M1 Pro, 10 cores), quiet: the 5-minute load was 3.8-4.2 at the start
of every run except where noted. Build: `lane/SW-4806` release binary, with the dev feature
for the AoC bench (`task bench:compare:proofs` rebuilt it, 3 min, before its timed part), the
plain `target/release/stitchwort` copy for the formatter runs. Lean 4.34.1 in the AoC bench
(the flake's, unchanged), Lean 4.35.0 and Rocq 9.1.1 (rocq-stdlib 9.0.0, the same store path
as 22 Nov) from nixpkgs for the slice 1 files, hyperfine 2.0.0, `-N --warmup 1 --runs 5`.
**The empty files:** Lean's `Empty.lean` (234 ms now, 247 ms on 22 Nov); Rocq's `EmptyStd.v` with
the batch files' `Require` line (158 ms; the 22 Nov file wasn't kept, so I used the
Pilot's require line: 154 ms then).

### Part 2a: three AoC days against Lean

`nix develop -c task bench:compare:proofs -- --runs 3`, medians, 5-minute load 3.8 at the
start of the build and 4.1 at the end **[measured]**. **One job:** each `sw` run is
`check --no-cache <namespaces> --only <theorems>`, and `check` forces one job for `--only`
("one job: --only checks part of a namespace", seen with `--timings` on the day 2 command; the
code in `crates/cli/src/main.rs` says the same, and `--no-cache` alone would also keep one job
unless `PARALLEL_NO_CACHE`), so the default workers don't change the bench **[measured]**.

| day | theorems | sw check | sw load | sw net | lean file | lean load | lean net | sw net / lean net | sw load (cached) | sw net + cached load | that / lean file | lake build, cold |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 17 | 2.52 s | 2.23 s | 293 ms | 355 ms | 262 ms | 93 ms | **3.15x** | 481 ms | 774 ms | 2.2x | 890 ms |
| 2020 day 18 | 23 | 9.29 s | 8.21 s | 1.08 s | 462 ms | 262 ms | 200 ms | **5.42x** | 685 ms | 1.77 s | 3.8x | 993 ms |
| 2021 day 15 | 41 | 5.82 s | 4.27 s | 1.55 s | 757 ms | 262 ms | 495 ms | **3.13x** | 545 ms | 2.10 s | 2.8x | 1.30 s |

Then and now (21 Nov = section 3, 22 Nov = the rerun):

| day | sw net / lean net: 21 Nov | 22 Nov | **25 Nov** | sw net: 21 Nov | 22 Nov | **25 Nov** | that / lean file: 22 Nov | **25 Nov** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 2.9x | 2.12x | **3.15x** | 289 ms | 304 ms | **293 ms** | 1.8x | **2.2x** |
| 2020 day 18 | 7.9x | 5.00x | **5.42x** | 1.57 s | 943 ms | **1.08 s** | 3.2x | **3.8x** |
| 2021 day 15 | 3.2x | 3.35x | **3.13x** | 1.53 s | 2.01 s | **1.55 s** | 2.9x | **2.8x** |

- **No real change since 22 Nov.** "sw net" moves between 0.29 and 0.30 s, 0.94 and 1.08 s,
  1.55 and 2.01 s: the same spread as between the two earlier runs. The ratio of day 2 moved
  mostly because Lean's net time is a difference of two small numbers (93 ms now, 143 ms then).
  Day 18's "sw check" went 10.3 s to 9.3 s and day 15's 6.8 s to 5.8 s, but their "sw load" fell
  by the same amount (9.4 to 8.2 s, 4.8 to 4.3 s): library checking is a little faster, the
  days' own theorems are not.
- Cached library load 0.48-0.69 s (22 Nov 0.43-0.49 s): slightly worse on day 18, within noise.
- Lean 4.34.1 as before; the file times moved 5-12% across the runs, the noise guide.

### Part 2b: slice 1 sample against Lean and Rocq

Lean and Rocq: `hyperfine -N --warmup 1 --runs 5` on the SW-4537 files (copied to a scratch
folder), mean wall, load 3.8 **[measured]**. Ours: the sum of each sampled theorem's own
elaboration plus kernel time from the cold `STITCHWORT_JOBS=1 check --no-cache --timings=all` of
`tools/fmt` (below), picked by the same declaration names as before
([`slice1-sw-per-theorem-2511.csv`](SW-4608/slice1-sw-per-theorem-2511.csv); `then_ms` is
22 Nov's `slice1-sw-per-theorem.csv`; the three theorems inside a mutual group take the
group's row, as then, which reproduces the old 3,314 ms total exactly). All 31 found
**[measured]**. `parse_timings.py` wants `STEP_PHASES=1` output, which I didn't set, so the
rows were picked with a few lines of Python from the same table. Net = file minus the empty
file (Lean 234 ms, Rocq 158 ms).

| file (theorems) | Lean | Lean net | Rocq | Rocq net | ours, then | **ours, now** | now / Lean net (then) | now / Rocq net (then) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Pilot (3) | 415 ms | 181 ms | 241 ms | 83 ms | 85 ms | **25 ms** | **0.14** (0.4) | **0.30** (1.0) |
| Batch A (7) | 956 ms | 722 ms | 384 ms | 226 ms | 2,308 ms | **300 ms** | **0.42** (3.0) | **1.33** (10) |
| Batch B (7) | 1,559 ms | 1,325 ms | 419 ms | 261 ms | 395 ms | **268 ms** | **0.20** (0.3) | **1.03** (1.5) |
| Batch C (13) | 4,597 ms | 4,363 ms | 460 ms | 302 ms | 475 ms | **243 ms** | **0.06** (0.1) | **0.80** (1.6) |
| Reserve (1) | 342 ms | 108 ms | 178 ms | 20 ms | 51 ms | **1 ms** | **0.01** (0.5) | **0.05** (2.0) |
| all 31 | 7,869 ms | 6,699 ms | 1,682 ms | 892 ms | 3,314 ms | **838 ms** | **0.12** (0.5) | **0.94** (3.7) |

Lean and Rocq's own times reproduce 22 Nov's within 2-9% (Lean: 452, 1,021, 1,695, 4,735,
350 ms then; Rocq: 236, 377, 415, 454, 179 ms), so the toolchains and machine are comparable.

- **Batch A, then 2.3 s, is now 0.30 s**: `unaryHung` 2,223 to 258 ms, the rest of the batch
  about 40 ms. Our per-theorem times fell for the formatter proofs the read-back work touched.
- **Without the large theorems the picture is the same**: the small ones are already ms-level
  (`homeStands` 354 to 258 ms is now the largest of the 31 after `unaryHung`).
- **Caveats are those of section 4**, and they all lean our way: ours counts the theorems
  alone, their files count definitions and (some) support; automation costs them; both
  startups included for them, none for us. The table says we are no longer slow on this
  sample, not that we are faster than Lean on equal work.

### Context: the whole formatter, cold and library-cached

`tools/fmt` from its folder, release binary, 150 project + 72 library files; `/usr/bin/time -l`
**[measured]**. The 5-minute load (the middle `uptime` figure) is read at the start of each run. The last two runs started with load raised by my own earlier runs (the auto run
used ~149 CPU-s in 39 s), not by other work.

| run | wall | user / sys | peak RSS | 5-min load at start | 22 Nov |
|---|---:|---:|---:|---:|---|
| 1 worker, `--no-cache --timings=all` | **106.8 s** (checker's own clock 106.0 s) | 104.7 s / 1.0 s | 1.40 GB | 3.8 | 387 s (252 s plain, 3.25 GB) |
| 1 worker, `--no-cache` | **109.7 s** | 108.0 s / 1.2 s | 1.40 GB | 3.7 | 252 s |
| auto workers (default), `--no-cache` | **38.6 s** | 148.7 s / 2.6 s | 4.63 GB | 4.2 | not available |
| 1 worker, library cached, `--no-project-cache`, warming run (writes the library's cache) | 142.3 s | 121.7 s / 1.6 s | 1.21 GB | 5.1 | |
| 1 worker, library cached, `--no-project-cache` | **94.1 s** | 93.2 s / 0.8 s | 1.38 GB | 7.5 (own runs) | |

- **2.3x faster on one worker (252 to 110 s), 6.5x with auto workers (39 s)**, and a warm library saves
  about 15 s of that (94 against 110 s).
  Memory fell from 3.25 to 1.4 GB on one worker; auto uses 4.6 GB (several workers, each
  with their own state). The auto run's speedup over one worker is 2.8x on 10 cores (`auto` is the
  cores, at most 8, one per 2 GB of memory), so the critical path of the
  namespace graph is not the limit yet, but something is: user time rose from 108 to 149 s
  **[measured; the reason is not investigated]**.
- **The timings table no longer costs anything**: 106.8 s with `--timings=all` against
  109.7 s without, sys 1.0 s against 123 s on 22 Nov (item 2 of section 2.3 is fixed).
- **Library-cached with auto workers is not measurable**: `--no-project-cache` forces one job
  ("`--no-project-cache` writes no namespace entries"), and a normal cached check would need
  the project's own cache entries removed, which the docs don't describe except by that
  option. Skipped, as the brief allowed.
- The 22 Nov figure for the whole formatter was taken before the read-back work and the
  parallel check, from `lane/SW-4608` at `4a07c90fc`: the 252 s and 387 s are from there.
- **Where the time is now** (declaration rows, 13,118 against 13,103 then): elaboration 84.2 s,
  kernel 20.0 s (218.6 and 40.7 s then); the slowest declaration, `followsFieldsAt`, is 3.5 s
  (3.4% of declaration time) against `standsEachFile`'s 32.5 s (12.5%) then, and
  `standsEachFile` is now 11 ms. The slowest 10 declarations are 15.8% of the time (32.0%
  then), 63 are 37.5% (50%), 655 are 72.5% (73.8%): the time is much flatter, now spread
  over the parser's `Follows…` proofs, std's `Parse.runFrom…Tree` lemmas and the
  read-back proofs.

### Not comparable, or not done

- **Small differences from 22 Nov**: Lean is 4.35.0 for the slice 1 files and 4.34.1 in the AoC
  bench (as before); the Rocq empty file was recreated; the `--timings=all` run lacks
  `STITCHWORT_STEP_PHASES=1`, so no step table (the phase split above is from the declaration rows).
- 3 runs for the AoC medians and 5 for hyperfine: the figures carry 5-10% noise, ratios to
  two significant figures at most. One run each of the formatter timings; the 1-worker plain
  and timings runs agree to 3%.
- Our slice 1 time is still only the sampled theorems inside a whole check, so "0.94x Rocq"
  compares slices of different content. A like-for-like port of one namespace is still the fair
  next step (section 4's last paragraph).
- Not run: the AoC `--no-cache` days at auto workers (the bench's `--only` forces one job,
  so not applicable), the library-cached run at auto workers (above), a profile.

## Rerun with the fixed bench (SW-4810)

Sonnet lane SW-4810, 25 November 2026, about 12:50, `lane/SW-4810` (bench changes only; the
checker is `main` at `d7cf7913b`). Why the old bench was wrong:
[SW-4809](SW-4809-small-proof-profile.md). Changes: "sw net" is the day's own units' elaboration
plus kernel time from `--timings=all`'s unit table (not a difference of wall times against a
probe file that missed std files the day loads); the binary is built without the dev features;
a new column is the whole day, `check --no-project-cache`, library cache warm (our counterpart
of Lean's `.olean`); hyperfine's JSON is read in either format and the bench stops on a
missing key. Method: `bench/compare/lean-proofs/README.md`. Marks **[measured]**.

`nix develop -c task bench:compare:proofs -- --runs 3`, medians, Lean 4.34.1, hyperfine 1.21
(the flake's). The 5-minute load was 4.6 at the end of the run (3.7-4.2 before it; the 1-minute
figure was 9.8 at the end, so another process was busy for part of it, which may explain Lean's
empty-file time of 288 ms against 262 ms on SW-4806's run). The "sw net" figures come from one
`--timings=all` rerun of each day after the timed run (a first version of the bench counted the
`library files` summary row; fixed, and the timed columns don't depend on it).

| day | theorems | sw check (cold) | **sw net** | lean file | lean load | lean net | **sw net / lean net** | sw check, library cached | that / lean file | lake build, cold |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 17 | 2.64 s | 119 ms | 406 ms | 288 ms | 118 ms | **1.01x** | 721 ms | 1.8x | 896 ms |
| 2020 day 18 | 23 | 9.63 s | 132 ms | 501 ms | 288 ms | 213 ms | **0.62x** | 800 ms | 1.6x | 1.10 s |
| 2021 day 15 | 41 | 6.22 s | 433 ms | 861 ms | 288 ms | 573 ms | **0.76x** | 1.18 s | 1.4x | 1.51 s |

Then (SW-4806, 25 Nov morning, the old bench) and now:

| day | sw net: then | **now** | sw net / lean net: then | **now** | whole day, library cached / lean file: then | **now** |
|---|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 293 ms | **119 ms** | 3.15x | **1.01x** | 2.2x | **1.8x** |
| 2020 day 18 | 1.08 s | **132 ms** | 5.42x | **0.62x** | 3.8x | **1.6x** |
| 2021 day 15 | 1.55 s | **433 ms** | 3.13x | **0.76x** | 2.8x | **1.4x** |

- The "then" figure for the last pair is the old "sw net + cached load": a sum of two
  separately timed runs. "Now" is one timed run of the whole day with the library cached, so it
  includes the library index, project scan and core (about 0.5 s together, SW-4809).
- Our own time on the days' theorems is 119, 132 and 433 ms, within 1-2 ms of SW-4809's
  profiled 104-124, 123 and 458 ms, so the two lanes agree.
- A cold check (library rechecked from source) is unchanged, 2.6-9.6 s: it is the library.

**Where we stand against Lean:** on the proofs themselves we are level with Lean (0.6-1.0x its
time on the same theorems), and a whole day with the library cached takes 1.4-1.8x Lean's time
for the file, the gap being start-up we pay on every check (library index, project scan, core);
cold, with the library rechecked from source, we are 6-19x behind **[measured]**; one machine,
3 runs each.

## Rerun after the start-up fixes (SW-4818)

Sonnet lane SW-4818, 25 November 2026, 14:54-14:58, `lane/SW-4818`, on `main` at `ded1b942b`
(which has SW-4812's std name index cache, SW-4813's project scan cache and SW-4820's skipped
fill) with the bench changes Fable's review asked for (SW-4816 findings 3, 4, 8): "sw net" is a
median of 5 runs, every figure carries its runs' range, every ratio is a range, user and system
CPU time are recorded on both sides, and two new rows time the floor (see below). Method and what
each net leaves out: `bench/compare/lean-proofs/README.md`. Marks **[measured]**.

`nix develop -c task bench:compare:proofs -- --runs 5`; medians with min-max in brackets; Lean
4.34.1, hyperfine 1.21. **Load:** the 5-minute average was 5.97 when the bench started (the
1-minute 2.6, falling from 16 when the lane began) and 4.68 at its end (1-minute 3.7); I waited
for it to fall below 6, which it did only just. Nothing else of mine ran meanwhile.

| day | theorems | sw check (cold) | **sw net** | of it Aoc.Common | lean file | lean load | lean net | **sw net / lean net** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 17 | 2.43 s (2.34-2.58) | 104 ms (102-109) | - | 352 ms (346-362) | 258 ms (244-260) | 93 ms (86-118) | **1.11x (0.86-1.28x)** |
| 2020 day 18 | 23 | 8.55 s (8.32-9.04) | 116 ms (111-121) | - | 476 ms (459-519) | 258 ms (244-260) | 218 ms (199-275) | **0.53x (0.40-0.61x)** |
| 2021 day 15 | 41 | 5.66 s (5.56-5.74) | 435 ms (433-453) | 258 ms (254-259) | 769 ms (744-803) | 258 ms (244-260) | 510 ms (484-558) | **0.85x (0.78-0.94x)** |

| day | sw cached, one job | that / lean file | **floor, one job** | **floor, default jobs** | lake build, cold |
|---|---:|---:|---:|---:|---:|
| 2024 day 2 | 469 ms (467-475) | **1.33x (1.29-1.37x)** | 187 ms (179-189) | 193 ms (185-195) | 783 ms (776-881) |
| 2020 day 18 | 554 ms (547-565) | **1.16x (1.05-1.23x)** | 193 ms (183-197) | 202 ms (201-209) | 994 ms (982-999) |
| 2021 day 15 | 942 ms (908-950) | **1.22x (1.13-1.28x)** | 406 ms (393-426) | 382 ms (380-395) | 1.30 s (1.29-1.31) |

User + system CPU time (hyperfine's means over the 5 runs):

| day | sw cached: wall | CPU | lean file: wall | CPU | lean load: wall | CPU | floor (default jobs): wall | CPU |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 469 ms | 431 + 37 ms | 352 ms | 465 + 146 ms | 258 ms | 134 + 116 ms | 193 ms | 156 + 33 ms |
| 2020 day 18 | 554 ms | 500 + 50 ms | 476 ms | 821 + 171 ms | 258 ms | 134 + 116 ms | 202 ms | 165 + 35 ms |
| 2021 day 15 | 942 ms | 869 + 57 ms | 769 ms | 1.46 s + 232 ms | 258 ms | 134 + 116 ms | 382 ms | 337 + 44 ms |

- **The floor** is `check` of the day's namespaces (every theorem, nothing to check) with every
  cache warm: what any check costs after an edit elsewhere. **Default jobs** is the same command
  with `STITCHWORT_JOBS` unset (auto). It matches one job within noise (193 against 187 ms, 202
  against 193, 382 against 406): with nothing changed the skipped fill of SW-4820 leaves one
  job's work, as intended, so there is no default-jobs penalty any more, and no gain either.
  The like-for-like command (`--only`, `--no-project-cache`) is always one job, so **a
  default-jobs run of the same work is not measurable with this bench**; the floor is the
  only default-jobs figure here.
- Lean uses several threads: its CPU time (611, 992 ms and 1.69 s) is 1.3-2.2x its wall time. Ours
  on one job is 0.9-1.0x. On CPU time we are below Lean's: 468, 550 and 926 ms against 611, 992 ms
  and 1.69 s, even though Lean's wall time is lower **[measured]**.

Then (SW-4810, 3 runs, before SW-4812/4813/4820) and now:

| day | sw net: then | **now** | sw net / lean net: then | **now** | whole day, library cached: then | **now** | that / lean file: then | **now** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 day 2 | 119 ms | **104 ms** | 1.01x | **1.11x (0.86-1.28)** | 721 ms | **469 ms** | 1.8x | **1.33x (1.29-1.37)** |
| 2020 day 18 | 132 ms | **116 ms** | 0.62x | **0.53x (0.40-0.61)** | 800 ms | **554 ms** | 1.6x | **1.16x (1.05-1.23)** |
| 2021 day 15 | 433 ms | **435 ms** | 0.76x | **0.85x (0.78-0.94)** | 1.18 s | **942 ms** | 1.4x | **1.22x (1.13-1.28)** |

- The proofs' own time did not change, as expected (the fixes are all start-up): "sw net" is 104,
  116 and 435 ms against 119, 132 and 433 ms, within the runs' ranges of 3-10 ms. The movement of
  the ratio is Lean's side: its empty-file time is 258 ms against 288 ms then, and its files'
  times 352, 476 and 769 ms against 406, 501 and 861 ms, so this run's machine was quieter (the
  load figures above against SW-4810's 4.6), or Lean's wall time varies more than a 3-run median
  shows. Both runs' figures are inside each other's ranges for day 2's ratio only.
- The whole day with the library cached went from 721/800/1180 ms to 469/554/942 ms, 35%, 31% and
  20% less, which is the three fixes' saving (about 250 ms on a small day, 240 on day 15)
  **[measured]**; Lean's file times fell 9-13% over the same two runs, so about three quarters
  of the change is ours.
- A cold check, the library rechecked from source, is 2.4-8.6 s against 2.6-9.6 s: slightly
  faster, within noise of the machine's state.

**Not comparable, plainly.** (1) Day 15's "sw net" includes 258 ms of `Aoc.Common...` units, which
`--only` checks whole; the Lean file ports about 25 of its lemmas. Without that part day 15's net
is about 177 ms (0.35x), with all of it 0.85x; the real figure is between. Day 15's ratio is the
least reliable of the three for that reason. (2) Our "net" is the sum of one job's unit timers
and Lean's is wall time on several threads; on CPU time, Lean's is larger (above). (3) Lean's
net also includes compiling its `def`s; ours has no such step. (4) The floor rows check every
theorem of the namespaces from cache, the other rows only the ported ones. (5) The ranges
combine runs that happened at different instants on a shared machine; they show the spread, and
not a confidence interval.

**Where we stand against Lean, in plain words.** On the proofs themselves we are about level
with Lean: 0.4-1.3x its time on the same theorems, depending on the day and how the runs fall
(0.4-0.6x on day 18, 0.8-0.9x on day 15, 0.9-1.3x on day 2), on our one thread against its
several. For a whole day with the library cached we are now 1.1-1.4x Lean's file time
(1.33x, 1.16x, 1.22x): behind by 78-173 ms, where it was 1.4-1.8x (240-320 ms) before today's
three fixes, so they took the gap to about half **[measured]**. Almost all that is left is
start-up, since a check with nothing to do takes 187-406 ms (day 15's is bigger) of the 469-942
ms. On CPU time, which the machine's load and Lean's threads do not distort in the same way,
we use less than Lean on all three days. Cold, with the library rechecked from source, we are 7-18x
behind (2.4-8.6 s against 0.35-0.77 s), and nothing here changes that. One machine, 5 runs each,
the load as above.
