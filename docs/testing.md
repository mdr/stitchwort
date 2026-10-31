# Testing

Stitchwort's guarantees are only as good as the compiler's correctness, so the tests have several layers. Each layer catches mistakes the others can't.

## Tiers

Tests are only useful while they aren't friction, so they run in four tiers, each with a time budget. The budgets assume the release test binaries are built (`task build:tests`) and are for this 14-core Mac. Run them through [Task](https://taskfile.dev) (`Taskfile.yml`; `task --list` shows the menu), inside `nix develop`.

| Tier | Command | Budget | When | What |
|---|---|---|---|---|
| lane | `task test:lane AREA=…` | under 10 s | while working, in a subagent lane | a handful of fast tests for one area (the map below) |
| merge | `task test:merge` | under 60 s | after every merge | rustfmt, then a broad smoke test: every lane area, a quarter of the accepted, rejected and soundness examples, every AoC day's answers, every example's hash snapshots, every extraction example's generated JS and `.d.ts` snapshots, the `goal_index` tests |
| daily | `task test:daily` | under 5 minutes | a daily checkpoint; `nix flake check` runs the same | rustfmt, clippy, every test with each corpus sweep on a fixed sample, the doctests, `builtins` in the debug profile, the board's tests |
| full | `task test:full` | tens of minutes | only when Matt asks | every test, every sweep over the whole corpus, the full-only tests |

`task test:lanes-nonempty` fails, naming the profile, if any `[profile.lane-*]` in `.config/nextest.toml` selects no tests (a filter that matches nothing passes silently; `lane-aoc` once did). It runs `cargo nextest list` (nothing is run) for each lane profile it finds in the file, so a new one is covered at once; it costs about 1 s per profile with the binaries built (about 13 s for all), so `task test:daily` runs it, not the merge tier (it is not part of `nix flake check`). A filter naming a binary that does not exist is already a nextest config error.

`task test:one -- FILTER` runs the tests matching a nextest filter (a name substring, or `-E 'binary(lsp)'`), at the daily sample. `task test:gate` is `nix flake check` (the daily tier in the Nix sandbox, plus a build from clean), and `task test:full:nix` builds `.#stitchwort-full` (the full tier in the sandbox; only when Matt asks).

### How a tier is chosen

Two things make a tier, and the tasks set both:

- **Which tests run** is a [nextest profile](https://nexte.st/docs/configuration/) of the tier's name in `.config/nextest.toml`, through its `default-filter` (a [filterset](https://nexte.st/docs/filtersets/)): `merge`, `daily`, `full`, and `lane-AREA` for each lane area. A filter on the command line is intersected with it (`task test:merge -- -E 'package(stitchwort-core)'`).
- **The CLI is built with native code**: the tasks and the flake pass `--features stitchwort-cli/native` (Taskfile.yml `TEST_FEATURES`), so that `crates/cli/tests/build.rs` tests `build --native`; the default `stitchwort` leaves Cranelift out.
- **How much of a corpus a sweep covers** is the environment variable `STITCHWORT_TIER` (`lane`, `merge`, `daily` or `full`; unset means `daily`), read by `stitchwort_driver::driver::tier()`. A corpus sweep (a test that checks every example, std file or AoC day) takes `tier_sample(items, daily_stride)`: a fixed sample, every `daily_stride`-th item in sorted order in the daily tier, every `4 × daily_stride`-th in merge and lane, and all of them in full. A test or part of one that only the full tier runs asks `full_tier(name)`, which prints what was skipped.

Both are needed: a profile can only include or leave out a whole test, and the sweeps are single tests whose cost is the size of the corpus. The profiles keep the lists of what runs in one file that nextest checks; the environment variable keeps each sweep's sample next to the code that knows what is in its corpus. A sweep's assertion about how much it covered (say, "more than 1,000 arguments named") scales with the sample, and is exactly the old one in the full tier.

What only the full tier runs: the AoC project in the std_library, rewind and check-cache comparisons, `a_check_cancelled_part_way_rewinds`, the bench `examples` benchmark (in `baseline`, and repeated in `repeat`), the whole corpus in each sampled sweep (below), and `rt`'s AoC sweeps `aoc_agrees` and `every_aoc_main_lowers` (36 to 38 minutes each in the daily tier on 31 Oct 2026; SW-839 is to give the daily tier a fast check of AoC lowering instead).

| Sweep | Daily share | Merge and lane share |
|---|---|---|
| `std_library` `lazy_loading_changes_nothing_*`, `driver` `check_cache` and `rewind` examples | every 8th file (and every 4th project) | every 32nd |
| `differential` `the_evaluators_agree_on_the_prelude_and_every_example`, `conv_shortcut`, `fmt_hashes` | every 4th | every 16th |
| `extract` `run_lines_*`, `random_inputs_*` | every 2nd | every 8th |
| `cli` `examples` (every folder), `cli` `check_cache` projects | all (projects: every 4th) | every 4th (projects: every 16th); all of those matching `EXAMPLES` when it's set |

When the daily tier grows past 5 minutes, cut it from nextest's own times (`target/nextest/daily/junit.xml`, or the `SLOW` lines): give the slowest sweep a larger stride, or move a test to full only, rather than re-running to see. The merge tier likewise (`target/nextest/merge/junit.xml`); on a loaded machine compare tests with each other, not with the budget.

**Sizes that depend on the tier.** Besides the sampled sweeps, the constant-stack tests scale with the tier: `n2b` `tail_calls_of_every_shape_run_in_constant_stack` runs 10 million iterations on a 64 MiB stack in daily and full, and 1 million on 20 MiB in merge and the lanes; `n3` `tail_applies_run_in_constant_stack` runs 1,000,000 tail applies on 64 MiB in daily and full, 250,000 on 18 MiB in merge and the lanes. The native crossing reserves 16 MiB of any stack (`HOST_ROOM` and `HELPER_ROOM`, `crates/rt/src/native_abi.rs`), so the smaller stacks leave 4 MiB and 2 MiB to run in, which a leak of 8 (or 16) bytes an iteration still overruns: the same point, with a tenth of the work.

### Memory

Several worktrees test on one 48 GB Mac at once, and a tier that runs away can lock the machine up (it did, 26 Oct 2026: the daily tier at about 50 GB). Three things bound it.

**A cap on every test task.** Each task that runs tests (`test:lane`, `test:merge`, `test:daily`, `test:full`, `test:one`, `test:affected`, the `snap:*` tasks, `guide:update`, `bench`) runs its command under `dev/memguard`. About twice a second it sums the memory of the command's whole process tree (the physical footprint on macOS, as `top` shows it; RSS on Linux), leaving out the compiler and linker when cargo builds first. Past the cap, it prints the cap, the total and the five biggest processes with their command lines (a nextest child's names its test: `…/deps/examples-… --exact accepted_examples_check`), kills the tree (SIGTERM, then SIGKILL two seconds later) and exits 137, so the task fails.

| Tier | Cap | Measured peak |
|---|---|---|
| lane | 3 GB | up to 0.7 GB (`aoc`, `hashes`, `examples`, `std`, `core`) |
| merge | 3 GB | 1.7 GB |
| daily, `test:one`, `test:affected`, `guide:update`, `bench` | 16 GB | over 16 GB when `lsp` `aoc_navigation_matches_check_index` (7.9 GB alone) and `resources` `running_out_at_any_point_only_ever_means_no_answer` (6.7 GB alone) ran together (31 Oct 2026); the second is now in `corpus-sweeps` (SW-921) |
| full, `snap:*` | 16 GB | not measured |

The peaks are from 26 Oct 2026; the lane and merge caps are about 1.5 to 2 times them. The caps are the `MEM_CAP_*` variables at the top of `Taskfile.yml`. `STITCHWORT_MEM_CAP_GB` overrides any of them for one run (`STITCHWORT_MEM_CAP_GB=24 task test:full`; `0` for no cap), and `STITCHWORT_MEM_REPORT=1` prints the peak and the biggest processes at the peak when the command ends, for measuring a tier. A kill means a test regressed, or the cap is out of date: look at the named test before raising the cap. `ulimit -v` is no use here (macOS doesn't enforce it), hence the polling.

**One corpus sweep at a time.** A corpus sweep checks every example, std file or AoC day (or its tier's sample) on a thread pool of its own (`par_map` in `crates/driver/src/driver.rs`). The sweeps are in the nextest test group `corpus-sweeps` (`max-threads = 1`, in `.config/nextest.toml`, for every profile), so no two sweeps' pools hold memory together; other tests run beside the one. A new test that runs `par_map` over a corpus belongs in the group's filter, unless its pool is small and the group would only make it wait: `extract` `generated_code_is_stable` (about 320 MB at its peak) runs beside the sweeps, since the group's chain of sweeps is the end of the merge tier and it would add its own 4 to 7 s to it. `cargo nextest show-config test-groups --profile daily` lists the members.

**The pools' size.** `par_map` runs `STITCHWORT_TEST_THREADS` threads (default: the cores, at most 8). A thread's stack is reserved, not used, so a thread costs what its session holds: about 10 MB in `cli` `examples`, about 50 MB in `hash_stability` `examples` (lane sample, 1 thread against 8). Set `STITCHWORT_TEST_THREADS=2` to shrink every sweep's pool.

**Daily and full are run only by the orchestrator, on a quiet machine**, never by a lane: they are the tiers with the large caps, and two of them at once, or one beside other worktrees' builds, can still fill the machine. Lanes run `test:lane` and the named tests they changed (`test:one`).

### Lane areas

`task test:lane AREA=…` runs the nextest profile `lane-AREA`. Each is a handful of fast tests, chosen so the whole run (with nix and nextest starting) stays under 10 s; the times are from 25 Oct 2026.

| AREA | Runs | Time |
|---|---|---|
| `syntax` | `stitchwort-syntax`: lexer, parser, layout, fuzzing | 6 s |
| `core` | `stitchwort-core` unit tests and the `kernel`, `hash`, `admission`, `opaque` and `trusted` tests; the driver's `nested_oracle` (nested data types against their mutual encoding, 50 cases) | 6 s |
| `elab` | `stitchwort-elab` unit tests, but for five slow `omega_search` ones | 4 s |
| `effects` | `ability_errors`, `empty_row_kernel`, and the quick `effect_runtime` tests of `rt` and `cli` | 3 s |
| `std` | the quick `std_library` tests (the loader, the index, cycles); not the sweeps | 3 s |
| `rt` | `stitchwort-rt` unit tests, `stitchwort-host` (the threads on mapped stacks), `tick_counts`, `machine` `library_tests_agree`, two quick `effect_runtime` tests, two quick `partial_handlers` tests, `live_run`, `linked` (the tables a `--native` executable carries) | 5 s |
| `js` | `stitchwort-js` unit tests and five quick `extract` tests | 4 s |
| `native` | `stitchwort-native`: the Cranelift spike (stage N0 of native-compilation.md) and stages N1 to N4 against the machine (`tests/n1.rs`, `n3.rs`: outputs, allocation traces, resource points, every error exit; `tests/n2b.rs`: frame sizing, tail-call shapes, error-exit traces; `tests/frames.rs`: the frame bound on both architectures; `tests/n4.rs`: handlers and every `-- run:` line of the effect examples; the ten-million-iteration tail test is left to the merge tier), that the generated code holds no host address (`tests/relocatable.rs`, stage S4 of standalone-executables.md), and the object `build --native` links (`tests/object.rs`, S5) | 7 s |
| `lsp` | six quick `cli` `lsp` tests (hover, formatting, goals, navigation) | 3 s |
| `goals` | `cli` `goal_index`: goals in `check --index` end to end, every lemma and printed goal pasted back and checked again (SW-918) | 10 s at load 30 (`lemmas_check_as_the_same_goal` 8 s) |
| `fmt` | `stitchwort-fmt` (not `repo` or `fuzz`) and the `cli` `fmt` tests | 2 s |
| `aoc` | six AoC days on their real input, by exact name (`aoc_answers`: `year2024_day02`, `04`, `07`, `year2025_day01`, `05`, `07`; the rest are for merge and up) | 2 s |
| `cli` | `cli` `session`, `keys_mode` (`run` in a pseudo-terminal), `run` but for its five slowest, and `stitchwort build`: `crates/standalone`, and `build` (with and without `--native`) but for the roguelike's two tests (merge runs those too) | 12 s at load 70 (`build --native`'s `set_nat` the longest) |
| `hashes` | `hash_stability` `examples`, `projects` and `prelude`; `NAME=` keeps only the examples whose names contain it | 6 s |
| `examples` | `cli` `examples`: a quarter of each folder, or with `NAME=synonym` every example whose name contains it | 7 s (2 s with `NAME`) |
| `bench` | the `stitchwort-bench` unit tests and the quick `check_work` tests | 6 s |
| `web` | the quick `stitchwort-web` unit tests (not the playground, guide or AoC sweeps) | 3 s |

A lane that needs more than its area runs `task test:one -- NAME` for the tests it changed. The browser and VS Code tests are separate: `task test:browser`, `task test:vscode` and `task test:colour` (the playground tokenizer's colouring tests, run by node with no browser).

### Snapshots and generated text

`task snap:examples NAME=…` and `task snap:hashes NAME=…` update the error-message and hash snapshots (every example when `NAME` is unset), then list the changed `.snap` files for review; `task snap:one -- FILTER` does the same for any tests. `task guide:update` regenerates the language guide's quoted blocks.

| Layer | Where | What it catches |
|---|---|---|
| **Example programs** | `examples/`, run by `crates/cli/tests/examples.rs` | Whether the language behaves as designed, end to end. Rejections must have the expected error code, and error messages are snapshot-tested. This is the main suite, and it's readable without knowing the implementation. |
| **Kernel tests** | `crates/core/tests/kernel.rs` | The kernel on hand-built core terms, including terms the elaborator never produces. The examples can't do this: they only feed the kernel the elaborator's output, and when the elaborator rejects something first, the kernel never runs. |
| **Kernel fuzzing** | `crates/core/tests/fuzz.rs` | That the kernel never panics. Thousands of random, mostly ill-formed terms must each be accepted or rejected with a diagnostic. Alone: `task fuzz:kernel`. |
| **Syntax fuzzing** | `crates/syntax/tests/fuzz.rs` | That the lexer and parser never panic. 20,000 mutated example programs and random token soups (or more with `FUZZ_CASES`) must each lex and parse to a module or diagnostics. Fixed seed, so a failure prints the input and the generator state to reproduce it. Alone, at another count: `task fuzz:syntax CASES=100000`. |
| **Formatter fuzzing** | `crates/fmt/tests/fuzz.rs` | That the formatter never panics and never reports its own `Internal` error on mutated example programs and random token soups (the generator and seed of the syntax fuzzer), and that formatting its output again changes nothing. 50,000 cases by default. Alone, at another count: `task fuzz:fmt CASES=5000`. |
| **Elaborator fuzzing** | `crates/driver/tests/fuzz_elab.rs` | That a full check of a mutated example (token-level edits: swapped names, changed numerals, deleted, duplicated and swapped lines, dropped annotations) never panics, never reports `E-INTERNAL`, never lets the kernel's `E-MALFORMED` or `E-TYPE-MISMATCH` through to the user, finishes (a step limit, and a 60 s watchdog that names the case), and agrees between a cold and a warm check cache (every tenth case). 400 cases in the daily tier (about 20 s; four times as many in full), not in merge or the lanes. A failure prints the oracle, case, seed and generator state, and saves the input to `target/fuzz-elab/<seed>-<case>.sw`. `FUZZ_CASES`, `FUZZ_SEED` and `FUZZ_CORPUS=1` (the unmutated examples, to calibrate the oracles) control it; `task fuzz:elab CASES=2000 SEED=0x2 [CORPUS=1]` runs it alone in the release profile under the memory guard. |
| **Unit tests** | `#[cfg(test)]` modules (lexer, parser, unifier, rendering) | Internal algorithms on cases the examples don't happen to reach: pattern unification's occurs and scope checks, pruning, layout columns, … |
| **Differential tests** | `crates/cli/tests/extract.rs` | That extracted JS agrees with the reference evaluator, on the `-- run:` lines and on 100 random inputs per export. Where an export has a precondition, random inputs that fail it must be refused with `StitchwortInputError`, as must the `-- rejects:` lines. |
| **Generated code** | `crates/cli/tests/extract.rs` | Snapshots of the generated JS and `.d.ts` of every extraction example (`generated_code_is_stable`, in the merge tier: it checks the examples on `par_map`, about 4 s), and the `.d.ts` must type-check with `tsc` (`the_declarations_type_check`, daily: `tsc` takes about 10 s and checking the examples one by one 18 s). Decoders are tested against cyclic inputs, getters and later mutation; text decoders against the text proposal's boundary cases (lone surrogates, NUL, noncharacters, one scalar per `Char`) and both round-trip laws. Long inputs: tail calls to the same function must be loops, and running out of stack a `StitchwortResourceError`; values a million deep must cross the boundary both ways. Awkward names (`tag`, `__proto__`, primes, JS globals and reserved words, the runtime's own names), and attributes choosing awkward tag keys, tag values and keys (quotes, backslashes, control characters, `"0"`, non-ASCII), are generated at random: every object must have its own key for each field, and the `.d.ts` must accept exactly what the module does. A metadata-only edit (`js.name` in an imported namespace) reaches the generated code whether that namespace comes from the check cache or not, and changes no hash (`crates/driver/tests/check_cache.rs`). |
| **Caching** | `crates/cli/tests/caching.rs` | That hashes ignore names and layout but change with anything depended on, that data types are nominal, and that test results are reused exactly until a dependency changes. |
| **Running `main`** | `crates/driver/tests/run.rs`, `crates/cli/tests/run.rs` | That `stitchwort run` prints exactly what the prelude's `IO.simulate` records for the same input, and follows the interpreter's contract: line endings, end of input, UTF-8, flushing, errors and exit codes. The CLI tests run the built command as a subprocess. |
| **`run` against `run --reference`** | `crates/cli/tests/run_reference.rs`, `crates/rt/tests/machine.rs` | That the fast runtime (`stitchwort run`, `crates/rt`) behaves as the reference evaluator, which is the oracle: every example `main` (three inputs each), the AoC mains on real and example inputs, the bench programs, `readLine`/`readAll` at the edges, and the `test`s of the examples, the AoC project and the library (about 1,100) have the same output and the same end. `E-RESOURCE` is reported alike, though not at the same point. The CLI tests run the built command. |
| **`run --js`** | `crates/cli/tests/run_js.rs` (needs `node`) | That `stitchwort run --js` prints and fails exactly as `stitchwort run` does: every example with a `main` (including the `Partial` ones) on three inputs, and `readLine`/`readAll` at the edges of the input (line endings, end of input, invalid UTF-8). Also: non-tail recursion over a 500,000-element list, running out of resources, and a missing `node`. |
| **REPL and playground** | `crates/cli/tests/session.rs`, `crates/web` | Evaluating and printing expressions, and `import` lines typed in that accumulate, natively and through the WebAssembly interface; running `main` with scripted input, an output budget and a limit on reading past the end of the input, with its output returned or streamed a line at a time; warnings returned apart from errors; and that every example in `web/index.html` checks and passes its tests, and every example of the language guide (`web/guide/`, the page's Guide) checks and passes its tests, with the failing test's output and the `.d.ts` it shows being what the compiler really gives. |
| **Browser tests** | `web/tests/browser.mjs` (not in `nix flake check`: see [Browser tests](#browser-tests)) | The playground page in headless Chrome: every example checks and passes its tests (the failing one shows its failure); the Check, Tests, Evaluate, JavaScript and Run tabs; warnings shown apart from errors; the JavaScript tab's two boxes shown in full; Run with scripted input, `E-NO-MAIN`, `E-OUTPUT`, `E-INPUT`; output appearing while a run is going; Stop, and the 15 s timeout, keeping what was printed; a fresh worker after a crash; the in-page compiler when the `Worker` constructor throws or the worker script is missing; the syntax colouring lining up with the text (highlights and spans, scrolled, after typing); the draft, input and tab kept across a reload; direct links (`#aoc/2025/day02`, `#example/safe-division`) opening, following the dropdown and falling back to the default; Tab and undo; resizing the editor by dragging; the layout at a phone's width. |
| **Benchmarks** | `crates/bench`, `bench/baseline.toml` | Performance regressions: work, allocations and memory that grew more than 10% against the recorded baseline, and (by hand only) time that grew more than 50%. See [Benchmarks](#benchmarks). |
| **Coverage** | `cargo llvm-cov --workspace --summary-only` | Which code no test reaches |
| **Mutation testing** | `cargo mutants` | Code that tests reach but don't really *check*. Each mutant is a small deliberate bug, such as replacing a condition with `true`. A "missed" mutant is a bug no test would notice. |

Random tests use fixed seeds, so every run tests the same cases and a failure can always be reproduced.

## Editing the standard library

The standard library (`crates/elab/src/std/**`) is embedded in the binary, so normally an edit to it needs a rebuild before `stitchwort` or a test binary sees it. To skip the rebuild, point the compiler at the source tree:

```sh
export STITCHWORT_STD_DIR=$PWD/crates/elab/src/std   # or: stitchwort --std-dir crates/elab/src/std run …
target/release/stitchwort run prog.sw              # sees the edited std; no cargo build
target/release/deps/std_library-<hash> loads       # an already built test binary, filtered
```

- Run binaries that are already built (`target/release/stitchwort`, `target/release/deps/<test>-<hash>`). `cargo run` and `cargo test` still rebuild the elaborator, because the embedded copy changed.
- The directory is read once, when a process first uses the library. Library files are every `.sw` file outside `core/`, so a new one is picked up; the core's files are read in the order the build lists (`core_files!` in `crates/elab/src/lib.rs`), so a new core file needs a rebuild.
- The caches stay correct: the check cache's keys hash each library file's text as read, and with the variable set the test-result cache's build fingerprint also hashes the library's text (`build_fingerprint` in `crates/driver/src/driver.rs`).
- An error in a library file names its path on disk (`…/crates/elab/src/std/Nat/Iterate.sw:12:3`), so an editor can jump to it.
- The language server reads the library when it starts: restart it after editing std.
- The hash snapshots (`hash_stability`) and `std_library` print which copy they use (`std from …` or `embedded std`). Snapshots taken with the variable set are of the edited library; rebuild and rerun without it before committing.
- Release builds, the WebAssembly playground and `nix build` use the embedded copy unless the variable or flag is set; WebAssembly never reads it.

Lanes working on std: set `STITCHWORT_STD_DIR` in the shell for the session, build `stitchwort` once, and iterate with the built binary.

## Running

The tiers are above; `task --list` has the rest. By hand, or for what has no task:

```sh
cargo nextest run --release --workspace --features stitchwort-cli/native --profile merge    # a tier without Task (set STITCHWORT_TIER to match)
cargo insta review                             # after changing an error message
cargo llvm-cov --workspace --summary-only      # coverage per file
cargo mutants --package stitchwort-core --test-workspace=true --jobs 6   # slow: minutes to an hour
task bench                                     # benchmarks against the baseline: about a minute
task test:gate                                 # nix flake check: the daily tier, as CI would
task test:browser                              # the playground in headless Chrome: about 35 s
```

### Hash dumps

To show what a change to the elaborator does to the declarations it accepts, dump every declaration's hash before and after it and diff the two. `hash_stability`'s ignored test `dump` loads the whole library and one project, and writes one sorted line per declaration (`path hash`, `data path hash` for types) to the file `HASH_DUMP` names:

```sh
HASH_DUMP=/tmp/aoc.txt cargo test --release -p stitchwort-driver --test hash_stability -- --ignored dump                               # std + aoc: about 45 s, 10,420 lines
HASH_DUMP=/tmp/rogue.txt HASH_DUMP_PROJECT=games/rogue cargo test --release -p stitchwort-driver --test hash_stability -- --ignored dump  # std + rogue: about 7 s
```

- `HASH_DUMP_PROJECT` is a project directory relative to the repository's root; `aoc` if unset.
- With `HASH_DEPS` set to a second path, it also writes each definition's direct references, one line per definition, to work out which changed hashes only follow from another.
- It runs on a thread with the command line's 64 MB stack, so a project loads as `stitchwort check` loads it (on the harness's default stack AoC ran out with `E-RESOURCE`, SW-906).
- The accepted examples' and extract examples' hashes are the `hashes` area's snapshots: `STITCHWORT_TIER=full` with `cargo insta test` shows every one that changed.

## The allocation trace

A bring-up tool for native compilation (`docs/proposals/native-compilation.md`, "Bring-up trace"): the machine can record every `alloc`, `reuse`, `inc`, `dec` and `free` of a constructor cell, so the machine's memory decisions can be read, and later compared with native code's, event by event.

- **Build.** It is the cargo feature `alloc-trace` of `stitchwort-rt` (`stitchwort-cli` forwards it). Release `stitchwort` is built without it: the hooks are empty `#[inline(always)]` functions, so the machine compiles to the same code. A feature rather than `cfg(debug_assertions)` because the tests run in release mode. The `stitchwort-rt` tests switch it on for themselves (a dev-dependency on itself).
- **Use.** `cargo run --release -p stitchwort-cli --features alloc-trace -- run prog.sw --alloc-trace prog.trace` (a hidden flag; it runs on the fast runtime only). In a test, `stitchwort_rt::alloc_trace::start()` before the run and `finish()` after give a `Trace` with `render()`, `leaks()` and `count("reuse")`. See `crates/rt/tests/alloc_trace.rs`.
- **Format.** One event per line: `alloc #3 tag=1 arity=2`, `reuse #3 tag=1 arity=2` (a unique cell refilled in place), `inc #3`, `dec #3`, and `free #3` straight after the last `dec`. Identities are numbered by first appearance, and an address freed and reused is a new identity, so two runs give the same text.
- **Not traced** yet: closures, partial applications, delays, texts and big numbers. Only constructor cells (`Fields`).
- **Checks.** Every `alloc` must have a `free` by the end of a run, including one that ends in an escaped `Fail`.

## Browser tests

**The WebAssembly float tests.** `crates/cli/tests/float_paths.rs` runs the float gate on the playground's bundle in `web/pkg`. When the bundle is missing or built from other sources, those tests skip (a pass), so lanes work without a web build. With `STITCHWORT_REQUIRE_WASM=1` they fail instead, naming `web/build.sh`; `task test:daily` sets it and builds `web/pkg` first when it is out of date. The merge tier leaves it unset.

`web/test.sh` builds the playground into `web/pkg/`, then runs `web/tests/browser.mjs` with Node: it serves `web/` itself (on a port the system picks), starts headless Chrome with a temporary profile, drives the page over the DevTools protocol, and stops Chrome at the end. Each test has a fresh tab with empty storage.

```sh
nix develop -c ./web/test.sh                   # build, then run them all
nix develop -c ./web/test.sh --no-build Run    # only tests whose names contain "Run"
nix build .#playground && nix develop -c node web/tests/browser.mjs --dir result   # test the Nix build
```

Chrome comes from the system: `$CHROME`, then `/Applications/Google Chrome.app` or Chromium on a Mac, then `google-chrome` or `chromium` on the `PATH`. Without it, the tests are skipped with a message (exit status 0). They're not part of `nix flake check`: Chrome isn't in the Nix build sandbox (nixpkgs' Chromium doesn't build on macOS), and one test waits out the page's real 15 s timeout, so they depend on the machine's speed. Only Chrome is tested, not Firefox or Safari.

No program is known to crash the compiler any more (its depth guards stop deep programs first), so the crash test serves a worker that checks a marked program with the engine's stack nearly used up, which overflows it inside the WebAssembly as deep programs once did.

## Benchmarks

`crates/bench` runs a fixed set of benchmarks (`--list` shows them): the example suite, evaluation (`lengths 400 3000`), text operations, running a `main` that prints 20,000 lines, generating JS, and checking programs that are known to be slow or near the resource limits (number patterns: one of 200, a 256-row table, one of 10^30, a 1,000-row table, dependent arguments, several columns; long list equations, long sums, deep nesting). Each checks its own result, so it can't get faster by doing something else.

Each benchmark is measured in two ways:

- **Counts**, the regression signal. *Steps* are evaluation steps, from the resource budget (`Budget::total_work`). *Visits* are levels of the recursive passes that aren't evaluation, like the elaborator and type checker (`Budget::total_visits`). *Allocations* and *peak heap* come from a counting allocator in the benchmark binary. They depend only on the program and the compiler, not on how busy the machine is, so they're identical on every run (checked: separate processes give identical numbers, and `crates/bench/tests/repeat.rs` checks two runs in one process) and the threshold can be tight: **+10%**. Two things keep them so: hash maps hash the same on every run (`stitchwort_core::collections`; `clippy.toml` disallows the standard library's, whose random hashing now and then changes when a map grows), and the benchmarks' counterexample searches stop at their count of inputs, never at their time limit (`Elaborator::untimed_counterexamples`). They don't see everything: a loop that neither evaluates, recurses through a guarded pass nor allocates costs time without changing them.
- **Time**, the median of 5 runs of a release build. It's what matters in the end, but other builds on the same machine make it noisy, so its threshold is loose (**+50%**, and at least 20 ms more) and it's never checked automatically.

```sh
cargo run --release -p stitchwort-bench                  # run, compare with the baseline; fails on a regression
cargo run --release -p stitchwort-bench -- check-number  # only benchmarks whose names contain this
cargo run --release -p stitchwort-bench -- --no-time     # counts only, one run each: about 10 s
cargo run --release -p stitchwort-bench -- --update      # record this run as the baseline
```

The baseline is `bench/baseline.toml`: one table per benchmark, so a change reads well in a diff. Update it deliberately: after an improvement (the comparison says so, and the baseline should keep it), or after a regression that's worth its cost, saying why in the commit. Record times on a quiet machine. The example suite and JS generation read `examples/`, so the baseline records a fingerprint of those files, and when they change the counts aren't compared (a note says so) until the baseline is updated.

The test tiers run the counts part (`crates/bench/tests/baseline.rs`): one run of each benchmark, failing if a count grew past the threshold. Being deterministic, it can't fail by chance. The `examples` benchmark checks the whole example corpus on one thread (allocations are counted per process), over a minute and most of the test's time, so only the full tier compares its counts; the daily tier compares the rest, in about 30 s. It's skipped in debug builds (`cargo test`), where the benchmarks are slow and allocation counts may differ from the release build's.

## Writing tests

- **For a language feature, start with example programs.** Add an `accept/` example, and for each way it can go wrong, a `reject/` or `soundness/` example declaring the error code it expects. Pair every rejection with a nearby acceptance, so a check can't pass by rejecting everything.
- **For a kernel rule, also add a kernel test on core terms.** Prove that the kernel enforces the rule *by itself*, not just that the elaborator does.
- **The kernel must never panic.** If a malformed term can make it panic, that's a bug: it should be an `E-MALFORMED` error.
- **For a new export shape or codec, add an extraction example.** The random differential test then exercises it automatically.
- **Before trusting a new test, break the code it tests and watch it fail.** `cargo mutants` does this systematically.

## Where the time went

25 Oct 2026, when the tiers came in (times under load, from the gate's nextest log, so relative): the slowest sweeps each built an eager session (the whole library, about 1.7 s) for every example, twice in `named_arguments`. A worker now builds one and rewinds it to a mark before each example (`par_map_with`; the `rewind` tests check that a rewound session is a fresh one): `named_arguments` `named_calls_keep_every_hash` went from 796 s to 3 s for the whole corpus, `hash_stability` `examples` from 532 s to 3 s, and `int` `metavariables_under_int_operations` from 175 s to 7 s. The `extract` tests each checked all 48 extraction examples to use one or two; they now check only the ones they use (about 10 s to under 1 s each, 54 tests). `rt` `lower` and `machine`'s example sweeps and `cli` `run_reference`'s examples moved from serial loops onto `par_map`.

Earlier, 24 Oct 2026: wall time of each slow test binary alone, `cargo test --release` with the old slow tier on (8-core Mac with other lanes running cargo: load average 10 to 30, so read these as upper bounds). "After" is the same binary after its serial per-example loops moved onto the `par_map` thread pool.

| Binary | Before | After | Where the time goes |
|---|---|---|---|
| `driver --test std_library` | 146 s | (unchanged) | four `lazy_loading_changes_nothing_*` tests, each loading every example lazily and eagerly: CPU-bound, already on `par_map` |
| `driver --test rewind` | 114 s | 77 s | `rewinding_changes_nothing_for_the_examples` (CPU-bound, on `par_map`); the AoC tests were one serial chain of 7 to 10 whole-project checks, now side by side |
| `driver --test differential` | 79 s | 16 s | one test checking every example in a serial loop, now `par_map` |
| `driver --test check_cache` | 68 s | 40 s | the AoC test ran its two navigation modes one after the other, now side by side |
| `cli --test check_cache` | 58 s | (unchanged) | child processes per example project |
| `cli --test run_js` | 45 s | 12 s | every example run twice per input (`run` and `run --js`) in a serial loop, now `par_map` |
| `driver --test hash_stability` | 46 s | (unchanged) | already on `par_map` |
| `driver --test erasure` | 42 s | 8 s | one test with a serial loop over every example, now `par_map` |
| `cli --test examples` | 13 s | (unchanged) | |

A binary's tests already share the machine through libtest's test threads and `par_map`, so what is left is CPU work. Under `cargo test` the remaining cost of a whole-suite run was that cargo runs binaries one after another, so each binary's tail (its slowest test) left cores idle: the gate took about 31 minutes (`checkPhase`, 111 binaries, on a loaded 14-core machine; the test binaries summed to 29.5 minutes). The gate now runs under [cargo-nextest](https://nexte.st), which starts the next binary's tests as cores free up and runs every test in its own process.

## The flake

- `nix flake check` (`task test:gate`) is the **daily tier**: the `stitchwort` check (`cargo nextest run --no-fail-fast --profile daily` with `STITCHWORT_TIER=daily`, then `cargo test --doc` for the doctests), `clippy`, `fmt`, `debug-builtins` and `board`.
- `nix build .#stitchwort-full` (`task test:full:nix`) is the same with the `full` profile and `STITCHWORT_TIER=full`. It is a package, not in `checks`, so it is built only on request: only when Matt asks.
- Bench `repeat` repeats the whole example sweep in the full tier (about 190 s); the other tiers repeat three small benchmarks (`eval-lengths`, `run-prints`, `check-long-sum`; about 3 s).

### Under nextest

- Settings are in `.config/nextest.toml`: the tier profiles, no fail-fast, 8 tests at once in daily (memory is the limit), 6 in full, one per core in merge and the lanes (mostly sub-second tests).
- Every test is its own process, so statics, thread-locals and `OnceLock`s are never shared between tests, and pid-named temp directories are unique per test. State shared through the file system is not: `crates/cli/tests/lsp.rs` rebuilds one AoC copy under `CARGO_TARGET_TMPDIR` in each test, so those tests are in the `lsp-aoc-copy` test group (`max-threads = 1`). A new test that shares files between tests needs a group too.
- Tests that rely on one process holding a lock (`SPAWN` in `crates/cli/tests/run.rs` and `aoc_answers.rs`, which guards the fork/exec race on pipe descriptors) still work: the race is within a process.
- Nextest does not run doctests. `stitchwort-partial-model` has three (`src/typed.rs`, two `compile_fail`), so the check runs `cargo test --doc --workspace` after nextest.
- Per-test times: the `merge`, `daily` and `full` profiles write a JUnit report with the time of every test to `target/nextest/daily/junit.xml` (or `merge/`, `full/`), and nextest flags tests over 60 s (120 s in full) as SLOW while running. Under plain `cargo test`, the `finished in` line per binary is what there is.
- `conv_shortcut` now checks its examples on the `par_map` pool (the shortcut switch is thread-local): 107 s down to 17 s alone.

