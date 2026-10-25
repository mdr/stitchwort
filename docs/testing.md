# Testing

Stitchwort's guarantees are only as good as the compiler's correctness, so the tests have several layers. Each layer catches mistakes the others can't.

## Running a subset

`dev/t` runs just the tests for the area you changed, instead of the full gate. Use these lanes while working; run the full gate (`dev/t gate`) once before merging.

| Area | Runs |
|---|---|
| `dev/t syntax` | `stitchwort-syntax`: layout fuzzing and unit tests |
| `dev/t core` | `stitchwort-core`: all integration tests |
| `dev/t elab` | `stitchwort-elab`: unit tests |
| `dev/t driver` | `stitchwort-driver`: all integration tests |
| `dev/t js` | `stitchwort-js`, plus the CLI `extract` and `run_js` tests |
| `dev/t cli` | `stitchwort-cli`: all integration tests |
| `dev/t examples` | `stitchwort-cli --test examples` (every example, with snapshots; FILTER keeps only files or project folders whose names contain it, e.g. `synonym`) |
| `dev/t hashes` | `stitchwort-driver --test hash_stability` (FILTER keeps only examples whose names contain it) |
| `dev/t bench` | `stitchwort-bench`: the benchmark baseline check |
| `dev/t web` | `stitchwort-web`: unit tests only (browser tests are `dev/t browser`) |
| `dev/t browser` | Build and run the playground tests in headless Chrome |
| `dev/t lint` | `cargo fmt --check` and clippy |
| `dev/t all` | Every test in the workspace |
| `dev/t gate` | `nix flake check`, the full gate (6-7 minutes), including `debug-builtins`: `stitchwort-driver --test builtins` in the debug profile, to catch debug-only panics |

For `dev/t examples` and `dev/t hashes`, `dev/t AREA FILTER` sets `EXAMPLES=FILTER`, so only example files or project folders whose names contain `FILTER` run, for example `dev/t examples synonym`. For the other areas, `FILTER` is passed as the test-name filter after `--`. `dev/t snap AREA` sets `INSTA_UPDATE=always` and then prints the changed snapshots for review; unfiltered snapshots are left alone. Outside `nix develop` the script runs commands through `nix develop -c`; inside the dev shell it calls `cargo` directly.

| Layer | Where | What it catches |
|---|---|---|
| **Example programs** | `examples/`, run by `crates/cli/tests/examples.rs` | Whether the language behaves as designed, end to end. Rejections must have the expected error code, and error messages are snapshot-tested. This is the main suite, and it's readable without knowing the implementation. |
| **Kernel tests** | `crates/core/tests/kernel.rs` | The kernel on hand-built core terms, including terms the elaborator never produces. The examples can't do this: they only feed the kernel the elaborator's output, and when the elaborator rejects something first, the kernel never runs. |
| **Kernel fuzzing** | `crates/core/tests/fuzz.rs` | That the kernel never panics. Thousands of random, mostly ill-formed terms must each be accepted or rejected with a diagnostic. |
| **Syntax fuzzing** | `crates/syntax/tests/fuzz.rs` | That the lexer and parser never panic. 20,000 mutated example programs and random token soups (or more with `FUZZ_CASES`) must each lex and parse to a module or diagnostics. Fixed seed, so a failure prints the input and the generator state to reproduce it. |
| **Unit tests** | `#[cfg(test)]` modules (lexer, parser, unifier, rendering) | Internal algorithms on cases the examples don't happen to reach: pattern unification's occurs and scope checks, pruning, layout columns, … |
| **Differential tests** | `crates/cli/tests/extract.rs` | That extracted JS agrees with the reference evaluator, on the `-- run:` lines and on 100 random inputs per export. Where an export has a precondition, random inputs that fail it must be refused with `StitchwortInputError`, as must the `-- rejects:` lines. |
| **Generated code** | `crates/cli/tests/extract.rs` | Snapshots of the generated JS and `.d.ts`, which must type-check with `tsc`. Decoders are tested against cyclic inputs, getters and later mutation; text decoders against the text proposal's boundary cases (lone surrogates, NUL, noncharacters, one scalar per `Char`) and both round-trip laws. Long inputs: tail calls to the same function must be loops, and running out of stack a `StitchwortResourceError`; values a million deep must cross the boundary both ways. Awkward names (`tag`, `__proto__`, primes, JS globals and reserved words, the runtime's own names), and attributes choosing awkward tag keys, tag values and keys (quotes, backslashes, control characters, `"0"`, non-ASCII), are generated at random: every object must have its own key for each field, and the `.d.ts` must accept exactly what the module does. A metadata-only edit (`js.name` in an imported namespace) reaches the generated code whether that namespace comes from the check cache or not, and changes no hash (`crates/driver/tests/check_cache.rs`). |
| **Caching** | `crates/cli/tests/caching.rs` | That hashes ignore names and layout but change with anything depended on, that data types are nominal, and that test results are reused exactly until a dependency changes. |
| **Running `main`** | `crates/driver/tests/run.rs`, `crates/cli/tests/run.rs` | That `stitchwort run` prints exactly what the prelude's `IO.simulate` records for the same input, and follows the interpreter's contract: line endings, end of input, UTF-8, flushing, errors and exit codes. The CLI tests run the built command as a subprocess. |
| **`run` against `run --reference`** | `crates/cli/tests/run_reference.rs`, `crates/rt/tests/machine.rs` | That the fast runtime (`stitchwort run`, `crates/rt`) behaves as the reference evaluator, which is the oracle: every example `main` (three inputs each), the AoC mains on real and example inputs, the bench programs, `readLine`/`readAll` at the edges, and the `test`s of the examples, the AoC project and the library (about 1,100) have the same output and the same end. `E-RESOURCE` is reported alike, though not at the same point. The CLI tests run the built command. |
| **`run --js`** | `crates/cli/tests/run_js.rs` (needs `node`) | That `stitchwort run --js` prints and fails exactly as `stitchwort run` does: every example with a `main` (including the `Partial` ones) on three inputs, and `readLine`/`readAll` at the edges of the input (line endings, end of input, invalid UTF-8). Also: non-tail recursion over a 500,000-element list, running out of resources, and a missing `node`. |
| **REPL and playground** | `crates/cli/tests/session.rs`, `crates/web` | Evaluating and printing expressions, and `import` lines typed in that accumulate, natively and through the WebAssembly interface; running `main` with scripted input, an output budget and a limit on reading past the end of the input, with its output returned or streamed a line at a time; warnings returned apart from errors; and that every example in `web/index.html` checks and passes its tests, and every example of the language guide (`web/guide/`, the page's Guide) checks and passes its tests, with the failing test's output and the `.d.ts` it shows being what the compiler really gives. |
| **Browser tests** | `web/tests/browser.mjs` (not in `nix flake check`: see [Browser tests](#browser-tests)) | The playground page in headless Chrome: every example checks and passes its tests (the failing one shows its failure); the Check, Tests, Evaluate, JavaScript and Run tabs; warnings shown apart from errors; the JavaScript tab's two boxes shown in full; Run with scripted input, `E-NO-MAIN`, `E-OUTPUT`, `E-INPUT`; output appearing while a run is going; Stop, and the 15 s timeout, keeping what was printed; a fresh worker after a crash; the in-page compiler when the `Worker` constructor throws or the worker script is missing; the syntax colouring lining up with the text (highlights and spans, scrolled, after typing); the draft, input and tab kept across a reload; direct links (`#aoc/day02`, `#example/safe-division`) opening, following the dropdown and falling back to the default; Tab and undo; resizing the editor by dragging; the layout at a phone's width. |
| **Benchmarks** | `crates/bench`, `bench/baseline.toml` | Performance regressions: work, allocations and memory that grew more than 10% against the recorded baseline, and (by hand only) time that grew more than 50%. See [Benchmarks](#benchmarks). |
| **Coverage** | `cargo llvm-cov --workspace --summary-only` | Which code no test reaches |
| **Mutation testing** | `cargo mutants` | Code that tests reach but don't really *check*. Each mutant is a small deliberate bug, such as replacing a condition with `true`. A "missed" mutant is a bug no test would notice. |

Random tests use fixed seeds, so every run tests the same cases and a failure can always be reproduced.

## Running

```sh
cargo test                                     # everything (needs `node`; the dev shell has it)
cargo insta review                             # after changing an error message
cargo llvm-cov --workspace --summary-only      # coverage per file
cargo mutants --package stitchwort-core --test-workspace=true --jobs 6   # slow: minutes to an hour
cargo run --release -p stitchwort-bench        # benchmarks against the baseline: about a minute
nix flake check                                # build, tests, clippy, rustfmt, as CI would
./web/test.sh                                  # the playground in headless Chrome: about 35 s
```

## Browser tests

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

`nix flake check` runs the counts part (`crates/bench/tests/baseline.rs`, about 10 s): one run of each benchmark, failing if a count grew past the threshold. Being deterministic, it can't fail by chance. It's skipped in debug builds (`cargo test`), where the benchmarks are slow and allocation counts may differ from the release build's.

## Writing tests

- **For a language feature, start with example programs.** Add an `accept/` example, and for each way it can go wrong, a `reject/` or `soundness/` example declaring the error code it expects. Pair every rejection with a nearby acceptance, so a check can't pass by rejecting everything.
- **For a kernel rule, also add a kernel test on core terms.** Prove that the kernel enforces the rule *by itself*, not just that the elaborator does.
- **The kernel must never panic.** If a malformed term can make it panic, that's a bug: it should be an `E-MALFORMED` error.
- **For a new export shape or codec, add an extraction example.** The random differential test then exercises it automatically.
- **Before trusting a new test, break the code it tests and watch it fail.** `cargo mutants` does this systematically.

## How long the slow binaries take

Wall time of each slow test binary alone, `cargo test --release` with `STITCHWORT_SLOW=1` (24 Oct 2026, 8-core Mac with other lanes running cargo: load average 10 to 30, so read these as upper bounds). "After" is the same binary after its serial per-example loops moved onto the `par_map` thread pool.

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

A binary's tests already share the machine through libtest's test threads and `par_map`, so what is left is CPU work. The remaining cost of a whole-suite run is that cargo runs binaries one after another, so each binary's tail (its slowest test) leaves cores idle. `dev/t full` runs the suite under [cargo-nextest](https://nexte.st), which starts the next binary's tests as cores free up and runs every test in its own process. It runs the slow tier but not doctests (nextest does not run them); `nix flake check` is unchanged and is still the gate.
