# Testing

Stitchwort's guarantees are only as good as the compiler's correctness, so the tests have several layers. Each layer catches mistakes the others can't.

| Layer | Where | What it catches |
|---|---|---|
| **Example programs** | `examples/`, run by `crates/cli/tests/examples.rs` | Whether the language behaves as designed, end to end. Rejections must have the expected error code, and error messages are snapshot-tested. This is the main suite, and it's readable without knowing the implementation. |
| **Kernel tests** | `crates/core/tests/kernel.rs` | The kernel on hand-built core terms, including terms the elaborator never produces. The examples can't do this: they only feed the kernel the elaborator's output, and when the elaborator rejects something first, the kernel never runs. |
| **Kernel fuzzing** | `crates/core/tests/fuzz.rs` | That the kernel never panics. Thousands of random, mostly ill-formed terms must each be accepted or rejected with a diagnostic. |
| **Unit tests** | `#[cfg(test)]` modules (lexer, parser, unifier, rendering) | Internal algorithms on cases the examples don't happen to reach: pattern unification's occurs and scope checks, pruning, layout columns, … |
| **Differential tests** | `crates/cli/tests/extract.rs` | That extracted JS agrees with the reference evaluator, on the `-- run:` lines and on 100 random inputs per export. Where an export has a precondition, random inputs that fail it must be refused with `StitchwortInputError`, as must the `-- rejects:` lines. |
| **Generated code** | `crates/cli/tests/extract.rs` | Snapshots of the generated JS and `.d.ts`, which must type-check with `tsc`. Decoders are tested against cyclic inputs, getters and later mutation; text decoders against the text proposal's boundary cases (lone surrogates, NUL, noncharacters, one scalar per `Char`) and both round-trip laws. Long inputs: tail calls to the same function must be loops, and running out of stack a `StitchwortResourceError`; values a million deep must cross the boundary both ways. Awkward names (`tag`, `__proto__`, primes, JS globals and reserved words, the runtime's own names) are generated at random: every object must have its own key for each field, and the `.d.ts` must accept exactly what the module does. |
| **Caching** | `crates/cli/tests/caching.rs` | That hashes ignore names and layout but change with anything depended on, that data types are nominal, and that test results are reused exactly until a dependency changes. |
| **Running `main`** | `crates/driver/tests/run.rs`, `crates/cli/tests/run.rs` | That `stitchwort run` prints exactly what the prelude's `simulate` records for the same input, and follows the interpreter's contract: line endings, end of input, UTF-8, flushing, errors and exit codes. The CLI tests run the built command as a subprocess. |
| **REPL and playground** | `crates/cli/tests/session.rs`, `crates/web` | Evaluating and printing expressions, natively and through the WebAssembly interface; running `main` with scripted input, an output budget and a limit on reading past the end of the input, with its output returned or streamed a line at a time; and that every example in `web/index.html` checks and passes its tests. |
| **Browser tests** | `web/tests/browser.mjs` (not in `nix flake check`: see [Browser tests](#browser-tests)) | The playground page in headless Chrome: every example checks and passes its tests (the failing one shows its failure); the Check, Tests, Evaluate, JavaScript and Run tabs; Run with scripted input, `E-NO-MAIN`, `E-OUTPUT`, `E-INPUT`; output appearing while a run is going; Stop, and the 15 s timeout, keeping what was printed; a fresh worker after a crash; the in-page compiler when the `Worker` constructor throws or the worker script is missing; the syntax colouring lining up with the text (highlights and spans, scrolled, after typing); the draft, input and tab kept across a reload; Tab and undo; resizing the editor by dragging. |
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

- **Counts**, the regression signal. *Steps* are evaluation steps, from the resource budget (`Budget::total_work`). *Visits* are levels of the recursive passes that aren't evaluation, like the elaborator and type checker (`Budget::total_visits`). *Allocations* and *peak heap* come from a counting allocator in the benchmark binary. They depend only on the program and the compiler, not on how busy the machine is, so they're identical on every run (checked: separate processes give identical numbers) and the threshold can be tight: **+10%**. They don't see everything: a loop that neither evaluates, recurses through a guarded pass nor allocates costs time without changing them.
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
