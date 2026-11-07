# Fewer test binaries (SW-1736)

Status: plan, with a pilot on `stitchwort-rt` (this branch). Rolling out the
other crates waits for Matt's go-ahead.

## The problem

Every file in a crate's `tests/` folder is a test binary of its own: 166 of
them across 10 crates (driver 68, cli 42, core 20, rt 13, native 9, fmt 4,
syntax 4, bench 3, lsp 2, partial-model 1). Each is compiled and linked
separately, so a one-line edit in `core` or `elab` rebuilds about 157 test
binaries (174 executables with the unit-test ones). The SW-1716 profile
(`docs/reviews/SW-1716-dev-loop-profile.md`, §1.2) puts 628 of the 914
CPU-seconds of an `elab` edit into these test binaries, most of it
re-optimising the same generic library code once per binary, and the target
folder holds a copy of each (about 2.5 GB of 4.9 GB, by that profile's
estimate).

## The change

One test binary per crate, or a few where the crate has good reason to keep
some apart. In each crate `tests/foo.rs` becomes a module of
`tests/it/main.rs` (`tests/it/foo.rs`, `mod foo;`). It has to be a folder:
cargo makes a binary of every file directly in `tests/`, so a `tests/main.rs`
beside the others would not merge anything. The binary is called `it`, the
usual name for this.

What changes for people and tools:

| | Before | After |
|---|---|---|
| nextest binary id | `stitchwort-rt::lower` | `stitchwort-rt::it` |
| test name | `every_example_lowers` | `lower::every_example_lowers` |
| a whole old binary | `binary(lower)` | `package(stitchwort-rt) & binary(it) & test(/^lower::/)` |
| one old test | `binary(lower) & test(=x)` | `package(stitchwort-rt) & binary(it) & test(=lower::x)` |
| by hand | `task test:one -- -E 'binary(lower)'` | `task test:one -- lower::` (a bare name matches test names) |
| cargo | `--test lower` | `--test it lower::` |
| insta snapshots | `snapshots/lower__x.snap` | `tests/it/snapshots/it__lower__x.snap` |

Nothing else about the tests changes: nextest still runs each test in a
process of its own, so statics, `OnceLock` caches and the like behave exactly
as before (they are per test, not per binary). Only `cargo test`, which runs a
binary's tests as threads of one process, would see them shared; nothing here
uses it for the integration tests (the daily tier's doctests are separate).

### The translation is mechanical: `dev/merge-test-binaries`

```
dev/merge-test-binaries CRATE [--name it] [--keep BIN]... [--dry-run]
dev/merge-test-binaries --verify BEFORE.json AFTER.json CRATE
```

It moves the files with `git mv`, writes `main.rs`, deepens `include_str!`
paths, and rewrites every reference that names a merged binary: each
`filter` and `default-filter` in `.config/nextest.toml`, `EXTRAS` in
`dev/nextest-merge`, and the `binary = "x"` selects in
`dev/test-affected.toml`. It parses the filtersets (so it knows which
`test()` sits beside which `binary()` and which `package()` encloses them)
and edits only the predicates, leaving the layout alone. It refuses, naming
the spot, anything it cannot translate safely: a bare `binary(foo)` that
another crate also has, a merged binary under `|` or `!` beside a `test()`, a
top-level `|` in a test pattern. `--verify` takes two
`cargo nextest list --message-format json` outputs and fails unless each old
test has exactly one new name `module::name` and nothing else appears or goes.

Still by hand per crate, and the script says where: `mod common;`-style
helper modules (declared once in `main.rs`, the moved files then
`use crate::common`), a file-level `#![cfg(unix)]` (becomes
`#[cfg(unix)] mod x;`), the insta snapshot files (renamed `it__`), mentions
in `Taskfile.yml` (`fuzz:syntax` names `binary(fuzz)`), `docs/testing.md`,
and comments that name a path. `dev/test-affected` learns that a changed
`tests/it/foo.rs` selects `module foo`, and `tests/it/main.rs` or a helper
module the whole binary.

## Per crate

Global state that could make merging unsafe, checked by grep:
`#[global_allocator]` (one per binary: those tests count allocations)
in `rt` `effect_alloc` and `state_match`, `driver` `resources` and
`search_at_aoc`; no test sets an environment variable or changes directory;
the statics in `cli` `aoc_answers`, `effect_differential`, `lsp`, `run` and
driver `rewind` are per-process caches, which nextest keeps per test. The test
std cache turn and `search-cache` are files, shared between processes
already.

| Crate | Binaries now | After | Notes |
|---|---|---|---|
| syntax | 4 | 1 | `Taskfile.yml` `fuzz:syntax` names `binary(fuzz)` |
| rt | 13 | 3 | pilot (below); `effect_alloc` and `state_match` stay (global allocators) |
| core | 20 | 1 | 19 files declare `mod common;`: once in `main.rs`; `structural/` helper |
| native | 9 | 1 | `mod common;` in 6 files |
| fmt | 4 | 1 | `lane-fmt` leaves out `repo` and `fuzz`: `!(… test(/^repo::/))`; `golden/`, `support/` |
| lsp | 2 | 1 | `features` and `memory` share the `lsp-sessions` group, which translates as is |
| bench | 3 | 3 | stay: heavy, run by `task bench`, and `NOT_REACHED` in `dev/test-affected_test.py` is per binary |
| partial-model | 1 | 1 | nothing to merge |
| cli | 42 | 3 | 23,600 lines: split in about three groups by area (the sweeps, `lsp`/`run`/`session` and the rest) so no single compile is the critical path; `common/`, `pty/`; `#![cfg(unix)]` on `keys_mode` |
| driver | 68 | 6 | 31,600 lines: about four groups, plus the global-allocator binaries (`resources`, `search_at_aoc`) apart; `fuzz_elab` and `soundness_fuzz` stay apart (`NOT_REACHED`) |

Total: 166 to about 21. One crate-wide `it` for the large crates would put
31,000 lines in one compile; grouping keeps the compiles in parallel. This
needs `--group NAME=a,b,c` in the script (not written: the pilot has one
group).

## What it should do

Fewer links and, mostly, fewer compiles of the same library code. Measured on
the pilot (one-line edit in `core`, every test binary rebuilt with
`cargo build --tests --release --workspace`, incremental, in this worktree):

| | Before | After |
|---|---|---|
| integration-test binaries relinked | 157 | 147 |
| executables relinked, all | 174 | 164 |
| CPU (user + sys) | 979 s | 959 s |
| wall | 127 s | 171 s, not comparable |

The wall times are meaningless: two other lanes were building and the load
average was 46 for the first and 23 to 39 for the second. The CPU time is the
fair figure, and it fell by 20 s for 10 binaries merged, about 2 s each. That
is less than the profile's 4.2 s median per binary, as `rt`'s test files are
small (4,400 lines for the 13) and the cost of a merged binary is the sum of
its files' own code. Extrapolated crudely, about 145 fewer binaries is 300 CPU
seconds of 980, a third of an edit's work, which on 10 free cores is
10 to 25 s off an incremental rebuild of about 130 s under the same load, or
the SW-1716 estimate of 6 to 8 s of a quiet 21 s. The pilot cannot tell which:
it is a one-point measurement on the smallest sort of crate. The first
roll-out crate with real weight (`core`, 13,000 lines in 20 files) will say.

The pilot's tests: 114 of `stitchwort-rt` before and after, every old test
mapped to exactly one new name (`--verify`). The test timings store is keyed
by binary id, so the merged tests lose their recorded times until the next run
folds them back in (the roll-out can rewrite the keys in
`target/test-timings.json` with the same mapping).

## Costs and risks

- Names change in everything that quotes them: handled by the script in the
  repository's own files, but not in people's habits, or in tickets and notes
  that name `binary(x)`. These stay as history.
- A compile error in one test file now stops the whole crate's tests, not
  one binary's.
- Dead-code warnings: a helper module used by some modules but not others no
  longer warns once per binary, which is a gain.
- The critical path: one big binary is one serial front end. Hence the groups
  for `cli` and `driver`.
- Cargo can't rename a single test: `cargo test --test lower` stops working.
