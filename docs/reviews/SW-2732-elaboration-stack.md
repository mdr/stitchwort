# SW-2732: how much stack elab/check uses per nesting level

## What was measured and how

Three shapes were generated as small `.sw` files and checked with the debug
and release CLIs, and the same shapes were measured at the default limits with
a temporary test harness:

- **nested applications**: `def f (n : Nat) : Nat := n`, then
  `def deep : Nat := f (f (… 0))`, `n` applications deep.
- **nested constructors**: `type W = Leaf | Both (left: W) (right: W) |
  Witness (inner: W)`, then `def deep : W := Witness (Witness (… Leaf))`.
- **`Witness (Both …)`**: the shape from `List.foldMinByFirst`, then
  `Witness (Both (Witness (Both (… Leaf) Leaf)) … Leaf)`.

The CLIs were built with `nix develop -c cargo build -p stitchwort-cli` and
`nix develop -c cargo build --release -p stitchwort-cli`; each file was checked
with `target/{debug,release}/stitchwort check --no-cache FILE`. Depth was
found by binary search: the last depth that checks and the first that fails.
All failures were `E-RESOURCE`; the message names the pass (`elaborator`, or
`parse` at much greater depths).

The default-limit points came from the existing `just_past_the_limit` harness
in `crates/driver/tests/elaboration/nesting.rs` (Session::new, so
`Limits::default()`), with temporary cases for the three shapes. Those cases
were removed after measuring. I also temporarily put a `Backtrace::force_capture`
in `Budget::too_deep` to record the Rust recursion path, then reverted it.

Two budgets matter:

- **1.5 MiB**: `Limits::default()` is `Limits::for_stack(2 MiB)`, and
  `for_stack` reserves a quarter (512 KiB), leaving 1.5 MiB
  (`crates/core/src/budget.rs:117-126,163-168`). This is the default test
  thread's guarded stack.
- **48 MiB**: the CLI runs on a 64 MiB thread (`crates/cli/src/main.rs:695`)
  and its sessions use `Limits::for_stack(64 MiB)`, which leaves 48 MiB after
  the 16 MiB reserve.

## Results table

First depth that fails (`n`; the depth `n-1` checks):

| Shape | 1.5 MiB, debug | 1.5 MiB, release | 48 MiB CLI, debug | 48 MiB CLI, release |
|---|---:|---:|---:|---:|
| nested applications | 15 | 115 | 475 | 3709 |
| nested `Witness` | 25 | 249 | 866 | 8043* |
| `Witness (Both …)` | 13 | 125 | 433 | 4022 |

\* At 48 MiB the release `Witness` case reaches the evaluator's stack guard
(`ResourceError::Depth`, "it recursed more deeply than allowed") rather than
the elaborator's nesting check; the other debug and release failures are
`E-RESOURCE` from the elaborator. Both are the same guarded thread stack.

Bytes of stack per nesting level, from the slope between the two budgets
(`(48 MiB − 1.5 MiB) / (N48 − N1.5)`):

| Shape | Debug B/level | Release B/level | Debug/release |
|---|---:|---:|---:|
| nested applications | ~106,000 | ~13,600 | 7.8× |
| nested `Witness` | ~58,000 | ~6,300 | 9.3× |
| `Witness (Both …)` | ~116,000 | ~12,500 | 9.3× |

Dividing each budget by its threshold gives the same picture (e.g. 1.5 MiB /
15 = 105 KB for debug applications, 1.5 MiB / 115 = 13.7 KB for release), so
the cost is linear in depth over this range to within a percent or two.

The Rust functions on the recursion path, from the recorded backtraces:

- **Constructors** (`Witness (… )`, `Witness (Both (…))`):
  `check → check_inner → check_value → ctor_app → check` (the field's
  argument), plus `check::with_span` around each `check`. About 5 Rust frames
  per level.
- **Applications**: `check → check_inner → check_value → fallback_named →
  propagate → apply_args_with → apply_args_postponing → check_arg →
  queue::framed → check` (the argument), plus `with_span`. About 11 frames per
  level. This is why nested applications cost about twice as much per level
  as constructors.

`Budget::nesting("elaborator")` is charged in `check` and `infer`; the
recursion itself is in the `check`/`infer` cycle above, with `ctor_app` for
constructor arguments and `apply_args_postponing`/`check_arg` for application
arguments.

## Answers

### (1) Where the 1.5 MiB is set, and what runs std under which stack

There are two independent 1.5 MiB constants, both one and a half MiB:

- `crates/core/src/budget.rs:163-168`: `Limits::default()` is
  `Limits::for_stack(2 MiB)`; `for_stack` (lines 117-126) subtracts
  `max(stack/4, 256 KiB)` = 512 KiB, so the guarded stack is exactly 1.5 MiB.
  This is what `Session::new`, `Session::eager`, `Session::eager_from_source`,
  `Session::navigable` and the `*_for_stack` constructors start from when their
  caller doesn't pass a size.
- `crates/syntax/src/parser.rs:45`: `DEFAULT_STACK = 1536 * 1024` = 1.5 MiB,
  used by `parse_module`/`parse_expression` when the caller doesn't pass a
  stack (fmt, syntax docs/equivalence, LSP lens, CLI sweeps). It is not what
  the driver uses to parse a checked file: `Session::load` parses with the
  session's `Limits::stack`.

Modes:

- **CLI** (`stitchwort check`, `build`, `test`, `run`, `serve`): 64 MiB thread
  (`crates/cli/src/main.rs:695,763`), sessions via `Session::for_stack(64 MiB)`
  → **48 MiB guarded**. `serve` spawns the checker thread with the same 64 MiB
  (`crates/lsp/src/lib.rs:889`), so LSP std elaboration also has 48 MiB.
- **LSP tests**: 256 MiB thread and `Options::new(256 MiB)` → **192 MiB
  guarded**.
- **Whole-library driver tests**: `builtins.rs`, `hash_stability.rs`,
  `std_library.rs`, `fmt_hashes.rs` use `STACK = 16 MiB` → **12 MiB guarded**
  (`hash_stability`'s dump test uses 64 MiB). The proofs tests mostly use
  64 MiB; `pinned_hashes` and the search tests use 64 MiB.
- **The 1.5 MiB that bit**: the four `hidden_session()` tests in
  `crates/driver/tests/library/builtins.rs`
  (`syntax_means_the_prelude_whatever_its_names_mean`,
  `natives_stay_on_the_prelude_definitions`,
  `the_runner_uses_the_prelude_simulate_and_io`,
  `a_programs_own_list_prints_as_itself`) used `Session::new()`, i.e. the
  default 1.5 MiB guard, on Rust's default 2 MiB test thread. `PROGRAM` does
  `import Std (Char, Nat, Text)`, which loads the whole library, so these four
  were checking std from source under 1.5 MiB. The other builtins tests, which
  also load the whole library, were already on 16 MiB. That inconsistency —
  not the 16 MiB constant — is the source of SW-2731's "3.6 KB over 1.5 MiB".
- A few other tests use `Session::eager_from_source()` (1.5 MiB) because they
  only run in release (`std_library.rs:134,795,851`,
  `hash_stability.rs:300`); 1.5 MiB is the right *release* default there.
- WebAssembly builds deliberately use a 256 KiB guard
  (`crates/web/build.rs:23`), not 1.5 MiB.

### (2) Stack per level of constructor arguments and nested applications

The two-budget measurements above are the answer: in the debug build a level
of nested constructor arguments costs about **58 KB** (`Witness`) to **116 KB**
(`Witness (Both …)`), and a level of nested application about **106 KB**. In
release the same levels cost about **6.3 KB**, **12.5 KB** and **13.6 KB**
respectively. The recursion path is the `check`/`infer` cycle given above, with
`ctor_app` for constructor fields and `apply_args_postponing`/`check_arg` for
application arguments.

At the CLI's 48 MiB budget, the debug CLI first failed at depth 475 (plain
applications), 866 (`Witness`) and 433 (`Witness (Both …)`); the release CLI at
3709, 8043 and 4022. Depths 5, 10, 20 and 40 therefore all check in both
builds, as expected: they are far below the CLI's budget. In the debug build
the parser's own 1.5 MiB `DEFAULT_STACK` is not the limit for files checked by
the driver (that uses the session's 48 MiB); at much greater depths the parser
eventually fails too (about depth 2000 for the application shape with 48 MiB),
but elaboration fails first for these shapes.

### (3) Should the debug-only builtins tests use a larger stack?

Yes, and they now do. Debug frames use **7.8× to 9.3×** the stack of release
per nesting level for these shapes. So the four tests' old 1.5 MiB debug guard
was roughly a **190–200 KiB** release guard: it fires long before a release
build at its own 1.5 MiB would. That makes it a conservative canary — any
release path that grows to ~190 KiB would still be caught — but it does not
show a release problem at 1.5 MiB, and it produced a false positive (SW-2731)
that was "fixed" by contorting std.

The right calibration is the one the eager tests already use: a 16 MiB thread,
which gives a 12 MiB debug guard. At ~8× frame size that is about a 1.5 MiB
release guard, so it still catches a real release regression of the same shape
while ignoring debug-only frame bloat.

## Recommendation

- Keep `STACK = 16 MiB` for the whole-library builtins tests, and run the four
  `hidden_session` tests on it too. Done in this change: `hidden_session` uses
  `Session::for_stack(STACK)` and each test body is wrapped in
  `with_stack(STACK, …)`; the four tests pass in debug (8.2 s) and release
  (1.0 s).
- Do not raise the default `Limits` or the CLI's 64 MiB: the CLI's 48 MiB guard
  is already ~7× the largest path measured here and is not the limiting budget
  in practice.
- Do not add a workaround in std for the next few-KB debug overrun. If a
  release-representative guard is wanted, use the release nextest tier's
  `Session::eager_from_source()` tests (1.5 MiB) rather than the debug build;
  the debug build's absolute byte counts are not comparable to release's.
- The `let below` workaround in `List.foldMinByFirst` can stay (it also lowers
  release stack), but it should not be treated as required for correctness.

## Commands run

- `nix develop -c cargo build -p stitchwort-cli` — built debug CLI (34 s).
- `nix develop -c cargo build --release -p stitchwort-cli` — built release CLI (26 s).
- `target/{debug,release}/stitchwort check --no-cache <generated>.sw` — depth
  checks and binary searches; all results in the table above.
- `nix develop -c cargo test -p stitchwort-driver --test elaboration -- sw2732_ --nocapture`
  and the same with `--release` — temporary default-limit thresholds; 1.5 MiB
  first failures 15/25/13 (debug) and 115/249/125 (release).
- Temporary `Backtrace::force_capture` in `Budget::too_deep`, then
  `nix develop -c cargo build -p stitchwort-cli` and a debug check at the
  failure depth — recorded the `check`/`ctor_app` and
  `check`/`apply_args_postponing` cycles; instrumentation reverted.
- `nix develop -c cargo nextest run -p stitchwort-driver --test library -E '…four builtins tests…'`
  — 4 passed in 8.26 s (debug).
- `nix develop -c cargo nextest run --release -p stitchwort-driver --test library -E '…four builtins tests…'`
  — 4 passed in 0.99 s (release).
- `nix develop -c cargo fmt --check` — clean for the changed file.

Not measured: the exact minimum budget for loading the whole library (one load
is 70–90 s in debug), and the LSP's real std-load stack use (only its configured
budget was read from the code).
