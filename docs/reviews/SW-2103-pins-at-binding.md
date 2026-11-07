# SW-2103: review of SW-2081 (pins checked at binding)

A fresh-eyes review, by reading only, of merge `cb92ef092` (SW-2081, by
Sonnet). It answers findings P1–P4 of
[SW-2080-merges-7-nov.md](SW-2080-merges-7-nov.md). Nothing was built or
run.

## Summary

SW-2081 does what P1–P4 asked, and it is sound. Every way a pinned builtin
gets bound in a session now runs the pin check before its native is
registered: loading from source, replay from the check cache, interface
members, shared definitions, and the language server, which builds its
sessions the same way. The new test would catch a pin that nothing checks.
The fallback is now behind `test-bypass`, and both second-registration
cases have specific messages and a test.

The one finding that matters is older than this merge, but the merge makes
it wider. `test-bypass` does reach a shipped build: the flake's default
package, `stitchwort-bin`, which `nix build` and `nix run` give you. Crane
builds it with `cargo build --release --locked` at the workspace root.
`stitchwort-bench` has `stitchwort-dev-features` as a normal dependency,
and Cargo unifies features over the whole invocation. So that binary is
compiled with the whole dev feature set: `test-bypass` (now including the
stale-pin fallback), `reference`, `stack-check` and `alloc-trace`.
`cargo build --release -p stitchwort-cli` is safe, and so are
`stitchwort-native-bin` and the web bundle. No CLI input reaches the bypass
functions, so nothing is unsound today. But three comments say no release
build has them, and the shipped binary also carries the dev-only checks,
whose speed cost hasn't been measured.

Top recommendations:

1. Build `stitchwort-bin` with `-p stitchwort-cli -p stitchwort-standalone`,
   as `stitchwort-native-bin` already is, and add a check that the shipped
   feature set has no dev features (F1).
2. Make `BOUND_CHECKS` record only while a test has asked it to, as the
   kernel's `REJECTIONS` log does (F2).
3. Reword the two second-registration messages so the definition and the
   native can be told apart (F3).
4. Have the two primitive binding sites assert that what they bind has no
   pin (F4).
5. No change now for the test's single load path (F5). Add a from-source
   variant if replay ever gets a binding shortcut of its own.

Findings: 0 high, 1 medium, 4 low.

## Findings

| # | Severity | Confidence | Size | Where | What |
|---|---|---|---|---|---|
| F1 | medium | medium | S–M | `flake.nix:201` (`stitchwort-bin`), `crates/bench/Cargo.toml:19` | The default flake package, and any root `cargo build --release`, is compiled with the dev feature set, including `test-bypass` |
| F2 | low | high | S | `crates/core/src/pins.rs:235`, `:245`, `:251` | `BOUND_CHECKS` records in every `test-bypass` process and is never drained outside one test, so it grows in long-lived dev processes (the language server) |
| F3 | low | high | S | `crates/core/src/native.rs:594-603` | The new messages are ambiguous because a native is named after its definition: "`Nat.add` is bound to `Nat.add` already" |
| F4 | low | high | S | `crates/elab/src/lib.rs:2543`, `:2559` | The two primitive binding sites call `registry::bind_def` directly and skip `check_bound_def`. That's harmless today (no primitive is pinned), but only the test notices if that changes |
| F5 | low | medium | none now | `crates/driver/tests/library/pinned_hashes.rs:244` | The test covers only one load path per run (replay with a warm test cache, source with a cold one), on one thread |

### F1. The shipped flake binary has the dev feature set (medium, medium, S–M)

**Where:** `flake.nix:198-208` (`stitchwort-bin`, which is
`packages.default`, `flake.nix:322`); `crates/bench/Cargo.toml:17-19`.

**What:** `stitchwort-bin` is `craneLib.buildPackage commonArgs` with no
`cargoExtraArgs`, so crane runs its default, `cargo build --release
--locked`, at the workspace root. There are no `default-members`, so every
crate under `crates/*` is selected, `stitchwort-bench` included.
`stitchwort-bench` depends on `stitchwort-dev-features` under
`[dependencies]`, not `[dev-dependencies]`, so that `task bench` measures a
dev build. With resolver 3, Cargo unifies features across every package an
invocation builds. So `stitchwort-core` gets `test-bypass`, `reference` and
`stack-check`, `stitchwort-elab` and `stitchwort-driver` get `test-bypass`,
and `stitchwort-rt` gets `alloc-trace`, in the very compile that produces
the shipped `stitchwort` binary.

**Scope:** The bench dependency dates from SW-1091 (`4ac22d7c1`, 3 Nov), so
core's `test-bypass` has been in that binary since then. SW-2081 adds the
stale-pin fallback (`Options::stale_pins_fall_back`,
`Session::with_prelude_falling_back`) and `BOUND_CHECKS` (F2). These are
safe:

- `cargo build --release -p stitchwort-cli`: `dev` is off, and the bench
  crate is only a dev-dependency of the CLI, which `build` doesn't compile.
- `stitchwort-native-bin` (`-p stitchwort-cli -p stitchwort-standalone`).
- The web bundle (`-p stitchwort-web`, where dev-features is only a
  dev-dependency).
- `task build`, which turns on `stitchwort-cli/dev` on purpose.

**Why it matters:** Nothing reachable from the command line sets the
fallback or calls the bypass functions, so this isn't a soundness hole
today. It is a hole in the defence the SW-2080 review's P3 asked for: "a
release build carries a switch that turns off natives, with nothing to stop
a future caller". It also contradicts three comments:

- `crates/core/Cargo.toml:28-29`: "so no release build has them"
- `crates/dev-features/Cargo.toml` header: "Distributed builds (the flake's
  package, the browser bundle) don't depend on it"
- `crates/elab/src/lib.rs:3050`: "shipped builds always refuse"

`stack-check` and `reference` may also slow the shipped binary; I haven't
measured how much.

**Confidence:** Medium, because I couldn't build to confirm it. The
argument rests on Cargo's feature unification, which I'm sure of, and
crane's default `cargoExtraArgs = "--locked"` with no `-p`, which I'm
fairly sure of. `nix build` followed by `cargo tree -e features
-i stitchwort-core` with the same arguments would settle it.

**Recommend:**

- Give `stitchwort-bin` `cargoExtraArgs = "--locked -p stitchwort-cli -p
  stitchwort-standalone"`, the same as `stitchwort-native-bin`. Another
  option is a workspace `default-members` that leaves out `stitchwort-bench`,
  which also covers a plain `cargo build --release`.
- Add a guard that fails if the shipped feature set turns on `test-bypass`.
  The simplest is a flake check or task that runs `cargo tree --release -e
  features -i stitchwort-core` with the package's exact arguments and greps
  for `test-bypass`. Another is a hidden `stitchwort dev features` command
  printing `cfg!(feature = "test-bypass")`, which the check asserts is
  false on the built package.
- Keep the three comments, which become true again.

Size S–M (the flake edit is S; the guard and a `nix build` to confirm make
it a lane).

### F2. `BOUND_CHECKS` grows in every dev process (low, high, S)

**Where:** `crates/core/src/pins.rs:235`, `:245`, `:251-253`.

**What:** Under `test-bypass`, every check of a pinned binding pushes onto a
thread-local `Vec`, unconditionally. Only `every_pin_is_checked_at_binding`
ever drains it. The CLI from `task build` has `test-bypass` (through `dev`),
and so does the language server VS Code runs from that same binary. Each
session start on a thread adds 23 entries that are never freed. That's a
few bytes per load, so it's negligible in practice. But it breaks the
pattern the kernel's `REJECTIONS` log set (`crates/elab/src/kernel.rs:35-48`),
which records only while a `RECORDING` flag is on, "so a long-running
session (the language server) doesn't keep every refusal". With F1, it also
happens in the shipped binary.

**Recommend:** Add a `RECORDING` cell beside `BOUND_CHECKS`, turned on by a
`start_bound_checks()` (or by the first `take_bound_checks()`), and push
only while it's on. The test already calls `take_bound_checks()` before
loading, so it changes by one line. S.

### F3. The second-registration messages can't tell a definition from its native (low, high, S)

**Where:** `crates/core/src/native.rs:594-603`.

**What:** `Native::name()` is the name of the builtin it implements
(`native.rs:101`), so in a real session a native and its definition share a
name.

- Registering `Nat.add` twice, which is the case `a_native_is_registered_once`
  (`crates/driver/tests/elaboration/natives.rs:272`) exercises, now says
  "`Nat.add` is bound to `Nat.add` already". That reads like a tautology.
- The other case says "`Nat.add` is bound to a definition already", with
  the label on the second definition. A reader takes the backticked
  `Nat.add` to be the definition, and the message doesn't say which
  definition holds the native, although `builtins.native_defs` has it.

Both are refusals of the compiler's own registration code, not anything a
user can write, so the damage is limited to confusing whoever is debugging
it. The `String::new()` sentinel tested with `is_empty()` would read better
as `Option<String>`.

**Recommend:**

- "`{def}` has a native already (`{have}`'s)"
- "the native for `{native}` is bound to `{existing def}` already"

Build the message as an `Option`. Update the asserts in
`glue.rs:a_second_registration_is_refused_by_name`. S.

### F4. The primitive binding sites skip the check at binding (low, high, S)

**Where:** `crates/elab/src/lib.rs:2543` (`Delay`'s primitives) and `:2559`
(the float primitives `Float.mul` through `Float.toText`).

**What:** Both call `registry::bind_def` directly, not `bind_builtin_def`,
so `check_bound_def` doesn't run there. That's sound today: the names
`Primitive::named` and `FloatOp::named` match don't overlap with `PINS`
(the pinned float definitions are `PINNED_DEFS`, which have bodies). If a
primitive were ever pinned, `every_pin_is_checked_at_binding` would fail,
so the gap is guarded, but only by a test in the library tier.

**Recommend:** Add a `debug_assert!(pins::pin(b).is_none())` on the
returned builtin at both sites, or a small `bind_primitive` helper that
refuses a pinned one. Either way, the rule is stated where the bypass is.
S.

### F5. The test sees one load path, on one thread (low, medium, no change now)

**Where:** `crates/driver/tests/library/pinned_hashes.rs:244-263`.

**What:** `Session::eager_for_stack` uses `StdCache::Test`. With a warm
cache the library is replayed (`cache/mod.rs:2842`, `:2857`). With a cold
one it's checked from source (`after_definition`, `lib.rs:2986`;
`lib.rs:2305`). Either way the core prelude comes from source. Each run
proves the check for whichever path ran. Both paths call the same
`bind_builtin_*` today, so this only matters if one of them gains a binding
shortcut of its own.

The thread-local log isn't a problem:

- `with_session` runs `make` and `f` on the same spawned thread
  (`driver.rs:59-65`), and library loading is single-threaded.
- Checks on another thread could only make the test fail, never pass when
  it shouldn't.
- The `take_bound_checks()` before the load clears anything an earlier
  test left on a reused thread, which matters under `cargo test
  --test-threads=1`. Under nextest each test is its own process anyway.

**Recommend:** No ticket. If replay ever gets its own binding path, add an
`eager_from_source_for_stack` variant of the test in the daily tier.

## Checked and sound

- **Every binding path goes through `bind_builtin_*`.** Source loading
  (`after_definition`, `lib.rs:2986`; data at `lib.rs:2305`), interface
  members (`interfaces.rs:341`), shared definitions (`shared.rs:299`), and
  check-cache replay for library files (`cache/mod.rs:2842`, `:2857`). The
  other direct `registry::bind_*` calls are the two primitive sites (F4) and
  core's own test helpers (`core/tests/it/common/mod.rs:143-145`,
  `pretty.rs`).
- **The language server** builds sessions with `Session::for_stack` and
  `navigable_for_stack` (`lsp/src/lib.rs:2198`, `:3625`), which go through
  `Session::start` like the CLI. I found no prelude snapshot or kernel clone
  that would bind without a check.
- **Outside `bind_builtin_*`, `register_native` is called only from
  tests** (`driver/tests/elaboration/natives.rs`), and it checks the pin
  itself. `register_native_unpinned` is `test-bypass` only, and its only
  callers are in `core/tests/it/glue.rs`.
- **The order inside `bind_builtin_def`.** The fallback test runs before
  the check, so a fallback session neither refuses nor logs a stale pin, as
  intended. The data path has no fallback, which is unchanged: the stale
  `Float` data was already refused by `float::register_data`.
- **The cost of checking twice.** Each pinned binding is now checked in
  `check_bound_*` and again in its registration function (`native.rs:499`,
  `:624`, `float.rs:589`, `:684`). `def_hash` and `data_hash` are memoised
  in `g.caches.hashes` (`hash.rs:92`, `:161`), so the second check costs a
  table lookup, a 64-character `String` and a budget operation, 23 times per
  session start. That's negligible, and it is the duplication P1 asked for.
- **`?` on every new call.** `Result` is `#[must_use]` and clippy denies
  warnings, so dropping a `?` wouldn't build.
- **The `cfg` gating compiles both ways by construction.** `pins_fall_back`
  has a `cfg(not)` arm, and the field and its pattern in `Options::key`
  are gated together. The example `crates/driver/examples/pins.rs` (`task
  pins:show`) and the extract test still get the fallback: examples and
  test targets compile dev-dependencies, so dev-features is on, and the
  CLI's tests have it through `cli-with-dev`.
- **`-p stitchwort-cli` alone can't turn the feature on** (see F1 for what
  can).
- **The comments P2 flagged** (`pins.rs:21`, `pinned_hashes.rs:40-42`) now
  say only what holds.
- **P4's untested case** (a second definition for one native) is now
  tested in `glue.rs`, on two different definitions.

Not checked: the elaborator's rewind (`driver/tests/projects/rewind.rs`)
and whether it can ever rewind into the library load and bind again. I'd
expect not, but I didn't read it.

## Status of earlier findings

- **SW-2080 P1:** fixed.
- **SW-2080 P2:** fixed. The third bullet, about the redundant
  `nat_add`/float pin tests, was "harmless" and is unchanged.
- **SW-2080 P3:** fixed within the crate graph, but F1 means it doesn't hold
  for the default flake package.
- **SW-2080 P4:** fixed. The new messages have a wording problem (F3).
- **1 Nov review** (`docs/research/rust-codebase-review.md`): none of its
  findings are in this scope. It has nothing on pins, `test-bypass` or
  feature sets.

## Calls I made

- I didn't raise F1 as a D question. Keeping test switches out of shipped
  builds is already the stated design (D2295, the dev-features comments),
  so this is a fix, not a direction change.
- I rated F1 medium, not high, because no user input reaches the bypass
  functions today.
- I recommend no ticket for F5.

## Tickets to file

- **Lane 1 (Sonnet, about 45 min): keep dev features out of the shipped
  binary (F1).** Scope `stitchwort-bin` to `-p stitchwort-cli -p
  stitchwort-standalone`, or add workspace `default-members` without the
  bench crate. Add a check that the shipped feature set has no
  `test-bypass`, and confirm with one `nix build` plus `cargo tree`. The
  change is in the build configuration across crates, which is why it's
  Sonnet.
- **Lane 2 (DeepSeek, about 30 min): tidy-ups to the pin check (F2, F3,
  F4).** A recording switch for `BOUND_CHECKS`, the two reworded messages as
  an `Option`, and `debug_assert`s at the two primitive binding sites.
  Tests to run: `a_second_registration_is_refused_by_name` (core `it`),
  `a_native_is_registered_once` (driver `elaboration`), and
  `every_pin_is_checked_at_binding` (driver `library`).

No D questions.
