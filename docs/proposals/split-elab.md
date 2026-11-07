# Proposal: splitting the `elab` crate

**Status:** plan, 7 November 2026, SW-1737 (Developer loop speed epic).
No code changed. It follows fix 13 of the build profile,
[SW-1716-dev-loop-profile.md](../reviews/SW-1716-dev-loop-profile.md) (§1, §6).

**The short answer.** Don't split `elab` into crates now. It is one
knot: 89% of its lines depend on each other in a cycle, through
`Elaborator` and `Ctx`. Untying the knot is a large refactor that touches
every running lane, and it would save about 5 to 15 s of a clean build
and 0 to 4 s of a 21 s incremental rebuild. Instead, do a small change
that is not a split: stop compiling all of `elab` a second time for its
148 unit tests. That second compile ends every clean build and every
fresh-worktree build. Removing it should save **20 to 30 s** of each such
build, and 1 to 3 minutes of one core's CPU.

## 1. The problem

`elab` is 115,800 lines, more than every other crate together. The
profile found two serial stretches in a clean build:

- 50 to 90 s, one to four processes run: `elab` (65 s quiet; 80 to 100 s
  in tonight's loaded timings) and `cranelift-codegen` (67 s; 72 to 81 s
  loaded) finish side by side.
- The last 20 to 30 s, one process runs: `stitchwort_elab "lib" (test)`,
  which is `elab` compiled again with `cfg(test)`, as a binary at
  `opt-level = 3`.

Tonight's `--timings` reports, from SW-1754's runs (clean, incremental on,
machine shared):

| Build | Total | `elab` lib ends | `cranelift-codegen` ends | `elab` unit tests | Last unit before them ends |
|---|---|---|---|---|---|
| current settings | 264.6 s | 113.8 s | 99.8 s | 101.0 to 264.6 s | 244.0 s (`soundness_fuzz`) |
| `opt-level = 1` trial | 175.6 s | 93.2 s | 92.6 s | 92.6 to 175.6 s | 150.0 s (`core`'s unit tests) |

The unit-test compile starts late for a reason that a split won't change.
It is a binary, so cargo waits for the full libraries of everything it
links, and through `stitchwort-dev-features` that includes
`stitchwort-native` and so `cranelift-codegen`. Then it takes 46 s
(quiet) to 163 s (loaded) on its own.

With incremental builds (now on in the devShell), a one-line `elab` edit
takes about 21 s. Tonight's edit timings show `elab`'s own share at 2.7 to
6 s. The rest is the test binaries that depend on it, and they rebuild
after any `elab` edit, because cargo has no early cut-off.

## 2. The module graph

Edges are `crate::…` and `super::…` paths, plus `lib.rs`'s own
references to its modules. There are 76 top-level modules.

- **One cycle holds 58 modules, 102,800 lines (89%).** Its hub is
  `Elaborator` (`lib.rs`) and `Ctx<'e>` (`check.rs`, which holds
  `&Elaborator`). Almost every function takes `&mut Ctx`, and `check`
  reaches out to almost every tactic and feature module
  (`omega`, `rewrite`, `ring`, `calc`, `cases`, `matching`, `records`, …),
  which call back into `check`, `unify`, `undo` and `queue`.
  `state` (which owns the navigation index and the cache tables) and
  `cache` also point into each other.
- **18 more modules (about 10,000 lines) look like leaves by paths, but
  aren't.** `derive_*`, `closing`, `partial`, `attributes`, `tailrec`,
  `update_lemmas` and `redundant` add methods to `Elaborator` (42 files have
  an `impl Elaborator`), and the core calls those methods, for example
  `module.rs` calling `derive_data_eq`. A method call has no path, so the
  path graph misses the edge back. An inherent `impl` can't move to
  another crate, so each of these would need a hook.
- **True leaves, which use nothing in the crate:** `omega_search` (1,171
  lines), `cache/codec` (717), `shown` (508), `saturate` (345) and
  `std_dir` (260). That is 3,000 lines, 2.6%.

The crate has 1,339 `pub(crate)` items, 5 `#[inline]` attributes, and 142
generic functions.

## 3. Candidate cuts

Counts are from matching identifiers, so they are approximate. "Entry
points" are the items of the cut that the rest of the crate uses, so they
would become hooks or a public API. "Core items used" are `pub(crate)`
items elsewhere that the cut uses, so they would have to become `pub`.

| Cut | Lines | Entry points | Core items used | Breaks the cycle? |
|---|---|---|---|---|
| Leaves below `elab` (`omega_search`, `codec`, `shown`, `saturate`, `std_dir`) | 3,000 | – | 0 | no cycle to break |
| `derive_*` | 6,411 | 22 (`derive_data_eq`, `_ord`, `_show`, `_finite`, `derive_record_ext`, …) | ~99 | only with hooks: the core calls them |
| omega and decision procedures (`omega`, `omega_search`, `ring`, `saturate`, `congruence`) | 7,691 | 32 (`check_omega`, `prove_premise`, `prove_case`, `check_ring`, …) | ~134 | only with hooks: `check`, `auto` and `cases` call them |
| `counterexample` | 2,629 | 14 | ~90 | only with hooks |
| `rewrite` | 3,781 | 8 (`check_rewrite`, `infer_rewrite`, …) | ~159 | only with hooks; `matching` calls back into it |
| `cache` | 4,703 | 33 | ~158 | no: `state::Tables` holds cache types |
| `nav` | 2,041 | 35 | ~94 | no: `state::Presentation` owns `NavIndex`; only the builder could move |
| `matching` | 2,916 | 17 | ~129 | no: the main loop in `check` calls it everywhere |
| pretty printing | – | – | – | already in `stitchwort-core` (`pretty`); `shown.rs` is a leaf |

**How a real cut would work.** Split the crate in three. A new
`stitchwort-elab-core` holds `Elaborator`, `Ctx`, `check`, `unify`,
`state`, `scope`, `module` and the other modules in the cycle. It also
holds a table of hooks: plain function pointers, such as
`fn(&mut Ctx, &Expr, &Value) -> Result<Term>` for a tactic, or a `derive`
entry. Feature crates (`elab-derive`, `elab-decide`, …) depend on the
core and fill in the hooks. `stitchwort-elab` keeps its name, becomes a
small crate on top that builds an `Elaborator` with the hooks installed,
and re-exports the core's API, so `driver`, `lsp` and `cli` don't change.
Methods in an `impl Elaborator` in a moved file become free functions or
an extension trait.

**What it would save.** If the three hookable cuts (derive, omega and
friends, counterexample) moved, that would be 16,700 lines, 14%. With
`rewrite` and the cache codec as well, about 22%.

- *Clean build:* the core's front end and code generation shrink in
  proportion, to about 55 s from 65 s for 14%. The feature crates start
  after the core's metadata and run side by side. But the wide phase of
  test binaries also waits for `cranelift-codegen`, which tonight finished
  0.6 to 14 s before `elab`. So the gain is **at most 5 to 14 s**. On a
  fresh worktree, where kache has `cranelift` and the core's dependencies,
  `elab` alone is the path, and the gain is about 10 to 20 s.
- *Incremental rebuild after an `elab` edit:* an edit in a feature crate
  skips the core's incremental recompile (2.7 to 6 s of 21 s). An edit in
  the core rebuilds everything, as now. Driver, lsp and every test binary
  rebuild either way. So the gain is **0 to 4 s**, and only for edits in
  the moved parts.
- *Generic code:* little of it is in the cuts. Nothing in them is generic
  over caller types, so there would be no new monomorphisation downstream.

## 4. Risks of a real split

- **Visibility.** Each cut makes about 90 to 170 `pub(crate)` items `pub`.
  The core's internals (`Ctx` fields, `undo`, `lift`, `queue`) become
  crate API, and private `Ctx` fields such as `scope` and `locals` need
  accessors.
- **Inlining.** Without LTO, a small non-generic function called from
  another crate isn't inlined unless it is marked `#[inline]`, and the
  crate has 5 such marks. Hot paths (`unify`, `check`, `whnf` through
  core) stay in the core under these cuts. omega's search loops and the
  cache readers call small helpers often, so they would need marks and a
  check, such as `hash_stability prelude` (13.8 s) and an omega-heavy
  driver test, before and after.
- **Churn.** Nearly every lane touches `elab`. Moving a file and rewriting
  its `crate::` paths conflicts with any lane editing that file. Each
  stage would have to land between batches, as a short lane merged first.
- **Kernel-adjacent code.** `derive_induct`, `equations`, `omega` and
  `rewrite` build proof terms the kernel checks, and `cache` stores terms
  and hashes. A pure move shouldn't change a term. But installing hooks
  could change behaviour in two places. A tactic table that is checked in
  a different order would. So would an `Elaborator::default()` that builds
  one without hooks: today `Elaborator` derives `Default`, and a core-only
  test would silently lose `derive`. Each stage would need the
  `hash_stability` test and `snap:hashes` unchanged.

## 5. What to do instead: the unit tests

**The change.** Compile `elab`'s unit tests into the library, behind a
feature, and run them from one small integration-test binary, so `elab`
is no longer compiled twice.

- Add a feature, `unit-tests`, to `stitchwort-elab`, and switch it on in
  `stitchwort-dev-features`, as `core`'s `test-bypass` already is. Every
  dev and test build has it, and the flake's package and the browser
  bundle don't.
- Turn each `#[cfg(test)] mod tests` into
  `#[cfg(feature = "unit-tests")] pub mod tests`, with each `#[test] fn`
  a `pub fn`. There are 148 tests in 20 files (`queue` 38, `unify` 36,
  `omega_search` 14, …), about 4,700 lines. They stay inside their
  modules, so they keep access to private items. The 24 other
  `#[cfg(test)]` sites become `#[cfg(any(test, feature = "unit-tests"))]`.
- `crates/elab/tests/unit.rs` has one `#[test]` per function, calling
  `stitchwort_elab::…::tests::name()`, written by a small macro so test
  names stay the same for `task test:one`. A guard test checks that this
  list matches the test functions in `src/`, so a new test can't be
  forgotten. `#[should_panic]` and `#[ignore]` carry over to the wrapper.
- `[lib] test = false` in `crates/elab/Cargo.toml`.

**What it should do.** The 115,800-line second compile disappears. The
library grows by about 4% of test code, about 1 to 2 s. The new binary is
small and builds during the wide phase. A clean build should end at the
unit before it: tonight 244 s instead of 264.6 s, and 150 s instead of
175.6 s, so **20 to 25 s loaded and about 30 s quiet**. Each build that
recompiles `elab` (fresh worktrees, kache misses) also frees one core for
46 to 163 s. An incremental edit stays about the same (the test compile
was 2.6 to 6 s, not on the path).

Risks: little. The test bodies and the code they test don't change. The
feature only makes test modules public in dev builds. With fix 5 (one
integration binary per crate), `unit.rs` becomes one module of `elab`'s
binary.

## 6. Staged order

Each stage is one lane with its own measurement. The `--timings` runs
need a quiet machine, so the orchestrator schedules them when no other
lane is building.

1. **`elab` unit tests into the library (§5).** Sonnet: Cargo features
   across two crates, plus a guard test. Expected 45 min. Measure:
   - the same 148 test names pass, before and after (`cargo nextest list`
     and `task test:one -- stitchwort_elab`);
   - a clean `cargo test --release --workspace --no-run --timings`: total
     and last unit, against the profile's 191 s;
   - one incremental `elab` edit: about 21 s, unchanged.
2. **The same for `core`, if it becomes the tail.** `stitchwort_core "lib"
   (test)` takes 43 s and ended the `opt-level = 1` build at 150 s, right
   behind `elab`'s. Sonnet or DeepSeek, from stage 1's pattern. Expected
   30 min. Measure as in stage 1.
3. **Look again at the 50 to 90 s stretch,** which is `cranelift-codegen`
   as much as `elab`. A separate ticket could ask whether the test
   binaries that don't run native code need `stitchwort-native` through
   `stitchwort-dev-features`. A binary waits for the full `cranelift`
   library before it starts. Analysis first, no build. Expected 30 min.
4. **A real split, only if the numbers change.** Revisit if `elab`'s front
   end passes about 30 s quiet, or if incremental `elab` edits stop being
   dominated by the test binaries. The first cut would then be `derive_*`:
   one-off work per declaration, 22 coarse entry points, no hot paths.
   Then omega and friends, then counterexample. Opus for the hook design
   (it is near term generation), Sonnet for each move, one cut per lane,
   between batches.

## 7. Decisions for Matt

- **D-a:** Don't split `elab` into crates now. Do stage 1 instead.
  [rec: yes]
- **D-b:** Stage 1's way in: test functions compiled into the library
  behind a `unit-tests` feature, rather than moving the tests to
  `tests/` and making the items they use `pub`. [rec: the feature; it
  changes no visibility in the shipped crate]

## 8. Stage 3 analysis: does native hold up the test binaries? (SW-1777)

No build was run; this is from `cargo tree` and the timings quoted in
section 1 (no `--timings` reports are left on disk).

**Who uses `stitchwort-native`.** Only `stitchwort-cli`, as an optional
dependency behind its `native` feature (`dev` turns it on), and
`stitchwort-native`'s own tests. `stitchwort-dev-features` does **not**
depend on it, so section 1's "through `stitchwort-dev-features` that
includes `stitchwort-native`" is wrong. Native code is called from
`cli/src/main.rs` and `cli/src/build.rs` (`n1::compile`, `aot::compile_object`,
`checks::report`) and from the native crate's tests. `driver`, `elab`,
`core`, `rt`, `host`, `js`, `lsp`, `standalone` and `web` never reference
it (`rt/src/native_abi.rs` and `standalone/src/aot.rs` only mention the
name).

**What does reach `cranelift-codegen`.** `stitchwort-dev-features` itself
lists `cranelift-codegen` with `x86` and `arm64`, to unify the feature set
so that a `-p` build doesn't compile it again. Every crate's dev-dependency
on `dev-features` therefore puts `cranelift-codegen` under every test binary,
including `elab`'s unit tests, whether or not the crate runs native code.
Making `native` optional in the CLI would change nothing: it already is.

**What would help: drop that line from `dev-features`.**

- Change: remove `cranelift-codegen` from `dev-features`; give
  `stitchwort-native` an `all-isas` feature (`cranelift-codegen/x86`,
  `/arm64`) that the CLI's `dev` feature and native's tests turn on, so that
  `cli` and `native` builds agree under `-p` and `--workspace`. `task
  test:features` checks that no selection compiles a crate twice.
- Test meaning: no test loses native coverage. The CLI's and native's tests
  keep the full native build. The risk is only a feature-set mismatch that
  compiles `cranelift-codegen` twice for some `-p` selection (more build
  time, not wrong results).
- Clean build: `cranelift-codegen` ends at 99.8 s (264.6 s run) and 92.6 s
  (175.6 s run), always before `elab`'s library (113.8 s and 93.2 s), and the
  tail is `elab`'s and `core`'s unit tests, which wait for `elab`/`core` as
  well. So the critical path gains **0 s**. The test binaries that don't
  depend on `elab` (`core`, `rt`, `syntax`, `host`, `js`) could start up to
  the 0.6 to 14 s earlier, but they are not last.
- Incremental rebuild: **0 s**; `cranelift-codegen` isn't recompiled.
- Where it does pay: a single-package run (`task test:one -- stitchwort_elab`,
  a lane's first test) in a worktree whose kache is cold would skip about 67 s
  of `cranelift-codegen` CPU, about one core's work. With a warm kache it is
  seconds.

**Recommendation:** don't. It saves nothing on the clean build's critical
path or on rebuilds, and it takes apart a mechanism built to stop duplicate
compiles. Stage 3 is closed; correct section 1's sentence if this document
is edited again. Revisit only if `elab`'s library gets under about 60 s,
when `cranelift-codegen` becomes the last library.
