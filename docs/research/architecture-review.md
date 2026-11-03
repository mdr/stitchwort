# Architecture review: weak points, boundaries, elab's size, compilation

SW-1115 (D2239), 3 November 2026, at `e92ab4ed`. Analysis only: no code
changed. It builds on [rust-codebase-review.md](rust-codebase-review.md) (1
Nov) and SW-1091's phase 1 (on the board), checks their claims against the
code as it is now, and adds measurements. The scripts are in
[architecture-review/](architecture-review/): `modgraph.py` (module graph and
state-field use inside a crate), `cochange.py` (files that change together),
`timings.py` (summary of a `cargo build --timings` report). Figures below come
from those scripts or from the commands quoted. Text-based analysis without type
information is approximate. The counts say how large something is; they are not exact.

## 1. Summary

**The broad shape is right.** The crate layering (front end, kernel,
elaborator, driver, untrusted backends, interfaces) is sound. The runtimes never
depend on the elaborator. `driver` is a real shared pipeline: of its 18
modules, only 4 form a cycle. Rewind is enforced at compile time. The
differential tests (cache vs fresh, rewind vs fresh) are the right kind of
test. None of the weak points below needs a rewrite. Most need a few
types with private fields, and a change to how the build is invoked.

**Top five weak points**, ranked by consequence and cost of the fix (details
in §6):

| # | Weak point | Evidence | Fix | Size |
|---|---|---|---|---|
| 1 | **Rebuild fan-out, not elab's size, sets the edit loop** | An elab edit costs 37 s of elab compile, then 367 s of CPU time for driver's 64 test targets alone (median 5.3 s each). About 130 test binaries link elab. The whole stack is built in 2-3 feature variants. 163 of the 1,135 source commits since 1 Oct (14%) changed only `.sw` std files, and each such commit rebuilt the whole stack | One feature set; std read at run time outside distributed builds; fewer test binaries; lanes build what they run | S-M, mostly build config |
| 2 | **The Elaborator's state has no enforced lifecycle** | 116 fields (26 on 18 Oct, 90 on 25 Oct), 47 of them `RefCell`. Only one of the five mechanisms every table must join (rewind) is checked by the compiler. 32 fields are named by none of the hand-written lists. Seven more pieces of inference state are thread-locals in `unify.rs`. Probable instance: `no_finite`, `no_decide` and `generated_alls` are rewound but neither cache-encoded nor dumped, so the differential test can't see them | Group state by lifetime into types that each own their mark, restore, encode and dump, with exhaustive destructuring | L, incremental; needs a design note |
| 3 | **`Globals` is three things, all public** | One struct holds the kernel environment, the elaborator's metavariables, trail and placeholders, and backend metadata (`Data::js`, `erasure`). `Def::ty`/`ty_value` are still `pub`, so the §1.5 bypass is still open. Outside elab, `.globals` is reached at 62 sites in `src` and 279 in tests | Split into a private kernel `Env` with read views, an elaborator `MetaStore`, and backend side tables | M; design note |
| 4 | **Cache keys and fingerprints are hand-maintained lists** | `driver/build.rs` `SOURCES` still omits `rt` (review §1.2 is still open; the SW-1122/1123 lane is on it). The cache `FORMAT` is bumped by hand (20 bumps since 22 Oct). The dump that is meant to catch omissions is itself a hand-kept list | Derive the build fingerprint from cargo's dependency closure. Derive `FORMAT` from a schema hash of the encoders | S-M |
| 5 | **Phase and ownership aren't in the types at boundaries** | `Session { pub elab }`, `Elaborator`'s 19 `pub` fields (settings mixed with tables), callers pairing native code with its image (review §1.3), and about 60 control-flow decisions made by comparing diagnostic code strings (24 of them on `"E-RESOURCE"`) | An `ElabOptions` value, read-only query views, an owned native artifact, an internal error kind | M, several small steps |

**Target architecture (§4):** keep the crate set nearly as it is. Take the
`.sw` standard library out of `elab`'s compiled code. It becomes data,
embedded only by the binaries that ship. Keep `elab` as one crate for now, but
give it a real internal structure: state components with their own
lifecycles, and directories for its seven subsystems. Split it later only
where measurement after steps 1-6 shows a crate boundary would pay. The
candidate is proof automation, about 16k lines, behind a narrow context
trait. The `core`/`elab` boundary gets enforced privacy: the kernel's
environment can only be changed by admission.

**First three steps (§5):** (1) one feature set for every build, and lanes
building only the targets they run, done together; (2) the std library read
from disk in dev and test builds, so a `.sw` edit rebuilds nothing; (3) a
fingerprint derived from the dependency graph. Then come the test-binary
consolidation and the tuned test profile, measured as SW-1091 planned.
After those, the state-lifecycle design note, which is the largest
structural change.

## 2. The current structure

[docs/architecture/crates.pdf](../architecture/crates.pdf) has the graph.
Sizes now (Rust lines in `src/`, inline tests included / other Rust / `.sw`):

| Crate | src | tests etc. | .sw | Test files | Notes |
|---|---:|---:|---:|---:|---|
| elab | 99,460 (77 files) | 0 | 28,222 | 0 (124 inline unit tests) | 75% of source commits touch it |
| core | 20,471 (22) | 12,907 | | 18 | kernel and more |
| rt | 18,053 (29) | 5,023 | | 11 | dev-depends on driver and elab |
| syntax | 13,130 (12) | 780 | | 3 | `parser.rs` 7,809 lines |
| driver | 12,597 (18) | 28,643 | 112 | 63 | most of the integration tests |
| js | 8,718 (5) | 0 | | 0 | `lib.rs` 6,280 lines |
| cli | 6,634 (8) | 21,432 | | 39 | |
| native | 6,544 (8) | 2,568 | | 9 | dev-depends on driver |
| web, fmt, bench, partial-model, standalone, host | 8,172 together | | | 8 | |

Over three weeks elab grew from 17k lines (18 Oct) to 61k (25 Oct), 93k (1
Nov) and 99k now. SW-1091's correction stands: elab has 99k lines of Rust,
not 188k.

## 3. Findings

### 3.1 Modularity and boundaries

**elab.** I counted only `use` and path edges between modules (`crate::m`,
`super::m`, `m::x`). On those edges, 57 of 77 modules (84,880 lines) form
one strongly connected component. That matches SW-1091's 58. Adding method
edges (a call `.f(` to an `impl Elaborator` method defined in exactly one
module) puts 76 of 77 in the cycle. The only module outside is
`library_tests`. The hub is not a module but a type. `Ctx<'e>` (in `check.rs`)
holds `e: &'e Elaborator`, and 49 files take a `Ctx`. Mutation goes through
the `RefCell`s: 309 `.borrow_mut()` and 275 `.borrow()` calls. So any
function anywhere can read or write any table. The module graph only shows
where the code happens to sit.

The modules with the highest fan-in show what the de facto core is:
`module` (68 modules depend on it), `lib` (63), `queue` (52), `check` (49),
`scope` (43), `interfaces` (23), `nav` (20). Some modules depend on almost
nothing in the crate. They have no `crate::` references, or only one or two:
`omega_search` (1,171 lines), `saturate` (345), `shown` (503), `cache/codec`
(689), `timings` (340). They are leaves that could move anywhere. They are
small.

**Which modules touch which `Elaborator` fields** (`modgraph.py --state`;
"touch" means `.field` appears in the module):

- The mechanisms touch the most fields: `cache` 40, `lib` 34, `rewind` 31,
  `cache::dump` 19, `undo` 19, `module` 16, `library` 14, `check` 10.
- Most fields are local in practice. Of 116 fields, 64 are touched by one
  or two modules besides those mechanisms. `globals` is touched by 43
  modules, `scope` by 31, `loading_prelude` by 19 and `module` by 16.
  These four are the shared state. Most of the rest belong to one feature:
  `dot_heads`/`dot_failed` to `dot`, `cong_candidates` to `congruence`,
  `leaf_log`/`arm_probe` to `equations`. They sit on the shared object
  because there was nowhere else to put them.

This is the important structural fact. **The coupling is through one
object, not through a tangle of real dependencies.** Most features are
separable in principle: their state is private to them, and they read only
`globals`, `scope` and `module`. What blocks separation is that the state
lives on `Elaborator`, and that the mechanisms (cache, rewind, undo, dump)
need to see every table.

**Change coupling** (`cochange.py`, 1,135 commits touching crate sources
since 1 Oct): 742 touch one crate, 229 two, 164 three or more. The most
frequent pairs are `elab/check.rs + elab/lib.rs` (89), `elab/lib.rs +
elab/module.rs` (61), `elab/lib.rs + syntax/parser.rs` (60) and
`syntax/ast.rs + syntax/parser.rs` (56; 90% of `ast.rs`'s commits). A
language feature is a vertical slice through parser, AST, `lib.rs` and
`check.rs`. That is expected and not a defect. The mechanism files couple
to `lib.rs`: 87% of `rewind.rs`'s 45 commits also change `lib.rs`, and 9 of
`dump.rs`'s 11 commits change `cache/mod.rs`. That is the "every new table
joins five mechanisms" cost, visible in history. SW-1074 is the recent
example. One new table (`match_columns`) touched `lib.rs` (the field),
`rewind.rs`, `cache/mod.rs` (+33 lines), `cache/dump.rs`, `lift.rs` and
`local.rs`. It needed cache `FORMAT` 20 and an updated `hash_stability`
snapshot.

**core.** 17 of its 22 modules form one cycle (18,317 lines).
`globals` imports `js_repr` and `erase`, and `check` imports `pretty`.
`value` imports `step` (effect resumptions) and `native`. So the trusted
kernel is not a small closed set of modules. The `core` crate is the
kernel plus pretty-printing, JS representation, erasure, floats, native
builtins and the partial runner, all mutually reachable. Only `budget`,
`collections`, `sct` and `reference` stand outside the cycle. This
confirms the review's §2.1 remark ("crate names should not be read as exact
maps of the trusted computing base") and makes it concrete.

**driver** is well modularised: only `driver`, `run`, `check_cache` and
`counterexample` form a cycle (2,801 lines). `search_at`, `doc`, `live` and
`project` are leaves. **rt**: 13 of 29 modules form a cycle around `value`,
`machine`, `code` and `native_abi`. The passes (`lower`, `opt`,
`specialise`, `fusion`, `trmc`, `hoist`, `validate`, `codec`) are outside
it, which is the right shape. **syntax**: `parser` and `ast` form a cycle
with `docs`. `lexer` is a leaf. **cli** and **js** are a few large files
with little internal structure. `js/lib.rs` (6,280 lines) is the review's
§3.4 case.

**Leaky abstractions.**

- `Globals` (`core/src/globals.rs`) has 22 public fields. `defs`, `datas`,
  `metas`, `meta_trail`, `frozen_metas`, `placeholder_syntax`,
  `waiting_literals`, `print_labels`, `hashes`, `budget` and `erasure` are
  all `pub`. `Def::ty` and `Def::ty_value` are still `pub`. Only `body`
  and `state` are `pub(crate)`. The review's §1.5 probe would still
  compile.
- `Session { pub sources, pub elab, pub warnings }`. Outside elab, `.globals` is read
  at 62 sites in driver, cli, web and bench `src` and 279 in their tests
  (mostly `session.elab.globals`), and `.limits` at 40.
- `Elaborator` has 19 `pub` fields. They are settings
  (`rewrite_budget`, `numbers_as_succ`, `instance_budget`,
  `uniform_operators`, ...) mixed with state (`tests`, `total_rows`,
  `counterexample_log`). Hosts set them by assignment after `new`.
- Of elab's 150 distinct `pub fn` names, 85 are called from driver, cli,
  web or bench.

**Duplicated concepts.** Content hashes (`core/hash.rs`), cache keys
(`elab/cache`), the build fingerprint (`driver/build.rs`) and rt's build
hash (`rt/build.rs`, a separate FNV hash) are four answers to "what does
this result depend on". Each keeps its own list of inputs. "Why wasn't X
derived" appears five times as separate maps (`no_eq`, `no_show`,
`no_ord`, `no_finite`, `no_decide`). Three of them are encoded in the cache
and two are not (§3.2).

### 3.2 Data structures

**Core terms and values** (`core/src/term.rs`, `value.rs`). `Term` is an
`Rc` tree with de Bruijn indices. `Value` is NbE with `Rc` closures,
`Spine` is a shared `SmallVec` of eliminators, and `Value::Call` carries a
memoised `Unfolding` (`RefCell`). This suits the use: sharing is cheap,
the evaluator is purely functional, and the memo is a cache that doesn't
affect results. Two parts are **weak**:

- `Term::Meta` and `Term::Loc(Span, _)` are in the kernel's term
  language. `Meta` makes the kernel reject a term the elaborator didn't
  finish. `Loc` makes every kernel traversal skip span nodes. Both are
  elaborator concerns that the trusted checker has to tolerate.
  Fixing this costs a separate pre-kernel term type, which is a large
  change for a small gain. So my recommendation is to **keep** them and
  document the kernel's contract for them ("rejects `Meta`, ignores
  `Loc`").
- `Data::js: Option<Rc<JsRepr>>` and `Globals::erasure` put backend
  facts into the kernel's environment, and so into the trusted crate's
  cycle. These should be side tables keyed by `DataId`, owned by `rt`/`js`
  or by the elaborator. That costs a medium refactor of `js/lib.rs` and
  `cache` (which encodes `JsRepr`).

**The global environment.** `defs: Vec<Def>` and `datas: Vec<Data>` are
indexed by load order (`DefId(usize)`). Rewind truncates them to a
`GlobalsMark`, and the cache refers to declarations by path and content
hash, never by id. For a single session that grows and rewinds, this is the
right design: O(1) lookup, O(1) marks. Its weak point is **persistence
across edits**. Ids are positions, so an edit in an early namespace
invalidates the ids of everything after it. `LiveProject` therefore
rewinds to the first changed namespace and re-checks everything after,
replaying from the cache where it can. That is acceptable at namespace
granularity. Making it finer (per declaration) would need stable ids
(path-keyed) and a dependency graph between declarations. That is a large
change, and I would wait until editor latency on real projects demands it.

**The context** (`elab::check::Ctx`). It is eight parallel vectors (`env`,
`types`, `names`, `written`, `kinds`, `locals`, `lets`, `scope`) that must
be pushed and popped together. `bind`, `bind_hidden`, `define` and
`bind_local` do this, but the fields are `pub`, so nothing stops a caller
from pushing to one. A single `Vec<Entry>` with private fields, plus
accessors for the projections the evaluator needs (`env` as a slice), would
make the pairing structural. The cost is mechanical. I see no evidence that
cloning contexts is a hotspot. Persistent vectors are not justified
without profiling (review §4.5).

**Elaborator tables.** Each of the five mechanisms classifies each field
its own way. Cross-referencing the field lists of `undo::Snapshot`
(**U**), `clear_metas` (**C**, per-declaration cleanup), `rewind::Mark`
(**R**; `s` = a setting the destructuring ignores), `cache/mod.rs`
encode/decode (**E**) and `cache/dump.rs` (**D**):

| Pattern | Fields | Meaning |
|---|---:|---|
| `UC---` | 15 | Per-attempt inference state (obligations, row metas, queue, drafts, ...) |
| `--RED` | 11 | Persistent checked tables (tests, scope, module, interfaces, instances, nav, ...) |
| `--R--` | 11 | Session or project state, rewound but not cached |
| `--sE-` / `--s--` | 22 | Settings: part of the cache key or ignored |
| `--RE-` / `---ED` / `---E-` | 18 | Persistent, handled by some mechanisms but not others |
| `U----` | 4 | Undone but not cleared |
| `-----` | 32 | Named by no list: per-declaration scratch emptied in `rewind`'s body, caches, or omissions |

Rewind is the one mechanism the compiler checks. `Elaborator::rewind`
destructures `Elaborator` exhaustively, so a new field doesn't compile until
it says how it rewinds. The other four are lists kept by hand. **The
predicted failure mode probably exists.** `no_finite`, `no_decide` and
`generated_alls` are rewound (they are in the `retain(|d, _| d.0 <
datas)` group) but are neither encoded nor dumped. Their siblings `no_eq`,
`no_show` and `no_ord` are both. After a cache replay, a later namespace
loses the note explaining why `Decidable`/`Finite` wasn't derived
(`auto.rs:729`, `interfaces.rs:1143`). `derive_induct::all_of` no longer
finds an earlier `D.All`, so it may generate a local `T.%D%All` instead.
If so, a cached session elaborates differently from a fresh one, and
because the dump omits the table, `check_cache.rs` cannot notice. I have not
run anything to confirm this. It should be filed and checked (§7).

Hidden state outside the object: `unify.rs` keeps seven thread-locals
(`POSTPONED`, `RIGID_DIVERGENCE`, `AWAITED_HELPERS`, `SOLVING_ARGUMENTS`,
...). They are inference state that `undo` and `rewind` see only where
code remembers to call something like `unify::forget_lossy_since`.
`kernel.rs` keeps a thread-local rejection log. `queue.rs` keeps 26 global
atomic counters. Only tests read the counters. They are harmless under
nextest's process per test, but they are wrong for two sessions on one
thread, such as the language server alongside a proof-action search.

Snapshots are cheap where tables are append-only `Vec`s: a mark is a
length. Copied tables (`scope`, `instances`, `module`, the dot caches)
cost "a few milliseconds per mark". `nav` moved to an undo log (SW-1052)
when copying became quadratic. That log is the right general shape for any
table rewound by value.

**Cache encoding.** The encoder and decoder are hand-written field by
field (`cache/mod.rs`: `encode` lines 1167-1820, `decode`/`replay_tables`
2280-2970). The design is right: paths and hashes instead of ids, a
Merkle chain of keys, and trusted replay through
`check::admit_trusted_*`. The way it's built is the problem: it has no
structural link to the tables it must cover.

**Session and live index.** `LiveProject` (`driver/src/live.rs`) is a
clean design: texts in, answers out, no threads or files. Its cost model
(rewind to the first changed namespace) follows from load-order ids, as
above.

**Runtime IR.** `rt::Program` has a `validate` and the decoder bounds
counts. The review's §3.2 point (accept only validated or owned results at
entry points) and the native lifetime issue (§1.3) are unchanged.

**Error codes as control flow.** About 60 comparisons on
`Diagnostic::code` strings in elab and driver: `"E-RESOURCE"` 24 times,
`"E-TYPE-MISMATCH"` 13, `"E-FAILED-DEPENDENCY"` 4, and others. Review §3.5
stands.

### 3.3 elab's size: one crate or several?

**A split today would cost more than it saves.** It would not help the
build, and the boundaries aren't real yet.

- **Build.** Measured, an elab edit costs 37 s for elab: 11.3 s front end,
  25.7 s codegen, about 3.2 cores busy on average (118 s of user time over
  37 s). The next step costs much more. With pipelining, `driver` starts on
  elab's metadata after about 14 s, and the CLI binary is linked at about
  50 s. But the 64 driver test targets then take 367 CPU-seconds. A chain
  of crates (`elab-base → elab-check → elab-auto → elab`) only saves time
  when an edit lands in a crate near the top. Each crate's dependents are
  still rebuilt in full, because cargo always rebuilds reverse dependencies
  of a recompiled crate. Splitting also tends to cost runtime speed, since
  inlining across crates needs `#[inline]` or LTO, and the elaborator's
  hot paths (unify, eval callbacks) cross every candidate boundary. Raising
  `codegen-units` and turning on incremental compilation for a test profile
  (SW-1091 step 4) attacks the same 26 s of codegen without either cost.
- **Boundaries.** A crate boundary needs a stable interface. Here every
  subsystem's interface is "`&Elaborator` via `Ctx`". A crate split now
  would turn `pub(crate)` into `pub` on dozens of fields (the opposite of
  encapsulation), or would need the interface first. **The interface is
  the work.** It is the same work as weak point 2, and it should be done
  for correctness anyway.
- **The five mechanisms.** A split would make them worse. The cache
  encoder must see every persistent table. If the tables were spread over
  crates, either the encoder moves up to see them all (it is already the
  most coupled module), or each crate's tables carry their own codec. The
  second is only possible after the state has been grouped.

**What does have a real boundary:**

| Candidate | Lines | Boundary today | Verdict |
|---|---:|---|---|
| The `.sw` std library (`elab/src/std`) | 28k `.sw` | Data. Read via `std_text()`, and already loadable from disk (`STITCHWORT_STD_DIR`, SW-145) | **Move out of compiled code now** (§4). The highest build value of anything here |
| Pure leaves: `omega_search`, `saturate`, `shown`, `cache/codec` | 2.7k | No crate references | Not worth a crate. Keep them as modules |
| Proof automation: `omega`, `ring`, `congruence`, `rewrite`(+`under`), `closing`, `search`, `auto`, `calc`, `counterexample` | about 16k | Works on goals through `Ctx` (eval, unify, fresh metas, queue). `omega` uses `queue` and `undo` | **The candidate for a later crate**, behind a `ProofCx` trait, once the state is grouped. Its edits would then rebuild only it and its dependents |
| Equations and function induction (`equations`, `equations/induct`, `decreasing`, `equation_notes`) | 11.5k | Reads admitted defs, plus `leaf_log`, `arm_probe`, `match_columns`, `local_asts` | A directory, not a crate. Its inputs are tables written while the body is checked |
| Derived instances (`derive*`, `data_auto`) | 6.5k | `impl Elaborator`. Generates surface declarations and checks them | Directory |
| Cache (`cache/`) | 4.4k | Touches 40 fields | Stays with the state it encodes |

### 3.4 Compilation architecture

Measured on this machine (10 cores, 32 GB). The load average is noted for
each run, and the machine was shared: another lane started building `rt` and
`driver` during the last run. CPU-seconds and the lists of rebuilt units
are the figures that don't depend on load. Worktree builds go through
kache. My edits change file contents, so kache misses for the edited crate
and everything above it.

| Run | Rebuilt | Wall | CPU (user+sys) | Load (1-min, before→after) |
|---|---|---:|---:|---|
| `cargo build --release -p stitchwort-elab`, fresh worktree | core, elab | 42.5 s | 139 s | 3.8 → 4.8 |
| Append a comment to `elab/src/omega_search.rs`, same build, `--timings` | elab: 37.0 s (front end 11.3 s, codegen 25.7 s) | 39.7 s | 121 s | 4.4 → 7.3 |
| Revert it; `cargo build --release -p stitchwort-cli -p stitchwort-standalone --features stitchwort-cli/native --timings` (= `task build`) | elab 42.0 s, driver 10.5, cli lib 7.3, cli bin 6.0, native 3.9, standalone 2.7. The rest were kache hits | 51.0 s | 220 s | 6.5 → 13.2 |
| `cargo build --release -p stitchwort-driver --tests --timings` | **elab again** (core's dev feature set) 37.5 s, driver lib 8.8 s, 64 test targets 367 s (median 5.3 s), 421 s over all units | 77.7 s | 442 s | 10.7 → 23.0 |

What these show:

1. **Fan-out dominates.** Below elab, the cost of an elab edit to the
   test loop is about 10× elab itself, in CPU time. Each test target is a
   separate release crate. It compiles its test code at `opt-level=3` and
   links the 26 MB elab rlib plus the rest. About 130 test targets depend
   on elab: driver 63 + lib, cli 39, rt 11 and native 9 (through dev-dependencies on
   driver), bench 3, plus the unit-test targets of elab, driver, cli,
   bench and standalone. rt's and native's tests depend on the elaborator
   because they compile `.sw` programs. So an elab edit rebuilds the
   runtime's tests, although the runtime itself doesn't depend on elab.
2. **Feature variants are real, not inferred.** `cargo tree -e features`
   shows `task build` uses `stitchwort-core` with no features. Every
   test build adds `reference` and `stack-check`, and `stitchwort-rt`
   adds `alloc-trace`. Both come from dev-dependencies. Cargo unifies
   features per invocation, so a different `-p` selection gives yet
   another set (`-p stitchwort-driver --tests` doesn't turn on
   `alloc-trace`). This fresh worktree held three `stitchwort-core` and
   three `stitchwort-elab` rlibs after four invocations. The main
   checkout's `target/release/deps` holds three elab, four driver and four
   cli rlibs (26 MB each for elab). Consequence: **SW-1091's "lanes build
   only what they run" (its step 1) would cause variant rebuilds unless
   it is done together with "one feature set" (its step 2).** I would
   merge the two into one step.
3. **A `.sw` edit rebuilds the whole stack.** `elab/src/lib.rs` and
   `library.rs` `include_str!` all 90 std `.sw` files (24 core files through the `core_files!` macro, 66 library files in `library.rs`). `driver/build.rs` also hashes
   every `.rs` and `.sw` file under syntax, core, elab and driver into
   `STITCHWORT_FINGERPRINT`. So a `.sw` edit recompiles elab, then driver
   and everything above. That happened in 163 of 1,135 commits since 1
   Oct (14%; 272 commits touched std). The run-time path exists already
   (`std_dir.rs`), but tests don't use it.
4. **Not significant:** proc macros (none in the workspace), build
   scripts (under 1 s each; cranelift's 3 s is cached), and dependency
   crates (all kache hits, about 0.1 s each). `docs/research/compilation.md`
   is about compiling Stitchwort programs, not this build, and has nothing
   to add here.
5. **Release for tests is necessary** (SW-1091: debug frames are about 10× larger
   and sweeps are slow). The question is the profile's settings
   (incremental, codegen units, a lower `opt-level` for test crates only).
   That is SW-1091's measurement plan M0-M8, which this review does not
   replace.

## 4. Target architecture

**Crates** (changes in bold; dependencies only point downward):

| Layer | Crate | Responsibility | Key boundary types |
|---|---|---|---|
| Interfaces | cli, web | Commands, LSP, browser API. **The only crates that embed the std library** | `driver::Session` API |
| Orchestration | driver | Sessions, projects, live index, caches' stores, search, docs | **`Session` with private `elab`; read-only `Checked` query view** (defs, datas, names, spans) instead of `session.elab.globals` |
| Elaboration | elab | Surface to core: names, inference, patterns, equations, derives, automation, the check cache | **`ElabOptions`** (all settings, given at construction); **`Elaborator` composed of state components** (below); `StdText` injected by the host |
| Data | **std** (`crates/std`, or plain files) | The `.sw` library and its core-file order. A crate only to provide `include_str!` for distributed builds; dev and test builds read the directory | `StdText` |
| Backends | rt, js, native, host, standalone | As now, plus **the backend side tables (`JsRepr`, erasure facts) keyed by `DataId`** | **owned `PreparedNative`** (review §1.3); validated `Program` |
| Kernel | core | Terms, values, evaluator, **`Env` with private fields: admission is the only writer**; pretty-printing stays here | **`Env` / `EnvView`**, `GlobalsMark`; **`Metas` passed to eval as a store the elaborator owns** |
| Front end | syntax, fmt | As now | |
| Tests | **a few test binaries per crate**, grouped by area | | |

There is deliberately **no kernel crate split.** The `core`/`elab`
boundary is already a crate boundary, so making `Env`'s fields private
enforces the trust boundary at once. A further split of `pretty`, `float`
or `js_repr` out of `core` would not shorten any rebuild, because `core`
sits at the bottom. Its only value would be a visibly smaller TCB, and a
written TCB map gives the same (review §3.3).

**elab's internal structure.** It stays one crate, organised by lifetime
of state and by subsystem:

```
elab/src/
  state/        ElabOptions; Attempt (metas' elaborator side, obligations, row metas,
                queue, drafts, ...; unify's thread-locals move here); Decl (per-declaration
                scratch); Tables (persistent checked tables: scope, module, records,
                interfaces, instances, derive notes, lifted helpers, match columns, tests);
                Session (project and namespace bookkeeping); Presentation (nav, goals,
                warnings, logs); Caches (dot heads, performs, ...: derivable, dropped on rewind)
  check/        check, unify, queue, rows, effects, numbers, dot, defaults, named, local, ...
  decl/         module, admission (from lib.rs), records, interfaces, families, attributes
  patterns/     cases, matching, lift, patlet, induct_match, missing, redundant
  equations/    equations, induct, decreasing, notes
  derive/       derive*, data_auto
  auto/         omega, omega_search, ring, congruence, rewrite, closing, search, auto, calc,
                saturate, counterexample
  cache/        encode, decode, dump, codec
  nav/, library/, project/
```

Each state component implements one trait. Its body exhaustively
destructures the component, so a new field doesn't compile until each
mechanism says what to do with it:

```rust
trait Component {
    type Mark;
    fn mark(&self) -> Self::Mark;          // undo (Attempt) or rewind (Tables, Session)
    fn restore(&mut self, m: &Self::Mark);
    fn encode(&self, w: &mut Writer, since: &Self::Mark);   // Tables only
    fn dump(&self, out: &mut String);                      // Tables only
}
```

`Decl` gets `clear()` and an `assert_empty()` at each mark. `Caches` gets
`clear()`. `ElabOptions` gets `cache_key()` (today's `modes()`). The
`Elaborator` composes them, and the top-level transaction (`Snapshot`,
`Mark`) is a tuple of component marks. This is the review's §3.1
recommendation made concrete. It keeps the five-way classification, but
each table states its class once, beside its definition, and the compiler
checks it.

The canonical dump is meant to be independent of the encoder. Generating
both from one declaration would lose that. So `dump` stays hand-written per
component, but its exhaustive destructuring forces a decision for each new
field. That is what was missing for `no_finite`.

## 5. Migration plan

Each step leaves the system working and is mergeable on its own. **DN**
marks a step that needs a design note and Matt's decision first. Sizes:
S under half a day of lane time, M one to two days, L several lanes.

| # | Step | Size | Depends on | Unblocks |
|---|---|---|---|---|
| 1 | **One feature set, and lanes build what they run.** Make `reference`, `stack-check` and `alloc-trace` uniform across `task build`, tests and targeted runs. The options: always compiled with a run-time switch; or always on in every dev and test invocation (Taskfile passes them), with distributed builds (`nix build`, wasm) differing. Then `test:one`/`test:lane` pass `-p`/`--test` instead of `--workspace` | S-M; **DN (small): which option, and alloc-trace's cost if always compiled** | none | every later measurement; halves stack rebuilds when a lane both builds and tests |
| 2 | **Std from disk in dev and test.** Tests and dev builds read `crates/elab/src/std` (path from `CARGO_MANIFEST_DIR`). Only cli and web release builds embed it, through a tiny `stitchwort-std` crate that only the binaries depend on. `driver/build.rs` hashes `.rs` only, and the fingerprint adds the std text's hash at run time (as `std_dir.rs` already does for `STITCHWORT_STD_DIR`). `CORE_FILES` becomes a file in `std/core/` | M; **DN** (SW-1091 step 3) | none | a `.sw` edit (14% of commits) rebuilds nothing |
| 3 | **Fingerprints from the dependency graph.** `driver/build.rs` takes its source list from the transitive workspace dependencies (rt included). Or each crate's build.rs exports a hash and driver composes them | S | coordinate with SW-1122/1123 | closes review §1.2 for good |
| 4 | **Tuned test profile.** SW-1091 M0-M8 (incremental release, codegen units, opt-level for test crates) | S to set, measurement time | 1 | cuts the 26 s codegen and part of each test target's 5 s |
| 5 | **Fewer test binaries**: driver's 63 and cli's 39 integration tests become a few binaries per crate by area (`tests/<area>/main.rs` with modules). nextest still runs one process per test, so per-process isolation is unchanged | M; **DN** (SW-1091 step 5): grouping, and the cost of editing one test | 1, 4 | the 367 CPU-s of fan-out becomes a few links |
| 6 | **Check the cache omissions now**: test whether `no_finite`, `no_decide` and `generated_alls` diverge after replay; encode and dump them if so | S | none | correctness |
| 7 | **`ElabOptions`**: the 19 `pub` fields and the settings among the private ones (the 22 `s` fields) become one value given to `Elaborator::new`. Its `cache_key()` replaces `modes()` | S-M | none | a typed settings boundary for hosts |
| 8 | **State components** (§4): design note with the full field classification (the table in §3.2 is the start). Then one component per lane: `Attempt` (absorbs `undo::Snapshot`, `clear_metas` and unify's thread-locals), then `Tables` (absorbs rewind, encode and dump), then `Session`, `Presentation`, `Caches` | L; **DN** | 7 | weak point 2; makes step 11 possible |
| 9 | **Kernel environment encapsulated**: `Env` fields private, read views for driver and elab, admission the only writer, test bypasses behind a feature. The elaborator's metavariables move to an elab-owned store passed to `eval`/`quote` as a lookup (how eval sees solutions is the design question). JS and erasure facts become side tables | M-L; **DN** | 8 (Attempt) for the meta store; the `Env` privacy part can go first | weak point 3; review §1.5 |
| 10 | **Small typed boundaries**: an internal error kind (`Mismatch`, `Blocked`, `Resource`, `Cancelled`) alongside `Diagnostic::code`; `Session` with private `elab` and a `Checked` query view; owned native artifact (review §1.3); `Ctx` entries as one vector | M, in independent pieces | none (the query view is easier after 9) | weak point 5 |
| 11 | **Re-measure, then decide on an `elab-auto` crate** behind a `ProofCx` trait. Only if, after 1-5, elab's own compile is still on the critical path of typical edits and automation edits are frequent (`cochange.py` can tell) | M; **DN** | 4, 5, 8 | |
| 12 | **Mechanical file splits** where responsibilities mix: `check.rs` (6.1k), `equations.rs` (6.1k), `effects.rs` (5.0k), `lib.rs` (5.0k; admission to `decl/`), `parser.rs` (7.8k), `js/lib.rs` (6.3k). Done while touching them, with no behaviour change | S each | 8 helps for lib.rs | review locality |

Order by value: 1, 2, 3 and 6 first (cheap, and they remove most of the
rebuild cost, plus a probable correctness bug). Then 4 and 5 (measured).
Then 7 → 8 → 9, the structural work. 10 and 12 run alongside when an area
is touched, and 11 comes last, decided on numbers.

## 6. Weak points in full

1. **Rebuild fan-out.** *Symptom:* §3.4 (an elab edit costs 37 s of elab
   and 367 CPU-s of driver test targets; 2-3 feature variants; `.sw`
   edits rebuild everything). *Consequence:* lanes spend minutes per
   iteration, and CLAUDE.md's test budget exists partly because of it.
   *Fix:* steps 1-5. *Unblocks:* every lane's loop, and a clean
   measurement of whether elab's own size matters.
2. **Elaborator state lifecycle.** *Symptom:* 116 fields, five mechanisms
   with one enforced, 32 fields in no list, seven thread-locals, the
   probable `no_finite`/`generated_alls` gap. SW-1074 touched six files
   and a cache format for one table. *Consequence:* every feature that
   adds a table risks a cache-replay or rewind divergence that the
   differential tests can't see when the dump has the same omission.
   The cost grows with each table (fields went from 26 to 116 in 16 days). *Fix:* steps 7-8. *Unblocks:*
   safe growth; an elab crate split if ever wanted; finer-grained rewind.
3. **`Globals` mixes kernel, elaborator and backend state, all `pub`.**
   *Symptom:* §3.1, §3.2. *Consequence:* the trust boundary holds by
   discipline, not by types. The elaborator's undo has to reach into the
   kernel's struct (`meta_trail`). Backend changes (JS representation)
   edit the kernel crate. *Fix:* step 9. *Unblocks:* a TCB that can be
   stated in one sentence; backend work without touching core.
4. **Hand-kept dependency lists for caches.** *Symptom:* rt missing from
   the fingerprint; 20 manual `FORMAT` bumps; four hashing schemes.
   *Consequence:* stale cached results after a runtime change, with test
   evidence quietly reused. *Fix:* step 3, plus a `FORMAT` derived from a
   hash of the encoder's schema (the field list of each `Tables`
   component, once step 8 exists). *Unblocks:* trust in warm runs.
5. **Phase and ownership not in types at boundaries.** *Symptom:* `pub
   elab`, `pub` settings, native image/code pairing, about 60 string-code
   decisions. *Consequence:* errors in how callers pair pieces compile.
   A reworded error can change control flow. *Fix:* steps 7, 9 and 10.

Two things I checked and would **leave as they are**: `Rc`/`RefCell`
throughout (fine for single-threaded sessions; review §2.4), and
load-order ids in the environment (right for append-and-rewind; revisit
only for per-declaration live re-checking).

**Where the earlier notes are out of date:** review §1.2 (rt missing from
the fingerprint) and §1.5 (public `Def::ty`) are unchanged, so they are
still current. SW-1091's "inferred" feature duplication is now measured.
Its step order 1-then-2 should be one step (§3.4 point 2). Its proposal 3
is half built already: `std_dir.rs` exists, but tests and build scripts
don't use it. The review's line counts are a few hundred lines low
throughout. elab has grown by about 6.5k lines since 1 Nov.

## 7. Open questions for Matt

1. Feature uniformity (step 1): compile the reference evaluator,
   stack check and allocation tracing into every dev build with run-time
   switches, or turn them on in every dev and test invocation and let
   only distributed builds differ? [rec: always on in dev and test via
   the Taskfile; measure alloc-trace's run-time cost before deciding
   whether to always compile it]
2. Std library as data (step 2): may tests and dev builds read
   `crates/elab/src/std` from disk by default, with only cli and web
   release builds embedding it? [rec: yes]
3. State components (step 8): is this the structural priority after the
   build steps, ahead of more file splits? [rec: yes. It is the fix for
   the class of bug the differential tests can miss]
4. Elab crate split: agree to defer it until steps 1-5 and 8 are done
   and re-measured? [rec: yes]
5. File tickets for: the probable cache omission (`no_finite`,
   `no_decide`, `generated_alls`; step 6); `queue.rs`'s global counters
   and `unify.rs`'s thread-locals as session state; and `Data::js` and
   `Globals::erasure` moving out of the kernel? [rec: yes, the first now]
