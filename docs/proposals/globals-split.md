# Proposal: splitting `Globals` by lifetime

**Status:** Draft 1, 3 November 2026 (SW-1174, D2288). Nothing here is built.
This is step 8 of [elaborator-state.md](elaborator-state.md) §7, and the
architecture review's step 9 and issue 3
([architecture-review.md](../research/architecture-review.md)). The claims
about the code were checked by reading it at `70ce52e2`. Measurements say
what was run and where; estimates are marked as estimates. Decisions for
Matt are in §8 (D2290-D2295).

## 1. Summary

**The problem.** `Globals` (`crates/core/src/globals.rs`) is one public
struct of 22 fields with at least five lifetimes: the kernel's environment,
a hash cache, evaluator modes and caches, the unit's module name, the
elaborator's metavariables, and operation state. Three things follow.

- *Rewind, undo and the cache can't be checked whole.* The lifetime
  components of elaborator-state.md give every mechanism an exhaustive
  destructuring, but the 9 meta-store fields sit outside them. `undo.rs`
  restores 5 of them by hand. The 3 queue mirrors are kept in step by the
  queue's own code. `Globals::rewind` names every field, but treats
  per-declaration flags (`failed_mentioned`, `glue`) as part of a kernel
  mark. The external review said so: until the split is done, "the lifetime
  refactor hasn't established its invariants across the entire elaborator"
  ([elaborator-state-review.md](../reviews/elaborator-state-review.md)).
- *The trust boundary holds by discipline.* Every field is `pub`, and so
  are most of `Def`'s and `Data`'s. The elaborator writes facts straight
  into admitted declarations (`Data::js`, `Data::defaults`,
  `Def::update_shown`, `Def::param_defaults`). The kernel's admission runs
  in whatever evaluator mode its caller left: it resets `glue` itself, but
  not erasure.
- *Parallel checking would be blocked.* The kernel's environment would be
  the shared base of every worker. Today it lives in a struct full of
  `RefCell`s and `Cell`s, which can never be shared between threads.

**Recommendation.**

1. **`Env`** (core): `defs`, `datas`, `builtins`, `registry`, with private
   fields, read views, and admission as the only writer. It holds no `Cell`
   or `RefCell`.
2. **The meta store** (elab): the 9 meta fields move into `state::Attempt`,
   where `Attempt::mark`/`restore`/`reset` destructure them.
3. **The evaluator reads solutions through a context struct** that holds
   `&dyn Metas` (§3). Admission takes no store at all. It builds its own
   context with `NoMetas` and kernel modes, so the kernel can't see a
   metavariable solution, whatever the caller does.
4. **Evaluator state** that is neither environment nor metas (budget, glue,
   transparency, erasure mode, the `Apart` interner) goes into a core
   `Machine` that the session owns. The derivable caches (`hashes`, erasure
   per definition) go into per-session caches.
5. **The elaborator's facts leave `Env`.** `Data::js`, `Data::defaults`,
   `Def::update_shown`, `Def::param_defaults` and `unfinished` become
   `OwnedBy` tables in `Tables`. `module` goes to `Unit`, and the kernel is
   given each declaration's path.

**What it buys.**

- Rewind, undo and cache correctness becomes structural across the
  whole elaborator, not just the parts already in components.
- The kernel's trusted base becomes one sentence: "the admission functions,
  run on an `Env` with no metavariables and the kernel's own modes".
- `Env` becomes the shareable base that the frozen base (step 9) and
  parallel workers need, once terms move to `Arc`.

**What it costs.**

- About 7 lanes of 1-3 hours (an estimate). Most of the work is mechanical:
  278 lines in core that take `&Globals` or `&mut Globals`, 759 `.globals` uses
  in elab's sources, and 451 outside elab (134 in other crates' sources,
  317 in tests).
- An API change for every host crate (driver, cli, rt, js, native).
- At run time: nothing measurable. In the benchmark of §3.3, every way of
  reaching the store costs the same as today, within the noise of the
  benchmark's own code layout (about 2 ns per step).

## 2. What `Globals` holds today, and where each field goes

### 2.1 The fields

All 22 fields are listed, in declaration order. The kinds are
elaborator-state.md's (§4.1 components, §4.2 table kinds). "Reads" says
which code reads the field outside `globals.rs`, counted by `grep` at
`70ce52e2`.

| Field | Lifetime today | Reads | Destination | Why |
|---|---|---|---|---|
| `defs`, `datas` | grow with each unit; cut by length on rewind | everyone | `Env` (core, private) | the kernel's environment |
| `builtins` | per id; its own mark | evaluator, natives, hosts | `Env` | evaluation depends on it; bound only by kernel functions (`register_*`) |
| `registry` | per id; `forget_from` | evaluator, printer, hosts | `Env` | prelude identities; `install_library` is the one direct write by elab (`library.rs:728`) |
| `metas` | per declaration; undone by `Snapshot`, emptied by `clear_metas` | evaluator (solution only), elab | `Attempt` (meta store) | inference state |
| `meta_trail` | same | elab only | `Attempt` | the undo log of solutions |
| `frozen_metas` | same | elab only | `Attempt` | |
| `lifted_calls` | same | elab only | `Attempt` | |
| `unfilled_placeholders`, `placeholder_syntax`, `waiting_literals` | mirrors of the queue (`Queue::sync_item`) | elab; printer (`placeholder_syntax`) | `Attempt`, beside the queue | they mirror `Attempt::queue`; the printer reads one through a hint trait (§3.5) |
| `print_labels` | per declaration | printer, elab | `Attempt` | messages only; read through the hint trait |
| `meta_epoch` | counts solutions taken back | evaluator (`Unfolding`, `TREE_MEMO` keys) | `Attempt` (the store's) | read through `Metas::epoch` (§3.4) |
| `hashes` | derivable; cut by id on rewind | `hash.rs` | `Caches` (per session), `Derived` | a `RefCell` cache can't be in a shareable `Env` |
| `budget` | per operation; holds the cancel flag | evaluator (every step), everyone | `Machine`, owned by `Session` | operation state |
| `failed_mentioned` | per declaration; in `GlobalsMark` | written by the printer, read by `goals.rs` | `Decl`, through the hint trait | a message flag, not kernel state |
| `unfinished` | cut by id | elab only (the kernel "never reads this", its doc says) | `Tables`, `OwnedBy<DeclId, ()>` | an elaborator fact about failed declarations |
| `erasure` | mode flags set by a guard; per-definition cache cut by id | evaluator | mode flags in `Machine`; the cache in `Caches`; `disabled` in `Options` | see §2.2: not a backend side table |
| `module` | per unit; swapped by library loads | the kernel (`check.rs:1816`, `:2226`: a declaration's `path`) | `Unit`; the kernel is given the path | the path is hashed (§2.2) |
| `glue` | dynamic extent, set by guards; in `GlobalsMark` | evaluator, kernel | `Machine` (mode) | the kernel sets it itself while checking a body (D483) |
| `transparent` | dynamic extent, `TransparencyGuard` | evaluator, kernel | `Machine` (mode) | the kernel sets it for each check |
| `apart_sets` | grows only; kept by rewind | evaluator only | `Machine` | an interner for `Apart` names: no elab reads |

And the facts the elaborator writes into admitted declarations:

| Field | Written by | Read by | Destination |
|---|---|---|---|
| `Data::js` | elab (`attributes.rs:606`, cache replay) | js, cli | `Tables`, `OwnedBy<DataId, Rc<JsRepr>>` |
| `Data::defaults` | elab (`defaults.rs:100`, replay) | elab, js, cli | `Tables`, `OwnedBy<DataId, _>` |
| `Def::param_defaults` | elab (`set_param_defaults`) | elab | `Tables`, `OwnedBy<DefId, _>` |
| `Def::update_shown` | elab (`lift.rs:724`, replay) | printer, elab | `Tables`, `OwnedBy<DefId, _>`; printer through the hint trait |
| `Def::param_default` | elab (`set_param_defaults`) | **evaluator** (`value.rs:1054`, while gluing), printer | stays in `Env`; set by a kernel function on a pending definition, like `mark_folded` (§4) |

The check cache already writes the first four as "side facts of the
unit's declarations" (elaborator-state.md §4.2, "As built"), so moving them
into `OwnedBy` tables needn't change the entry's bytes.

*As built (SW-1187, step 8b).* The six facts (with `unfinished`, as two
tables, one per id kind) are `Tables` fields; the entry's bytes are the
same (466 entries of the example projects written by the build before and
after, equal apart from the key and salt). Four things differ from the
table above:

- **The printer reads `param_defaults` too** (`Printer::call_with_defaults`),
  not only `update_shown`. Both are read through `&Globals`, and the
  `Shown` trait (§3.5) doesn't exist until 8e. So `Globals::print_hints`
  (`PrintHints`) holds the two maps, and the `Tables` fields
  (`SharedOwnedBy`, the `OwnedBy` kind over a shared map) write the same
  maps: one set of rows, two readers. 8e deletes `PrintHints` when the
  printer takes `Shown`.
- **`unfinished` is read through `&Globals` too**, by the kernel wrappers'
  `goals::unfinished_dependency` (`elab/src/kernel.rs`), so those wrappers
  (`define_def`, `define_group`, `declare_def`, `retype_def`) take
  `&Tables`.
- **`param_default`** is set by `check::mark_param_default`, while the
  helper is pending (between its `declare_def` and `define_def`, in
  `make_helper`), and on a cache replay as the helper is admitted
  (`cache::submit`, from the entry's `param_defaults` rows).
- The backend reads `js` and `defaults` through
  `core::backend::View` (`Deref` to `Globals`, plus `js(d)` and
  `defaults(d)`), made by `Elaborator::backend()` over `Tables`.

### 2.2 Where the code differs from elaborator-state.md

- **`erasure` isn't a backend side table** (Appendix B says
  `Tables`, `OwnedBy<DataId, _>`). It is three things: a mode of the
  evaluator (`active`, `program`, set by `Erasure::running()` around a run),
  a lazily computed per-definition cache (`defs`, from `ty_value`), and a
  test switch (`disabled`). The evaluator reads it at 12 sites in
  `value.rs`. The mode is soundness-relevant: the checker must never erase
  (erase.rs: "The checker never runs with erasure"). Admission doesn't
  reset it today. Nothing calls admission inside a `running()` guard as far
  as I read (the guards are in `run.rs`, `driver.rs` and counterexample
  search), but nothing stops it either. §4 makes it impossible.
- **`Data::js` is the backend side table**, with `Data::defaults`,
  `Def::update_shown` and `Def::param_defaults` beside it (§2.1).
- **`module` is read by the kernel.** `push_def` and
  `push_data_group` (`check.rs:1816`, `:2226`) set `Def::path` and `Data::path` from
  `g.path(name)`. `Data::path` is hashed (types are nominal), so moving
  `module` out changes a kernel API, and hashes must stay byte for byte the
  same.
- **`unfinished` isn't kernel state** (Appendix B says `Kernel`). The
  kernel never reads it; it belongs in `Tables`.
- **`apart_sets` is the evaluator's**, not `Decl`'s. Only `value.rs` reads
  or writes it, and its names must stay valid as long as any value holding
  one lives. So it is a per-session interner, kept on rewind, as today.
- **"Empty whenever the kernel runs"** (the doc of `Globals::metas`) isn't
  true. `lift` admits helpers while the declaration's metavariables exist
  (`lift.rs:805`). `check_proof_glued` calls `infer_closed` before
  `clear_metas` (`lib.rs:840`). Seven elaborator sites use the kernel's
  `infer`/`check`/`check_type` as a typing oracle over elaborator values
  with unsolved metavariables (`rewrite.rs:1244`, `:1255`, `:1363`,
  `cases.rs:862`, `:1821`, `check.rs:4180`, `matching.rs:1341`). §3.6 says
  why this is sound today, and what the split changes.

## 3. How the evaluator reads metavariable solutions

### 3.1 What the evaluator needs

Core reads very little of the meta store:

- `meta_solution(m)`, at 7 sites (`value.rs:550`, `:942`, `:1064`,
  `:1562`, `:3299`; `reference.rs:40`, `:236`);
- `meta_epoch`, at 3 (`Unfolding::get`/`set`, and the key of `TREE_MEMO`
  at `value.rs:2904`);
- the printer reads `placeholder_syntax`, `print_labels` and
  `failed_mentioned` (one site each), and `Def::update_shown`.

Nothing in core reads `meta_trail`, `frozen_metas`, `lifted_calls`,
`unfilled_placeholders` or `waiting_literals`. Nothing in core solves a
metavariable: `solve_meta` and `new_meta` are called only by elab (and four
driver tests). So the evaluator's interface to the store is two methods:

```rust
pub trait Metas {
    fn solution(&self, m: usize) -> Option<Value>;
    fn epoch(&self) -> u64;
}
pub struct NoMetas; // solution: None; epoch: 0
```

The evaluator also reads, on every step or nearly, things that aren't
metavariables: `env` (defs, datas, builtins, registry), `budget`, `glue`,
`transparent`, the erasure mode, `apart_sets`. So whatever replaces
`&Globals` as the evaluator's argument carries four things: the
environment, the store, the machine (budget and modes), and the caches.

### 3.2 The options

| | Shape | Kernel passes |
|---|---|---|
| A | `Ev<'a> { env: &Env, machine: &Machine, metas: &dyn Metas }`, passed as `&Ev` | `&NoMetas` |
| B | generic: `Ev<'a, M: Metas>`, every evaluator function `<M>` | `NoMetas` (a second instantiation) |
| C | the store as a separate argument: `eval(env, machine, metas, ..)` | an empty store |
| D | `Ev` with a concrete `&MetaStore` (core defines the store type) | an empty `MetaStore` |
| D' | as D, with `Option<&MetaStore>` | `None` |

### 3.3 Hot-path cost (measured)

**The benchmark.** A throwaway crate (not committed: it models the
evaluator, so it says nothing a recorded benchmark should track). It has a
toy evaluator shaped like `value.rs`: an environment of 30,000 large `Def`s
indexed by id, a budget step per node, solutions behind a `RefCell`, and
`Rc` values. The workload is a balanced tree of 2^16 leaves (about 200,000
steps per evaluation). A leaf is a definition unfolding or, at 0%, 10% or
50% of leaves, a metavariable read. Each evaluator function is
`#[inline(never)]`. There were 41 samples of 2 evaluations each. The
variants were interleaved in a rotating order, so that load drift hits all
of them alike. The table gives the minimum time, the measure least affected
by other load. It was run on Speedwell (10 cores) at 23:08 on 3 November,
load average 16.4 at the start and 13.7 at the end (other lanes' tests
were running). Release build, `codegen-units = 1`.

| ns per step (min of 41) | 0% metas | 10% | 50% |
|---|---:|---:|---:|
| today: `&Globals` | 17.0 | 15.3 | 18.0 |
| D: `&Ev` with `&MetaStore` | 16.7 | 14.5 | 16.2 |
| A: `&Ev` with `&dyn Metas` | 13.6 | 13.9 | 14.7 |
| B: generic, `MetaStore` | 13.4 | 13.8 | 14.5 |
| C: separate arguments, by value | 14.0 | 13.9 | 14.5 |
| D': `Option<&MetaStore>` | 13.6 | 13.8 | 14.5 |
| kernel, B with `NoMetas` | 13.7 | 11.8 | 9.1 |
| kernel, A with `&NoMetas` | 13.8 | 11.9 | 9.2 |
| kernel, D' with `None` | 13.5 | 12.0 | 9.2 |

**What it shows.**

- No option costs more than today. `&Globals` and D are slower than A, B,
  C and D' even at 0% metas, where the meta path never runs. D's code is
  the same as C's apart from passing by reference. So the 2-3 ns between
  the two groups comes from code layout, not from the option. That is the
  benchmark's noise floor. A run in a fixed order at load 17, and a
  second rotated run, showed the same grouping.
- A trait object costs nothing measurable. The call is perfectly
  predicted, and the work behind it (a `RefCell` borrow and an `Rc` clone)
  is the same in every option.
- The kernel's rows are faster only because a metavariable leaf with no
  store is a cheap neutral, with no clone. That is an artefact of the
  workload: the kernel never meets a metavariable on a real check (§3.6).
- *Estimate:* a real evaluator step does far more than the toy's (spines,
  closures, case trees). So whichever option is chosen, its share of an aoc
  check is under 1%. That can't be seen with `STITCHWORT_TIMINGS` without
  building the change, so lane 8e measures it (§6).

**Compile time and code size** (estimates). B instantiates the shared
evaluator twice if the kernel uses `NoMetas`: `value.rs`, `reference.rs`,
`step.rs`, `native.rs` and part of `pretty.rs`, about 8,000 lines. It also
puts `<M: Metas>` on roughly 150 signatures. With a single instantiation, B
buys nothing over A. A, C and D compile once.

### 3.4 Borrow-checker consequences

- **Eval borrows `Env` immutably while the elaborator mutates metas.** This
  is the case today, and it stays fine. The store keeps its `RefCell`s:
  they move with their fields into `Attempt`, which elaborator-state.md §4.1
  allows ("the `RefCell`s stay where code with `&Elaborator` mutates
  them"). Eval borrows a solution only for the clone in
  `Metas::solution`. Elab code solves metavariables through `&Elaborator`,
  between evaluations, as it does now.
- **Admission needs `&mut Env`.** The elaborator calls admission from
  `&mut self` methods (`kernel::define_group(&mut self.globals, ..)`
  today). With the split, the call borrows `&mut self.kernel.env` and
  `&self.session.machine`, two disjoint fields, so it compiles if the call
  names the fields directly rather than going through a `self.ev()` method
  that borrows all of `self`. No `Ctx<'e>` (which holds `&Elaborator`) ever
  admits.
- **C** breaks nothing but adds two or three arguments at every one of
  about 1,500 call sites, and the next piece of evaluator state adds another
  everywhere. **A** and **D** change each `&self.globals` once, into
  `&self.ev()` (an `Ev` built from four references, by value), and the next
  piece of state is a field of `Ev`.
- **The epoch.** With one store per session, and none in the kernel, the
  epoch belongs to the store. `NoMetas::epoch()` is 0, and the store's
  epoch starts at 1. An `Unfolding` stamped 0 was made with no
  metavariables, so it is valid in any store. An implementation detail,
  decided here: `Unfolding::get` accepts epoch 0 or the current epoch, so
  values made by the kernel (`Def::ty_value`) keep their unfoldings in the
  elaborator. `TREE_MEMO` lives for one outermost comparison and never
  spans two stores, so its key needs no change.

### 3.5 The printer's hints

The printer reads three per-declaration hints and one table. It gets a
second small trait, decided here as an implementation detail:

```rust
pub trait Shown {
    fn placeholder(&self, m: usize) -> Option<PlaceholderSyntax> { None }
    fn print_label(&self, head: &Term) -> Option<&PrintLabel> { None }
    fn update_shown(&self, id: DefId) -> Option<Rc<UpdateShown>> { None }
    fn note_failed_mentioned(&self) {}
}
```

The elaborator implements it over `Attempt`, `Decl` and `Tables`. The
kernel's messages use the defaults.

### 3.6 The soundness story

**What is true today** (read from the code, not probed at run time):

1. Admission takes terms and kernel-made declarations, never `Value`s. The
   admission functions are `declare_*`, `define_*`, `admit_trusted_*` and
   `register_*`.
2. A `Term::Meta` in a submitted term is refused. `infer` returns
   `E-MALFORMED` "unsolved metavariable" (`check.rs:408`), whether or not
   the elaborator has solved it, and `check` falls through to `infer` for
   it. The test `rejects_an_unsolved_metavariable`
   (`crates/core/tests/kernel.rs:103`) covers the unsolved case. No test
   submits a solved one.
3. Hashing a `Term::Meta` panics (`hash.rs:649`).
4. So the values the kernel evaluates during admission come from checked,
   meta-free terms, and from `Def::ty_value`, which only the kernel writes
   (`check.rs:1870`; no elab site assigns it, though the field is `pub`).
   The kernel's evaluator would read a solution if it met a `Head::Meta`.
   Admission gives it none, but nothing in the types guarantees that.
5. The oracle uses (§2.2's seven sites) run the kernel's `infer`/`check`
   over elaborator values that may hold unsolved metavariables, with the
   elaborator's solutions visible. Their answers are advice: the
   elaborator acts on them, and the term it finally builds is admitted
   from scratch. They aren't part of the trusted base.

**After the split:**

- Admission's signature has no store: `define_group(env: &mut Env, machine:
  &Machine, members)`. It builds `Ev { env, machine: kernel modes, metas:
  &NoMetas }` itself. The kernel can't see a solution, solved or rolled
  back, because none is reachable from its arguments. A `Term::Meta` is
  still refused by point 2. If it weren't, it could only evaluate to a
  stuck neutral. No assertion is needed: the guarantee is in the types.
- The oracle builds its kernel `Ctx` from the elaborator's `Ev`, store
  included (`kernel::Ctx::with_variables(&ev, ..)`), as today. The trusted
  base is then the admission functions and the code they reach, run with
  `NoMetas` and the kernel's modes. The same checker code run by the
  elaborator with its store is not trusted.
- Lane 8e adds the missing test: a metavariable that the elaborator has
  solved, submitted to admission, is refused.

## 4. The trust boundary

**What `Env` holds:** `defs`, `datas`, `builtins`, `registry`, and nothing
the kernel and the evaluator don't read. Every field is private to core.

**Who writes it, and when:**

| Write | Today | After |
|---|---|---|
| a declaration's type, body, state, arity, group, transparency set, `lift_leaf`, `recursive`, validators | kernel functions; but `Def::ty`, `ty_value`, `arity`, `group`, ... are `pub` | kernel functions only (fields `pub(crate)`, read through getters) |
| evaluation hints on a pending declaration (`opaque`, `unfolding`, `fold`, `instance`, `auto_params`, `param_default`) | kernel functions `mark_*`, `set_*` for most; `param_default` written directly by `Globals::set_param_defaults` | kernel functions only, on a pending declaration; `param_default` gets one |
| built-in bindings | kernel functions (`register_*`, `registry::bind_*`); `registry.install_library()` directly | kernel functions only |
| the elaborator's facts (`js`, `defaults`, `param_defaults`, `update_shown`) | elab writes the fields directly, after admission | not in `Env`: `OwnedBy` tables in `Tables` |
| rewind | `Globals::rewind` (truncate, cut) | `Env::rewind(&EnvMark)`: kernel-side, lengths only |
| tests that build broken states | `#[doc(hidden)] set_*_unchecked_for_tests` (3 uses) | the same functions behind a `test-bypass` cargo feature of core, which only the dev feature set enables |

**How it is enforced.** By privacy, with no capability type. `Env`'s
fields are private to `stitchwort-core`, and every write is a `pub fn` of
the kernel's (`check.rs`, `native.rs`, `registry.rs`). That is the review's
"admission the only writer". A capability token (`struct Admit(())`,
handed to the elaborator) would add nothing: the elaborator is the kernel's
only caller anyway, and the kernel checks what it is given, whoever passes
it.

**The modes.** Admission sets its own `Machine` modes: glue off at entry
and on only for a body (D483), an empty transparency set except where the
kernel sets one, and erasure off. This replaces `kernel.rs`'s `unglued`
wrapper and the four `debug_assert!(!g.glue.get())`s. It closes the
erasure gap of §2.2 by construction. The budget is the caller's, since
resource limits and cancellation apply to the whole operation.

**`param_default` is read by the kernel's evaluator** while it glues a body
(`value.rs:1054`). It changes which calls stay folded, never what is equal
(the folded-calls invariant), so the kernel's verdict doesn't depend on it.
The note keeps it in `Env`, set through a kernel function, so that the
evaluator's input stays inside the boundary. Folded-calls already relies on
the same argument for `fold`.

## 5. Keeping parallel checking possible

elaborator-state.md §4.9's constraints, applied here:

- **`Env` is the shareable base.** After the split, `Env`'s own fields
  hold no `Cell` or `RefCell`: `Builtins` and `Registry` have none (read at
  `70ce52e2`), and the two lazy caches (`hashes`, erasure per definition)
  leave it. What still stops `Env: Sync` is `Rc` in terms and declarations
  (28 `Rc<` lines in `globals.rs`, 28 in `term.rs`, 54 in `value.rs`). That
  is §4.9's core-wide `Arc` question, and this split doesn't need to answer
  it. Step 9's frozen base wraps `Env` in `Rc` now and `Arc` later.
- **The meta store is per worker.** It lives in `Attempt`, so a worker
  that elaborates a namespace has its own. `Ev` borrows it as `&dyn Metas`,
  which needs neither `Send` nor `Sync`.
- **`Machine` and the caches are per worker.** The budget is per operation
  already. Its cancel flag is an `Arc<AtomicBool>` that the host can share
  with each worker.
- **No new interior mutability.** The interior mutability the split moves:
  11 `RefCell`s and 3 `Cell`s of `Globals`, the `Rc<RefCell<..>>` of
  `Transparency`, `Erasure`'s 3 `Cell`s and 1 `RefCell`, and `Budget`'s 18
  `Cell`s and 2 `RefCell`s. All of it moves out of the shareable part
  (into `Attempt`, `Machine`, `Caches`, `Tables`). None of it is new. Of
  core's 6 `thread_local!`s, `TREE_MEMO`, `EQUAL_CALLS` and `RUNS` are
  evaluator scratch for the dynamic extent of one evaluation, which is
  per thread by nature. `EMPTY` and `LEAF` are constants. The split doesn't
  touch them. `kernel.rs`'s `RECORDING`/`REJECTIONS` (elab) are §2.8's test
  hook, also untouched.

## 6. Migration

Each step is one lane and keeps `main` working. Every lane runs `test:lane
AREA=core` and the targeted tests named below. The orchestrator runs the
merge tier, `task audit` and `test:merge` (core changes in every step).
Every step that generates or admits kernel terms is reviewed by Opus
(CLAUDE.md).

| # | Step | What it fixes | Acceptance |
|---|---|---|---|
| 8a | **Read views.** `Def`'s and `Data`'s kernel-written fields `pub(crate)` with getters; `Env` as a type inside `Globals` (`globals.env`) with private fields; the test bypasses behind the `test-bypass` feature. Mechanical; a sweep of driver (104 `defs` reads), rt, js, cli | the §1.5 bypass: nothing outside core writes a type, body or state | everything builds; `test:lane AREA=core`; core's `kernel.rs`, `admission.rs`; `hash_stability`, `pinned_hashes` |
| 8b | **The elaborator's facts out of `Env`.** `Data::js`, `Data::defaults`, `Def::param_defaults`, `Def::update_shown`, `unfinished` into `Tables` as `OwnedBy`; the JS backend and cli read them through a view the session hands over; `param_default` through a kernel function | backend changes stop editing core; the facts get table kinds (rewind, encode, dump by kind) | `check_cache.rs` (entries byte for byte the same as before, as step 5 checked), `rewind.rs` (normal sample), `test:lane AREA=js`, `navigation.rs` |
| 8c | **`module` out.** `declare_def` and `declare_*data_group*` take the declaration's path; `module` into `Unit`; `library::Context`'s swap of it goes | the kernel stops reading unit state | `hash_stability`, `pinned_hashes` (hashes unchanged), `namespaces.rs`, `std_library.rs` |
| 8d | **`Machine` and the caches.** `budget`, `glue`, `transparent`, erasure mode, `apart_sets` into `core::Machine`; `hashes` and erasure's per-definition cache into a core `EvalCaches`; `failed_mentioned` into `Decl`. `Globals` is now `{ env, machine, caches, metas.. }` | `GlobalsMark` keeps only lengths; modes have one home | `rewind.rs`, `resources.rs`, `test:lane AREA=core`, core's `glue.rs` |
| 8e | **`Ev` and `Metas`.** Core's evaluator, printer and checker take `&Ev` instead of `&Globals`. Admission takes `(&mut Env, &Machine)` and builds `Ev` with `NoMetas` and kernel modes. The 9 meta fields move into `Attempt` as `MetaStore: Metas`, and `Globals` is deleted. Two lanes if the diff is too large: 8e-1 introduces `Ev` with all fields still borrowed from `Globals`, a mechanical sweep; 8e-2 moves the store | the trust boundary (§3.6, §4); undo and reset destructure the store; the erasure gap | the new kernel test (a solved metavariable submitted is refused); elab's `undo` unit tests; `postponement.rs`, `rewind.rs`, `check_cache.rs`, `fuzz_elab.rs`'s rejection checks; `STITCHWORT_TIMINGS` on aoc before and after (a background run of about a minute each, an estimate) |
| 8f | **The meta store's own mechanisms.** `Attempt::mark`/`restore` destructure `MetaStore`; the three queue mirrors become views of the queue, or are restored by it, whichever its lane finds simpler | undo completeness for the store (see finding G2) | `undo` unit tests, `postponement.rs`, a new test per mirror |

**Order** (an implementation decision, made here). 8a-8f run one at a
time: every one edits core and its callers. 8a can start any time after
step 6c, since it doesn't touch elab's state. 8b and 8c touch
`cache/mod.rs`, so they wait for 6c, which is rewriting how entries are
built. Step 7 (`Presentation`) is independent of all of them. It can run
before, between or after, but not side by side with one that edits
`lib.rs`. Step 9, the frozen base, comes after 8d: it freezes `Env`, and
it is simpler once `Env` holds no caches and no modes.

*Estimate:* 7 lanes (8e as two), 1-3 hours each. 8a and 8e-1 are
mechanical sweeps that suit DeepSeek from a goal-level brief, with Opus
review of the core diff. 8e-2 and 8f suit Opus or Sonnet.

## 7. Alternatives rejected

- **Leave the metas in core's `Globals` and make only `Env` private.**
  This is the cheapest option, and it fixes the §1.5 bypass. But the
  kernel's admission would still run in a struct that holds the
  elaborator's solutions, and the undo mechanism would still reach into
  core (`meta_trail`). The review's issue 3 and the "invariants across the
  whole elaborator" concern would stay open.
- **A generic evaluator (option B).** It gives the strongest static
  guarantee: the kernel's instantiation can't read a solution. A's
  guarantee is just as strong in practice, because admission's signature
  has no store. B costs about 8,000 lines compiled twice, `<M>` on about
  150 signatures, and slower edits to core (an estimate), for no
  measurable run-time gain (§3.3).
- **The store as separate arguments (option C).** It touches every call
  site again whenever evaluator state is added. It also makes "admission
  takes no store" a convention about which argument is passed.
- **A concrete store type in core (options D and D').** As fast as A. But
  core would keep defining elaborator state (frozen metavariables,
  placeholders), which is what the split is meant to undo. It would also
  have to grow a field each time the elaborator's store does. With A, the
  store is elab's own type, and core sees two methods.
- **A capability token for admission.** It adds nothing to privacy (§4).
- **Computing hashes and erasure eagerly at admission,** to keep `Env`
  free of caches without a separate cache struct. It would cost a hash of
  every declaration, even with the check cache off, and it changes what
  admission does. The lazy caches move out instead. Step 9 can revisit
  this for the frozen base, which may want hashes precomputed.
- **Making the meta store persistent, for cheap forks.** elaborator-state
  §5.2 measured persistent vectors at 10 times a `Vec`'s indexed read. The
  store is per declaration and restored in stack order, which the trail
  serves.

## 8. Decisions for Matt

Implementation details decided here, and said so in the text: the hint
trait (§3.5), epoch 0 for "made with no metavariables" (§3.4), the order
of the steps relative to 6c, 7 and 9 (§6), the lazy caches moving out
rather than becoming eager (§7), and how 8f handles the queue mirrors.

- **D2290: the end state.** `Env` is private to core and only admission
  writes it. The meta store is the elaborator's, in `Attempt`. Admission
  takes no store and runs with `NoMetas` and its own modes, so the trusted
  base is "the admission functions and what they reach", and the
  elaborator's use of the checker as a typing oracle (§3.6) is outside it.
  *Rec: yes.*
- **D2291: how the evaluator reaches solutions:** a context struct holding
  `&dyn Metas` (option A), rather than a generic evaluator (B), separate
  arguments (C) or a concrete store in core (D). All measured the same
  (§3.3). A keeps the store's type in elab and compiles core once.
  *Rec: A.*
- **D2292: `Env` holds only what the kernel or evaluator reads.** The
  elaborator's facts (`Data::js`, `Data::defaults`, `Def::param_defaults`,
  `Def::update_shown`, `unfinished`) become `OwnedBy` tables, and the JS
  backend reads `js` and `defaults` from a view the session gives it.
  `Def::param_default` stays, set through a kernel function. *Rec: yes.*
- **D2293: the kernel is given each declaration's path** instead of
  reading the unit's `module`. Hashes are unchanged, which the hash tests
  check. *Rec: yes.*
- **D2294: admission fixes its own evaluator modes** (glue, transparency,
  and erasure off) instead of inheriting the caller's. This closes the
  erasure gap of §2.2. The budget stays the caller's. *Rec: yes.*
- **D2295: test bypasses behind a `test-bypass` feature of core**, enabled
  only by the dev feature set, so that a release build has no way to write
  a body or state without admission. *Rec: yes.*

## 9. Findings worth filing

- **G1. Admission inherits the erasure mode.** `unglued` resets `glue`,
  but nothing resets `Erasure::active`, so admission inside a `running()`
  guard would check with erasure on. No caller does this as far as I read.
  A one-line fix: have the kernel's entry points clear it, as they do glue.
  It could land before step 8. Kernel change, so Opus review.
- **G2. The meta store's undo is partly by hand.** `Snapshot::restore`
  cuts `frozen_metas` and `lifted_calls` to the metavariables that remain
  (`retain(m < self.metas)`). An entry made inside the attempt for an
  *older* metavariable survives the undo: `lifted_calls.insert` at
  `queue.rs:1300` and `:1438` and `frozen_metas` pushes at `search.rs:1550`.
  Whether that can happen in an attempt that is then undone isn't checked.
  The three queue mirrors are restored only as far as the queue resyncs
  them. Worth a test before 8f.
- **G3. The doc of `Globals::metas` is wrong** ("Empty whenever the kernel
  runs"; see §2.2). A doc fix, or it is gone with 8e.
- **G4. elaborator-state.md Appendix B is wrong about `erasure`,
  `unfinished` and `module`** (§2.2). Corrected there by a pointer to this
  note.
- **G5. No test submits a solved metavariable to admission** (§3.6). It is
  refused today; a kernel test should say so. Small, independent of the
  split.
