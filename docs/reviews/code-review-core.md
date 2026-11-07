# Code review: `crates/core` (SW-1869)

Reviewed 7 Nov 2026 by reading `crates/core/src` at `d4bff5a5c` (about
23.6k lines). I read only, with no builds and no runs. I read most closely
what moved since 20 Oct: record eta (`319c28c0c`), SW-1782's `Kept`/`Modes`,
the globals split (SW-1186 to SW-1190), and the pretty printer's literal
helpers after SW-1799.

## Summary

**SW-1829 (the slowdown after record eta): one likely cause, from reading
the code.** When a field of a glued call is stuck, `(f x).i`, it becomes a
plain neutral, `Neutral(Def f, [x, .i])`, and loses the call's unfolding
cell (`value.rs:1653`). `is_folded` now counts every such neutral as
folded, so every later look at it runs `f`'s case tree again from the
start: each comparison that doesn't match on structure (`conv_step`'s
`unfold_folded`, `value.rs:2956` → `2220`), and each unfolded read-back
(`value.rs:2597` builds the call again with a fresh `Rc::default()` cell).
Rule 1 does the same to a call stuck in the kernel: `{ a = …, b = … }`
against a stuck `f s` projects `f s` once per field, and each projection
is then a field call that re-runs `f`. With rule 2 binding every field of
a record to such a call, a record of `k` fields costs `k` re-runs per
meeting, and nested records multiply. `CallMemo`, which stops exactly this
blow-up for glued calls (the comment above it explains the `2ⁿ`), keys
only on `Value::Call` cells, so it never sees these neutrals. Before record
eta, the same access was `R.field (f x)`: a stuck accessor call that isn't
"folded", so it was never re-run. **Confidence: medium.** It fits the code,
but I haven't measured it. A quick test: count `unfold_folded` calls on
field-call neutrals during the slow namespace.

**Overall.** The kernel is in good shape, and better than on 1 Nov. Since
SW-1186 the 1 Nov review's main finding is mostly fixed: every logical
field of `Def` and `Data` is `pub(crate)`, and the bypasses are behind the
`test-bypass` feature. The comments explain why things are sound and why
they terminate, and the soundness arguments for record eta (rules 1 and 2,
`qualifies_for_eta`) and for the glued-call shortcuts hold up when checked
against the code. Conversion, read-back and the machine take budget steps
and propagate errors. The address-keyed tables are all sound: each keeps
its keys alive or only borrows live values. There are four classes of
problem:

- **Unchecked power through the public Rust API.** `register_native`
  checks only a native's type, `Kernel.machine` and `Kernel.caches` are
  public (so `apart_sets` and the content-hash cache can be rewritten),
  and the `admit_trusted_*` functions are ordinary `pub fn`s.
- **Three places where a limit chooses instead of failing (D2543).** The
  inert marks and the proof parameters are installed empty when their
  analysis runs out, and `start_attempt`/`restore` loses the
  stack-exhaustion and deadline propagation that `attempt()` has.
- **Walks with no budget step.** `identical` and `free_variables`
  (SW-1698, confirmed), `matches_at_once`'s recursion and the content
  hasher's term walk take no steps.
- **The record-eta cost issue above.**

`value.rs` has grown to 4,552 lines (3,790 on 1 Nov) and now holds five
subsystems.

**Top five recommendations**

1. Keep a field call's link to its call when it gets stuck, or memoise
   field-call unfolding per outermost comparison, and give the unfolded
   read-back the base cell instead of `Rc::default()` (F1; likely SW-1829).
   M, Opus.
2. Pin the content hashes of the Nat natives in `register_native` and
   `register_nat_neq`, as `float::register_def` and `nat_add::register`
   already do, and refuse a second registration of the same native (F2).
   S to M, Opus.
3. Make a limit fail rather than choose. When `inert::group_marks` or
   `check::proof_params` runs out, fail the admission instead of
   installing empty marks. Give `start_attempt`/`restore` the out-of-stack
   and deadline propagation that `Operation::drop` has, or remove it in
   favour of the guard (F3, F4). S each, Sonnet.
4. Give `identical`, `free_variables`, `matches_at_once` and the content
   hasher budget steps or nesting guards (F5, F6, F9; SW-1698 is part of
   this). M, Opus (kernel).
5. Finish the encapsulation. Make `Kernel.machine` and `Kernel.caches`
   `pub(crate)` with narrow accessors (no public `apart_sets` or `hashes`).
   Put the trusted path behind a capability type that only the check cache
   can construct (F7, F8). M, Sonnet.

**Counts:** 0 high, 9 medium, 10 low.

## Findings

| # | Where | Finding | Sev | Conf | Size |
|---|---|---|---|---|---|
| F1 | `value.rs:1653`, `2220-2253`, `2585-2598`, `2956`, `3141` | A stuck field call drops its call's cell, so every comparison and unfolded read-back re-runs the call; rule 1 makes field calls out of stuck calls; `CallMemo` doesn't cover them. **Likely SW-1829** | medium | medium | M |
| F2 | `native.rs:395-477`, `491` | `register_native` and `register_nat_neq` check only the type, not the definition: a kernel native can be bound to a body it doesn't compute; a second registration isn't refused | medium | high | S-M |
| F3 | `check.rs:1778`, `inert.rs:272-277`; `check.rs:2488-2502` | When the inert analysis or `proof_params` runs out, the declaration is installed with empty marks and is final, so behaviour depends on the budget (D2543) | medium | high | S |
| F4 | `budget.rs:326`, `390` vs `256-273` | `start_attempt`+`restore` drops out-of-stack and deadline propagation; callers (`elab/equations.rs:2496`) then take "ran out" as "no" | medium | high | S |
| F5 | `value.rs:4052-4117` | `identical` and `free_variables` take no step: tree walks over shared values can be exponential and can't be cancelled (SW-1698, confirmed) | medium | high | M |
| F6 | `value.rs:682-711` | `matches_at_once` recurses on the Rust stack through nested glued calls with no step or nesting guard, and is called again for every call node read back | medium | medium | S |
| F7 | `globals.rs:618-626`, `machine.rs:44`, `caches.rs:17` | `Kernel.machine`/`caches` are public: `apart_sets` entries (the meaning of `Apart` facts) and content hashes can be rewritten outside the kernel | medium | high | S-M |
| F8 | `check.rs:2857-3015` | The trusted admission path is a set of plain `pub fn`s; anything with `&mut Kernel` can admit unchecked declarations | medium | high | M |
| F9 | `hash.rs:511-…` | The content hasher's term walk takes no budget step; a term with heavy `Rc` sharing hashes as a tree, unbounded and uncancellable | medium | medium | S |
| F10 | `machine.rs:52-55`, `value.rs:215-219` | Confirms SW-1821 (`reset` keeps glue and erasure) and SW-1819 (`Apart::new` always pushes); more detail below | low | high | S |
| F11 | `check.rs:1493`, `1519` | `Unchanged.seen` is address-keyed and has removals, so the map's growth, and the allocation count, can depend on heap layout (bench repeatability) | low | medium | S |
| F12 | `value.rs:1627-1660` | `Frame::CallField` re-runs the base call's step (`unfold_once`, a nested `run`) right after forcing it, when the call matches at once | low | high | S |
| F13 | `value.rs:2316-2333` | Instrumentation `force_unglued` uses `start_attempt` with a 1 TB stack limit and is not unwind-safe | low | high | S |
| F14 | `check.rs:3049-3130` | `admissible` doesn't look at `Term::Proj`'s `DataId`; harmless on the checked path (`infer_proj`), but on the trusted path an unknown id reaches `hash.rs`'s `data_ref` → panic | low | high | S |
| F15 | `check.rs:2189-2197`, `pretty.rs:703` | `mark_auto_params` doesn't check the vector's length against the parameters; the printer indexes `data.params[k]` by it | low | high | S |
| F16 | `native.rs:481-488` | `native_def` finds a native by iterating a `HashMap`; with two registrations the answer depends on map order | low | high | S |
| F17 | `nat_add.rs:207`, `value.rs:83-135` | `nat_add_rule` turns on mid-prelude, but it isn't one of `Kept`'s modes; a prelude `ty_value` cell filled before `Nat.addSucc` binds keeps the stuck form | low | medium | S |
| F18 | `check.rs:1154`, `1318` | `refine_branch` and the num-case path evaluate with `cx.env` directly, bypassing `Ctx::eval`'s pending-`let` forcing; sound only because no `let` is pending where a `case` is checked (an invariant in comments only) | low | medium | S |
| F19 | `value.rs` (whole) | 4,552 lines: machine, read-back, conversion, tree comparison and memos, `identical`. Split it mechanically | low | high | M |

## Details

### F1. Field calls lose their unfolding cell (likely SW-1829)

How a field call of a glued call is forced (`force_call`, `value.rs:975`):
the base call `f x` is forced through its shared `base` cell. If the base
is a non-meta neutral (stuck), `Frame::CallField` returns
`Value::Neutral(Head::Def(id), spine)` with the projection still in the
spine (`value.rs:1653`). From then on the value has no `Rc<Unfolding>`, and
`is_folded` (`value.rs:2135`) counts it as folded, because any definition
fully applied and then projected is.

Every consumer of a folded value re-runs the case tree:

- `conv_step` (`2956`): if the two sides differ on structure,
  `unfold_folded` runs `f`'s tree from its arguments (`2220`). When `f` is
  stuck, that whole run is thrown away (`return Ok(current)`), and the
  next comparison pays for it again.
- Unfolded read-back (`visit`, `2585-2598`) rebuilds the call as
  `Value::Call(*id, call, Rc::default())`, a fresh cell, so the base call
  is computed again for every field read back.
- Rule 1 (`3141`) against a stuck kernel call `f s` pushes
  `project(d, k, n)` for each field. Each of those is a
  `Neutral(Def f, [s, .k])`, so it is folded, and each pair re-runs `f`.

Scenario: a proof in the shape of a simulation day, `step s` returning a
record of 6 fields, compared after two steps. Each mismatching comparison
of `(step (step s)).pos` re-runs `step (step s)`, whose arguments contain
`(step s).*` fields, each re-run when they are compared in turn. The
`CallMemo` comment (`value.rs:2820-2847`) explains the `2ⁿ` this causes
for nested calls and why the memo fixes it. The memo's key is a
`Value::Call` cell, so field-call neutrals miss it.

Recommendation, in order of size:

- (a) In the read-back, push the base call with the field call's
  `unfolding.base` cell rather than `Rc::default()`. That needs the cell
  kept, so:
- (b) keep stuck field calls as `Value::Call(id, spine, cell)` with the
  stuck value in the cell, instead of turning them into neutrals. Or give
  `CallMemo` (or a per-`conv` memo keyed by `(DefId, args)` with
  `identical`) the field-call neutrals and the result of `unfold_folded`.

Verify with SW-1829's slow declaration before changing anything: count
`unfold_folded` calls on field-call neutrals with record eta on and off.
Size M, Opus (kernel, conversion).

### F2. Kernel natives are bound by type shape only

`register_native` (`native.rs:395`) accepts any final definition whose
arity and type match the native: `Native::Add` on any `Nat → Nat → Nat`.
From then on the kernel computes that definition natively in conversion.
A prelude edit that changes `Nat.sub`'s body but keeps its type leaves the
old native bound, and the kernel then decides equalities from the old
code: `rfl` proofs of the new definition's values fail, and `rfl` proofs
of the old ones pass. The differential tests catch such an edit if they
run. The kernel itself doesn't. `float::register_def` (`float.rs:744-757`)
and `nat_add::register` (`nat_add.rs:220`) pin content hashes for exactly
this reason. The Nat natives and `register_nat_neq` are the only kernel
natives that don't. `registry::bind_def` binds by name, first come, and
the elaborator is trusted to call it only for the prelude and library
files.

A second `register_native` of the same `Native` on another definition
isn't refused, and `native_def` (`481`) then picks one by `HashMap`
iteration order (F16).

Recommendation: a `NATIVE_HASHES` table for the Nat natives, checked as
in `float.rs`, with a test that prints the new hashes. Refuse to register
a native twice. S to M, Opus (trusted base). See D2640.

### F3. Inert marks and proof parameters are installed empty on running out

`define_group` (`check.rs:1770-1781`) makes a group final, then installs
`inert::group_marks`. On any error, including a deadline, cancellation or
work running out, `group_marks` returns no marks and admission returns
`Ok(())`. The declaration is then final with fewer equalities (sound) but
permanently different from the same declaration admitted with room to
spare. `check::proof_params` (`2488`) does the same for a data type's proof
parameters. Usually the budget is sticky and the next step fails the
operation. But a long-lived host that rewinds, or an operation that ends
at that point, keeps the empty marks. The check cache recomputes the marks
on replay ("so the check cache needn't store them"), so a cache hit and a
cold check can disagree. Recommendation: propagate the error, and fail the
admission as other resource errors do. S, Sonnet.

### F4. `start_attempt`/`restore` lose propagation

`Budget::attempt` returns an `Operation` whose `Drop` (`budget.rs:256-273`)
passes an attempt's stack exhaustion and deadline (which
`deadline_passed` signals through `out_of_stack`) to the enclosing
operation: "no answer, rather than the one the attempt's 'no' gives". The
manual pair `start_attempt` (`326`) and `restore` (`390`) doesn't. `restore`
writes back `saved.out_of_stack` and `saved.exhausted`, dropping both.
`elab/equations.rs:2496-2510` then sees `E-RESOURCE` with the outer budget
not exhausted, and skips the equation. So whether an equation is generated
can depend on the stack (debug against release, SW-962) or on the clock.
`elab/nav.rs:702` is benign, since it's display only and says so.
Recommendation: make `restore` take an `attempt: bool` or return the
propagated error, or replace both callers with `attempt()`. S, Sonnet.

### F5. `identical` and `free_variables` take no budget steps (SW-1698)

Confirmed. `identical` (`value.rs:4052`) is a work list over values,
closures and terms. Its doc says "the cost is at most the size of the
smaller side", but that is the tree size: values share `Rc`s, and two
sides built separately (no `ptr_eq` hits) are walked as trees, which for a
balanced DAG is exponential in its memory size. It is called from
`same_closure` (every `Lam`/`Lam` and every codomain pair in `conv`),
`TreeMemo::known_equal` (a linear scan of the filed pairs, each a full
`identical`) and `ShapeMemo::contains`. `free_variables` (`4102`) walks
the whole closure body each time a closure pair is compared, and is
neither memoised nor counted. Neither ignores a limit by choosing, but
neither stops for the step limit, the deadline or cancellation. Planned as
a stage in `docs/proposals/bounded-readback-remaining.md` §7. Recommendation
as there: a step per pair (an `Ev` is available at every caller but
`same_term`), and cache `free_variables` per body `Rc` for the outermost
comparison.

### F6. `matches_at_once` recursion is unguarded

`matches_at_once` (`value.rs:682`) recurses through an argument that is
itself a glued call (`704`). `force_solved` returns a `Value::Call`
unchanged in both glue modes, so a chain `f (f (f … x))` whose tree cases
on that argument recurses to its full depth with no `budget.step()` or
`nesting()`. A chain of tens of thousands, which a fold over an AoC input
can build, overflows the native stack, and that aborts rather than raising
`E-RESOURCE`. `visit` also calls it for every call node in a folded
read-back, so a chain of `n` costs `O(n²)`. Recommendation: a
`budget.nesting("read-back")?` at entry, and memoise per call cell (the
answer depends only on the call and the modes). S, Opus.

### F7. Remaining public mutable kernel state

`Kernel` (`globals.rs:618`) has `pub env`, `pub machine` and `pub caches`.
`Env` is closed now (SW-1186). Still open:

- `Machine::apart_sets` (`machine.rs:44`) is `pub RefCell<Vec<…>>`. An
  `Apart` is an index into it, and `Apart::excludes` lets a number case
  take its default arm. Replacing an entry changes what existing values
  are "known not to be", so a kernel `case` takes the wrong branch. This
  is the same class as the 1 Nov probe (Rust API only, not source).
- `EvalCaches::hashes` (`caches.rs:17`) is `pub`. The kernel never
  consults hashes for checking, but the runtime binds its natives by them
  (`rt/src/natives.rs:171`) and the check cache keys on them, so a wrong
  entry gives a wrong program answer or a wrong cache hit.
  `elab/src/cache/mod.rs:2600` writes it on purpose (trusted replay).
- `Machine::glue`, `transparent` and `erasure` are public, which is
  harmless to admission: `in_kernel_modes` resets them. The elaborator
  needs them.

Recommendation: `pub(crate)` for `apart_sets` with `Apart::new`/`numbers`
as the only access; a `seed_hash` method for the cache's replay. S to M,
Sonnet. See D2641.

### F8. The trusted path isn't separated by type

The 1 Nov review recommended "Isolate trusted replay behind a deliberately
named interface". The functions are well named and their comment block
(`check.rs:2830-2851`) is clear, but they are plain `pub fn` on
`&mut Kernel`. Recommendation: a `TrustedReplay` token with a private
constructor, made only by the check cache's reader (pass it in, or make
the functions methods on it). That makes the bypass visible in every
signature. M, Sonnet. See D2641.

### F9. The content hasher walks shared terms as trees

`Hasher::term` (`hash.rs:511`) is a work list with no step. Terms built by
the elaborator can share `Rc` subterms. Each shared one is hashed once per
path, and hashing can't be cancelled. Lower risk than F5, since quoted
terms are usually trees, but hashing runs over every declaration.
Recommendation: a step per node, or memoise by `Rc` address within one
`def_hash` (keeping the `Rc`s alive, as `ShapeCache` does). S.

### F10. SW-1819 and SW-1821, confirmed with detail

- `Machine::reset` (`machine.rs:52`) resets the budget and the
  transparency set only. A panic caught mid-`in_kernel_modes`, or
  mid-elaborator mode guard, leaves `glue` on, so later read-backs keep
  calls. `Kernel::rewind`'s doc lists erasure's switches as settings that
  stay, but `glue` is a mode, not a setting, and should reset.
- `Apart::new` (`value.rs:215`) pushes every time: no dedup and no
  rewind (on purpose, since names must stay valid). In a kept session it
  grows by one per number match with a `_` arm per request. At `2³²` it
  panics through `expect`; that's unreachable in practice. A dedup map
  `Rc<[BigUint]> → Apart` keeps names stable. Both are filed; nothing new
  to add except that `apart_sets` being `pub` (F7) means the elaborator
  could already reuse entries itself.

### F11. Address keys with removals: allocation counts can vary

`collections.rs` fixes the hasher so that "every run does the same",
including map growth after removals. `Unchanged.seen` (`check.rs:1493`) is
a `HashSet<*const ()>`, and `check` removes from it (`1519`). Where
removed slots become tombstones, and so when the set grows, depends on the
hashes, and so on heap addresses. The verdicts don't change, but the
allocation counts that `crates/bench/tests/repeat.rs` compares can, in the
SW-1797 family. `CallMemo` and `ShapeCache` are address-keyed but never
remove, so their growth doesn't depend on hash values. Recommendation:
instead of removing, clear the whole set when a value turns out unclean
(or keep `added` in a separate set). S.

### F12. `Frame::CallField` steps the base call twice

When the forced base is a non-meta neutral and `matches_at_once` holds,
`Frame::CallField` (`value.rs:1638-1641`) calls `unfold_once(g, id,
spine)`. That recomputes the base call's step in a nested `run`, right
after the outer machine forced it. The nested run is guarded by its own
steps, but the work is duplicated per field. Recommendation: keep the
step from the force (the `unfolded` flag already tracks one of these
cases). S, part of F1's lane.

### F13. `force_unglued` instrumentation

`value.rs:2323`: `start_attempt` with `stack: 1 << 40` (its floor falls
back to the outer floor, so it's bounded inside an operation but not
outside one), and a manual `glue.replace` / `restore` that a panic skips.
It's instrumentation only (`STITCHWORT_DEBUG_FORCE_UNGLUED`), so note it,
or use `attempt()` and a guard. S.

### F14. `admissible` and `declared_later` skip `Term::Proj`

`admissible` (`check.rs:3049`) checks the `DataId` of `Data`, `Ctor` and
`Case`, but not of `Proj`. On the checked path `infer_proj` refuses an
unknown or non-eta type, and eta implies final, so this is harmless. On
the trusted path only `admissible` runs, and a corrupted cache entry with
an unknown `Proj` id reaches `hash.rs`'s `data_ref` and `g.data(d)` and
panics rather than missing. Add `Term::Proj(d, ..)` to both matches. S.

### F15. `mark_auto_params` length

`check.rs:2189` stores the elaborator's vector as it is. The printer
(`pretty.rs:701-703`) reads `data.params[k]` wherever `auto_params[k]` is
true, so a longer vector panics the printer. Check
`auto.len() == data.params.len()`. S.

### F16. `native_def` by map iteration

See F2. Once a second registration is refused, `native_def` is
unambiguous. Better still, store `natives` as `Native → DefId` as well. S.

### F17. `nat_add_rule` is not a cell mode

SW-1791 checked that the mode set is complete for everything that can
change while an `Ev` is borrowed. `nat_add_rule` changes between
declarations (when `Nat.addSucc` binds, partway through the prelude),
while `ty_value`s of earlier prelude declarations are kept, and since
SW-1779 they hold glued calls with kernel cells. A cell filled before the
binding serves the stuck `n + Succ m` after it, where a fresh unfolding
computes further. That changes representation, not meaning, and the
prelude's order is fixed, so it's deterministic. Note it beside SW-1791's
list, or clear cells by bumping an environment epoch when a rule binds. S.

### F18. Direct `eval` on `cx.env` in branch refinement

`Ctx`'s doc says every evaluation goes through `Ctx::eval`, so a pending
`let`'s placeholder is never read. `refine_branch` (`check.rs:1154`) and
the num-case path (`1318`) call `eval(&g, &cx.env, goal_term)` directly.
That's correct only because `case` appears only in case trees, so no
`let` is pending when a case is checked. Add a
`debug_assert_eq!(cx.unforced, 0)` there, or use `cx.eval`. S.

### F19. `value.rs` size

The file mixes the machine (`run`/`resume`/frames), field calls and eta,
read-back, conversion (`conv_step`, `CallMemo`), tree comparison
(`same_stuck_trees`, `TreeMemo`, `ShapeMemo`, `shape_hash`) and
`identical`. A mechanical split into `value/{machine,quote,conv,trees,
same}.rs` with no behaviour change would make reviews like this one, and
F1's fix, more local. M, Sonnet. Do it after F1 lands, not alongside it.

## Checked and sound

- **The globals split's boundary.** `Env`'s fields are private, `Def` and
  `Data`'s logical fields are `pub(crate)`, the `*_mut` accessors are
  `pub(crate)`, and every `*_for_tests` is behind `test-bypass`. No
  non-test code outside core calls a bypass (one use, in
  `elab/src/unify.rs`'s test module). The flake's packages build
  `-p stitchwort-cli -p stitchwort-standalone` without `dev`, so release
  artifacts lack the bypasses. Local `task build` binaries have them by
  design (D2295, `dev-features`).
- **The metadata setters** (`mark_*`, `set_unfolding`, `retype_def`) all
  require `State::Pending`. `set_run_body` requires final, checks the
  type, and never unfolds in the kernel. `abandon_pending` only fails
  things.
- **`in_kernel_modes`** resets glue, transparency and erasure around every
  admission function I found. It isn't unwind-safe, as its doc says, and
  that only matters with SW-1821.
- **Record eta soundness.** `qualifies_for_eta`'s six conditions match the
  comment, and rule 1's ordering, its proof skipping in normal mode and
  its termination argument hold. Rule 2 isn't applied when a program is
  running, nor in a native's tree (`eta_held`, also in `walk_tree`).
  `infer_proj` refuses another type's constructor (the Lean bug), and
  `project` refuses it at run time. `same_layer`, `spine_pairs`,
  `shape_hash` and `quote` all handle `Elim::Proj`. I agree with SW-1764
  §1 that field calls and projections can't be told apart in a way that
  adds an equality.
- **`Kept::fits`** (SW-1782): epoch, glue (glued serves unglued),
  erasure, program and transparency. Every `Value::Call` construction
  makes a fresh cell, except `force_call`'s base, which reuses the base
  call's own cell. So "same cell ⇒ same call" holds, and with it the
  `Rc::ptr_eq(u1, u2)` shortcut in `same_layer` and `CallMemo`'s keys.
- **Address-keyed tables.** `CallMemo` holds its values, answers only
  "different" or skip, and its lookups are order-free. `ShapeCache` keeps
  owners. `Unchanged.seen` only borrows values that live for the whole
  substitution. The `ptr_eq` stuck checks in `resume` and `unfold_folded`
  compare a spine with the one the same run returned. None of them can
  change a verdict with heap layout (but see F11 for allocation counts).
  `TreeMemo`'s key includes the epoch, mode, relation and level, and it
  is dropped when the outermost comparison ends.
- **`identical` ignoring `Apart`** (via `Head`'s `PartialEq`) is by
  design: within one context a level has one fact, and it is true there.
- **Read-back limits.** `quote_as` counts a step per node and fails with
  `Size` past the limit. `quote_at_most`'s cap is deterministic and below
  the limit. `same_when_solved`'s "false on error" relies on the budget
  being sticky, and it is (`exhausted` persists until `restore`).
- **Budget nesting** (SW-1446): `start` clamps the floor to the outer one.
  `attempt()`'s `Drop` propagates stack and deadline exhaustion (F4 is
  only the manual pair). `limited` resets only its own cap.
- **Termination.** SCT's closure is bounded by `max_graphs` and a step per
  composition, and both fail as errors.
- **`erase::of_def`** doesn't cache on failure, and erasing nothing is
  safe.
- **Content hashes** include `record` and `no_eta` (so eta is hashed
  through them), opacity and instance. The kernel never reads hashes to
  decide anything.
- **The pretty printer after SW-1799.** Every literal helper
  (`nat_literal`, `int_literal`, `char_literal`, `text_literal`,
  `char_list`, `list_literal`, `open_list`) guards the arity it indexes.
  The `args[0]`/`args[1]` uses in `term_prec` all sit under
  `args.len() == 2` or `== 3` guards, `label` checks
  `args.len() >= l.levels.len()` before slicing, `defaulted` uses `.get`,
  and `Term::Proj`'s field name uses `.get` chains. The one remaining
  unguarded index is F15. `note_failed_mention` checks
  `stack_exhausted()` at each level.
- **Deterministic hashing.** Every core map uses `collections::Fixed`, and
  the one iteration whose order matters (`note_deepest`) is sorted.

## The 1 Nov review's findings in this crate

| 1 Nov finding | Status |
|---|---|
| Kernel environment can be mutated outside kernel admission (§1.5, §6.3) | **Mostly fixed** by SW-1186/SW-1190: declarations are read-only outside core. Still open: `Kernel.machine`/`caches` are public (`apart_sets`, `hashes`), F7; natives bind by type only, F2 |
| Test-only admission bypasses compiled as public methods | **Fixed**: behind `test-bypass`, which only `dev-features` turns on |
| Isolate trusted replay behind a deliberately named interface (§3.3) | **Partly**: named and documented (`admit_trusted_*`), but not separated by type, F8 |
| The core crate also contains printing, elaborator metavariables and a partial-program runner (§2) | **Changed**: the metavariables moved out (SW-1190, `Metas` trait, `NoMetas` for the kernel). Printing (`pretty.rs`), `step.rs`/`partial.rs` and `js_repr.rs` are still here. Low priority |
| Manual save/change/restore of modes is not panic-safe (§4.1) | **Unchanged** in core: `in_kernel_modes` and `force_unglued`. It matters only together with SW-1821 (caught panics in a kept session) |
| `value.rs` 3,790 and `check.rs` 3,461 lines with mixed responsibilities (§4.4) | **Grown**: 4,552 and 3,957. F19 |
| Deterministic hasher doesn't resist chosen collisions (§4.5) | **Unchanged**, still documented in `collections.rs`; fine for the local threat model |

## Tickets to file

Grouped into lanes:

1. **[Opus] Field calls keep their cell (F1, F12), after SW-1829
   confirms.** Measure re-runs on SW-1829's declaration. Keep stuck
   field calls as calls with the stuck value in their cell, or memoise
   them per comparison, and give the unfolded read-back the base cell.
   Test: a nested record-of-calls comparison whose steps grow linearly.
   About 90 min.
2. **[Opus] Pin the Nat natives (F2, F16).** A `NATIVE_HASHES` table
   checked in `register_native` and `register_nat_neq`, refusal of a
   second registration, and a test that prints the hashes. About 45 min.
3. **[Sonnet] Limits fail, never choose, in core (F3, F4, F13).**
   Propagate the errors from `group_marks` and `proof_params`. Give
   `restore` propagation, or move its callers to `attempt()`, with a test
   that an attempt reaching the stack floor fails the operation.
   `force_unglued` uses `attempt()`. About 60 min.
4. **[Opus] Steps for the uncounted walks (F5, F6, F9).** Overlaps
   SW-1698 and `bounded-readback-remaining.md` §7: fold F6 and F9 into
   that stage, or run it alongside. About 90 min.
5. **[Sonnet] Kernel encapsulation, part 2 (F7, F8, F14, F15).**
   `apart_sets` and `hashes` become private with narrow access, a
   `TrustedReplay` token, `Proj` in `admissible`/`declared_later`, and the
   `auto_params` length check. About 75 min. After D2641.
6. **[DeepSeek] `Unchanged.seen` without removals (F11), and a
   `debug_assert` for F18.** About 30 min.
7. **[Sonnet] Split `value.rs` mechanically (F19).** After lane 1. About
   60 min.
8. **Note only, add to SW-1821 (F10):** `Machine::reset` should also
   clear `glue` and erasure's active flag. Add to SW-1819: dedup by set.
9. **Note only (F17):** add `nat_add_rule` to SW-1791's list of
   environment settings, with the cell caveat.

## Questions for Matt

- **D2640:** Should the kernel's Nat natives (`Nat.add`, `sub`, `mul`,
  `leq`, `eqNat`, `divFuel`, `decEqNat`, `eqNatRefl`, `eqNatSound`, and
  `natNeq`) be bound only to definitions with pinned content hashes, as
  the float natives and `+`'s rules already are? A std edit to one of
  them would then turn the native off (and fail a test that prints the new
  hash) instead of leaving the old code deciding equalities. [rec: yes]
- **D2641:** Should the kernel close its last public mutable state? That
  means `Kernel.machine`'s `apart_sets` and `Kernel.caches` (private, with
  narrow methods), and the trusted admission functions callable only with
  a token that only the check cache can make. It's the remaining half of
  the 1 Nov review's top kernel recommendation. [rec: yes]
