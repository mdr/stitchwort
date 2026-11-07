# Code review: `crates/elab`, part 1 (checking and solving)

SW-1870, 7 November 2026, Opus, by reading only (no build, no tests run).
Baseline: `d4bff5a5c`. Scope: `check.rs`, `unify.rs`, `queue.rs`, `state/`,
`local.rs`, `scope.rs`, `named.rs`, `dot.rs`, `rewind.rs`, `undo.rs`,
`lib.rs`'s elaborator core, `bind.rs`, `autobind.rs`, `pipe.rs`,
`records.rs`, `numbers.rs`, `matching.rs` and `matching/`. About 40,000
lines. Read in full: `state/` (all of it), `undo.rs`, `rewind.rs`, `pipe.rs`,
`queue.rs`'s module doc, mark, restore and resume, `unify.rs`'s `run`,
`unify_step`, `first_order`, `undo_since` and the call memo, `check.rs`'s
`check`/`check_inner`, `dot.rs`'s prefix form and its caches, `lib.rs`'s
`glued`, `with_local_retries`, `group`'s body loop and `test`. Skimmed the
rest by outline and by grepping for the patterns the brief names.

Questions for Matt are D2650 to D2653.

## Summary

The checking core is in better shape than its size suggests. The state
refactor the 1 November review asked for has largely landed: the
`Elaborator` is now eleven fields, nine of them lifetime components whose
`mark`, `restore`, `reset` and `rewind` destructure every field, so a new
field doesn't compile until it says what each mechanism does with it. Undo,
rewind, the queue's resumption log and the unifier's call memo are each
argued for in their comments, and the arguments hold where I checked them.
I found no soundness risk: everything here hands terms to the kernel. The
problems are of three kinds. First, a few pieces of state that escaped the
component discipline after it was set up (a thread-local in the unifier, a
glue flag set rather than restored, the dot-call tables outliving the
metavariable store they are keyed by). Second, invariants that are written
down and checked only by `debug_assert!`, which no test tier runs, since every
tier builds `--release`. Third, size: `check.rs` grew from 5,990 to 7,228
lines in six days, and `lib.rs`'s single `impl Elaborator` block is 3,750
lines. Both have natural seams.

**Top five recommendations**

1. **Empty the dot-call tables whenever the metavariables are cleared**, not
   only per declaration (F1). Several paths check the same syntax a second
   time from a fresh store inside one declaration (the rigid-divergence
   re-check, the local-definition retries, the partial-test retry). The
   walk up to a given call is the same on both passes, so `dot_failed`'s
   `(metas, trail)` key matches exactly and replays a failure from a pass
   whose premises the second pass changed on purpose.
2. **Run the queue's invariant checks in the test tiers** (F3, D2651). The
   seventeen `debug_assert!`s in `queue.rs` are the only checks of
   invariants 1 to 6, and `cargo nextest run --release` compiles them out.
3. **Put back what is set, everywhere** (F2, F4). `auto::decide_from` sets
   glue to `true` when it finishes, whatever it was before, so with
   `glue: false` (the `proof_equivalence` differential test,
   `STITCHWORT_GLUE=0`) the rest of the declaration is checked glued. The
   unifier's new `NO_ETA` thread-local is restored by hand, and
   `search.rs` catches panics and goes on using the session. Use
   `ScopedCell`, and move `NO_ETA` into `Attempt`.
4. **Split `check.rs`, `lib.rs` and `unify.rs` along their seams**, one
   mechanical lane each, in a quiet window (F6, D2652). The seams are listed
   in the details.
5. **Write the internal error classification down before more control
   flow depends on codes** (F5, D2653). About 25 sites in scope choose a path
   by comparing `Diagnostic::code` strings, two by matching message text.
   That is the 1 November review's §3.5, still open and grown.

**Findings by severity:** 0 high, 6 medium, 12 low.

## Findings

| # | Severity | Confidence | Where | What | Size |
|---|---|---|---|---|---|
| F1 | medium | medium | `state/caches.rs:93`, `dot.rs:2164-2179`, `lib.rs:2627-2648`, `lib.rs:2457` | Dot-call tables outlive `clear_metas`; `dot_failed`'s state key repeats on a second pass | S |
| F2 | medium | high | `auto.rs:824-832` | `decide_from` turns glue on unconditionally | S |
| F3 | medium | high | `queue.rs` (17 `debug_assert!`s), `Taskfile.yml` | The queue's invariants are never checked by any test tier | S, after D2651 |
| F4 | medium | high | `unify.rs:1669-1673`, `2030-2032`; `search.rs:1402` | New thread-local `NO_ETA`, restored by hand, in a session that survives caught panics | S |
| F5 | medium | high | ~25 sites (list below) | Control flow chosen by error-code strings and message text | L (design note) |
| F6 | medium | high | `check.rs`, `lib.rs:624-4381`, `unify.rs` | Files too large to hold in mind, with clear seams | M ×3 |
| F7 | low | low | `lib.rs:1356-1399` | A test retried as partial after `lift` has already admitted its helpers | S to investigate |
| F8 | low | medium | `dot.rs:1592-1607` | `dot_heads` hits are never revalidated across attempts | L (with SW-1801) |
| F9 | low | high | `lib.rs:4927-4957` | `?` inside the default arm skips `leaf_log.path.pop()` and the context restore | S |
| F10 | low | high | `records.rs:1266` | `unify(..).unwrap_or(false)` turns running out into a choice (D2543) | S |
| F11 | low | high | `matching.rs:1873-1974`, `core/src/value.rs:4036` | Three structural term equalities; `same` duplicates `same_shifted` | S |
| F12 | low | high | `check.rs:3419-3490` | Three copies of one telescope walk, each swallowing every error | S |
| F13 | low | high | `records.rs:178`, `lib.rs:4460`, `matching.rs:1507`, `undo.rs:130` | `E-RESOURCE` tested by string beside `undo::fatal`; `recoverable` by message suffix | S |
| F14 | low | medium | `nav.rs:445-451` | Go-to-definition refs noted in an undone attempt are kept | S |
| F15 | low | medium | `state/mod.rs:84-96` | `Scoped::drop` silently skips the restore when the cell is borrowed | S |
| F16 | low | medium | `unify.rs:294`, `dot.rs:2164` | Trail length used as "nothing changed since" where `meta_epoch` or a serial is the identity | S |
| F17 | low | high | 68 `clear_metas()` calls | "Inference state is empty at a declaration's start" is kept by convention at 68 call sites | M |
| F18 | low | high | `state/decl.rs:150,155`, `state/attempt.rs`, `state/mod.rs:9-12`, `queue.rs:384` | History in comments, a stale module doc, a dead variable | S |

## Details

### F1. The dot-call tables outlive the metavariable store they are keyed by

`Caches::forget_dot_calls` runs at the start of each declaration
(`Elaborator::glued`, `lib.rs:905`), since SW-1800. `dot_failed` records that
a call's prefix form failed "in one metavariable state", and the state is
`(metas.len(), meta_trail.len())` (`dot.rs:2164`). But inside one `glued`
call the store is emptied and refilled several times on the same syntax:

- `Elaborator::group` (`lib.rs:2627-2648`): a body that fails after meeting a
  rigid divergence is checked a second time with the divergence total, after
  `clear_metas`;
- `with_local_retries` (`lib.rs:2457`): an owner's body is elaborated again
  after its local definitions are preadmitted, after `clear_metas`;
- `test` (`lib.rs:1356-1399`): a test is checked again as a partial
  computation after an `E-PARTIAL`.

Each second pass starts at `(0, 0)` and walks the same syntax in the same
order. Up to the point where its deliberate change makes a difference, it
creates and solves the same metavariables, so at a given dot call the
counts are the same as on the first pass, and the address and spans are
the same because the syntax is borrowed throughout. A prefix form that
failed on the first pass *because* of what the second pass changes (a
callback's row with the divergence partial, a local definition still a
frozen unknown) is then skipped: `call_or_block` goes straight to
`dot_or_block` (`dot.rs:2122`). SW-1800 showed the two readings can give
different terms or different errors. So this is a deterministic stale hit,
not the allocator luck SW-1801 is about. I have not built a repro. The
rigid-divergence case is the likeliest.

The same is true, more mildly, of sibling attempts inside one pass: after
an undo the counts return to the mark's, and a sibling attempt that solves
something else reaches the same counts in a different state.

**Recommendation.** (a) Call `forget_dot_calls` from `Elaborator::clear_metas`
as well (it already runs `Attempt::reset`). The second passes are rare, so
the cache loses little. (b) For `dot_failed`'s state, use an identity that an
undo restores but a sibling attempt can't repeat: give each trail entry a
serial number from a counter that never goes back, and key by
`(metas.len(), trail.len(), serial of the last entry)`. Don't add
`meta_epoch`: the prefix form's own `Snapshot::restore` bumps it, which would
make every lookup miss (the 5 s to 180 s case in SW-1800). Add an example
that fails on the first divergence pass and succeeds on the second through a
dot call. Opus, since the tables' correctness argument is subtle.

### F2. `auto::decide_from` sets glue rather than putting it back

```rust
g.machine.glue.set(false);
let found = cx.eval(&written).and_then(|prop| decide_unglued(cx, &prop, depth));
g.machine.glue.set(true);
```

(`auto.rs:827-831`, outside my scope but on the checking path.) Gluing is
on for elaboration only when `Options::glue` is (`glued`, `lib.rs:912`). It
is off under `STITCHWORT_GLUE=0`, and in
`driver/tests/proofs/proof_equivalence.rs:245`, whose point is to compare the
two modes. Any declaration there that reaches a decision procedure is
checked glued from then on, so the test compares less than it says.
**Recommendation:** `let _glue = ScopedCell::set(&g.machine.glue, false);`.
Grep the other save/restore sites (`kernel.rs:66`, `closing.rs:192`/`221`,
`goals.rs:584`/`747`, `interfaces.rs:1281`, `lib.rs:912`) and convert them
to guards at the same time. Those do restore on `Ok` and `Err`, but not on
a panic (F4).

### F3. The queue's invariants are only debug assertions

`queue.rs`'s module doc says "The debug assertions below check 1-6 where
they can be seen". There are 17: invariant 1 at `Queue::restore` (`:382`)
and `fill` (`:1417`), invariant 2 in `fill` (`:1413`), the requeue and
default checks at `:1364` and `:1692`, among others. Every test tier and the
build task use `cargo nextest run --release` (`Taskfile.yml:110`, `122`,
`190`, `254`, `274`), and the workspace's release profile keeps Rust's
default, debug assertions off. So no tier ever checks these invariants,
including the queue's own unit tests, which "exercise each with items made
directly". Nor `state/table.rs`'s, `state/journal.rs`'s or
`state/paths.rs`'s debug checks.

**Recommendation (D2651):** a cargo feature, `invariants`, that turns these
into `assert!`s, on in the lane and merge tiers and off in benchmarks and
the release CLI. Or turn the cheap ones into `assert!` outright: most are a
length comparison or a `head_meta` on a value already forced.

### F4. `NO_ETA`: unifier state outside `Attempt`, in a session that survives panics

Record eta (SW-1642, 6 November) added
`thread_local! { static NO_ETA: Cell<bool> }` (`unify.rs:1669-1673`), set
and restored by hand around `first_order`'s comparison of last arguments
(`:2030-2032`). That breaks `elaborator-state.md`'s principle 5 ("no session
state outside the object"), which SW-1129's move of the unifier's seven
thread-locals into `Attempt` had just established. It matters because
`search.rs:1402` catches panics from `search_one` and goes on with the same
`Elaborator`, counting them as `internal_errors`. A panic inside that
comparison leaves `NO_ETA` set for the thread, so every later comparison on
the thread, in this session or the next one the language server or a test
harness runs there, compares records without eta, with no error. The 1
November review's §4.1 asked for a policy that a panicked session is
discarded; `search.rs` doesn't follow one.

**Recommendation:** a `no_eta: Cell<bool>` in `Attempt`, beside
`solving_arguments`, set by `ScopedCell` and listed under "set by a guard" in
`mark`, `restore`, `reset` and `rewind`. D2650 asks which panic policy holds.

### F5. Control flow chosen by error codes and message text

The 1 November review's §3.5 found `undo::fatal`'s `e.code == "E-RESOURCE"`
and said "other elaboration paths inspect codes to decide whether to retry
or postpone". In scope now, sites that *choose* by code (not just reword a
message):

- `check.rs:1815`, `:1840`: `E-ABILITY` decides whether `pure_first` tries
  running the expression;
- `check.rs:2979`: `E-CANNOT-INFER` decides which of two errors is kept;
- `check.rs:4572`, `:4794`, `:5072`, `:5741`; `numbers.rs:1568` (`E-CANNOT-INFER`
  queues a leaf), `:1638`; `records.rs:567` (`E-NOT-A-CONSTRUCTOR` chooses
  the record-argument reading of braces);
- `lib.rs:1397`: `E-PARTIAL` retries a test as partial; `lib.rs:4664`;
- `undo.rs:130`: `recoverable` is `E-RESOURCE` plus
  `message.ends_with("too large to show")`;
- `matching.rs:239` and `:278`: `E-NONEXHAUSTIVE` plus
  `message.contains("no arm matches")`, then rewrites the message by string
  replacement.

None is a demonstrated misclassification. But rewording a message (which
the docs lanes do often) can change which path elaboration takes, and
nothing would catch it. **Recommendation (D2653):** a short design note (Opus)
for an internal `kind` on `Diagnostic` (or beside it): `Resource { recoverable }`,
`CannotInfer`, `Ability`, `Partial`, `NotAConstructor`, `Mismatch`, `Other`.
Set where the error is made, matched where the path is chosen, codes left
for users. Then one Sonnet lane moves the sites.

### F6. Size, and where the seams are

| File | 1 Nov | Now | Production lines |
|---|---:|---:|---:|
| `check.rs` | 5,990 | 7,228 | ~7,100 (tests from 7,120) |
| `lib.rs` | 4,862 | 5,048 | `impl Elaborator` alone is 624–4,381 |
| `unify.rs` | — | 4,285 | ~3,060 (fixture and tests from 3,059) |

`check.rs` is the bidirectional dispatcher (`check_inner`, `check_value`,
`infer_value`, which mostly delegate, which is right) plus four other
things that have grown inside it:

- **`Ctx` and its context methods** (`:46-700`): binding, lookup, marks,
  `eval`/`quote`/`unify` wrappers. → `check/ctx.rs`.
- **Messages** (~1,500 lines): `Ctx::show*`, `mismatch`, `unknown_notes`,
  `alias_notes`, `unrefined_hint` (`:698-1270`); the callback and argument
  notes (`:3265-3770`); `awaiting_note`; `refl_error` and its helpers
  (`:6935-7120`). → `check/messages.rs`.
- **The match-equation transport** (`along_match_equation*`,
  `transport_along`, `refines_to`, `:1283-1550`), which is `matching`'s
  concern and calls into `matching::as_written`. → `matching/transport.rs`.
- **Application elaboration** (`infer_app_with`, `apply_args*`, `retrying`,
  `apply_args_postponing`, `hold_argument`, `insert*`, `implicit_arg`,
  `propagate*`, `fallback*`, `compare`: `:2159-3970` and `:5356-6170`,
  ~2,600 lines). → `check/apply.rs`.
- Conditions and decisions (`check_if*`, `decide*`, `:4899-5760`) could join
  `logic.rs`; list literals (`check_value`'s 120-line arm at `:4556`) could be
  a function.

`lib.rs`'s `impl Elaborator` mixes declaration admission with pattern
compilation: `Row`, `Tree` and `compile*`/`pattern_ctor`/`*_pattern`/
`int_coverage` (`:375-620`, `:3468-4381`) and `check_tree*`/`check_leaf`/
`check_guard` (`:4443-4997`) are ~1,700 lines → `patterns.rs`. Data
declarations (`data*`, `same_header`, `after_data`, `:1868-2340`) →
`data_decl.rs`; abilities (`:1429-1750`) beside them.

`unify.rs`: the rules (`row_rule`, `divergence_rule`, `plus_rule*`,
`:537-960`) → `unify/rules.rs`; solving (`solve`, `rename`, `prune`,
`strengthen`, `:2204-2490`) → `unify/solve.rs`; zonking and folding back
(`:2493-3058`) → `zonk.rs`; the call memo (`:990-1250`) beside `run`.
`unify_step` (435 lines) is long but is one case analysis whose order
matters; I would keep it whole.

Per the 1 November review's §4.4, do each as a pure move, no behaviour
change, one file per lane, when no lane in flight touches that file
(D2652). The moves change no hashes.

### F7. A test retried as partial after its helpers were lifted

`Elaborator::test` (`lib.rs:1356-1399`) loops: check the test as `Bool`;
on `E-PARTIAL`, check it again as a partial computation. Inside the
attempt, `e.lift(&label, false)?` declares the test's helpers in the
kernel (`resolve_batch` calls `declare_helper`, `lift.rs:715`; the comment
at `lib.rs:1386` says they are "admitted first") before `e.finish`, which
settles the queue and so can resume a postponed check that reports
`E-PARTIAL` itself. The retry then lifts again under the same label. I
couldn't tell from reading whether that re-admits helpers with the same
keys, fails with `E-DUPLICATE`, or leaves the first pass's helpers in the
kernel, unreachable. **Recommendation:** a repro: a test whose partial call
sits in a dot call on a lambda parameter of unknown type, inside a
`match`. If it misbehaves, rewind the kernel to a mark taken before the
first attempt. Sonnet, 30 min.

### F8. `dot_heads` hits are never revalidated

`dot_heads` maps a receiver's syntax to the head and function its dot call
found, with no metavariable state in the key (`dot.rs:1592-1607`). That's
deliberate: a chain `x.f.g.h` finds each level's head inside the next
level's speculative inference, in a different state, and must hit
afterwards. But it means a head found in an attempt that was undone is used
in a sibling attempt where the receiver's type may have a different head:
for example, a lambda parameter's type solved by expected-type propagation
in the first attempt (`check::propagate`), which then fails and is
retried the old way. SW-1800 found that with both tables off every hash is
the same, so the corpus doesn't meet this case today. **Recommendation:**
fold into SW-1801's note (`syntax-node-ids.md`) as a second requirement: a
hit checks that the receiver's type head, where it is already known
cheaply (`view_start` without inference), agrees, and treats a
disagreement as a miss.

### F9. `?` between `leaf_log.path.push` and `pop`

`check_tree`'s number-case default (`lib.rs:4927-4957`) pushes onto
`decl.leaf_log.path`, then inside the `match` calls `eval(..)?` and
`kernel::substitute_folded(..)?` three times before the `pop`. An error
there returns from `check_tree` with the path one entry too long, and
`cx.env` and `cx.types` not put back. The errors are resource errors, so the
declaration usually stops. But a "too large to show" error is recoverable
(`undo::recoverable`), and a later leaf is then recorded under the wrong
path, which goes into the generated equations (`equations.rs`). The six
other push/pop pairs capture the result first and are balanced.
**Recommendation:** a small guard, `LeafPath::enter(cx, c)`, that pops on
drop, used at all seven sites; compute the default's `env`/`refined`/goal
in a closure, as the constructor arm does.

### F10. A swallowed limit that chooses

`records.rs:1266`: `cx.unify(ty, expected).unwrap_or(false)`. Running out of
resources there reads as "not the same type", and the caller then takes the
other branch (`learnt.filter(|_| !same)`). Against D2543. Use `?`. The other
`unwrap_or(false)` and `.ok()` sites in scope are either already in the
bounded-readback plan's §1.2 table, or only shape a message
(`check.rs:3438`/`3466`/`3489`, `named.rs:564`/`572`/`859`/`904`,
`dot.rs:1358`/`1388`/`1390`/`1435`/`1810`/`2197`), which is fine.

### F11. Three structural term equalities

`matching::same` (`:1873`) is `same_shifted(a, b, 0, 0)` (`:1922`) written out
again, arm for arm. Both recurse on the Rust stack, without a depth guard.
`core::value::same_term` (`value.rs:4036`) does the same comparison with a
work list "as values can nest deeply", except that it compares `Let`'s
erasure flag and `same` doesn't. The recursion is bounded by the needle's
depth (it stops at the first difference), and needles are scrutinees and
`let` values, so the stack risk is small. **Recommendation:** make `same`
call `same_shifted`, and give `same_shifted` a `nesting(PASS)` check or a
work list. DeepSeek.

### F12. Three copies of one telescope walk

`expects_total_result`, `builds_delay_value` and `gives_partial_result`
(`check.rs:3419-3490`) each bind a function type's parameters in a loop,
then look at the result, and each ends in `result.unwrap_or(false)`. They
only shape notes, so swallowing is acceptable, but `E-RESOURCE` is
swallowed too. One helper, `result_after_parameters(cx, ty, |cx, result|
…)`, that passes `fatal` errors on.

### F13. `E-RESOURCE` by string beside `undo::fatal`

`records.rs:178`, `lib.rs:4460` (`branch_failed`), `matching.rs:1507` and
`module.rs:466` compare `code == "E-RESOURCE"` themselves; `undo::recoverable`
also needs `message.ends_with("too large to show")`. Use `undo::fatal`
everywhere now, and let F5's kind replace both.

### F14. Navigation refs from undone attempts

`Elaborator::note` (`nav.rs:445-451`) inserts go-to-definition refs straight
into `nav.refs`; `Snapshot` only truncates `pending` (the types). A dot call
resolved in an attempt that is undone (`dot.rs:1058` notes on success, but
an enclosing attempt can still be undone) keeps its ref unless the final
elaboration notes the same span again. The editor can then jump to a
function the program doesn't call. Low: editor only, and usually
overwritten. Log refs in `pending` too, or record `refs.len()` in
`Snapshot`.

### F15. `Scoped::drop` gives up silently

`state/mod.rs:84-96`: if the cell is borrowed when the guard drops, the old
value is not put back and nothing says so. That can only happen with a
borrow held across the guard's scope, which is a bug. Add
`debug_assert!` (or, after D2651, an invariant check) on the failed
`try_borrow_mut`.

### F16. Trail length as "nothing changed"

`run`'s `Task::Later` (`unify.rs:294`) treats `trail.len() <= trail` as
"nothing solved since". A nested `undo_since` followed by a different
solution can return the trail to the same length, and the pair is then
called different without being compared again. That only loses a
solution, never makes a wrong one, but the unifier already has the right
identity for "solutions taken back", `meta_epoch`, which `CallMemo` uses
(`:1056-1066`). Key `Later` by `(meta_epoch, trail)`. `dot_failed` is F1.

### F17. 68 calls to `clear_metas`

`Elaborator::clear_metas` is called at 68 places. The invariant behind
them, that a declaration starts with an empty `Attempt`, is kept by each
caller remembering. `rewind::mark` asserts it between loads. A cheaper
check: `glued` asserts `attempt.store.metas` is empty on entry, as `mark`
does. Then the calls that only re-establish it can go, and the ones left are
the deliberate restarts (F1's list). Sonnet, after F1.

### F18. Comments and dead code

- `state/decl.rs:150`, `:155` and the `pending_run_bodies` doc say what the
  field was "before SW-1149"; `state/attempt.rs` says "as when they were
  thread-locals" three times. History goes in the commit message.
- `state/mod.rs:9-12` says only some components exist and "the rest of the
  state is still fields of the `Elaborator`". The rest is now `scope`,
  `goals` and `kernel`.
- `queue.rs:384`: `let _ = changed;`, a variable computed and never used.

## Checked and sound

- **`Attempt::mark`/`restore`/`reset`/`rewind`** (`state/attempt.rs`): every
  field is named in each, and each table is cut at the right mark: by
  metavariable count, by trail position (`lossy`, `local_dictionaries`), or
  by length. The deliberate exceptions (`rigid_divergence`,
  `instance_steps`) are argued in their docs and tested
  (`undo.rs` tests). `lossy` left stale by a rewind is only a counter
  (`queue.rs:1433`).
- **`MetaStore::restore`** bumps `meta_epoch` whenever it takes anything
  back, and `undo_since` does too, so kept unfoldings and the call memo
  never trust a solution that's gone.
- **`Queue::restore`**: the log is popped newest first, a `Done` taken back
  removes its fill from `lifted_calls`, dropped items leave the mirrors,
  survivors are re-synced. Order relative to `MetaStore::restore` is right.
- **`Caches::rewind`**: `result_heads` truncated and `performs` cut to the
  definitions that remain, since definition numbers are reused after a
  rewind; `cong_candidates` and `decision_order` emptied.
- **`Elaborator::rewind`** names every field; `Decl` is asserted empty at a
  mark (`Decl::leftover`).
- **The unifier's stack**: `run` calls `budget.step()` for every task, and
  `step` checks the stack floor, so the nested `run`s (`unify_pair`,
  `same_stuck_trees`, `first_order`, sealed definitions) end in
  `E-RESOURCE`, not a crash.
- **`with_local_retries` terminates**: it loops only while `preadmit` grows
  `preadmitted`, which is bounded by the local definitions.
- **Hash order**: every iteration of a hash map or set in scope that reaches
  output is sorted first (`scope.rs:1671`, `1980`, `2034`, `2120`, `2512`,
  `2554`, `2648`; `lib.rs:783`, `794`); `compile_numbers` uses a `BTreeMap`;
  `queue.rs`'s stuck report uses maps for lookup only. The collections hash
  deterministically (`core/src/collections.rs`).
- **Addresses**: beyond the dot-call tables, the address-keyed uses
  (`Decl::condition`, `conjunction`, `app_expected`, `named::filled_by`,
  `ptr::eq` in `unify_step`) compare against syntax borrowed for the whole
  time, as `syntax-node-ids.md` §2 says. I found none it missed.
- **Panics in scope** (`unreachable!`, `expect`): each is an internal
  invariant established a few lines above or by the caller. None depends on
  user input that I could see.
- **`pipe.rs`**: the lambda's codomain metavariable is made under the
  binder and closed over the outer environment correctly.

## The 1 November review's findings in this scope

| Finding | Status |
|---|---|
| §3.1 Group state by ownership and lifetime | **Largely fixed.** `state/` components with exhaustive destructuring; `Snapshot` keeps four things outside `Attempt`. Regressed in one place: `NO_ETA` (F4). |
| §3.5 Internal error classification | **Open, grown** (F5, F13). |
| §4.1 Manual save/restore; discard panicked sessions | **Open.** Manual sites remain (F2's list); one is now a real bug (F2); `search.rs` reuses a session after a caught panic (F4). |
| §4.4 Large files (`check.rs` 5,990, `lib.rs` 4,862) | **Open, worse**: 7,228 and 5,048 (F6). |
| §2.5 Comments explain invariants | Still true: `undo.rs`, `queue.rs`, the call memo, `Caches`. Some history narration (F18). |
| §1.5 Kernel mutable outside admission | Not in scope (core), but `Elaborator::kernel` is still `pub`. |

## Seen in passing (parts 2 and 3)

- `auto.rs:824-832` is F2.
- `search.rs:1402` (part 2) catches panics and reuses the session (F4).
- `core/src/value.rs` keeps `TREE_MEMO` and `SHORTCUTS_OFF` as
  thread-locals. `TREE_MEMO` is emptied when the outermost comparison ends,
  and keyed by epoch, so it is sound, but the same panic question applies.

## Tickets to file

Grouped into lanes.

1. **Put back what's set** (Sonnet, 45 min): F2 (`decide_from` and the
   other glue sites to `ScopedCell`), F4 (`NO_ETA` into `Attempt`), F9
   (`LeafPath` guard), F10, F15, F18's dead variable. Tests: `task test:one`
   on `proof_equivalence`, the elab `undo` and `queue` unit tests, the
   record-eta examples.
2. **Dot-call tables and the metavariable store** (Opus, 60–90 min): F1 (empty
   on `clear_metas`; trail serials for `dot_failed`), F16, and a regression
   example through the rigid-divergence re-check. Coordinate with SW-1801.
3. **Invariant checks in the test tiers** (Sonnet, 30–45 min, after D2651): F3.
4. **Split `check.rs`** (Sonnet, 90 min, pure move): `ctx`, `messages`,
   `apply`, and the match-equation transport into `matching/transport.rs`.
5. **Split `lib.rs`** (Sonnet, 60 min, pure move): `patterns.rs`,
   `data_decl.rs`.
6. **Split `unify.rs`** (Sonnet, 60 min, pure move): `rules`, `solve`, `zonk`.
7. **Duplicates** (DeepSeek, 30 min): F11, F12, F13.
8. **Internal error kinds** (Opus design note, 60 min, after D2653): F5.
9. **Partial-test retry after lift** (Sonnet, 30 min): F7, repro first.
10. **Unifier agrees with conversion** (Sonnet, 60 min): `unify_step` repeats
    `conv`'s rules ("as in `conv`" ten times). A property test over the
    fuzz corpus's closed values: with no metavariables, `unify(a, b)` equals
    `conv(a, b)`. It would catch a rule added to one and not the other.
11. Smaller, any time (Sonnet, 30 min together): F14, F17 (after lane 2),
    F18's comments.

F8 goes into SW-1801's note rather than a ticket of its own.

## Questions for Matt

- **D2650: After a panic inside the elaborator, is the session thrown away?**
  `search.rs` catches panics per candidate and carries on, which is useful
  (one bad lemma doesn't end the search) but means every temporary setting
  must be a guard and no state may live in thread-locals. [rec: keep
  `search.rs`'s recovery, and adopt the rule "temporary settings are guards,
  no thread-locals in elab" (lane 1 does the sites in scope). Throwing the
  session away would lose the search's results so far.]
- **D2651: Run debug-only invariant checks in the lane and merge tiers?**
  Today no tier runs any `debug_assert!`, since all build `--release`. [rec:
  yes, through an `invariants` cargo feature on in the test tiers only. The
  queue's checks are cheap; measure the merge tier before and after, and
  keep only those under 1%.]
- **D2652: When to split `check.rs`, `lib.rs` and `unify.rs`?** Each split
  is a pure move but conflicts with every lane touching the file. [rec: one
  file at a time, scheduled when no lane in flight touches it, `check.rs`
  first. Not during a heavy run.]
- **D2653: Write the internal error-kind design note now?** [rec: yes, a
  short Opus note, so the code comparisons stop growing; the sweep after it
  is one Sonnet lane.]
