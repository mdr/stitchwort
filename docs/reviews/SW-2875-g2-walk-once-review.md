# SW-2875 review: rule E walks a chain of stuck sums once per comparison

Fable paper review (D3473) of commit 885c81222 on `lane/SW-2875`, 11 Nov 2026.
Read-only: no builds or tests were run. Costs are reasoned from the code and
marked "unmeasured" where a run should confirm them. Line numbers are the
lane branch's. Follows up
[SW-2874's review](SW-2874-g2-nested-sums-review.md) (3c, 4c, 7).

The change: `nat_add::reread` (`crates/core/src/nat_add.rs:140-212`) is a
loop with its own stack (`above`), charges a budget step per sum it goes
down to (`:175`), and files the sums of a walk that unfolded nothing in an
`Unread` (`:250-281`), where a later walk stops (`:150`, `:174`). The
machine's conversion keeps the `Unread` in its `CallMemo`
(`value.rs:3521-3524`, `:3647`), the unifier in its own, tagged with what
had been solved (`unify.rs:1049-1090`); `case`, `NumCase` and the reference
evaluator use a fresh one each call.

## Verdicts

| # | Verdict | Finding |
|---|---|---|
| 1a | OK | The record is true wherever it's reused: "this sum reads as nothing" is a function of the sum and of state that is fixed while the record is kept |
| 1b | OK | A wrong record could only ever make a comparison answer "different" or stay stuck, never "equal": `reread` returning `None` keeps the value as it was |
| 1c | OK | The unifier drops the record on every solution, undo and postponement: the tag (epoch, trail length, postponed count) can't come back to an old value with different solutions |
| 1d | NOTE | The record also relies on the flags `is_folded` and `force` read not changing inside one comparison; none does today |
| 2 | OK | Address keys: a filed address can't be reused or its spine changed in place while filed |
| 2b | NOTE | `Unread` trusts its callers to have checked the value is a sum; cheap to make it check |
| 3a | OK | Answers don't depend on the record, the order of comparisons or addresses; step counts are deterministic |
| 3b | NOTE | Counters move: steps up one per sum gone down to, visits down; the reference evaluator and shortcuts-off now pay the quadratic walk in steps |
| 4a | OK | The loop ends, within the budget inside an operation |
| 4b | NOTE | A chain that unfolding builds is not helped by the record; the commit's 34 s to 1.1 s isn't explained by what I read |
| 5 | OK | `docs/core.md` rule E says what the code does |
| 6 | SHOULD-FIX | Tests: nothing checks the unifier's invalidation, and the new chain test runs in one mode only |
| 7 | NOTE | The lane's three findings: tickets, none caused by this change |

No MUST-FIX. The change can merge; 6 is small and could go in the same lane
or a follow-up.

## 1. Is the record true where it's reused?

**What is filed.** A walk files `walked` only when it returns with
`unfolded_any` false (`:198-200`). `walked` is the sum the walk started at
and each sum it went down to (`:156`, `:176`). With nothing unfolded, every
one of them was read to its end, which is one of: `n` is a number (`:161`);
its base is a folded `k * x` (`:165`); its base isn't folded, or is stuck,
and isn't a sum (`:168`, `:180`); or its base is a sum already filed
(`:174`). So for each filed sum `S`, a walk started at `S` makes the same
`view_with` and `unfold` calls the first walk made from there down, gets
the same answers, unfolds nothing and returns `None`. An error on the way
(`?` on `view_with`, `unfold`, `step`) returns before anything is filed.

**1a (OK).** That argument needs `view_with(…, force)` and `unfold` to give
the same answers later as they gave the first time. They read the value,
the definitions, and (in the elaborator) the metavariables' solutions.
Neither depends on the level or on the comparison's mode (normal or
shortcut): `reread_sum` (`value.rs:2334`) takes neither, so one record
across both modes and all levels of a `conv` is right, unlike the pairs of
calls beside it, which are keyed by mode and level.

- Machine: `conv` (`value.rs:3421`) makes a new `CallMemo` per outermost
  call and solves nothing, so the state is fixed for the record's life. A
  `conv` reached from inside an unfold starts its own record.
- `branch` (`value.rs:2256`, `:2312`) and the reference
  (`reference.rs:563`): a fresh record per call, so nothing is reused.
- Unifier: 1c.

**1b (OK): a wrong record can't make anything accepted.** The record is
only consulted to return `Ok(None)` early (`:150`) or to stop going down
(`:174`). `None` means "leave the sum as it is", and comparing a value as
it is, by its parts, is always sound; what's lost is an equality by R3/R4
that reading would have found. So a stale or aliased record could turn
"equal" into "different" (or a `case` into a stuck one), never the reverse.
The kernel uses "different" only to reject. The unifier can take another
route after a failed unification, but whatever it builds is checked by the
kernel, whose record is per `conv` with no metavariables. So the worst a
bug here could do is reject, or elaborate differently, something valid.

**1c (OK): the unifier's invalidation.** `reread_sum` (`unify.rs:1076-1090`)
uses the kept record only if its tag equals `effects(g)` now, and stores it
back only if `effects(g)` is still that after the walk. `effects`
(`:1064-1070`) is (`meta_epoch`, trail length, postponed count).

- Every solution goes through `solve_meta`, which pushes on the trail
  (`state/metas.rs:186-189`; `plus_rule_with` at `unify.rs:919` too).
- Every take-back bumps the epoch before popping: `undo_since`
  (`unify.rs:1990-1991`), `restore` (`metas.rs:226-228`, also when only
  metavariables are dropped, so a reused number can't alias), `clear_metas`
  (`:255`).
- The epoch only goes up, and within an epoch the trail only grows. So two
  moments with the same (epoch, trail length) have the same solutions, and
  the ABA case (solve `?a`, undo, solve `?b`, same trail length) has a
  different epoch.

So "a recorded 'nothing to unfold' becomes false after a metavariable is
solved" can't be observed: the first walk after any solution sees a tag
that differs, starts an empty record, and overwrites the old one. Example:
`x + (y + ?m)` is walked and filed; `?m := two 0`; the next read of the
same value walks in full and gets `2 + (x + y)`. In practice the path is
guarded twice, since a pair put aside is re-evaluated (`afresh`,
`unify.rs:276-281`, `:298-`) and the new values have new addresses.

The record is taken out of the memo for the walk (`std::mem::take`, `:1080`)
so the `RefCell` isn't held across evaluation; a `reread_sum` nested inside
the walk would see an empty record and its entries would be overwritten at
`:1087`. That loses entries, never adds a wrong one.

The postponed count in the tag isn't needed for this record (a postponed
row constraint changes no solution); it's harmless.

Each entry point that changes the comparison's context
(`unify_waiting`, `unify_solving_arguments`, `unify_awaiting_helpers`,
`unify_postponing`, `unify.rs:116`, `:399`, `:415`, `:451`) starts a new
`CallMemo`, so the sums record ends there with the calls record.

**1d (NOTE).** `unfold_folded` answers through `is_folded`
(`value.rs:2694-2715`), which reads `body_seen` (what's opaque and hidden
here) and `folds_on_lift` (`program_running`). I found nothing that changes
these inside `conv_step` or inside one outermost unification
(`value.rs:3400-4700` has no scoped flag), so the record is fine today. If
a comparison ever compares part of its work under a different visibility
or with gluing switched, the record must be dropped there, as the doc on
`reread` says (`nat_add.rs:138-139`). By 1b the cost of missing that would
be a rejection, not an acceptance.

## 2. Address keys (OK)

- The key is the address of the spine's `Rc` (`value.rs:547-551`), and the
  record holds a clone of each filed value (`nat_add.rs:274-278`), so the
  allocation stays alive and its address can't be given to another spine
  while filed. An address is in `spines` only if its value is in `kept`.
- No in-place change: the only writers of a spine are `Spine::push`
  (`Rc::make_mut`, `value.rs:524`), `into_vec` (`Rc::try_unwrap`, `:532`)
  and `Drop` (`:683`), and each acts in place only at a count of 1. The
  record holds a count, so they copy.
- No hash-consing of spines: two values share a spine `Rc` only by cloning,
  so the same address under the same head is the same value. The key
  leaves the head out, but both lookups (`:150`, `:174`) come after
  `Sum::of` matched, which fixes the head to the bound `Nat.add` and the
  spine to two applications.
- Thunks and glued calls inside the spine are filled in place when forced.
  That changes when they're computed, not what they are, except through
  metavariable solutions, which 1c covers; a glued call's kept unfolding
  is itself tied to the epoch.
- With shortcuts off nothing is filed (`:270`), and with nothing held there
  are no keys to go stale.
- Holding values raises spines' share counts. The only reader of a spine's
  count that isn't one of the writers above is `Spine::shared_key`
  (`check.rs:1669`, `:1732`), a memo in the kernel's checker, which doesn't
  run during a `conv`; a hit or miss there changes cost only.
- Memory: the record holds every sum of both chains until the comparison
  ends, O(depth). Dropping it goes through the iterative free
  (`value.rs:681-686`).

**2b (NOTE).** `Unread::contains` and `extend` (`nat_add.rs:262-280`)
accept any neutral value and `Spine::addr` gives 0 for an empty spine.
Both are private and only see values that passed `Sum::of`, so it's right
as written; a `debug_assert!` that the spine is non-empty, or taking the
spine from `Sum`, would keep it right if someone adds a caller.

## 3. Determinism

**3a (OK).** By 1a the record never changes what `reread` returns, so
verdicts, elaborated terms and hashes are as without it. Step counts with
the record depend on which values share a spine and the order of walks;
both follow from the deterministic evaluator and the work list's order,
not from the addresses' numeric values (the set is only asked "is this
in", never iterated). So `E-RESOURCE` at a given budget is reproducible.
The kernel and the elaborator can spend different step counts on the same
comparison (the unifier loses the record at each solution), as they
already could; they can't disagree on an answer.

**3b (NOTE).** For the verifier and `bench/baseline.toml`:

- Steps: plus one per sum a walk goes down to (`:175`), in every mode.
  Flat sums (`x + two 0`) are unchanged.
- Visits: down. The `nesting("conversion")` call is gone, which also ends
  SW-2874's 4c (frame-size-dependent E-RESOURCE from this walk) and its 7
  (the "nested too deeply" wording, for this walk).
- The reference evaluator and shortcuts-off mode keep no record, so a
  plain chain of depth D costs them about D² steps where the machine pays
  about 2D. Same answers; but a differential run on a deep chain can now
  get `E-RESOURCE` from the reference where the machine answers (before,
  the reference's walk was uncounted). At depth 400 that's 160,000 steps,
  fine; the harness must go on treating `E-RESOURCE` as no answer.
- In the unifier, a comparison that solves something at every level of a
  chain starts a fresh record each time, so it is quadratic again, now in
  counted steps. Unmeasured; I'd expect it only in contrived goals.

## 4. Termination and bounds

**4a (OK).** Each turn of the outer loop does one of: unfold (`:168`,
which runs the machine, at least a step); go down to a sum (`:175`, a
step, a push); or finish the current sum and pop at least once or return
(`:193-210`). Pops can't outnumber pushes. So turns are bounded by a
constant times the steps charged, and inside an operation the budget ends
it. Outside one (no limit) it ends as SW-2874's recursion did: unfolding
is of total definitions, and going down is into a proper part of a finite
value or of what an unfold built. No Rust recursion is left in the walk;
`above` and `walked` are heap, O(depth).

The walk is the old recursion made explicit, and I checked it gives the
same result: `Sum::read` (`:242-247`) is the old "`None` if nothing was
unfolded, else `stuck_value`"; a child that reads to `Some` replaces the
parent's base under the same `k` `Succ`s (`:204`, the `k` saved at `:177`)
and the parent is viewed again, as the old loop did; a child that reads to
`None` ends the parent's reading with the parent's `n` as it was. The
`k * x` cut is tested on every view, as before.

The top-level call no longer checks that the operation is still running
(the old `nesting` did). Harmless: `conv_with` and the unifier's `run`
take a step per task before calling it (`value.rs:3458`, `unify.rs:262`).

**4b (NOTE).** The record is only made when a walk unfolds nothing. A chain
that unfolding builds (`f 200 y`, `decreasing`, in
`nested_sum_reads_a_long_unfolded_chain`) sets `unfolded_any` on every
walk, and each walk still reads as `None` (the bottom reads `y + 0` to `y`
and the sum above stays stuck), so nothing is filed and the comparison
`x + f K y` against `x + f (K-1) y` still walks and unfolds from each
level: about K² unfolds, all counted. That matches SW-2874's 3c second
bullet and is acceptable (the budget sees it). But then I can't account
for the commit message's "a `decreasing` chain compared unequal 34 s … 1.1
s" from the record alone. Either that chain has a different shape from the
test's, or the gain came from elsewhere (the removed `nesting` calls, the
loop). Worth one line on the ticket saying which input was measured, so
the number means something later.

## 5. Docs (OK)

`docs/core.md:322`, rule E's new sentences: "a budget step per sum below
the first", "steps, not stack", "within one comparison (for the unifier,
while nothing is solved)", "remembering only saves work" all match the
code. Two optional precisions: the unifier's condition is "solved, taken
back or put aside"; and eliminations (`case`, `NumCase`) and the reference
evaluator don't remember, which the last sentence covers in spirit.

`nat_add.rs`'s module comment (`:34-39`) now says evaluation leaves folded
calls and comparisons read them with `reread`: SW-2874's 5b is done. The
docs on `reread` (`:130-139`), `Unread` (`:250-254`) and the unifier's
`reread_sum` (`unify.rs:1072-1075`) state the conditions the record
depends on.

## 6. Tests (SHOULD-FIX)

`nested_sum_walks_a_plain_chain_once`
(`proof_equivalence.rs:1390-1404`) is a good test of the cost: its bound
(200,000) sits between the measured 75,000 and the quadratic walk's extra
320,000, and it checks acceptance through the unifier and the kernel with
the record in use. Missing:

- **The unifier's invalidation**, the one piece of new logic that an
  answer depends on. At source level it's hard to hit (1c: a pair put
  aside is re-evaluated). A unit test beside the others in `unify.rs`
  (`:3881` on) can do it directly: inside one outermost comparison, read
  `x + (y + ?m)` (nothing, filed), solve `?m := two 0`, read the same
  value again and expect `2 + (x + y)`; then undo and expect nothing
  again.
- **Agreement across modes.** The new test loads once, in the default
  mode. Put the `repEnd` theorem (depth 400 or less) where the matrix
  runs every kernel mode, shortcuts off and the plain evaluator, so the
  run with a record is compared with the runs without one. That is the
  direct check of "the record changes no answer".
- **A rejection with the record in use**: `repEnd 400 x y = repEnd 400 x x`
  is a type error, not `E-RESOURCE` and not accepted.

## 7. The lane's findings (NOTE)

I had the three by name from the brief, not the lane's report, so these
are readings of the code, not checks of its measurements.

- **`rfl`'s error message cost.** Not touched by this change; the failure
  path prints both sides. Worth a ticket if a failing `rfl` on a deep
  chain takes seconds after the comparison has answered: measure the
  message apart from the comparison first (it may also be the 1.1 s in
  4b).
- **`Nat.add` chains compared with a Rust frame per level.** The test's
  comment (`proof_equivalence.rs:1393-1394`) says deeper chains run out of
  stack "comparing the sums' arguments". In the kernel's `conv_step`, two
  stuck sums take the branch at `value.rs:3825-3833`, which puts the
  argument pairs on the work list: no recursion. So the frames are
  somewhere else: `same_spines` (`value.rs:3571-3595`, one nested
  `conv_with` per level of calls in arguments), reached when the chain's
  tails are still glued calls of the recursive definition, or the
  unifier's counterpart. The ticket should start from a backtrace at the
  stack guard rather than a guess. It ends in `E-RESOURCE`, not a crash,
  so it's a limit, not a soundness matter.
- **Evaluation `E-RESOURCE` at 50,000.** The walk no longer uses stack, so
  this is the evaluator's own depth limit building the chain (a
  non-tail-recursive definition at a large numeral), as before this
  change. A ticket for the stack-safe evaluation work if a real program
  meets it; nothing for this lane.
