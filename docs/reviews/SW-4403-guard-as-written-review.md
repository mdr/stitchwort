# SW-4414: review of lane/SW-4403 (a refined guard's arms show the goal as written)

Reviewer: Opus, paper lane, 20 Nov 2026. Read from `git diff main...lane/SW-4403`
(one commit, 4cbccd844). Nothing was built or run.

**Verdict: merge after one named fix (M1) and its test (M2).**

## What the change does

`refined_guard` (`crates/elab/src/matching.rs`) now calls `as_written::first` with
the same `Today` the usual test builds and, if it returns something, binds the
as-written generalisation inside `undo::attempt` and keeps it when
`motive_checks_now` passes. Otherwise it reports `Unchecked` and goes on to the
usual unfolded bind, then the transport retry, as before. This mirrors
`generalised_now` (lines 1465-1503 on the branch), except in one place (M1).

## 1. Soundness

No new way to prove a different statement.

- `as_written::first` only returns a result that passes checks 1, 2 and 4 of
  `matching/as_written.rs`: the same copies as the usual test (plus missed
  ones that check 2 confirms), and each generalised target read back unfolded
  agrees with the usual result, except where the usual result keeps a subterm
  equal (by computation, solving nothing) to the scrutinee. An occurrence is a
  subterm with the scrutinee's head as written and equal to it by computation.
  So the as-written motive can only abstract things definitionally equal to
  the condition, at the places the unfolded path abstracts them. It can't pick
  up something that isn't the condition.
- Even if it did, the result is checked twice: `motive_checks_now` before the
  arms, and the kernel on the lifted helper and its application
  (`lift::draft_with`), whose type must convert to the declared goal. A wrong
  motive ends as a type error, not as a proof of something else.
- The facts the arms get (`%guard`'s equation, or `sound`/`refute` of the
  decision) and `cx.scrutinees` (still the unfolded `normal`) are untouched.

## 2. D3688: can a proof that checks on main stop checking?

Two routes.

**(a) The as-written motive is found but doesn't check now: a real bug (M1).**
On this path, `attempt`'s closure returns `Ok(None)`. `attempt` wraps that as
`Ok(Some(None))`, and `transaction` treats `Ok(Some(_))` as success and **does
not restore** (`undo.rs:150-172`). So the variables `bind_generalised` bound
(the hidden scrutinee at level `base`, the `%guard` equation, the copies) stay
in `cx`. `generalised_now` handles exactly this case with an explicit
`snapshot.restore(cx)` in its `else` branch (branch line 1502). `refined_guard`
doesn't: it goes straight on to `let unbound = Snapshot::take(cx)` and binds
the usual generalisation **on top of** the stale bindings. After that,
`x = base` names the stale scrutinee variable rather than the one the usual
motive abstracts, and `extra`'s length doesn't match the context. The likely
outcome is an elaboration or kernel error. That isn't unsound (the kernel
still checks), but the error goes back to `check_guard_if` as an arm error,
which retries in place (for a `Bool` variable) and then unrefined. **A proof
that checked on main through the unfolded path, after an as-written attempt
that came back `Unchecked`, now needs the unrefined split to work too.** If it
relied on the refinement, it stops checking. The module doc names a common
trigger: a folded `x / d` carries its hidden `d ≠ 0`, which the unfolded goal
doesn't, so check 3 fails.

Fix: take a snapshot before the `attempt` and restore it when `kept` is
`None`, as `generalised_now` does. It's a two-line change.

**(b) As-written is kept, then an arm fails under the folded types.** The
retry still runs. The arm's error comes out of `refined_guard`'s `body` as
`Err`, and `check_guard_if` sees a non-fatal error, so `generalised = true`.
It tries in place (when the condition is a `Bool` variable that isn't split
below), then the unrefined `proof_if`. What it never retries is the
**unfolded refined** split. So a proof whose arm works only against the
unfolded hypothesis types, and doesn't work unrefined, would stop checking.

How likely is that? The as-written types are convertible with the unfolded
ones (check 2), so anything that checks up to conversion (`byComputing`,
`exact`-style terms, `let` ascriptions, unification that unfolds) behaves the
same. Only syntax-directed steps can differ: `rewrite` key search, `cases`,
`match` on a hypothesis, `arithmetic`'s atom reading (it `force`s values, so
it should see through `pick True`). Mostly the change goes the helpful way: a
`rewrite pick.eq.ifTrue` that found nothing on main now finds `pick True`.
`match` has had the same contract since goal-as-written stage 2 (no unfolded
retry after an arm fails), and that was measured across std and AoC. The
guard version hasn't been measured. I don't make this must-fix, but it needs
measuring (F1).

The one guard I found inside a proved tool's proofs:
`tools/fmt/src/Syntax/GoodItemProofs.sw:395`
(`| ['!', 'i', 'n', next, .._] if !isWordChar next => cases`). There the
condition probably sits inside a call in the goal, so as-written returns
`Incomplete` and the path is unchanged. The orchestrator should still check
that one fmt namespace before merging, because D3688 is about proved tools.

## 3. The helper that "disappeared" in split-below

It didn't disappear. On main, `guard-refinement-split-below.snap` lists
`firstPlusZeroOrPositive`, `.%match1` and `.%match2`, and the branch lists the
same three names with new hashes (3 lines out, 3 in). All three hashes change
because the helpers' motives are now folded. The brief's premise is wrong;
nothing to fix.

The other changed snapshots also keep their declaration lists, and only the
hashes of the declarations that use a refined guard change. The unchanged
guard snapshots (`rewrite`, `rewrite-at`, `rewrite-at-term`, `chain`,
`either-way`) fit the design. In those, the condition is hidden in a call
(`clamp`, `weight`), so as-written can't see it and check 2 says
`Incomplete`; or the folded and unfolded forms read back the same.

## 4. The note's wording

The note fires when `expected` is a `Term::Eq(l, r)` with `same(l, r)`, so
`expected` is literally `side = side`. "What's expected computes to
`side = side`" is then true whether `expected` was read back computed (the
`0 < 1` case, where the label shows `0 < 1` and the note `True = True`) or
written that way (zero steps). `side` comes from `self.show(eval(l))`, which
may print a different form of the same value than `l`; that's still "computes
to". The `byComputing` claim is the one the old note made. The new wording
fixes the old note's false "both sides are `True`" for a decided proposition,
and it is true whenever it fires.

## 5. Tests

- `goals/guard-hypotheses-as-written` covers the kept path for a `Char`
  condition and for a `Bool` variable, in hypotheses and the goal. Good.
- `reject/guard-refined-written-in-arm` covers the note. The error itself is
  unchanged from main: a type written in the arm is never refined.
- **Missing, must add with M1 (M2):** a guard whose as-written attempt comes
  back `Unchecked` and whose unfolded path checks. A guard in a proof whose
  goal has a folded division `x / d` with the condition visible as written is
  the likely shape; confirm it with `STITCHWORT_MATCH_METRICS=1` showing
  `match-as-written: unchecked`. It should fail before M1 and pass after
  (D3608).
- Missing, worth having (F2): an arm that fails under the as-written types
  and recovers, or a note that none is known to exist.
- The `Incomplete` path is covered implicitly by the unchanged `rewrite*`
  hash snapshots.

## Must-fix before merge

- **M1.** In `refined_guard`, restore a snapshot taken before the as-written
  `attempt` when `kept` is `None`, as `generalised_now` does. Otherwise the
  failed attempt's bindings stay in the context, and the usual path is built
  on top of them (§2a).
- **M2.** Add an example that goes through `Unchecked` and then the unfolded
  path. Show it failing without M1 (§5).

## Follow-ups

- **F1.** Measure the change across std, AoC and `tools/fmt`. The lane ran
  only the guard examples. Hashes of every proof with a refined guard will
  move (the verifier's hash snapshots and Overmind's rolling check will show
  this), and route (b) of §2 needs to be confirmed empty in practice. Before
  merging, check the fmt namespace holding `GoodItemProofs.sw:395`.
- **F2.** Decide whether an arm failure after an as-written kept should retry
  the unfolded refined split before the unrefined one. That would make the
  D3688 promise cover route (b) too, at the cost of one more attempt per
  failing guard. Bound it the way `guard_no_retry` bounds the in-place retry.
  This is a ticket for after F1's numbers.
- **F3.** `as_written::report` labels guard outcomes `match-as-written`, so
  the metrics mix guards with `match`es. Give guards their own label
  (`guard-as-written`) through `report_as`.
- **F4.** The match path warns `W-MATCH-UNCONFIRMED` when a type was read as
  shown. The guard path gives up earlier (`read_type`'s `true` returns
  `None`), so that doesn't apply here. It's worth a line in the comment so a
  later change doesn't copy the match path half-way.
