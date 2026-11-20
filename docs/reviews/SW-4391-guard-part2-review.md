# SW-4402: review of lane/SW-4391 (guard refinement, part 2; D3701)

Reviewer: Opus, paper only (no builds or tests), 20 Nov 2026. Read
`git diff main...lane/SW-4391` (one commit, 0c05d1951), the branch's
`check_guard_if` (check.rs), `check_guard`, `Tree::moved`,
`split_levels`, `compile_guard`, `is_flat`, `check_flat` (lib.rs),
`refined_guard`, `in_place_level`, `refined_in_place`, `bind_generalised`,
`variable`, the variable-`match` lift (matching.rs), `lift::draft_with`,
`undo::attempt`, `along_match_equation`, docs/core.md on `Case`/`Let`,
the design note and the part-1 review (docs/reviews/SW-4385-guard-review.md).

**Verdict: merge.** No must-fix items. The in-place term is the same
shape `match flag with` already produces, every renaming error ends in an
elaborator type error (then a fallback) or a kernel rejection, never a
proof of another statement, and the attempt count stays bounded
(quadratic in a guard chain, as on main). Two small fixes are
recommended but not blocking (a one-line `debug_assert!` and a test that
shows the in-place split is *needed*); the rest are follow-ups.

One fact the lane didn't state, which settles several questions at once:
**the trees `check_guard` moves are always flat.** `compile_guard`
(lib.rs ~5246) requires `is_flat(otherwise)` (only `Leaf`, `Missing` and
`Guard`; a `Case`, `NumCase`, `FinNumbers` or `Absurd` there is
`E-GUARD-ARMS`), and `leaf` is always a `Tree::Leaf`. So the compiler
splits every column the rows below need *above* the guard.

## 1. Soundness of `moved` and of the in-place term

**A wrong renaming can't give a proof of a different statement.** The
renaming acts on elaborator levels in the tree; the term is built from
those same levels, and the lifted helper's parameters are those levels
(`lift::spine`). So the elaborator and the kernel agree on what each level
is: a wrong renaming would pick the wrong variable, typed the same way by
both, and the result is an elaborator mismatch (caught by the retry chain)
or a kernel `E-TYPE-MISMATCH`. The theorem's type is fixed by its
signature and checked by the kernel; the `%match` helpers' types are
kernel-checked too. Nothing here touches the kernel.

**`moved` in `check_guard`.** Since both trees are flat, the only levels
`moved` meets are leaf aliases, text-rest lets, `unsplit`, arm facts and
`Missing` columns: no split `depth`, so no fields. The map `at` is
"`l ≥ split_at` → `l + added`; an original < `split_at` → its copy;
otherwise unchanged". Counting the bindings: generalised, `x` at
`split_at`, the `k` copies, the equation, then the arm's fact, so
`added = k + 2` and the old fact variable `split_at` lands on the new
fact. In place, `%guard` then the fact, `added = 1`, no copies.
Both right. Copies are always of levels below `base = split_at`
(`bind_generalised`), so no original ≥ `split_at` is ever looked up.
`bind_generalised` inserts `(original, copy)` into a `HashMap` and the
lane sorts the pairs: orientation and determinism are right.

**The in-place term.** `refined_in_place` builds
`Loc(Case(flag, Bool, [Let(%guard, False = False, refl, arm),
Let(%guard, True = True, refl, arm)]))` and lifts it with
`lift::draft(cx, base, [], …)`. That is the shape the variable-`match`
path already lifts (matching.rs ~640: `check_tree_here` emits a `Case` on
context levels, `draft_with(cx, base, Vec::new(), …)`), with a `Let` leaf
on each branch. Checked against docs/core.md:

- `Case` is at the top of the helper's body, on a parameter (the level is
  a plain variable, not a `let`, by `in_place_level`). Correct.
- No `Case` under a `Let`: the `then` arm is a leaf; the `else` arm is
  `check_flat` of a flat tree, whose `Missing` case lifts an impossible
  case's `Case` into its own helper (lib.rs `check_flat`), and whose
  `Guard` gives a helper call or `proof_if`'s application. Correct.
- The `%guard` fact is `refl : c = True` with `c` evaluated in the
  substituted environment, so `True = True`; the kernel checks it under
  the branch, where the variable is `True`. Trivially sound. For a
  decided proposition whose `holds d` happens to force to a variable,
  `d.sound eq` with `eq : True = True` needs `holds d ≡ True` in the
  branch, which holds once the variable is substituted.
- The elaborator's per-branch `env`/`types`/goal substitution mirrors the
  kernel's `Case` refinement, exactly as `refined_guard` and
  `check_tree`'s `Case` do.

Residual, not new: a metavariable from outside the arm solved inside it
with a value that uses the substituted `True` would be wrong outside.
That risk is the same for every refining `match` arm and for part 1;
nothing here makes it worse.

## 2. D3688: can anything that checks on main stop checking?

The chain is now: generalise (part 1, arms now moved onto copies) → on
`Ok(None)` or a non-fatal `Err`, if retrying, the in-place split inside
`undo::attempt` under `guard_no_retry` → on `Ok(None)` `proof_if`, on
`Err` the unrefined retry under `unrefined_guards` → else the refined
errors again. The in-place try only adds a success route: a failure rolls
back fully (`attempt` is a `transaction`) and the chain continues as on
main. So:

- **Against the behaviour before refinement (D3701's promise)**: kept.
  `proof_if`, with inner guards unrefined, is still the last thing tried
  on every path, as on main.
- **Nested guards that don't retry inside the in-place try**: inside it an
  inner guard whose generalisation fails errors out without its own
  retry, so the whole in-place try fails and the outer guard goes on to
  `proof_if` or the unrefined retry, which is main's path. That loses
  in-place successes that needed an inner retry, but never something main
  had. Fine.
- **Against main with part 1 (the lane's risk 1)**: a narrowing is
  possible in principle. A proof that checks on main *only* refined
  (the goal needs the `True`), whose guarded arm uses a pattern variable
  at its original, unrefined type somewhere that must agree with
  something else unrefined and that transport can't fix, now fails the
  generalised try (the name means the copy), and the unrefined retry
  fails too because the goal needs refinement. `along_match_equation`
  works in both directions for proofs, so this needs a *data* use, e.g.
  `f b w` with `f : (c: Bool) → Vec Nat (pick c) → …`, whose result doesn't
  reach the goal. Contrived, it's exactly what a `match g:` arm would
  reject too, and part 1 has been on main only hours. The unchanged hash
  snapshots of part 1's examples show none of them is affected. I
  wouldn't add a fourth attempt (generalise with unmoved arms) to cover
  it: it would keep a mixed semantics that `match` doesn't have. This is
  the proof language, not a proved tool, so it's the orchestrator's call
  under D3701; mention it in one line.
- **Other ways a proof can stop checking**, all marginal: extra attempts
  can push a proof near the elaboration budget over it (only on paths
  that failed the generalisation); a fatal error raised only inside the
  in-place try propagates (`?` on `counted(…attempt…)`), where main would
  have gone on to `proof_if`. Neither is likely; the second is worth one
  line in a follow-up (catch only budget exhaustion as fatal there).
- **Hashes outside the snapshots**: a theorem that fell back on main and
  now succeeds in place gets a new term, so its hash moves (std, AoC,
  fmt). That's allowed (D2303), and theorems carry no native pins, but
  "no existing hash moved" is true only of the snapshot set. The
  verifier's hash snapshots won't show it; Overmind's checks will pass.

## 3. Determinism and cost

Deterministic: fixed order of attempts, snapshots restored, copies
sorted, `split_levels` used only for membership.

Bounded. Let T(k) be a chain of k guards with retrying, N(k) and U(k)
the same under `guard_no_retry` and `unrefined_guards`. N and U are
linear (each guard prepares once and checks its arms once; the in-place
try is skipped without retry). T(k) = T(k−1) (inner chain inside the
generalised try) + N(k−1) (in place) + U(k−1) (unrefined) + N(k−1) (errors
again) + c, so T is O(k²), the same order as main, with one more linear
term. Only a failing guard pays it; a guard that refines generalised
costs one attempt, as before. Guarded matches nested inside a guarded
arm's *right side* are checked once per attempt of the outer guard: up to
4^d at nesting depth d (main 3^d). d is syntactic and small in practice.

`split_levels` now runs for every guard, programs included; it walks a
flat tree, at most `MAX_GUARD_NODES` nodes, so the cost is negligible. It
could run only when the goal is a proof (follow-up, cosmetic).

## 4. Should `moved`'s invariant be a debug assertion?

Yes, but a different one from the doc comment's. In `check_guard`'s use
the "fields stay above every renamed level" invariant is vacuous, because
the trees are flat. What should be asserted is flatness:
`debug_assert!(is_flat(tree))` in the `refined` closure (one line).
That's what makes the copy map safe; it would catch a future compiler
change that lets a `Case` below a guard; and it documents why. `moved`'s
doc could also say that the one non-monotone map comes from `check_guard`
over flat trees. `shifted`'s map is a uniform shift and needs nothing.

On the same grounds `split_levels`' `Case`/`NumCase`/`FinNumbers`/`Absurd`
arms are dead for its only caller: only `Missing` columns can reach
`guard_splits`. And a `Bool` variable the arms below match on is already
split above the guard (its value is a constructor, not a variable), so
`in_place_level` would refuse it anyway. Harmless; worth a comment or a
trim.

## 5. Docs

- docs/syntax.md: accurate. "a `Bool` variable the arms below don't match
  on" is true, but since rows below that match on it make the compiler
  split it first, suggest "(where the arms below match on it, it is
  already split)" or dropping the clause. "refines like `| p => match g: c
  with …`" is now literally right (see 6).
- docs/proving-guide.md: accurate.
- Not updated: the design note's status line ("Nothing is built") and the
  part-1 review's wrong premise (below). A one-line erratum under the
  review's §3a would stop the next reader repeating it. Both are small
  orchestrator edits, not this lane's.

## 6. The lane's two corrections of the part-1 review

Both right.

- **`match g: b` generalises rather than splitting.** matching.rs
  `variable()` returns `None` for any scrutinee with a name, so `match g:
  b` goes down the expression path (`generalised`); only an unnamed
  `match b` splits the column. The part-1 review (my §2, §6) said
  otherwise.
- **`eitherWay` refines on main.** Because `otherwise` must be flat, the
  compiler splits `b` above the guard, so at the guard the condition is
  the constructor `True` or `False`, not the variable, and the tree below
  never splits an original after generalising. The part-1 review's 3a
  premise ("the tree's split on the original `b` no longer touches it")
  was wrong. Its must-fix (the unrefined retry) still stands on other
  grounds (3b to 3e) and is on main.

## 7. Tests

The three accept examples with hash snapshots cover: names in both arms
meaning copies (`copiedInBothArms`, `copiedBelow`), arms below not
seeing the guarded arm's names whether the outer name is copied or not
(`outerCopied`, `outerKept`), and the in-place route being taken
(`byName`, pinned by its hash).

Gaps:

1. **No test shows the in-place split is needed.** `byName` checks
   unrefined on main (`same (pick flag) v` against `v = v` needs no
   refinement), so it pins the route but not the gain. Add one where
   generalise and unrefined both fail and only in place succeeds, e.g.
   a goal that needs `pick flag` to compute and an arm that writes
   `flag` in a data position. Recommended before merging; small.
2. A chain: an in-place guard followed by another guard, so `added = 1`
   composes with an inner refinement, and the no-retry rule inside the
   in-place try is exercised.
3. A named in-place guard (`| 0 if g: flag => … g …`) using `g` as
   `flag = True`: the fact form changes to `True = True`, and conversion
   is what makes it work.
4. A goals snapshot for an in-place arm, for the "`True = True` not
   listed" display change (lane risk 4). The change itself is right:
   display only, the fact is still bound for `auto` and `cases`. Note that
   `trivial` also hides a part-1 fact that is literally `True = True`
   (a guard whose condition is already a constructor, as in `eitherWay`)
   and a decided `Red = Red`. Also fine.
5. A fallback test for lane risk 1 (a guarded arm that checked refined
   with the original name now checks through the retry), so the claim
   "they still check through the retry" is pinned.

## Lane's risks, judged

| risk | judgement |
|---|---|
| some proofs that refined now fall back (`rewrite e` with the original) | falling back is fine; a narrowing against part-1 main is possible only in a contrived shape (data use of the original, goal needing refinement), the same as `match g:`; no fourth attempt (§2) |
| in-place term shape | the variable-`match` shape plus a `refl` `Let` leaf; well-formed under core.md's `Case`/`Let` rules; sound (§1) |
| `moved`'s invariant only argued | vacuous here: the trees are flat. Assert `is_flat` instead (§4) |
| unnamed `True = True` not listed | right, display only; add a goals snapshot (§7.4) |

## Must fix before merging

None.

## Recommended before merging (small, could also be follow-ups)

1. lib.rs, `check_guard`'s `refined` closure:
   `debug_assert!(is_flat(tree))`, and a line in `moved`'s doc that the
   copy map relies on it.
2. examples/accept/guard-refinement-variable.sw: a theorem that checks
   *only* in place (§7.1).

## Follow-ups (file as tickets)

- Tests §7.2 to §7.5: in-place then a chain, a named in-place fact used as
  `flag = True`, a goals snapshot of an in-place arm, a fallback for
  lane risk 1 (Sonnet, small).
- `refined_in_place` lifts with `lift::draft`, without `columns`, so
  `match_columns` has no entry for the helper: a stuck call to it displays
  as the raw helper, not `match flag with`, and `equations.rs` (a def
  with a proof-typed result) has no column record. Pass
  `Some((vec![level], vec![None]))` through `draft_with` (Sonnet, small).
- In the in-place try, treat as fatal only budget exhaustion, so an
  error that's fatal only there falls back as main would (Opus, small;
  read `undo::fatal` first).
- `split_levels`: trim to `Leaf`/`Guard`/`Missing`, or comment that the
  others can't occur below a guard; compute `guard_splits` only for proof
  goals (Sonnet, cosmetic).
- docs/syntax.md wording of "the arms below don't match on" (§5).
- Orchestrator: erratum line in docs/reviews/SW-4385-guard-review.md §3a
  and §2/§6 (`match g: b` generalises; the column is split above the
  guard); the design note's status line.
- Tell the orchestrator (one line, its call under D3701): against part-1
  main a contrived proof can stop checking (§2); against the behaviour
  before refinement, nothing can.
