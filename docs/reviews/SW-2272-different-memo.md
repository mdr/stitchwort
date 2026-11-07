# SW-2272: review of SW-2269 (tree memo remembers "different")

Reviewed: merge `e089948d1` (`crates/core/src/value.rs`, `reference.rs`,
`crates/elab/src/unify.rs`, `docs/core.md`, the two new tests). Read only;
nothing built or run.

## Summary

The change is sound and, as far as I can see, complete. I found no way a
remembered "different" can go stale. Within one outermost tree comparison
nothing that can change the answer moves: solutions are kept out by
`unifying` and `settled`, taking a solution back bumps the epoch, and mode
and level are in the key. The reference does the same as the kernel. The
new sentence in `core.md` is accurate. The findings below are all low: one
invariant that lives only in the order of the match arms, and missing tests
for the cases where "different" must not be remembered.

Top recommendations:

1. Make `settled` in the unifier's same-definition arm say what it relies
   on, rather than leaving it implied by the arm above (F1).
2. Add a regression test for the cases where "different" must not be
   remembered: a pair that mentions an unknown, found different, then equal
   once a sibling solves the unknown, all within one outermost comparison
   (F2).

| # | Severity | Confidence | Where | Finding | Size |
|---|---|---|---|---|---|
| F1 | low | high | `crates/elab/src/unify.rs:1627` | `settled` relies on the order of the match arms | S |
| F2 | low | high | tests | Nothing tests the cases where "different" isn't remembered | S–M |
| F3 | low | medium | `docs/core.md:236` (glued calls) | Two "remembers pairs found different" mechanisms, easy to confuse | S |

## Details

**F1. The same-definition arm's `settled` is right only because of the
arm above it.** In `unify_step`'s same-definition tree arm,
`same_stuck_trees` is passed `settled = !NO_ETA` with no check for unknowns.
That is correct because the earlier guard `may_mention_meta(s1) ||
may_mention_meta(s2)` has already sent every spine that might mention an
unknown elsewhere, but the invariant lives only in the arm order and a
comment ("With no unknown in either spine …"). If those arms are ever
reordered or the guard narrowed, unification would start remembering a
"different" for pairs that mention an unknown. A later solution in a sibling
pair could then make the pair equal, and the memo would still say
different. That is a completeness bug, and a silent one. Fix: compute it as
the `i1 != i2` arm does (`!NO_ETA && !may_mention_meta(s1) &&
!may_mention_meta(s2)`; at most 64 parts each), or add a `debug_assert!`.
Size S.

**F2. Nothing tests the cases where "different" must not be remembered.**
The two new tests check speed: `conv` and unification each answer
"different" quickly on nested `pred`. Nothing fails if `settled` or the
`unifying` gate is wrong. Suggested tests:

- (a) Unification, two different tree-opening definitions with a spine that
  mentions `?m`. The pair is found different, then a later sibling in the
  same outermost comparison solves `?m` so that the same pair is equal.
  Expect success.
- (b) A `conv` run inside an open Unify tree comparison leaves no
  `different` entry. This is a unit test in `value.rs` on `TREE_MEMO`
  (`unifying > 0` gives `settled == false`).

(a) may take some care to build, so allow a lane. Size S–M.

**F3. The docs now describe two memos of pairs found different.** The
"Glued calls" bullet already says the kernel's `conv` "remembers the pairs
of calls found different in one comparison so the fallback doesn't repeat
work, D483". That is `CallMemo`, per `conv` call. The new sentence in the
`≡` bullet describes `TreeMemo`'s "different" record, per outermost tree
comparison, which the unifier also uses. Both are accurate, but nothing
tells the reader they're separate. A half-sentence pointer would help.
Size S.

## Checked and sound

- **Key** `(Relation, Mode, level, epoch, def, def, shape, shape)`, with
  pairs told apart by `identical`:
  - Relation keeps `conv` and unification answers apart.
  - Mode keeps a shortcut-mode "different" (where proof fields count) from
    answering normal mode.
  - The epoch is 0 for the kernel and starts at 1 in the elaborator
    (`MetaStore::default`).
  - `undo_since`, `MetaStore::restore` and `clear_metas` all call
    `metas_taken_back`, so any taking back makes older entries unusable.
- **Lifetime.** Entries are dropped when the outermost `TreeMemo` drops,
  including on `Err`: the `TreeMemo` exists before `enter`'s fallible
  shape hash, so `Drop` still decrements `open` and `unifying`. An `Err`
  is never recorded, since `record` comes after the `?`.
- **The `unifying` gate.** A `conv` records "different" only when no Unify
  tree comparison is open around it. For that to be stale, something would
  have to solve an unknown while the record lives. `conv` in an outermost
  `TreeMemo` can't do that: `stitchwort-core` can't call the elaborator
  (crate layering), and the `Metas` trait only reads solutions and the
  epoch. A `conv` that the unifier calls outside any tree comparison opens
  its own outermost memo, which is dropped before the unifier goes on. So
  "no unification open" is detected reliably, by construction, not only by
  convention.
- **`NO_ETA`.** It is only ever set to true (`first_order`, around one
  `unify_in`), and it only weakens unification. So a "different" found with
  eta is still right under `NO_ETA`, and an "equal" found under `NO_ETA`
  still holds with eta. `NO_ETA` needn't be in the key. Gating `settled` on
  `!NO_ETA` is exactly what's needed.
- **`may_mention_meta`** is conservative: anything it doesn't know about
  (metas, glued `Call`, closures, projections), or more than 64 parts,
  counts as "may mention". For meta-free pairs, unification never
  postpones, so clearing `waiting` in `nested` doesn't matter.
- **Order inside `same_stuck_trees`** (memo, then arguments, then trees).
  A cached "equal" skipping the argument unification loses no solutions:
  that arm is meta-free (F1), and in general an identical pair found equal
  in the same epoch stays equal. The unifier's double `undo_since` on
  failure does nothing the second time.
- **The reference agrees with the kernel**: the same order (memo, then
  `conv_spines`, then `same_trees`), recording both answers, keyed by mode,
  level and printed quotes, conv only. It doesn't check
  `shortcuts_disabled()`, but it didn't before this change either, and an
  exact memo gives the same answers anyway.
- **`core.md`'s new sentence** is accurate. "Where no solution made before
  the comparison ends could change that" matches the code, and "a
  remembered answer only saves work" holds for both relations under the
  conditions above.
- The 1 Nov codebase review has no findings on this memo (it came later,
  SW-395 and SW-2269), so there is nothing to update there.

## Tickets to file

- **Lane A (Sonnet, about 45 min):** F1 (explicit `settled`) and F2
  (regression test (a) in `proof_equivalence.rs` or `unify` tests, and unit
  test (b) in `value.rs`).
- **Small fix (orchestrator or DeepSeek, 5 min):** F3, the docs pointer.

No D questions.
