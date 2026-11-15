# SW-3317 review: goals at a match arm show the arm as written

Opus review, 15 November 2026, of `lane/SW-3317` (`2cbb78e74`, board
`9c2472916`) against docs/proposals/catch-all-goals.md option A. Probes are
in the reviewer's scratchpad (`sw3317-review/probes/r1.sw` to `r5.sw`). They
were run with the lane's release binary, rebuilt at 04:45, and compared with
the main checkout's release binary (built 04:05).

## Verdict

The bookkeeping is sound. Terms and hashes can't change: `Row::unsplit`,
`Tree::Leaf::{unsplit, cases}`, the split path and the arm stack are read
only by `arm_display::view`, `case_note` and the goal printer. Nothing in
term construction reads them, and the steps counted on day 18's and day 7's
proofs are identical. The common catch-all goals the paper set out to fix
now read well: `p s`, `p other`, `p o` after `Some True`, `p (q s)` for an
expression, and `h: q o` for a hypothesis.

But there is one must-fix display bug. The `computes to` line folds the
leaf's values back into variables by searching for them, which is exactly
what the proposal ruled out. It prints wrong computations: `f c = Blue`
"computes to `c = c`", and `isSomeTrue o = True`, whose real goal is the
unprovable `False = True`, "computes to `value✝`". A second must-fix is
cheap: the note "the goal shown is the arm as written" also appears when the
`same()` guard fell back to the leaf's goal, so it can assert something
false.

Fix those two and it can merge. The nested-match, lambda-body, indexed-family
and or-pattern gaps can be follow-up tickets: each falls back to roughly
today's display.

## Must-fix

1. **`computed_back` folds back by value, not by position: wrong
   `computes to` lines** (`arm_display.rs` `computed_back`). For each level
   in `arm.unsplit`, it replaces every subterm equal to the leaf's value for
   that level with the variable. Two cases go wrong:
   - **A closed value** (a nullary constructor, a literal) also matches
     occurrences that have nothing to do with the scrutinee. Probe `r4.sw`
     `k`: `type Color = | Red | Green | Blue`, `f` maps `Red` to `Red` and
     everything else to `Blue`, `theorem k (c: Color): f c = Blue`. The
     catch-all shows `⊢ f c = Blue`, `computes to c = c`. Main showed
     `computes to Blue = Blue`, which is what conversion sees.
   - **Fields of a skipped split** (cells the user can't write) are folded
     too. Probe `r4.sw` `m`: `isSomeTrue o = True` after `Some True`. The
     catch-all shows `computes to value✝`. The leaf's real goal is
     `False = True`, which is unprovable, and the display hides that. In
     `r3.sw` `d`, `isSomeTrue o = isSomeTrue o` shows
     `computes to value✝ = value✝`.

   Suggested fix: fold back only levels that aren't fields of a split the
   arm skipped (the `fields` set `case_note` already computes), and only
   values that mention one of those fields (`MkText [MkChar code✝ valid✝,
   ..tail✝]`, which can't be mistaken for anything else). Otherwise show
   the leaf's computed goal unchanged. Add `r4.sw` to
   `examples/goals/arm-as-written-computes.sw`.

2. **The "checked in N cases" note claims "the goal shown is the arm as
   written" even when it isn't** (`goals.rs` `arm_goal`). `says_cases` is
   true for any proof at a multi-case arm, whether or not `view.goal`
   replaced the leaf's goal. Probes:
   - `r2.sw` `cnt` (`count l ≤ List.length l`, arms `[True, ..rest]` and
     `_`): the goal stays the leaf's `count [False, ..rest✝] ≤ Succ
     (List.length rest✝)`, `l: List Bool` is listed above it, and the note
     says "the arm as written, not any one case". It is one case.
   - `r2.sw` `v1` (indexed family): it shows `p (Succ n✝) (VCons n✝ x✝
     xs✝)` with the same note, but the arm also covers `VNil`.

   Fix: when `view.goal` is `None`, either give no note or word it
   truthfully: "this arm is checked in 2 cases; the goal shown is the
   last". The wording is the orchestrator's call; see item 4 below.

## Should-fix (tickets)

3. **Nested arms don't compose.** In an inner match inside an outer
   multi-case arm, the inner arm's goal keeps the outer leaf's shape. The
   context now also lists the outer variable, which makes the mismatch more
   visible than before. Probe `r1.sw` `n1`: outer `Some True` / `_`, inner
   `"ab"` / `_`. The inner `"ab"` arm shows `o: Option Bool ⊢ p (Some
   False) "ab"`, and the same happens in `r5.sw` `n2`. Main showed the same
   goal without `o`. The causes:
   - `enter_arm` records nothing for an inner arm with empty `unsplit` and
     one case, so the inner splits are lost.
   - Even when they are recorded, `undo` for the outer arm compares the goal
     with the outer leaf's goal, which the inner split has already changed.

   The fix is to replay the inner tree's splits starting from the outer
   arm's replayed state, not from the inner `Root` snapshot. Fall back when
   the arm body changed the state between the outer leaf and the inner
   root. Two related points:
   - `case_note` counts only the innermost arm. The inner `_` in `n1` says
     "5 cases", but `in_tree` compiles the inner match once per outer leaf,
     so it is checked 10 times.
   - An error in a nested arm gets two notes that both begin "this arm is
     checked in 2 cases" (`r5.sw` `n2`). Better: one note, "where `o` is
     `None` and `r` is `Some False`".

4. **Holes that aren't the arm's own goal get a mixed display and no
   note.** Probe `r1.sw` `l1`: `| _ => n => ?` shows `o: Option Bool, n:
   Nat ⊢ p (Some False) n`, with no "checked in 2 cases" note, though the
   body is also checked at `None`. Probe `i1` (`(x => x) ?`) shows `o:
   Option Bool, value✝: Bool ⊢ p (Some False)`. Before, the context and the
   goal were at least consistent. A ticket could cover this:
   - always give the note at a multi-case arm in a proof, even when the
     goal isn't replaced (once item 2's wording is truthful), and
   - leave `env` as the leaf has it when the goal can't be replaced, so
     the context doesn't contradict the goal.

5. **Indexed-family splits aren't recorded.** `families::check_case` calls
   neither `root_of` nor `enter_split`, so a later `Case` takes its root
   after the family split. `r2.sw` `v1` then shows `VCons n✝ x✝ xs✝` for a
   catch-all that also covers `VNil`. It degrades safely (except for the
   note, item 2). A ticket should record family splits, or start no root
   below one.

6. **Or-pattern arms show only their first alternative** (pre-existing; the
   lane leaves it as it was). `r1.sw` `o1`: `| Some True | None => ?`
   shows `⊢ p (Some True)` with no note, though the arm is also checked at
   `None`. Part of the same misleading-goal family, so worth a line in the
   follow-up ticket.

7. **`enter_split`/`leave_split` can be left unbalanced.** In
   `check_tree`'s `Case`, the match guard `&& let Some(term) =
   impossible_case(cx, columns, &branch_goal)? =>` returns from
   `check_tree` between the two calls. The code there already skips
   restoring `cx.env` on that path. A parent `Case` repairs it, since each
   leave restores what its enter saved. At the top `Case` nothing does, so
   `goals.split_path` stays set until `clear_goals`, and the next
   declaration's first `root_of` builds on a stale path. That is display
   only, and `replay`'s `?`s and `same()` checks make garbage unlikely to
   show, but a guard object or a reset at the start of each declaration
   would make the pairing structural. Not a panic risk in release.
   Debug builds could hit `quote`'s `debug_assert!(l < level)` if a stale
   arm were ever viewed from a shorter context. I found no path that does
   that.

## Nits

8. **The error note shows text cells raw**: "where `s` is `MkText ['a', 'b',
   head✝, ..tail✝]`". The proposal suggested `"ab" ++ …`, and that form is
   kinder in a note.
9. **Replay evaluation draws on the declaration's step budget.** `replay` and
   `computed_back` evaluate under `cx.g()`. A hole near the budget's end
   could exhaust it, and `branch_failed` then stops on
   `budget.exhausted()`. This only happens at holes and errors.
10. **The `syntax.md` paragraph is long.** It also promises "`computes to …`
    shows (for the last case, with the matched value written as `s`)",
    which item 1 changes. Re-read it after the fix.

## The questions in the brief

1. **Display only.** Confirmed. The new fields feed only `goals.rs` and the
   error notes, `count_cases` runs after `annotate`, and `Row::unsplit`
   doesn't affect any compile decision. Term construction ignores them all.
   - `enter_arm`/`leave_arm` in `check_leaf` have no `?` between them.
   - `enter_split`/`leave_split` are balanced except for item 7.
   - Nested matches and matches in lambdas, guards and recursion
     (`r2.sw` `cnt`) neither panic nor change what is checked. `count_cases`
     indexes `counts[span]` over the same tree it tallied, so it can't
     miss.
   - Steps are identical on the namespaces measured (below).
2. **The replay and its `same()` guard.**
   - Body changes are respected: a hole after `rewrite … at h` in a
     catch-all shows `k: p o`, `h: n = 3` and `⊢ p o ∧ n = 3` (`r5.sw`
     `rw`).
   - The `match e:` equation keeps the leaf's shape, as designed.
   - `p o ∧ q None` stays `p o ∧ q None` (`r2.sw` `pos`), so the undo
     works by position for the goal.
   - No hypothesis the arm can use is hidden. Variables shown are ones the
     user can write, except the arms form's unnamed parameters (`o✝`,
     `b✝`, `s✝`, as before) and the cells in item 1.
   - Wrong claims: item 1 (`computes to`) and item 2 (the note).
3. **Pasting goals back.** `binary(server) &
   test(/lemmas_check_as_the_same_goal|printed_goals_paste_back_as_lemmas/)`:
   1 passed and 1 failed in 489 s. That was build plus run, at load 25 to
   37 from other lanes, and well over budget.
   - The failure is `lemmas_check_as_the_same_goal` ("gives no goal (or
     several)", 0 found). Pasting every lemma of all 48 `examples/goals`
     back and checking it with the lane's binary turned up exactly one
     failure: `reify-return` goal 1, `toResultThenGoal2 … : Err msg = Err
     msg`. It fails with "a `_` in a declaration's type must be worked out
     from the type alone". Main's binary prints the same lemma, and it fails
     the same way there.
   - So the failure predates this change: SW-3317 doesn't touch
     `reify-return`. Worth a ticket if it isn't filed already.
   - The new arm lemmas (`stepsGoal3 (s: Text): 2 ≠ 0 ∨ s = "" := ?` and
     the rest) all check as one goal.
   - With item 1 fixed, check that the `computes to` lemmas still paste
     back.
4. **Wording.** My recommendations:
   - Goal note: "this arm is checked in 4 cases; the goal shown is the arm
     as written, not any one case". It is clear and fine when true. When
     the goal wasn't replaced: "this arm is checked in 4 cases; the goal
     shown is the last of them".
   - Error note: "this arm is checked in 4 cases, and this error is in the
     case where `s` is …". Good. For nested arms, merge it into one note
     (item 3), and print text cells as `"ab" ++ …` (item 8).
5. **Cost.** `check --no-cache`, run in the lane's `aoc/`, two runs each
   at load 11 to 27 (noisy), lane binary against main's:

   | Namespace | Lane run 1 | Lane run 2 | Main run 1 | Main run 2 | Steps (both) |
   |---|---|---|---|---|---|
   | `Aoc.Year2020.Day18.Proofs` | 10.6 s | 10.1 s | 13.1 s | 10.5 s | 1,079,603 |
   | `Aoc.Year2020.Day07.Proofs` | 16.1 s | 14.3 s | 16.0 s | 14.6 s | 1,383,653 |

   - The main namespaces took 2.4 s against 2.8 s (Day18) and 5.8 s against
     6.6 s (Day07).
   - The steps (from `STITCHWORT_TIMINGS`) are identical, and the times
     are within noise.
   - In hole-free code, the cost is one `env`/`types` clone per top-level
     `Case` (`root_of`) and one `Rc` plus a field-type copy per branch. None
     of it is measurable here.
