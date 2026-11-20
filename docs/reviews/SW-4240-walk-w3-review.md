# Review of the walk step, W3 (SW-4240): two-run walks

Opus paper review (SW-4395), 20 Nov 2026. Branch `lane/SW-4240` (5 commits, 23355db88..d0263f9e3), 18 files, +1211/−401. Read against `docs/proposals/proof-walk-step.md` (§3.4, §4.2), `docs/reviews/SW-4238-walk-step-review.md` (§3.3, §3.10, §4) and the W1 review (`docs/reviews/SW-4239-walk-review.md`). Nothing was built or run: every claim is from reading the diff, and line numbers are on the branch (`walk/two.rs`, `walk/leaf.rs`, `walk/registry.rs`, `walk/mod.rs`).

## Verdict

**Merge after named fixes.** There is no soundness hole: every new path ends in a term the elaborator checks and the kernel re-checks, and the one new conversion (the goal after `rewrite`) is checked with `conv_now` before the walk uses it. The statements in `Syntax.FollowsBase` are unchanged (same 25 theorems by name, only proof bodies and `@[walk]` tags differ), so nothing is weakened. The fixes are three small bugs in the new code (one can crash the compiler, one fails a walk that should go on, one breaks the "never a choice" rule under unknowns) and the tests that pin the new closers down. Each is a few lines.

## Must fix before merging

1. **A nested walk has no depth bound (`leaf.rs`, the `family_statement` arm, about 134-165).** A leaf that is a family statement is walked; that walk's lemma can have a premise that is a family statement; and so on. Nothing counts: `PATH_CAP` counts splits between the root and a node (`walks.splits`, mod.rs 1468), and a chain of nested walks with no split adds none. Two registered lemmas whose premises are about each other's functions loop for ever, a Rust stack overflow that takes down `check` and the language server:

   ```
   @[walk] theorem followsF (gs: ∀ n => Parse.Follows S A (() => g n) (() => g n)): ∀ n => Parse.Follows S A (() => f n) (() => f n)
   @[walk] theorem followsG (fs: ∀ n => Parse.Follows S A (() => f n) (() => f n)): ∀ n => Parse.Follows S A (() => g n) (() => g n)
   theorem followsH: Parse.Follows S A (() => h()) (() => h()) := byWalking []   -- h calls f
   ```

   That shape is FollowsBase's own rule ("one hypothesis for each function in another file that `f` calls directly"), so once W4 tags lemmas across files it is one missing hypothesis away. **Change:** keep the nesting depth on `NodeInfo` (or `CallInfo`), and stop with `E-WALK` ("a premise's walk needs another premise's walk, more than N deep", N = 4 or 8) or, better, refuse to start a nested walk of a statement (relation and thunk heads) already on the nesting stack. Add a reject example with the two lemmas above.

2. **`rewrite_twin` fails the walk when the twin isn't in the goal (`two.rs` 280-345).** `equate` is set after every two-run bind with two values (`bind_step`, mod.rs, `binders.len() > 2`), and `rewrite_twin` rewrites whenever the fact is an equation. If the continuation doesn't use the value (`let _ := here(); 1`, or a value used only by a branch the computation has already removed), the goal after the bind is `Follows … (() => 1) (() => 1)`, the twin doesn't occur, and `rewrite` stops with `E-REWRITE-NOTHING` ("the rule's left side isn't in the goal", `rewrite.rs` 1053-1056). The walk then fails with "the rewrite didn't check" where `followsDone` would have closed it. **Change:** before writing the rewrite, check that the twin's variable occurs in `cx.quote_folded(expected)`; if not, return `Ok(None)` and walk on without it. Add an accept case to `walk-two-run.sw` (a bind whose value is unused). While there, handle the fact written the other way (`twin = value`) by rewriting forwards, or say in syntax.md that only `v = vTwin` is used.

3. **The bracket-term leaf closer takes the first item that checks, even when the goal has an unknown (`leaf.rs` 112-133).** Its comment says "the goal has no unknown here, so the first that checks is as good as any". That isn't established: the guard at the top of `leaf` refuses only *pending* unknowns (`search_pending_in`), and the hypothesis closer a few lines later still handles goals with unknowns (`[.., last] if !has_unknown(..)`), which is exactly the case where W1's must-fix 3 made "first that unifies" a choice. Here `check(cx, &e, expected)` under `attempt` keeps whatever the first item fixed. With a closed goal, first-that-checks is fine (any proof of a closed proposition will do, as W1's review agreed for hypotheses), so this is the design's rule only where an unknown is left. **Change:** if `has_unknown(cx, expected)`, try every bracket item under a `Snapshot`, restore after each, and use one only if exactly one checks; otherwise go on to the next closer. Keep first-that-checks for closed goals, and fix the comment to say why.

4. **Tests for the new closers and the fixed-function rule.** The accept example exercises the nested walk (`followsCollectHeres`) but nothing exercises:
   - the bracket-term leaf closer at all (it is used in `FollowsBase`, `followsTupleSecond`, but no example pins it);
   - a leaf that is a family statement the nested walk *can't* prove, closed by `then t` (the fallback after `snapshot.restore`). This is the one-run regression risk: in a W1 walk, a leaf `then t` used to close now meets the nested walk first. It also settles one question I couldn't answer by reading: a nested walk's inner leaf with an unknown is queued (`tactic_or_wait`) inside `check`, so the outer `check` may return `Ok` with a wait that fails later, after the leaf has stopped trying `then t`. The test shows whether that happens;
   - the fixed-function rule in a one-run walk (a `Gives` lemma with an explicit function parameter whose type keeps an unknown).

   One accept example per bullet, the second in `walk.sw` (one run) and in `walk-two-run.sw`. If the second bullet shows the queued-wait problem, the nested walk should run with waits turned off (fail rather than queue) and fall through.

## Follow-ups to file

1. **Overlapping two-run `@[walk]` lemmas are accepted at registration (`registry.rs`, the `@[walk]` arm).** Uniqueness compares the whole list of thunk heads, so `(fail, any)` and `(fail, bump)` both register and then fail with "two lemmas fit" at the first `(fail, bump)` pair. That keeps "never a choice" (it is an error, not a pick), but moves the error from the lemma's author to every walk that meets the pair. Treat `None` as a wildcard: two lemmas whose head lists overlap (each position equal or either `None`) are `E-WALK-LEMMA`. The message should name the pair, not only the first-thunk head it names now (`g.def(head).name()`). Before W4 tags more `Follows` lemmas. Add a walk-time two-fit reject for two runs too (bar 3's "two lemmas" case has no two-run example).
2. **`followsTupleClose` needs its thunk written out (lane's risk 6).** `byWalking [followsFatalAny]` works in `followsAnnotatedEnd` and `followsListSpread` but not here, where the `fatal` call is reached after `unfold tupleCloseAfter` under the rewrite. A bare name failing where its applied form works suggests a fitting or `Param::Shown` printing bug (the expansion writes `cx.show_term` of the thunk, which may not re-parse: `fatal` against `Syntax.fatal`). Diagnose with `--expand-walk` and the bare form before W4, since bare names are what every walk will use.
3. **Names in a lone split's second run** are the first run's with a numeral (`items1`, `trailingComma1`, `field11`, `y1`), and users write them in `then t` (`followsTupleEnd`, `followsListItemsEnd`). The values use `Twin`; the split fields should too (`itemsTwin`). Also `x` in `(x, y)` comes out as `field1`: W1's follow-up 8 (`generated` treats a user's `x` as the compiler's), now visible in an expansion.
4. **Thunks found by "a `Lam` in the statement" or "a binder of function type".** `families` takes every literal lambda in a done or bind lemma's conclusion as a thunk, so a user family whose done-lemma writes its post as a lambda (`(v => True)`) becomes a two-run family. `then`'s first-premise thunks are "every argument whose binder is a function", which for `Parse.followsThen` gives four (`same`, `between`, `p`, `q`); it is harmless today only because `thunk_indices` looks at the family first and `Follows` has no bridge. Recognise a thunk by its type, `() → {e} a`, in both places, and refuse a family with more than two at `E-ATTRIBUTE` (a three-thunk family is now walked silently as one run on its first thunk, `step`'s `thunks.len() == 2` test).
5. **`families`' new sort fixed a silent W1 bug,** worth saying in the merge note: on `main` a weaken-lemma whose `DefId` was below its family's done and bind lemmas was dropped (its statement has no literal thunk, so it created no family and was skipped). `Parse.readsWeaken` (Reads.sw:443) is below `Parse.readsThen` (718) and `Parse.readsDone` (785), so `ReadsIn` walks had no weaken step. They now do. A one-run `ReadsIn` accept case that weakens would pin it.
6. **`quoted` counts brackets inside strings** (`expand.rs`, the new function): `render` was made string-aware in this lane, `quoted` wasn't. A bracket item like `followsFatalAny "(" …` gets a `)` too many. Share one string-aware counter.
7. **Error text.**
   - The missing-lemma message names only the first run's function ("this pair of calls of `here`"); when the runs' heads differ it should name both. Its note says "give a lemma for it", better "for the pair".
   - The shapes reject shows the code as elaborated (`Std.Effect.bind (here ()) (at => Done (at + 1))`) and the goal's `(x y => True)` as `(x y => True = True)`: the second is a display bug in proposition coercion. Quoting the source span of each run's step would read better.
   - When the nested walk and `then t` both fail, the leaf reports the nested walk's error only. Show `then t`'s as a note: a user who wrote `then t` for that leaf expects to see why it didn't close it.
8. **Check time.** The new closers run at every leaf that reaches them, after `arithmetic`: every bracket item is elaborated against the goal, then a nested walk is attempted, before `then t`. With the worst theorem at 2.9× against a 3× bar, W4 will cross it. Try `then t` before the nested walk when the walk has one, and skip bracket items whose type's head isn't the goal's.
9. **Code health.** `two::step` repeats the one-run loop's reduce-and-unfold structure, and both have the bare `1000`. `bind_step` keeps `too_many_arguments` (W1 suggested a `Here { node, info, family }`). `calls_shown` joins `shown[1..]` for what is always one. None of this blocks.
10. **The proposal's §3.4 two-run bullet** describes `followsIf`'s agreement goal; the code rewrites equal values instead, and splits once after. A one-line note in the proposal (or the ticket) saves the next reader the comparison.

## The eight questions

### 1. Soundness

There is no way past the kernel.

- **`rewrite_twin`.** It writes `rewrite <- fact then (resume next)` and elaborates it with `check_written`, so the rewrite is the ordinary `rewrite` (its motive and transport are the kernel's to check). The walk then reads the rewritten goal, which is unfolded, as the folded goal with the twin replaced (`Planned` with `Replacement::Variable`); `planned_goal` builds that and returns it only if `conv_now(goal, expected)` holds (mod.rs 401-427), so a wrong reconstruction is a stop, not an assumption. The fact must force to `Eq` with sides convertible to the two value variables, so a `WordsAlike` fact is never rewritten with.
- **The nested walk.** It is `check(cx, resume(next) or (names => resume(next)), expected)` under a `Snapshot`, restored on a non-fatal error; it produces an ordinary term. The risk is termination, not soundness (must-fix 1).
- **The lone split.** It is the same `split` as a two-run split, against `refolded`, which is conv-checked against `expected` (two.rs 212-231). A one-constructor `match` can't drop a path. An indexed one-constructor type would fail to elaborate, not pass wrongly.
- **The bracket-term closer** returns `check`'s own term.
- **`Param::Shown`** puts a hole in the term (`Expr::Hole`) and the text in the expansion; the hole is solved by unification against the goal when the lemma is applied, or the step fails.
- **The fixed-function rule** only changes whether a solved explicit argument is passed as a premise leaf or as the value unification already gave it; the term is the same.
- **Statements.** `FollowsBase`'s 25 converted theorems keep their statements; the std change is three attributes.

### 2. The design's rules

- **Two fits at one rank is an error.** Kept in `choose` for pairs: all four tiers collect every fit and stop at two, and a lemma fits only if each thunk unifies with its run's call (`fit_type`, `indices.len() != calls.len()` refuses a one-run lemma for a pair). Overlapping registrations surface as this error at walk time (follow-up 1).
- **The bracket-term closer's "first that checks"** is a choice only where the goal has an unknown (must-fix 3). For a closed proposition it isn't one in the sense the design forbids: the design's concern is a pick that changes *what* is proved or fixes an unknown by accident, and proof irrelevance makes any closer of a closed goal equivalent (W1's review accepted the same for hypotheses). It does add the brittleness §3.9 warned about (adding a bracket item for a call can change how an unrelated leaf is closed), but only in the text, never whether the walk succeeds.
- **Only visible lemmas.** `families`, registration and `choose`'s tier 4 filter by `crate::auto::visible`; `family_statement` uses `families`; the closer uses only what the user wrote in the brackets.
- **One done, weaken and bind lemma per family.** `Parse.followsDone`, `Parse.followsThen` and `Parse.followsWeaken` are the only tags; `followsThenEq` (also a bind lemma with a `Follows` first premise) is left untagged, which `unique_family_lemma` would otherwise refuse. Good.
- **Splits on different values are refused,** with both shown (`differ`). The lone split is an extension the design didn't list. It is in the spirit of "never guesses how two shapes line up": a one-constructor split doesn't branch, and the run taken is fixed (the first run's, then the second's).

### 3. One-run regressions

- **The bracket-term closer** runs after every W1 closer and before `then t`, so a W1 leaf that something earlier closed is unchanged. A leaf `then t` closed may now be closed by a bracket item instead: a different text, the same statement. It can fail a walk only through must-fix 3 (an unknown fixed wrongly) or a successful `check` that leaves a failing wait.
- **The nested walk** also runs before `then t`. If it succeeds, `then t` isn't used there; if it fails, it is restored and `then t` runs. The two risks are must-fix 1 (no bound) and the queued-wait question in must-fix 4.
- **The fixed-function rule** changes only parameters of function type whose meta the call solved and whose type still has an unknown. Before, `is_proposition` on such a type (an unknown sort) could call it a premise and make it a leaf, which only a hypothesis could close. Now it is the value unification found. A W1 walk can change its expansion's text here, not its outcome.
- **Weakening** now reads which premise is the implication; for `givesWeaken`, `readsWeaken` and `readsAtWeaken` (relation first) it does what it did. The value-binder position for one run is `binders.len() - 2`, as before.
- **`families`' sort** gives `ReadsIn` a weaken lemma it lacked (follow-up 5): walks that stopped for want of it now go on.
- The lane rechecked `ParseWalk` and `walk.sw`; the walk-expansion test covers `walk.sw` and `walk-two-run.sw`.

### 4. Determinism under retries and hypothesis order

- The two-run step reads both runs in a fixed order: both reduce, then `unfold` in either run, then the classification pair; a lone split takes the first run before the second.
- Names: values are the program's binder and `<name>Twin`, the fact `<name>Facts`; the lone split's names take a numeral (follow-up 3). Neither depends on hypothesis order, only on what is in scope.
- Retries: each run of a node re-creates its children (`place`), as in W1; `rewrite_twin` re-runs from `equate`, which is on the node, and the node it creates carries no `equate`, so it can't repeat itself.
- Hypothesis order matters only where W1 allowed it (none left after W1's must-fix 3), plus the bracket-term closer's item order (must-fix 3).

### 5. Error quality

The two new rejects are clear: each says what the runs do ("the first runs a call and goes on, the second gives a value"; "no lemma for this pair of calls … one in each run"), shows both runs and the goal, and says what to do ("prove this point by hand, or with a lemma for the pair named in the brackets"). The place names both functions (`in reading and fixed`). Weak points are in follow-up 7: the first run's head alone in the missing-lemma message, the elaborated code and the `True = True` display, and the hidden `then t` error.

### 6. Docs

- **syntax.md** matches the code on lockstep, the names (`v`, `vTwin`, `vFacts`), the rewrite, the split once, the lone split, `followsDone`/`followsWeaken`, the second-run wildcard, the leaf closers and their order, and the family shape for two runs. Gaps: "one per pair of functions" in the attribute table should say that a lemma leaving a run open covers every function there (follow-up 1); "where the fact says the two values are equal (`Same v vTwin`, `v = vTwin`)" should say the reversed form isn't used (must-fix 2).
- **proving-guide.md** says what the walk can't do (related but unequal values, `Parse.mark()`'s marks), which matches `differ`. Good.
- **Guide 10-proofs.md**: one paragraph, accurate.
- **Module docs**: `two.rs`'s list matches `step`'s match arms. `leaf`'s doc summary ("closed by a hypothesis, computation, a conjunction of closed parts, `arithmetic`, or the walk's `then t`") should add the two new closers.
- **FollowsBase's header** now says most proofs are walks and the steps are what a walk writes. Good.

### 7. The bars (SW-4238 §4)

| Bar | Evidence | Judgement |
|---|---|---|
| 1, lines | proof lines 181 → 31 over 25 theorems; every converted proof is shorter | Met by a wide margin |
| 2, check time | namespace 1.39× (bar 1.5×); worst theorem 2.9× (bar 3×) | Met, thinly. One run each, as far as I can tell; 2.9 against 3 is inside run-to-run noise, so W4 should take the median of three. Follow-up 8 is where the time goes |
| 3, rejects | missing lemma (pair) and different shapes, both naming the call or place and showing the goal | Met for what exists; two-run "two lemmas" has no example (follow-up 1) |
| 4, expansions check | `walk_expansions_check_again` now runs on `walk-two-run.sw`, text and trace snapshotted; the lane reports `FollowsBase`'s expansions recheck | Met for the example; FollowsBase's is a claim, which is acceptable for a pilot |
| 6, ten two-run walks | 25 | Met |
| 7, walks needing expansion | not reported; proving-guide names `followsListItems` and `followsAtomAfter` as kept by hand | The lane's report should give the count (kept by hand, and `followsTupleClose`'s written-out thunk) |

### 8. Code health

`two.rs` is a clean, separate module, as W1's review hoped; the one-run code changed only where it had to (vectors of calls and thunks, `Replacement`, `lambda`, the weaken order). The `lambda` helper with empty-at-end spans is a tidy way past `W-LAMBDA-SHADOW`. The `quoted` and string-aware `render` fixes are right in direction (follow-up 6). The duplications and leftovers in follow-up 9 can wait for W6.
