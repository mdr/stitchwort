# SW-3602 review: `rewrite repeatedly` stage 1

Reviewer: Opus, paper lane SW-3615, 16 Nov 2026. Read `main...lane/SW-3602`
(37 files), the ticket, simp-revisited.md "As built", helpful-errors.md §3.
Probed with the lane's release binary on scratch files (p1–p10 below). No
builds or tests run.

Line numbers are in `crates/elab/src/rewrite/repeatedly.rs` on the lane
branch unless another file is named.

## Verdict

**Sound.** Nothing is trusted that the kernel doesn't see. The term is
`J(motive, base, proof)` per step, from `rewrite_once` (the same code path
plain `rewrite` uses), around a base that is either the `then` body checked
against the final goal, `byComputing` elaborated with `check`, or a term
from `cases`' closers. The new proof form, a definition's one-step equation
(`unfold_equation`, 707–750), is `Refl` ascribed with `Eq`, so the kernel
checks it by conversion. The goal as written that is carried between steps
never reaches the proof or the search (below).

Merge after the three must-fixes. The perf bar is missed, so the Words.sw
conversion is the main open question (M1).

## Focus questions, answered

1. **Soundness.** As above. One cosmetic point: for `<- f` (a reversed
   definition step) the ascription still says `body = f x…` while the
   `J` needs `f x… = body` (732–741). The kernel accepts it because the
   two sides are convertible, so it isn't unsound, but the stated type is
   wrong (S1).
2. **Carrying the goal as written.** `written_goal` is used in only two
   places: the `may_fit` pre-filter (`goal_keys`, 96–129, which takes the
   union of written and computed keys) and the no-progress check
   (262–269). `rewrite_once` gets it as `written`, but uses it only in
   `goal_as_written` for messages, and that runs after the `quiet` return
   (rewrite.rs:1013–1021). The as-written search reads the goal *value*
   (as_written.rs:319). So it can drift without affecting the proof. For
   example, written `g a` computes to something containing `f a`, and
   rule `f a = 0` is found in the computed goal: `written_after` replaces
   only the visible `f a`, and `g a` no longer evaluates to the real goal.
   The effects are limited to extra searches, plus an unlikely case where
   a genuine step is judged no progress. It is also never checked against
   the goal at the start (183), unlike plain `rewrite`, which checks it
   with `goal_as_written` (S5).
3. **Termination and budget.** The main loop terminates. Each success
   resets `idle`, each attempt adds to it, successes are capped at
   `STEP_LIMIT`, and each search has `rewrite`'s evaluation budget.
   Problems:
   - an off-by-one (S4);
   - `expand`'s `for k in 1..` loop, which ends only by an invariant of
     another module (S2);
   - **the cycle naming is wrong** (M2).
4. **Rule elaboration.** `f` as arm equations works (p2, p6), and
   `waits` dropping constructor-pattern arms works. Gaps:
   - with `<-`, folding `<- len` drops every arm and silently does
     nothing (p2 `folded` passes only because the hypothesis closes it by
     conversion), and this isn't documented (S6);
   - a rule whose right side has an unknown its left side doesn't fix is
     accepted and leaves `_` in the goal (M3).
5. **Messages.** No `?N`: unknowns print as `_`. But E-REWRITE-REPEATEDLY
   breaks §3.2/§3.3 in several ways (S3), and the no-op `<- f` gets advice
   to "turn the rule round with `<-`" (S3).
6. **Docs.** Good coverage: syntax.md, guide ch. 10, the proving guide
   row and bullet, and tour page 44 are all present and accurate, with
   three wording points (S6).
7. **Performance.** I agree with the diagnosis, from the code (I can't
   measure in a paper lane).
   - `Shape.computed` deliberately has no `needs` (791–796). The computed
     key of a printer lemma's left side is the printer-state constructor,
     which almost every goal in Words.sw contains. So `may_fit` (145–156)
     doesn't filter printer lemmas out, and every such rule falls through
     to `replace_solving_instances`' comparison by computing.
   - Every failed rule is tried again after *every* successful step
     (`failed_at` is keyed by version, 211), so the cost is about
     (steps × rules) computed searches per proof, and again in each arm.
   - Separately, the computed goal is read back `1 + rules tried` times
     per version: once in `goal_keys` (107–109) and once in each
     `rewrite_once` (rewrite.rs:855).

   Cheap fixes, in order of value (L1):
   - **(a) Two passes per version.** First every rule as written only
     (`as_written::first`, no comparison by computing). Only when no rule
     applies as written, run the full search, rule by rule. The three
     proofs that need the computed goal after `match`/`cases` still get it
     at the point where the as-written pass stalls, and most steps stay
     cheap. Expected: computed searches drop from about steps × rules to
     about stalls × rules [estimated]. This changes the order in which
     rewrites happen, so the converted proofs must be rechecked.
   - **(b)** Read back the computed goal once per version and pass it into
     `rewrite_once` (a new `Option<&Term>` parameter).
   - A per-rule negative cache across versions isn't safe in general (a
     step elsewhere can create an instance), so I don't recommend it.

   (a) is cheaper than as-written-only and keeps the three proofs. I'd do
   (a) and (b) before taking the stage-2 decision on as-written-only.

## Must fix before merge

**M1. Words.sw misses the bar (3.6× against 1.5×) and is in the merge.**
`tools/toyfmt/src/Toy/Doc/Words.sw`. The ticket's bar said "converted on a
branch". Fix: take Words.sw out of this merge (`git checkout main --
tools/toyfmt/src/Toy/Doc/Words.sw` on the lane, and keep the conversion as
a patch or branch for the perf follow-up), or land it only together with
fix L1(a), measured within 1.5×. Merging a 3.6× slowdown into a file the
rolling checks run is Matt's call, not the lane's (D question if wanted).

**M2. The budget error's "cycle" can be false.** In `budget_error`/`cycle`
(492–525), a cycle is detected by *rule indices* repeating, not by goals.
Repro (p4):

```
theorem walk ∀ (g h: Nat -> Nat) (sg: ∀ (n: Nat) => g (n + 1) = h n)
  (sh: ∀ (n: Nat) => h (n + 1) = g n) (z: g 0 = 7): g 600 = 7 :=
  rewrite repeatedly [sg, sh]
```

This prints "they go round in a cycle: `sh`, `sg` undo each other's work".
They don't: the goal goes `g 600 → h 599 → g 598 …`. Fix: in `cycle`,
also require the goal before `trail[n - p]` to be the same as the current
goal (`matching::same` on `quote_folded`, which is cheap at this point).
If it is, keep the "undo each other's work" note. If not, say "`sg`, `sh`
keep applying and the goal keeps changing", and show the goal now (§3.4).
The period-1 note, "keeps applying to its own result", needs the same
check. syntax.md's budget bullet cites this note (S6).

**M3. A rule with an unknown its left side doesn't fix.** `check_rule_inner`
(763–853) accepts it, and the result is misleading. p5:
`h: ∀ (x y: Nat) => f x = y + x` rewrites `f a` to `_ + a`, then the
proof fails with `E-UNSOLVED` "can't work out an implicit argument …
supply it explicitly with `f [x := …]`". That advice is wrong: the unknown
is `h`'s `y`, not an implicit of `f`. In p7, a later rule never fits the
`_`, and the error calls it "never applied", which explains nothing. This
is the lane's D candidate "unsolved args = doesn't apply". I recommend
refusing the rule up front instead, since this is a property of the rule
and not of where it is used:

- after `elaborate_rule` in `check_rule_inner`, collect the rule's unknowns
  (metas created since `equation.rule_metas`) in `equation.rhs` that don't
  occur in `equation.lhs`, leaving out premises' proof metas, which
  `discharge` solves;
- if there are any, return `E-REWRITE-REPEATEDLY-RULE` "this rule's right
  side has `y`, which its left side doesn't fix", with `try: h _ 3`;
- add a reject example.

## Should fix (this lane or a follow-up straight after)

**S1. `<- f` ascribes the reversed equation the wrong way round** (732–741).
Fix: build `stated` after the swap, as `Eq(ty, new_rhs, new_lhs)`.

**S2. `expand` loops forever if every `f.eqK` is `E-NO-EQUATION`** (589–610).
`equations::no_equation` (equations.rs:7597) returns `E-NO-EQUATION` for
*every* `eqK` of a theorem or an instance, so if such a definition ever
reaches here with a `Case` body, `Some(false)` repeats forever.
`definition_named` excludes theorems; it does not exclude instances. I
couldn't build an instance whose body is a top-level match (p10), so this
is latent, but termination shouldn't rest on that. Fix: bound `k` by the
definition's arm count, or stop after the first `E-NO-EQUATION` whose
label says "instance"/"theorem". Simplest of all: `definition_named`
returns `None` for `def.instance()`.

**S3. Messages** (helpful-errors.md §3):
- 431–435: all of `E-REFL`'s notes are copied, including its generic
  "`byComputing` proves `a = b` only when both sides compute to the same
  value" (see the left-open snapshot's Note 2). Copy only the
  first-difference note, or call `first_difference_note` directly.
- 429: "what is left" uses `cx.show(goal)`. Show it as written
  (`written_goal`, when there is one) with "computes to" as goals do
  (§3.3, "as written first").
- The left-open snapshot ends with "Note 6: this statement is false; a
  counterexample". §3.2 item 6 says that outranks the proof-failure
  notes. If the counterexample is appended by shared machinery, file it
  there. Otherwise lead with it and drop Notes 2–5.
- 457–461: "never applied" claims the reason is "its left side is in the
  goal … with its premises proved". That's generic teaching, and wrong when
  the rule was found but skipped for `E-REWRITE-PREMISE`/`-MOTIVE`/`-CONG`
  (282). Keep each rule's last skip reason and say it: "`foo` fits
  `x - y` but its premise `y ≤ x` isn't proved".
- 787: "turn the rule round with `<-`" is given even when the rule is
  already reversed (p8, `<- wrap`). Say "write it without `<-`" when
  `rule.reverse`.
- `budget_error`: add the goal now (with M2).
- The left-open message runs to six notes, over the 600-character target.
  After the above, it should fit.

**S4. Off-by-one at the budget** (276). It errors after 501 rewrites while
saying 500. Use `trail.len() >= STEP_LIMIT`.

**S5. The initial goal as written isn't validated** (183). Use
`goal_as_written(cx, cx.written_goal.take(), expected)` (rewrite.rs:2332)
as plain `rewrite` does, so the pre-filter and no-progress check start
from a term that is known to denote the goal.

**S6. Docs.**
- `docs/guide/10-proofs.md`, the new paragraph: "in whatever order that
  takes" suggests the result doesn't depend on order. It does: rules are
  tried round robin in the listed order, and the rules aren't confluent.
  Say "in turn, in the order listed, until none fits".
- `docs/syntax.md`, the `rewrite repeatedly` section:
  - say that `<- f` with constructor-pattern arms does nothing (those arms
    are dropped), and to state the fold as a lemma;
  - write the `reverseSnoc` example as `(xs ++ [x]).reverse`, as tour
    page 44 does (CLAUDE.md: chain with dots);
  - the budget bullet's "(`there`, `back` undo each other's work)" follows
    M2.
- `docs/proposals/simp-revisited.md`, §8 stage table row 1, still says
  "`… in t`, `… in ?`" and "`E-SIMP-RULE`". Change these to `then t`,
  `then ?` and `E-REWRITE-REPEATEDLY-RULE`.

**S7. A wrong comment** (798–800): "A rule whose sides compute to each
other (a definition's step) can't loop". A step of a recursive definition
without a top-level `match` exposes another call of itself, so it can
loop; the budget catches it. Fix the comment ("is never refused here; the
budget catches a recursive one"), or refuse a one-step rule whose right
side, read back folded, contains a call of the same definition.

## Later (file as tickets)

**L1. Performance:** two passes (as-written, then computed) and one
read-back of the computed goal per version, as in focus 7. Measure on
Words.sw with `STITCHWORT_TIMINGS=decls` and `STITCHWORT_REWRITE_METRICS`.
Do this before D-asking as-written-only for stage 2.

**L2. Stray warnings from rolled-back attempts.** `unconfirmed` pushes
`W-REWRITE-UNCONFIRMED` into `lambda_warnings` (rewrite.rs:1091–1099).
`Snapshot::restore` doesn't roll that back, so an attempt that
`rewrite repeatedly` then discards as no progress (267) can leave a
warning for a rewrite that isn't in the proof. Fix: record
`lambda_warnings.len()` in `restore` and truncate to it, as
`branch_errors` already is.

**L3. A cascade message.** A rule naming a definition that failed to
elaborate gets "`rewrite` needs a proof of an equation … has type
`Nat → Nat`" (p1). `definition_named` sees `body().is_none()` and falls
through to `E-REWRITE-RULE`. It should stay quiet, as other cascades do.

**L4. `may_fit`'s computed shape** almost never filters. Consider keying
it on the left side's first *stuck* call after computing, once the rule's
unknowns are solved for one candidate.

**L5. Single-rule uses in Words.sw** (`rewrite repeatedly [steps]`, where
`rewrite steps` did before) count towards the −15% characters but buy
little. Once L1 has landed, check whether they cost time that a plain
`rewrite` wouldn't.

## Probes (scratch, lane binary)

| # | What | Result |
|---|---|---|
| p2 | `[len]` on `len [x, ..rest]`, `then ?`; `<- len` fold | arms dropped; goal unchanged as written; fold does nothing (closed by a hypothesis by conversion) |
| p3 | hypotheses chaining a→b→c | fine |
| p4 | `sg`/`sh` making progress for 500 steps | budget error claims a cycle (M2); 0.34 s |
| p5 | rule with an unfixed `y` | `_ + a`, then a misleading E-UNSOLVED (M3) |
| p6 | `[List.appendNil, sum, sum]` | fine; a rule called `repeatedly` is a name (E-UNKNOWN-NAME, as documented) |
| p7 | a later rule against a goal `_` | not solved by it; "never applied: `k`" (S3, M3) |
| p8 | `<- wrap` where `n + 0` computes to `n` | E-REWRITE-REPEATEDLY-RULE, advice "turn it round with `<-`" (S3) |
| p9 | `<- twice`, `twice` | check (S1 is cosmetic) |
| p10 | an instance's name as a rule | fine (not a `Case` body) |
