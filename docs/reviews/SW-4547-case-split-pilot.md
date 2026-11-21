# Case-split proofs with today's features: a pilot (SW-4547)

**Status:** Sonnet lane, 21 November 2026. Follows SW-4537's finding that case splits are the largest
gap to Lean and Rocq (about 14% of slice 1's lines, [`SW-4537-results.md`](SW-4537-results.md) §1 and §5).
Before anyone sweeps, this measures what the features that exist today (`cases x then t`,
`cases a, b then t`, merged or-patterns, `byComputing`, `byFacts`, `rewrite repeatedly`) reach on the
SW-4537 case-split theorems and on two files drawn at random. Marks: **[measured]** counted or checked
today; **[estimated]** judgement. It stopped at 1.5 times its estimate: not every theorem got every
attempt (stated below).

## 1. The sample

`gaps.py` files nine theorems under "case split": `exprBlanks`, `headerResult1`, `wordsCalmKeep`,
`closerFitsOf`, `walkAttributesAlike`, `heldItemSeat`, `parenInnerKept`, `refinesAppend`,
`anyHangsOf`. Random files: `random.seed(4547)`, `random.sample` of the 152 files of
`tools/fmt/src/{Fmt,Syntax}` that remain after excluding `ReadBackRuns*`, `ReadBackHung*`, `Tests/`,
`MustAccept*` and files over 3,000 lines (none of the rest is over 3,000), first two drawn:
`Fmt/ElementsChain.sw` (399 lines, 19 theorems, 190 proof lines) and `Fmt/SplitProofs.sw` (483
lines, 33 theorems, 287 proof lines). Proof lines are `SW-4519/count.py`'s method (non-blank,
non-comment lines after the statement's `:=`).

## 2. Results, per theorem **[measured]**

Steps are `check --no-cache --timings=all --only THEOREM NAMESPACE`, the theorem's `steps` column.

| Theorem | Proof lines before → after | Steps before → after | Outcome |
|---|---|---|---|
| `headerResult1` | 35 → 4 | 14,509 → 78,220 (5.4x) | **reverted** (over the D3696 3x bar) |
| `exprBlanks` | 89 → 86 | 2,566,164 → 2,565,848 (1.00x; the group of six) | kept: `Atom \| Unit \| Universe \| Include => deaf.expr input` |
| `codeTextsOf` (SplitProofs) | 39 → 34 | 421,087 → 463,490 (1.10x; the group of four) | kept: `Infix kind … => cases kind then infixTextsOf kind …` |
| `wordUnled` (ElementsChain) | 3 → 1 | 4,510 → 25,612 (5.7x) | **reverted** (over 3x): `cases word, around then byComputing` |
| `wordsCalmKeep` | 51 | | no rewrite found (arms differ) |
| `closerFitsOf` | 9 | | not changed (see class c) |
| `walkAttributesAlike` | 8 | | not changed (one `calc`, no repeated arm) |
| `refinesAppend` | 5 | | not changed (two arms, different bodies) |
| `heldItemSeat` | 6 | | no case split left (a tuple of closers) |
| `parenInnerKept` | 3 | | already `\| _ => each` |
| `anyHangsOf` | 2 | | no case split left |

`headerResult1` as tried: `match header with | { exportKeyword, opaqueKeyword, kind, forallKeyword,
params, decreasingClause, unfoldingClause, result, .. } => cases exportKeyword, …, unfoldingClause
then Bool.andRight grammar`. It checks and is 31 lines shorter, but `cases` takes 5.4 times the
steps of the nested matches, so it is reverted by the rule (the diff is kept in the scratchpad;
`cases header then byComputing` without the record pattern fails with E-CASES-BUDGET, because it
also splits the `Word` fields of `keyword` and `name`).

Per file, proof lines **[measured]**:

| File | Before | After | Change |
|---|---|---|---|
| `Fmt/TraverseFail.sw` | 441 | 438 | −3 (0.7%) |
| `Fmt/SplitProofs.sw` (random) | 287 | 282 | −5 (1.7%) |
| `Fmt/ElementsChain.sw` (random) | 190 | 190 | 0 (the one rewrite, `wordUnled`, was reverted at 5.7x steps) |

File-level steps: not measured. A `--no-cache` check of one of these namespaces rechecks its 41
to 51 dependency namespaces and took 1 to 8 minutes, over the lane's budget; each kept rewrite is
a single theorem and its steps are in the table. Whole-file steps stay within 1.5x trivially if
the three kept theorems do (they are a few percent of their files' steps).

## 3. Why the case splits that stay long stay long

Lines are the proof lines of the sample's theorems after the pilot (the nine named, and the
random files' case-split proofs I read). "At stake" is what a closer in that class could save.

| Class | Theorems | Lines at stake **[estimated from the proofs]** |
|---|---|---|
| (e) arms genuinely differ | `exprBlanks` (86: 40 arms, each a `Fail.toResultAlike1/2/3Then` on that constructor's children, rebuilding the constructor), `wordsCalmKeep` (51), `refinesAppend` (5), `walkAttributesAlike` (8) | about 150 (to about 20 if a lemma over a node's children did the arms) |
| (b) a nested match on a record, one step | `headerResult1` (35, done in 4 but 5.4x steps), `unledLeading` (14) and `ledWord` (9) in ElementsChain (not attempted) | 31 achieved but reverted; about 20 more |
| (d) a big enum in the split | `numeralOneCalm` (10), `leadCalm` (6), `spacingCalm` (18), `baseLinks` (10): the arm is `Atom _ _` over `Tok`'s 64 constructors, or `Infix kind` over several; `cases expr then byComputing` on `numeralOneCalm` ran over three minutes and was stopped | about 30 (one attempt, stopped) |
| (c) a case on an expression, not a name | `closerFitsOf` (`least <= indent`, a `match low: … with` on a comparison) | about 4 |
| (a) the closer needs hypotheses or lemmas | none found in the sample: `cases … then byFacts [..]` was not needed | 0 |
| (f) other: already merged or no split left | `parenInnerKept`, `heldItemSeat`, `anyHangsOf`: SW-4521's sweep and earlier shortening took them; `gaps.py`'s causes are as at the draw (`110e3e3fc`) | 0 |

Two findings on the way:

- `cases a, b then t` on two records (`wordUnled`) works where the goal is stuck on fields of both,
  and splits them as far as the goal needs: the 3-line record match for a token and its place
  becomes one line. `headerResult1` and `wordUnled` show the cost: the same splits take 5.4 and
  5.7 times the steps of hand-written nested matches, which stop as soon as the hypothesis fails.
- An or-pattern can't bind a shared variable across different constructors, but `deaf.expr input`
  (the scrutinee itself) works as the body of `| Atom _ _ | Unit _ _ | … =>`.

## 4. Prediction for a whole-slice sweep

Measured on the two random files: 7 lines of 477 proof lines, **1.5%** (two files, 3 of their 52 theorems changed; no interval). Applied to the 44,064 proof lines of the 152 eligible
files (`count.py`'s method, today): 1.0% × 44,064 = **about 450 lines** **[estimated]**, with a
range from 0% (ElementsChain, 0 lines) to 1.7% (SplitProofs, 750); with the step-cost reverts undone, 1.5%, about 650. The named case-split
theorems alone: 3 lines of 208 (1.4%), plus 31 if the `headerResult1` step cost were accepted.
That is well below SW-4537's 14%, which counted the gap to the *shorter port* (the ports' one-line
`simp_all`), and below SW-4521's 363 lines, the repeated-arm sweep that already took the
`cases x then byComputing` cases.

The extra a fix for the top missing class would add, from the lines at stake: class (e), arms
that differ by constructor, about 150 lines on the named theorems, of which `exprBlanks` and
`wordsCalmKeep` are 137. If one lemma covered "the traversal of a node is its children's, rebuilt" for
all of `Expr`'s constructors, `exprBlanks` and its siblings in `Fmt.TraverseFail` and `Fmt.Walk`
(not counted here) could drop to a few arms each. The random files show no (e) theorem, so the share over the slice is unknown: the named
sample was chosen for being the longest case splits, so 150 is an upper bound on a per-theorem
basis and not a rate. A better-measured class is (d): arms over `Tok` or `InfixKind` that
`cases` can't take in one step; that costs about 30 lines in the two random files (6%), so a
`cases` that splits a data type in as many constructors as the hypothesis rules out (or
stopping when the other constructors are contradictory) would be worth about 6% of such files,
**[estimated, one attempt]**.

## 5. What this does not settle

- Two files is a small sample; the interval on 1.5% is wide.
- Attempts per theorem were one or two: no `byFacts`, no `rewrite repeatedly` closer was needed
  by any case-split proof here.
- File-level steps (D3696's 1.5x bar) were not measured; per theorem, `headerResult1` is the
  only ones over 3x are `headerResult1` and `wordUnled`, both `cases` over several fields of a record (a 5x step cost), which is itself a finding: today's `cases a, b then t` on records trades lines for steps.
