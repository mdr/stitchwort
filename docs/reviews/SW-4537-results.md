# Slice 1 against Lean 4 and Rocq: the results (SW-4537, stage 2)

**Status:** Opus lane SW-4544, 21 November 2026. Combines the pilot and port batches A, B and C
of [`SW-4537-lean-rocq-sample.md`](SW-4537-lean-rocq-sample.md) (the method, strata, sample and
rules) into one estimate. The theorems are as at the draw, `110e3e3fc`: later shortening (SW-4521's
`cases x then byComputing` sweep, for one) is not in these figures. No Stitchwort code was built or
checked; all nine Lean and Rocq files were compiled.

Marks: **[measured]** counted or compiled today; **[estimated]** my judgement.

## In plain words

**Where we stand.** For the same theorems, proved again, Lean needs about **0.82** of slice 1's
lines (90% between 0.71 and 0.92) and Rocq about **0.76** (0.66 to 0.87) **[measured, 30
theorems]**. By characters the figures are almost the same: 0.83 and 0.77. Put the other way,
our proofs run about a fifth longer than Lean's and about a third longer than Rocq's. The statements
are level (Lean 1.09 of ours by lines, 0.97 by characters); the whole gap is in the proofs, where
Lean takes 0.69 of our proof lines and Rocq 0.64.

This is much closer than the batches' own totals suggested (0.35 to 0.62). Those totals pool the
sample's lines, so the five long proofs count twice: once because the draw picks long theorems
more often, and again because they are long. The estimate here weights each draw once, as the
draw intends, and most of slice 1's lines are in ordinary short and medium theorems, where the
ports are only a little ahead or behind.

**Closest and furthest.** Behind both ports by the most: **settle** (Lean 0.55, Rocq 0.58),
**top** (0.58, 0.64), **lexer** (0.56, 0.69) and **readback** (0.66, 0.61). Level or ahead:
**two-run** (Lean 1.21, Rocq 1.14: our `byWalking` has no counterpart in the ports), **tree**
(1.02, 0.93) and **walk** (Lean 1.19, Rocq 0.69). The **printer**, 38% of the slice, sits at 0.75 and
0.77. With 2 to 4 draws a stratum, read these as "behind, level, ahead", not as numbers.

**Why the gap.** Measured on the ports (the ranked table is in section 5):

1. **Case splits** (about 14% of slice 1's lines): a proof that takes a value apart and closes each
   case the same way. The ports write `cases x <;> simp_all` or one `destruct` pattern; we write
   every arm. `exprBlanks` (95 lines against 10 in each), `headerResult1` (37 against 4 and 6), `wordsCalmKeep`
   (65 against 12 and 10).
2. **Small steps closed by ordinary automation** (about 8%): short proofs where `simp`, `omega`,
   `inversion` or `now` close in one line what we spell in three to six.
3. **Layout** (about 4%): our formatter puts each argument of a long call on its own line.
   It costs the long proofs a lot (`homeStands` about 75 of 258 lines, `blankItemHangs` 54 lines
   holding one argument each), but at the 100 columns the ports wrap at, short statements go the
   other way, and over the slice lines and characters give the same ratio.
4. **Bookkeeping the ports drop** (about 4%): the ports' parser has no `Honest` offsets, so the
   read-back proofs that thread them through std's lemmas are shorter in the ports for a reason
   that isn't the language's. This part of the gap is the comparison's, not ours.
5. **Boolean bookkeeping** (about 1.5%): `Bool.andIntro`/`andLeft` chains that Lean's `simp_all`
   and Rocq's rewrites do implicitly; nearly all of it is in `homeStands`.

Where we are ahead: `byWalking` (two-run's `followsParenAtom`, 1 proof line against 7 and 8) and
computing through record fields (`argumentMinusDeaf`, 3 against 4).

**What the figure means.** It is an upper bound for Lean and Rocq on this material: they re-prove
*our* theorems, one by one, under our decomposition, with cut-down definitions and no Mathlib. A
native Lean or Rocq development would state fewer theorems (SW-4222 counted 23 and 26 for our
30), and its definitions would be shaped for its tactics. So "Lean needs 0.82 of our lines" means
"at least 18% of our lines are ones Lean's automation would not need", not "a Lean formatter
proof would be 82% of ours".

## 1. What was done

- **`count_ports.py` fixed.** It took a line starting `--` as a Lean comment in Rocq files too,
  where `--` is a bullet. Batch B had dodged it with `++` bullets; batch A had not: `unaryHung`'s
  Rocq proof was undercounted by 5 lines (57 to 62) and 258 characters **[measured]**. Batch C and
  the pilot have no `--` bullets. The script now also reports any counted line over 100 columns
  (rule 12) and exits 1 if there is one, and prints a theorem listed twice in `sample.json` once
  per main draw, with a `role` column.
- **Rewrapped to 100 columns** (rule 12): 27 counted lines were over 100 columns, 5 in the
  pilot, 21 in batch A and 1 in batch C. Counts that changed **[measured]**:

  | Theorem | Lean before → after | Rocq before → after |
  |---|---|---|
  | `readsBlockResult` | 3 + 19 (same) | 2 + 10 → 3 + 10 |
  | `followsParenAtom` | 8 + 8 → 9 + 8 | 7 + 6 → 9 + 7 |
  | `runsBlockOneLine` | 8 + 4 → 9 + 4 | 7 + 6 → 9 + 7 |
  | `unaryHung` | 11 + 66 → 11 + 72 | 5 + 57 → 6 + 64 (57 → 62 the bullet fix) |
  | `closerFitsOf` | 7 + 3 → 8 + 3 | 7 + 4 → 8 + 4 |

  All nine files compile **[measured]**: Lean 4.35.0, Rocq 9.1.1 with Stdlib 9.0.0, no errors,
  no `sorry`, `admit` or `Admitted` in a counted theorem.
- **`homeStands` counted once.** It appears twice in `sample.json`: as settle's main draw 3 and as
  settle's third reserve. The second is a reserve, never used, so it is one draw, counted once.
- **The reserve `appFromSpells` ported** (`Reserve.lean`, `Reserve.v`), for the variant that sets
  `exprBlanks` aside: 7 + 75 lines in Stitchwort, 8 + 21 in Lean, 7 + 15 in Rocq **[measured]**.
  Support about 78 lines in Lean and 66 in Rocq; about 5 minutes for both.
- **`estimate.py` rewritten** to give statement, proof and both, by lines and characters, per
  stratum with bootstrap intervals and the range seen. For a part of a theorem it uses the ratio
  estimator that the length-weighted draw calls for, mean(port / x) over mean(Stitchwort / x)
  with x the theorem's Stitchwort lines, where the old script took the plain mean of ratios; for
  the whole theorem by lines the two agree. `gaps.py` files each theorem's gap by cause
  (section 5).

The batches' own `pilot.csv` and `batch*.csv` are their counts before the fix and the rewrap;
these supersede them. Files: [`results.csv`](SW-4537/results.csv) (the 30 main draws),
[`results-reserve.csv`](SW-4537/results-reserve.csv) (plus `appFromSpells`). To redo:

```
git archive 110e3e3fc tools/fmt/src | tar -x -C /tmp/draw
cd docs/reviews/SW-4537
python3 count_ports.py /tmp/draw/tools/fmt/src sample.json Pilot.lean Pilot.v BatchA.lean BatchA.v \
  BatchB.lean BatchB.v BatchC.lean BatchC.v > results.csv
python3 estimate.py results.csv
python3 estimate.py results.csv --impute exprBlanks
python3 estimate.py results-reserve.csv --drop exprBlanks
python3 gaps.py results-reserve.csv
```

## 2. The whole slice

Ratio to Stitchwort, 90% bootstrap interval **[measured, 30 theorems, seed 4537]**:

| Measure | Lean | Rocq |
|---|---|---|
| Lines, whole theorem | **0.82** (0.71 to 0.92) | **0.76** (0.66 to 0.87) |
| Lines, statement | 1.09 (1.00 to 1.19) | 1.03 (0.95 to 1.11) |
| Lines, proof | 0.69 (0.55 to 1.22) | 0.64 (0.51 to 1.11) |
| Characters, whole theorem | **0.83** (0.74 to 0.90) | **0.77** (0.69 to 0.84) |
| Characters, statement | 0.97 (0.96 to 0.98) | 0.91 (0.89 to 0.93) |
| Characters, proof | 0.70 (0.59 to 0.83) | 0.64 (0.52 to 0.77) |

The proof-lines interval reaches above 1 because of one theorem: `followsParenAtom`, one proof line
in Stitchwort and 8 in Lean, is one of two-run's two draws, and a resample that draws it twice
puts that stratum's proof ratio at 8. By characters, where its one line is long, it weighs less.

**`exprBlanks` three ways.** Its support is over rule (b)'s 300 lines (316 in Lean, 330 in Rocq),
and the orchestrator kept it. Lines, whole theorem:

| Variant | Printer, Lean | Printer, Rocq | Slice, Lean | Slice, Rocq |
|---|---|---|---|---|
| Kept (the headline) | 0.75 (0.59 to 0.92) | 0.77 (0.61 to 0.92) | **0.82** (0.71 to 0.92) | **0.76** (0.66 to 0.87) |
| Set aside, reserve `appFromSpells` in its place | 0.78 (0.63 to 0.93) | 0.79 (0.64 to 0.92) | 0.83 (0.73 to 0.93) | 0.77 (0.67 to 0.87) |
| Set aside, counted at the printer's worst ratio (1.40, 1.20) | 0.87 (0.72 to 1.03) | 0.87 (0.74 to 0.99) | 0.86 (0.76 to 0.97) | 0.80 (0.70 to 0.90) |

By characters the three are 0.83 / 0.85 / 0.87 for Lean and 0.77 / 0.78 / 0.81 for Rocq. The choice
moves the slice by at most 0.04, inside the interval. The reserve, a long proof the ports shorten
almost as much (82 lines to 29 and 22), agrees with keeping `exprBlanks`; the worst-ratio
imputation is the bound against the ports.

## 3. Per stratum

Lines, whole theorem, `exprBlanks` kept. "Range" is the smallest and largest single-theorem
ratio; with 2 or 3 draws the bootstrap interval is too narrow and the range says more.

| Stratum | Share of slice | n | Lean | 90% | Range | Rocq | 90% | Range |
|---|---|---|---|---|---|---|---|---|
| walk | 9.8% | 2 | 1.19 | 1.00 to 1.38 | 1.00 to 1.38 | 0.69 | 0.57 to 0.81 | 0.57 to 0.81 |
| two-run | 9.5% | 2 | 1.21 | 0.88 to 1.55 | 0.88 to 1.55 | 1.14 | 0.82 to 1.45 | 0.82 to 1.45 |
| readback | 14.3% | 4 | 0.66 | 0.45 to 1.00 | 0.39 to 1.20 | 0.61 | 0.47 to 0.86 | 0.45 to 1.00 |
| tree | 9.8% | 2 | 1.02 | 0.55 to 1.50 | 0.55 to 1.50 | 0.93 | 0.36 to 1.50 | 0.36 to 1.50 |
| lexer | 5.0% | 3 | 0.56 | 0.32 to 0.80 | 0.11 to 0.82 | 0.69 | 0.35 to 1.02 | 0.16 to 1.17 |
| settle | 10.8% | 3 | 0.55 | 0.45 to 0.66 | 0.39 to 0.71 | 0.58 | 0.45 to 0.70 | 0.34 to 0.71 |
| printer | 38.3% | 11 | 0.75 | 0.59 to 0.92 | 0.11 to 1.40 | 0.77 | 0.61 to 0.92 | 0.11 to 1.20 |
| top | 2.4% | 3 | 0.58 | 0.31 to 0.85 | 0.18 to 1.00 | 0.64 | 0.36 to 0.93 | 0.15 to 1.00 |
| **slice** | | 30 | **0.82** | 0.71 to 0.92 | | **0.76** | 0.66 to 0.87 | |

Characters, whole theorem:

| Stratum | Lean | 90% | Rocq | 90% |
|---|---|---|---|---|
| walk | 0.89 | 0.80 to 0.98 | 0.67 | 0.60 to 0.75 |
| two-run | 1.02 | 0.80 to 1.21 | 1.00 | 0.76 to 1.20 |
| readback | 0.78 | 0.68 to 0.87 | 0.76 | 0.63 to 0.86 |
| tree | 0.90 | 0.54 to 1.24 | 0.75 | 0.45 to 1.04 |
| lexer | 0.76 | 0.51 to 0.94 | 0.85 | 0.51 to 1.07 |
| settle | 0.78 | 0.72 to 0.87 | 0.78 | 0.72 to 0.87 |
| printer | 0.77 | 0.62 to 0.89 | 0.72 | 0.57 to 0.84 |
| top | 0.65 | 0.44 to 0.77 | 0.65 | 0.39 to 0.79 |
| **slice** | **0.83** | 0.74 to 0.90 | **0.77** | 0.69 to 0.84 |

Statement and proof per stratum, lines (Lean, Rocq):

| Stratum | Statement | Proof |
|---|---|---|
| walk | 1.00, 1.00 | 1.27, 0.55 |
| two-run | 0.94, 0.90 | 1.92, 1.76 |
| readback | 0.98, 0.90 | 0.48, 0.45 |
| tree | 1.48, 1.48 | 0.86, 0.74 |
| lexer | 0.79, 0.79 | 0.48, 0.65 |
| settle | 1.37, 0.86 | 0.47, 0.55 |
| printer | 1.09, 1.06 | 0.49, 0.54 |
| top | 1.00, 1.12 | 0.39, 0.42 |

Statements longer in the ports (tree, settle, printer) are one-line Stitchwort statements of 101 to
120 columns that wrap to two at the ports' 100. By characters every stratum's statement ratio is
between 0.85 and 1.01.

Layout across the strata: settle's line ratio (0.55) is far below its character ratio (0.78), which
is `homeStands`' one-argument-a-line calls; walk goes the other way (Lean 1.19 by lines, 0.89 by
characters): Lean's `readsBlockResult` takes more, shorter lines. Over the slice the two cancel.

**Set-asides:** none by rule (a); `exprBlanks` is over rule (b) and kept (section 2).
**Mathlib:** one `mathlib:` note in all the ports, `List.Forall₂` in `walkAttributesAlike`
(Lean core lacks it), which touches support only: 0 counted lines. Rule 14's bias is nil on this
sample **[measured]**.

## 4. Fairness, gathered from the batches

Each item with the way it tilts the ratio. "For the ports" means it makes the ports look shorter
than a fair comparison would.

| Item | Batch | Tilts | Size |
|---|---|---|---|
| The ports' parser drops `Honest` and the offset bookkeeping; Stitchwort threads it through std lemmas (`runsBlockOneLine` 23 proof lines against 4) | pilot, A | for the ports | about 4% of slice lines (section 5) |
| Our formatter puts each argument of a long call on its own line; the ports pass them on two lines (`homeStands`, `blankItemHangs`, `unaryHung`) | B, C | for the ports on long proofs | lines 0.39 against 0.82 by characters in `homeStands` |
| The ports wrap at 100 columns, our formatter at 120 (short statements gain a line in the ports) | B, C | against the ports | tree and settle statements 1.37 to 1.48 by lines, 1.0 by characters |
| Over the slice, the two layout effects | all | neutral | line ratio 0.82, character ratio 0.83 (Lean) |
| `byWalking` has no port; a prelude tactic would take `followsParenAtom` to about 2 proof lines and `followsListPatternStep` to about 4 | A | against the ports | two-run's Lean 1.21 would fall to about 0.9 **[estimated]** |
| Functions reached only through named lemmas are opaque; the lemmas are axioms on both sides alike | all | neutral, slightly for the ports | `exprBlanks` rests on 18 such axioms |
| Cut-down types: constructors and fields no proof reaches dropped (`Expr` to 4 constructors in `unaryHung`, slice 1's in the printer) | A, C | neutral, slightly for the ports | catch-alls are the same length either way **[estimated]** |
| Rocq packs several binders a line | A | for Rocq, lines only | `unaryHung`'s statement 6 lines against 11; characters level |
| `simp_all` with axioms in scope (Lean `homeStands`): short but brittle, the kind a reviewer might query | B | for Lean, slightly | not counted |
| `blankPure` as an `abbrev` in Lean; a plain `def` needed a helper lemma | C | for Lean, slightly | 1 to 2 lines |
| Computing through record projections: Lean must unfold `Item.kind` and friends for `simp`, Rocq instantiates by hand | B | against the ports | `argumentMinusDeaf` 1.5 |
| Rocq's `simpl` unfolds too far or not at all (`plainOfShapes` restates a step with a five-line `change`) | B | against Rocq | 1.17 on that theorem |
| Rocq lacks record update; equivalent definitions (`forallb`, `flat_map`, `calm` inlined for the guard checker) | C | neutral | support only |
| Lean's `++` groups left, ours right; brackets keep our terms | C, stage 2 | neutral | support and statements |
| No Mathlib | all | against the ports | measured nil (one note, support only) |
| Forced renames (rule 3) | all | neutral | |
| Three writers, one per batch, confounded with strata | all | unknown | no cross-check was run |

What the figure does not mean:

- **Not a native development.** The ports re-prove our theorems under our decomposition; a Lean
  or Rocq user would state fewer of them and shape definitions for their tactics. The ratios are
  an upper bound on what those systems need.
- **Definitions and libraries aren't counted** on either side, and the ports' definitions are cut
  down. Support ran 3 to 330 lines a theorem, uncounted.
- **No Mathlib, no Batteries**, by rule 14; it would have changed nothing here.
- **Text only**: not check time, error messages, or how long the proofs took to write (the ports
  took one to nine minutes a theorem in both systems).
- **At `110e3e3fc`.** Shortening merged since (SW-4521 and the sweeps after it) is not counted.

## 5. What would close the largest gaps

Each theorem's proof gap is our proof lines less the shorter port's, filed under the cause the
batch notes and the ports show (`gaps.py`); the share of slice 1 is the same length-weighted
estimate as above, of all 71,786 lines. Two theorems are split as measured: `homeStands` about 75
lines of layout and the rest Boolean bookkeeping (batch B); `unaryHung` 19 lines restating a
hypothesis after a `rewrite` and 32 lines holding one argument (counted in its source), the rest
mixed.

| Rank | Cause | What the ports do that we don't | Proof lines on the sample | Est. share of slice 1 |
|---|---|---|---|---|
| 1 | Case splits | `cases x <;> simp_all […]`, one `destruct` pattern for a record, `split at h <;> simp_all` | 197 | 14.1% |
| 2 | Small steps | `simp`/`omega`/`lia`/`inversion`/`now` closing a three-to-six-line step in one | 43 | 7.8% |
| 3 | Layout | two lines for a long call, not one per argument | 187 | 4.2% |
| 4 | `Honest` dropped | (the comparison, not the language: the ports' parser has no offsets) | 25 | 3.9% |
| 5 | Boolean bookkeeping | `simp_all` builds `&&` facts implicitly | 101 | 1.4% |
| 6 | Equation transport | `obtain ⟨…, rfl, …⟩` substitutes everywhere; we restate each hypothesis with `rewrite <- e then` | 19 | 0.4% |
| | Mixed (`unaryHung`'s rest) | | 30 | 0.7% |
| | Monad steps (`byWalking`) and record computing (we're ahead or level) | | −2 | −2.3% |
| | **All** | | **600** | **30%** |

The reserve `appFromSpells` adds one more cause, not in the main sample: **restated terms**, 60 of
its 75 proof lines' gap, where we write out each option of a `Choice` in full for `spellsChoice`
and the ports let unification find them.

What that says for the work, read with SW-4531 (sweeps with features the language already has
cost about a twelfth as much per line as building tools):

1. **Case splits** are the one large lever, and the evidence points at the existing tools first:
   SW-4521 has just swept repeated `byComputing` arms with `cases x then byComputing`, trailing
   wildcards and merged or-patterns (363 lines, after this draw). What the ports have beyond that
   is a closing tactic that takes lemmas and hypotheses (`simp_all [lemmas]`) after the split, and
   splitting a nested match on a record in one step (`headerResult1`, 36 lines against 2). How
   much a sweep with `cases … then` reaches before a stronger closer is needed is not measured
   here.
2. **Small steps** are spread thin (43 lines over 15 theorems): no single feature, and not a target.
3. **Layout** is 4% and only in long proofs; it is the formatter's choice of one argument a line,
   not the proof language. Over the slice it cancels against the ports' 100-column wrap, so it
   would change how long proofs read more than the slice's total.
4. **`Honest`** is ours to keep: a fairer port would carry it, and the gap would shrink.
5. **Boolean bookkeeping and equation transport** are small on this sample (about 2% together),
   each mostly one theorem; not enough evidence for a tool.

Taking every gap, the sample says slice 1 would be about 30% shorter (of all its lines) if each
theorem's proof were as short as the shorter port's, of which about 4 points are the `Honest` cut.
