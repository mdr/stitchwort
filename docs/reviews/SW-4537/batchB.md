# SW-4537 port batch B: the syntax side (SW-4539)

**Status:** Opus lane, 21 November 2026, from `main` at `c93be57a0` (the slice 1 sources are unchanged
since the draw at `110e3e3fc`). Seven drawn theorems, tree 1 and 2, lexer 2 and 3, settle 1 to 3,
ported to Lean 4 and Rocq under the rules in `../SW-4537-lean-rocq-sample.md` §3. Files:
[`BatchB.lean`](BatchB.lean), [`BatchB.v`](BatchB.v), counts in [`batchB.csv`](batchB.csv).

Both files compile with no errors or warnings **[measured]**: Lean 4.35.0, and Rocq 9.1.1 with Stdlib
9.0.0, from Nix, with the commands in §5 of the note (Rocq from a scratch copy). Neither file has
`sorry`, `admit` or `Admitted`.

## Counts

Lines, statement + proof, from `count_ports.py` **[measured]**:

| Theorem | Stratum | Stitchwort | Lean | Rocq | Lean / SW | Rocq / SW |
|---|---|---|---|---|---|---|
| `argumentMinusDeaf` | tree | 1 + 3 = 4 | 2 + 4 = 6 | 2 + 4 = 6 | 1.50 | 1.50 |
| `walkAttributesAlike` | tree | 3 + 8 = 11 | 3 + 3 = 6 | 3 + 1 = 4 | 0.55 | 0.36 |
| `headerResult1` | lexer | 1 + 36 = 37 | 2 + 2 = 4 | 2 + 4 = 6 | 0.11 | 0.16 |
| `plainOfShapes` | lexer | 3 + 9 = 12 | 3 + 6 = 9 | 3 + 11 = 14 | 0.75 | 1.17 |
| `endsQuietJoin` | settle | 1 + 6 = 7 | 2 + 3 = 5 | 1 + 4 = 5 | 0.71 | 0.71 |
| `settledHomed` | settle | 5 + 45 = 50 | 3 + 25 = 28 | 3 + 31 = 34 | 0.56 | 0.68 |
| `homeStands` | settle | 9 + 258 = 267 | 9 + 95 = 104 | 9 + 82 = 91 | 0.39 | 0.34 |
| **Total** | | **23 + 365 = 388** | **24 + 138 = 162** | **23 + 137 = 160** | **0.42** | **0.41** |

Non-blank characters, statement + proof **[measured]**:

| Theorem | Stitchwort | Lean | Rocq | Lean / SW | Rocq / SW |
|---|---|---|---|---|---|
| `argumentMinusDeaf` | 100 + 78 | 101 + 120 | 90 + 95 | 1.24 | 1.04 |
| `walkAttributesAlike` | 160 + 311 | 159 + 95 | 154 + 60 | 0.54 | 0.45 |
| `headerResult1` | 96 + 719 | 97 + 55 | 95 + 96 | 0.19 | 0.23 |
| `plainOfShapes` | 161 + 383 | 161 + 287 | 158 + 484 | 0.82 | 1.18 |
| `endsQuietJoin` | 85 + 107 | 86 + 86 | 81 + 99 | 0.90 | 0.94 |
| `settledHomed` | 198 + 2,024 | 198 + 1,349 | 197 + 1,432 | 0.70 | 0.73 |
| `homeStands` | 412 + 5,746 | 413 + 4,616 | 411 + 3,902 | 0.82 | 0.70 |
| **Total** | **1,212 + 9,368 = 10,580** | **1,215 + 6,608 = 7,823** | **1,186 + 6,168 = 7,354** | **0.74** | **0.70** |

The ratios in the last columns are of the whole theorem. The stage 2 estimate takes the mean of
per-theorem ratios within each stratum, not these pooled totals.

The statements come out the same length in all three, give or take a wrapped line: only the
proofs differ.

`sample.json` lists `homeStands` twice (main draw 3 and settle's third reserve), so `count_ports.py`
prints its row twice. `batchB.csv` keeps one row, the main draw.

## Support, time, set-asides

Support is the non-blank lines in each theorem's namespace or module outside the counted block:
definitions, axioms and comments **[measured]**.

| Theorem | Lean support | Rocq support | Opaque or axioms (both sides) | Time, both systems **[measured, clock]** |
|---|---|---|---|---|
| `homeStands` | 204 | 191 | `movable`, `stepsBack`, `barBelow` opaque; 10 lemma axioms | about 9 min (Lean 4, Rocq 5) |
| `settledHomed` | 100 | 81 | the passes and most predicates opaque; 16 lemma axioms | about 2.5 min |
| `plainOfShapes` | 51 | 45 | `itemKind` opaque; 3 lemma axioms | about 1 min |
| `headerResult1` | 25 | 26 | `Expr`, `Word`, `Comments`, `Group`, `isName1`, `Expr.grammar1` opaque | about 1 min |
| `argumentMinusDeaf` | 31 | 21 | `argumentPrefix` opaque; 1 lemma axiom | about 1 min |
| `walkAttributesAlike` | 15 | 8 | `Attributes`, `blankAttributes` opaque | about 1 min |
| `endsQuietJoin` | 8 | 10 | `Word`, `arrowText` opaque | under 1 min |

The whole batch took 17 minutes of clock time from the first read to the last compile (19:37 to
19:54), plus a few minutes to rewrap to 100 columns and to write this note. No theorem came near
either set-aside rule (45 minutes, 300 lines of support). **No set-asides, no reserves used.**

Every axiom states a Stitchwort lemma the proof names (rule 6), over opaque functions or over the
real cut-down definitions it holds of (rule 7). The cuts are named in each file's comments. The
main ones:

- `homeStands`: `Tok` cut to `Lower`, `Comma`, `RParen` and `Pipe` (the one kind outside slice 1,
  so `within1` still excludes something). `movable`, `stepsBack` and `barBelow` are opaque because
  they read record-update bars (`recordBar`), which the proof reaches only through
  `movableQuiet1`, `chainSteps`, `landedHere` and `barsQuiet1`. Everything the proof computes with
  is real: `stands`, `tucked`, `held`, `matched`, `owing`, `homeFrom`, `trailingAt`, `chainTo`,
  `lands`, `homedBack`, `Leaf.word`, `headedAs` and `fits`.
- `settledHomed`: the proof is a chain of named lemmas, so `homeFrom`, `commasFrom`, `arrows`,
  `letsFrom`, `Trivia.trimmed`, `alphabet1`, `laidOut`, `plain1`, `plainFrom`, `backOk`,
  `homedLeaf`, `relatedLeaf`, `skipped` and `endsWithComment` are opaque. `Lexed.settled`,
  `tokens`, `homedBehind`, `related`, `walkClean` and `CleanFor` are real, because the proof
  computes their empty cases.

## Mathlib notes

One `mathlib:` note, on `walkAttributesAlike`. Lean core has no `List.Forall₂` (checked: `Unknown
constant`), so `BatchB.lean` defines it, as support. With Batteries or Mathlib the definition goes
and the counted lines don't change. Nothing else wanted Mathlib: this material is lists, Booleans
and case splits, and `simp`, `simp_all` and `split` covered it.

## What made a comparison unfair, either way

In Lean's and Rocq's favour:

- **Layout carries most of `homeStands`' gap.** Stitchwort's formatter puts each argument of a
  long call on its own line, and the proof's six recursive calls take 12 or 13 lines each, about
  75 of its 258 lines. The ports pass the same arguments on two lines. By characters the gap is
  much smaller (Lean 0.82, Rocq 0.70) than by lines (0.39 and 0.34).
- **`headerResult1` is the case-split gap at its plainest.** Stitchwort spells out the nested
  match on seven fields to reach the one arm that isn't `False` (36 lines). Lean says `split at
  grammar <;> simp_all` and Rocq takes the record apart in one `destruct` pattern (2 and 4 proof
  lines). This is the same "dispatcher" pattern SW-4222 found, here on a record.
- **Implicit Boolean bookkeeping.** In `homeStands`, Stitchwort builds each `matched`/`owing`
  fact by hand with `Bool.andIntro`/`andLeft` chains. In Lean these are `simp_all [held, matched,
  …]` (several `simp_all` calls close a whole hypothesis of the recursive call). In Rocq they
  are `rewrite`s of the hypotheses into the unfolded Boolean.

Against Lean and Rocq:

- **`argumentMinusDeaf` (ratio 1.5).** Stitchwort's `rewrite argumentPrefixDeaf [a, ..more]`
  closes the goal by computing on both sides. Lean needs the record projections unfolded for
  `simp` (`Item.kind`, `Item.stripped`, `Leaf.stripped`). Rocq needs `simpl` and the lemma
  instantiated by hand.
- **`plainOfShapes` in Rocq (ratio 1.17).** `simpl` either leaves `sourcePlainFrom` folded or
  unfolds the recursive call too far, so the proof restates the one unfolding step with a
  five-line `change`. A Rocq user might instead write an unfolding lemma (or use `Equations`),
  but that would be support written for this theorem, counted with it under rule 18, so it would
  be no shorter.
- **Wrapping at 100 columns, against the pilot.** Rule 12 says to wrap at 100, and these files
  do. The pilot's files wrap at about 120: five of its counted lines run 108 to 117 columns. At
  100 columns this batch gains about 10 Lean lines and 15 Rocq lines over a 120-column layout
  **[estimated, from the rewrap]**. Characters don't change. Stage 2 should either rewrap the
  pilot or note the difference.

Neutral, but worth knowing:

- The opaque functions make the ports' support small and keep the counted proofs honest, as on
  the Stitchwort side: both sides use the same named lemmas. A Lean or Rocq developer might not
  have split `settledHomed`'s chain into these lemmas at all (the note's §2 caveat).
- The Lean proof of `homeStands` leans on `simp_all` with axioms in scope. It compiles, but it
  is the kind of proof that breaks when a definition changes. The Rocq proof is more explicit
  and about as long.

## A counting script bug, worked around

`count_ports.py` skips any line starting `--` as a Lean comment, in Rocq files too. In Rocq `--`
is a bullet, so a Rocq proof that uses `--` bullets is undercounted (by 4 lines and 214 characters
in `homeStands`, before the fix). `BatchB.v` uses `++` bullets instead, so its counts are right.
The script should take `--` as a comment only in `.lean` files. Batches A and C may have hit the
same bug.
