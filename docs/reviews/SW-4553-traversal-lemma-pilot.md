# SW-4553: a lemma for "traversing a node rebuilds it from its children's traversals" (one-file pilot)

Pilot by hand on `tools/fmt/src/Fmt/TraverseFail.sw`, 21 Nov 2026 (Opus). The question
(from SW-4547's class (e)): the long case splits are arms that each rebuild a different
constructor around their own recursive calls. Can a lemma, in today's Stitchwort, state that
shape once so the arms stop restating it?

## The shape and the lemma

Every arm of `exprBlanks` (and `patternBlanks`, and most of `declBlanks`) was

```
| Paren open inner close =>
  Fail.toResultAlike1Then (exprBlanks on deaf inner) (v1 => deaf.expr (Paren open v1 close))
```

that is: the children's induction hypotheses, fed to `alikeN`, and then the step's `Blanks`
fact on *this* constructor rebuilt around the children's results. The only thing that differs
between arms is which children there are and which `…Blanks` theorem covers each; the
constructor itself is already in the goal. The Lean and Rocq ports (SW-4537 BatchC) get this
for free from `simp` with the equation lemmas and the induction hypotheses.

The new lemmas, `rebuilds1`, `rebuilds2` and `rebuilds3` (in `TraverseFail.sw`, 3 proof
lines in all), say it once:

```
theorem rebuilds1 ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} r] [blr: r → r]
    (deaf: ∀ (z: r) => Fail.toResult (() => k (blr z)) = (Fail.toResult (() => k z)).map blr)
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (rebuilt: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)):
    Fail.toResult (() => k (g2 (s1 ()))) = (Fail.toResult (() => k (g (t1 ())))).map blr :=
  Fail.toResultAlike1Then h1 (v1 => rewrite rebuilt v1 then deaf (g v1))
```

A node rebuilt around a child's run (`g`, `g2` inferred from the goal, as `alikeN` already
does), handed to a step `k` that keeps blanking (`deaf.expr`, `deaf.pattern`, `deaf.decl`):
if the child agrees (its induction hypothesis) and rebuilding around a blanked child is
blanking the rebuilt node (`rebuilt`, always `byComputing` here), the node agrees.

Because the constructor no longer appears in the arm's text, arms whose children have the
same `…Blanks` theorems now share one or-pattern arm (D3694):

```
| Paren _ a _ | Spread _ a | RecordField _ _ a | NamedArg _ _ _ a _ | Section a | Prefix _ a | Facts _ _ a =>
  rebuilds1 deaf.expr (exprBlanks on deaf a) (v1 => byComputing)
| CtorFields a b | Infix _ a _ b | Annotation _ a _ b _ =>
  rebuilds2 deaf.expr (exprBlanks on deaf a) (exprBlanks on deaf b) (v1 v2 => byComputing)
```

The or-patterns need the same names in every alternative, so the children are `a`, `b`, `c`
in the order the traversal visits them. Statements unchanged; no top, MustAccept or
acceptance theorem touched; nothing accepts less.

## Measured

Proof lines by `docs/reviews/SW-4519/count.py` (body lines after `:=`, comments and blanks
not counted):

| Theorem | Before | After | Ratio |
|---|---:|---:|---:|
| `exprBlanks` (40 constructors) | 86 | 33 | 0.38 |
| `patternBlanks` (12) | 25 | 13 | 0.52 |
| `declBlanks` (only its 6 simple arms; the 8 `Data` arms untouched) | 92 | 85 | 0.92 |
| `rebuilds1`, `rebuilds2`, `rebuilds3` (new) | | 3 | |
| File | 438 | 369 | 0.84 |

Saving 72 proof lines; the lemmas cost 3 proof lines plus 21 statement lines (and 6 doc
lines). Net of statements: about 48 lines, 11% of the file.

Steps, `check --no-cache --timings=all --only <theorem> Fmt.TraverseFail` before and after
(mutual groups are one row):

| Row | Before | After | Ratio |
|---|---:|---:|---:|
| `exprBlanks` group (26 theorems) | 2,575,609 | 2,530,727 | 0.98 |
| `patternBlanks` group (6) | 494,539 | 482,977 | 0.98 |
| `declBlanks` | 2,666,828 | 2,660,999 | 1.00 |
| `rebuilds1` / `2` / `3` (new, paid once) | | 97,965 / 164,679 / 249,979 | |
| `TraverseFail` rows in the `declBlanks` run | 6,227,848 | 6,678,198 | 1.07 |

No theorem got slower; the file is 1.07x, all of it the three lemmas (D3696 bar: 3x per
theorem, 1.5x per file). Moving the lemmas to std's `Fail/Walk.sw`, next to `alikeN`, would
take their cost out of this file, and they say nothing about the formatter (finding below).

## How far it generalises

The same shape, by family (`grep '^theorem (expr|pattern|decl)'` in `tools/fmt/src`):

| Family | Theorems with constructor arms (proof lines) | Fits? |
|---|---|---|
| `Fmt.Walk` `…Ok` (steps that can't fail) | `exprOk` 99, `patternOk` 30, `declOk` 147 | Yes: arms are `rewrite Fail.toResultSeqNThen (IHs), agree.expr (Ctor …walked children…)`; needs a `Seq` twin of `rebuildsN` (`agree.expr` for `deaf.expr`, `Ok` for `.map`) |
| `Fmt.Walk` `…Twice` (pure walk twice) | `exprTwice` 105, `patternTwice` 29, `declTwice` 132 | Likely: arms are `rewrite keeps.expr (Ctor …), IH, IH`; needs a pure congruence twin, and `rewrite` with an or-pattern's per-alternative names (untested) |
| `Fmt.BlankProofs` `…Walk` | `blankExprWalk` 19, `blankDeclWalk` 12 | No: already a catch-all plus a few arms |
| `Fmt.ReadBackFile` | `exprChecks` 14, `declLowers` 68 | No: each child's hypothesis takes its own part of a `Bool` fact, so arms differ for real |

Prediction from the measured ratios (expr-like 0.38, pattern-like 0.52, decl-like 0.92 while
the `Data` arms stay as they are):

- `…Ok`: 99 × 0.38 + 30 × 0.52 + 147 × 0.92 = 38 + 16 + 135 = 189, from 276: save about 87.
- `…Twice`: 105 × 0.38 + 29 × 0.52 + 132 × 0.92 = 40 + 15 + 121 = 176, from 266: save about 90.
- Less about 24 statement lines a family for its own lemmas: about 63 + 66 = 130 lines net
  across both, on top of this file's 48. Today's lesson applies: these are predictions from
  one measured file, and the `…Twice` one has an untested step (a pure rewrite family).

The `Data` arms are the larger untouched block: 8 arms of about 8 lines in each of
`declBlanks`, `declOk` and `declTwice` (about 190 lines), a product of the `indices` and
`body` cases where each arm repeats the other three children. Proving the `indices` part and
the `body` part as two small lemmas each would make it two arms, not eight; that is a
different shape (the product), not this lemma.

## Readability

After reads better, in my judgement. Before, each of 40 arms restated its constructor twice
(the pattern and `deaf.expr (Paren open v1 close)`), and a reader had to compare arms to see
that they were all the same move. After, the proof says the move once (the lemma, with a doc
that names the induction hypothesis, the rebuilding and the step), and the arms are a table:
which constructors have which children, and which theorem covers each child. Which fact
closes which case is still visible: the hypotheses are named in each arm.

What is lost: the children are `a`, `b`, `c` rather than `inner`, `items`, `condition`,
since an or-pattern's alternatives must bind the same names. The traversal's own arms carry
the domain names one jump away. The `(v1 => byComputing)` tail is noise in every arm; a
default for the `rebuilt` premise (or the checker closing it by computation when left out)
would remove it.

## Findings

- `rebuilds1..3` are about `Fail.toResult` only and belong in std's `Fail/Walk.sw` beside
  `Fail.toResultAlikeNThen` (as `Fail.toResultRebuildsN`, say), with a `Seq` twin for the
  `…Ok` family.
- The `…Ok` and `…Twice` families are the next candidates (about 175 lines predicted, 130 net).
- The `Data` arms in the three `decl…` theorems (about 190 lines) want a lemma per child
  part, not this one.
