# Proof automation: rewriting under binders, a `ring` normaliser and a controlled `simp`

**Status:** draft 1, 24 October 2026. Design only: nothing here is built. Ticket SW-374
(D1044; the trigger was the Day 2 review's suggestions C and D: `weightedIds` restating whole
sums, `writeTimesMul`'s seven-step regrouping, and the non-linear residue `omega.md` lists in
"Stage 1 on AoC", item 7 and 8). Four questions for Matt are in [§9](#9-decisions-for-matt).
Related: [omega.md](omega.md) (built; this note copies its design for `ring`),
[calc-rewrite.md](calc-rewrite.md) and [rewrite-hypothesis.md](rewrite-hypothesis.md) (built;
`simp` reuses their search), [folded-calls.md](folded-calls.md) (built as SW-257),
[proof-irrelevance.md](proof-irrelevance.md) (not built), [attributes.md](attributes.md),
[well-founded-recursion.md](well-founded-recursion.md) (its congruence-lemma lookup is reused
here).

**The short answer.**

- **What costs lines today** is not arithmetic so much as *saying the same term twice*. The
  biggest measured bucket in the AoC proofs is rewriting *inside* a function argument, such as
  the body of a `List.sumBy`: `rewrite` can't go there, so the proof calls a congruence lemma
  (`List.sumByCong`, `List.mapCong`, `List.sumRangeCongr`) and writes out both functions in
  full. That is 33 `calc` steps and 146 lines in AoC, 27% of all `calc` lines
  ([§1](#1-the-measurement)). Ring-law regrouping (`Nat.mulAssoc`, `mulComm`, `mulDistribLeft`
  and friends) is smaller in AoC (about 50 lemma mentions, most of them in Day 2) and larger in
  the standard library (370 mentions).
- **Recommendation, in three stages, the kernel unchanged in all of them:**
  1. **`rewrite` under binders**: let `rewrite` (and `rewrite … at`) go inside a lambda by
     using the function's congruence lemma (`List.sumByCong` for `List.sumBy`), the same
     lookup `decreasing` already does (`decreasing.rs:2189`). No new syntax.
  2. **`ring`**, a proof term like `omega` that proves `a = b` over `Nat` (and `Int`) when the
     two sides are equal as polynomials. Built the way `omega` was: a normaliser written in
     Stitchwort, in the library, with its correctness proved once; each `ring` is then one
     application of that theorem plus one `rfl` that the kernel checks by running the
     normaliser. **Nothing new is trusted.** A scratch prototype checks `writeTimesMul`'s
     arithmetic in 4,708 evaluation steps (0.2 ms) **[run]**.
  3. **`simp [rules]`**, a proof term that rewrites the goal with exactly the listed
     equations, left to right, everywhere (under binders too), until none applies, and then
     closes it by computation. It writes ordinary `J`/`Eq.trans` terms, as `rewrite` does.
     `simp [rules] in t` and `simp [rules] at h` mirror `rewrite`. No `@[simp]` attribute in
     the first version ([§9](#9-decisions-for-matt), Q2).
- **What it buys.** On the eight proofs of [§1.4](#14-eight-proofs-before-and-after), 62 lines
  become about 12. Across AoC, the estimate is 7 to 14% of proof lines (150 to 300 of 2,093),
  concentrated in Day 2 and in the congruence-heavy parts of Days 6 and 8. In the standard
  library it is less, about 5% (most of its proofs are case analysis and structural
  recursion, which no rewriting tool shortens). These are estimates from reading proofs,
  **[inferred]**, not measured on converted code; each stage's acceptance test measures them.

Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given (at
  `06084471`), or in a source listed at the end ([S1] and so on), fetched on 24 October 2026;
- **[run]**: run on 24 October 2026 with the release CLI built from `06084471`, or a Python
  script over the sources (scripts in the lane's scratch directory, not committed; their
  method is described where the numbers are used);
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [1. The measurement](#1-the-measurement)
- [2. Words this note uses](#2-words-this-note-uses)
- [3. How Stitchwort proves things today](#3-how-stitchwort-proves-things-today)
- [4. How other systems do it](#4-how-other-systems-do-it)
- [5. Options](#5-options)
- [6. The proposal in detail](#6-the-proposal-in-detail)
- [7. Staged plan and acceptance tests](#7-staged-plan-and-acceptance-tests)
- [8. Risks](#8-risks)
- [9. Decisions for Matt](#9-decisions-for-matt)
- [Sources](#sources)

## 1. The measurement

### 1.1 Method

Two Python scripts read every `theorem` in `aoc/src/Aoc/*/Proofs/` (27 files) and in
`crates/elab/src/std/**` **[run]**:

- A theorem runs from its `theorem` line to the next line in column 0. Its **body lines** are
  the non-blank, non-comment lines after the statement's `:=`, plus every `| …` clause line.
- Each body line gets one class, from the names it mentions: *ring laws* (`Nat.`/`Int.`
  `addComm`, `addAssoc`, `mulComm`, `mulAssoc`, `addZero`, `zeroAdd`, `mulZero`, `mulOne`,
  `oneMul`, `addSucc`, `mulSucc`, `addOne`, `mulDistribLeft`/`Right`, `negAdd`, `powAdd`,
  `toIntMul` and similar), *plumbing* (`Eq.cong`, `Eq.trans`, `Eq.sym`, `J`, and congruence
  lemmas, whose names end in `Cong`/`Congr`), `omega`, `rewrite`, other lemma calls, or
  "other" (`rfl`, lambdas, `let`s, `Void.exfalso`). A `| …` line is classified by what is
  after its `=>`.
- A second script classifies each `calc` step (`_ R e := proof`) by its proof.

This is a heuristic: a line can do two things, and the class says which names it mentions,
not what a reader sees. So §1.3 adds two hand-read samples, one of them random.

### 1.2 Results

**Totals [run]:**

| | AoC proofs | standard library |
|---|---:|---:|
| theorems | 383 | 1,384 |
| body lines | 2,093 | 4,732 |
| of which `| …` clause lines (case analysis) | 516 (25%) | 2,179 (46%) |
| `calc` steps (lines) | 257 (543) | 144 (247) |
| theorems with two or more `Eq.trans` (their lines) | 13 (180) | 188 (1,202) |
| theorems calling a `…Cong`/`…Congr` lemma (their lines) | 40 (356) | 40 (229) |

**Body lines by class [run]** (a clause line counted by what follows its `=>`):

| class | AoC | std |
|---|---:|---:|
| a lemma or hypothesis applied directly | 656 (31%) | 1,658 (35%) |
| other: `rfl`, lambdas, `let`, `Void.exfalso`, `match` heads | 571 (27%) | 1,112 (24%) |
| `rewrite` with lemmas | 212 (10%) | 232 (5%) |
| a lemma inside `Eq.cong`/`Eq.trans`/`…Cong` plumbing | 189 (9%) | 1,003 (21%) |
| clause line with its proof on the next line | 167 (8%) | 461 (10%) |
| `calc` step statement lines | 113 (5%) | 32 (1%) |
| `omega` | 103 (5%) | 5 (0%) |
| plumbing only | 63 (3%) | 101 (2%) |
| ring laws only | 19 (1%) | 128 (3%) |

**Mentions [run]:**

| | AoC | std |
|---|---:|---:|
| `Eq.trans` / `Eq.sym` | 185 | 1,267 |
| ring-law lemmas | 46 | 370 |
| `Eq.cong (x => …)` with a written motive | 53 | 316 |
| congruence lemmas under a binder (`…Cong`, `…Congr`) | 61 | 42 |
| `rewrite` | 302 | 358 |
| `omega` | 227 | 35 |

Ring-law mentions by file **[run]** (a grep for the ring-law names above plus
`sumByMulLeft` and `Nat.addSubCancel`, so slightly wider than the table): AoC Day 2
`Part2.sw` 23, `Repeated.sw` 15, `Templates.sw` 1; Day 1 4; Day 6 2; Day 7 5. In the library: `Int/Int.sw` 67, `List/Sort.sw`
56, `Nat/Arith.sw` 54, `core/Arith.sw` 53, `Mod/Mod.sw` 30, `Omega/Sound.sw` 29.

**`calc` steps by their proof [run]:**

| a step proved by | AoC steps (lines) | std steps (lines) |
|---|---:|---:|
| a lemma or hypothesis, directly | 132 (253) | 67 (110) |
| **a congruence lemma under a binder** | **33 (146)** | 5 (15) |
| `rewrite` | 33 (49) | 20 (30) |
| `Eq.cong (x => …)` around a lemma | 28 (52) | 20 (31) |
| ring laws and another lemma | 13 (19) | 18 (43) |
| ring laws only | 10 (11) | 10 (14) |
| `omega` | 7 (11) | 0 |
| nothing (computation) | 1 (2) | 4 (4) |

What the tables say:

1. **Case analysis is the largest single part** (25% of AoC's body lines are `| …` clauses,
   46% of the library's), and the next largest is a lemma applied directly. No rewriting tool
   shortens either. This bounds what any of the options can do.
2. **Under-binder congruence is the biggest target in AoC**: 33 `calc` steps, 146 lines, 27%
   of all `calc` lines. Each step restates two lambdas in full, because `rewrite` skips
   occurrences that mention a bound variable (`rewrite.rs:732`, `mentions_bound`).
3. **Twenty-eight AoC steps (52 lines) write `Eq.cong (t => …) lemma`**, and many of them
   could be `rewrite lemma` today. That is a style residue from before `rewrite` existed
   (SW-153), not a missing feature. Not all: `rewrite` replaces *every* occurrence, and an
   `Eq.cong` with a motive picks one (in `divisorWeightsTop`, `rewrite <- Nat.addOne j` would
   also change the `Succ j` inside `Succ (Succ j)`) **[inferred]**.
4. **Ring laws are a Day 2 and library matter.** 23 AoC steps (30 lines) are regrouping, most
   in Day 2. The library has 370 ring-law mentions, but many are in the files that *prove*
   the ring laws (`core/Arith.sw`, `Int/Int.sw`), which a `ring` built on those laws can't
   use (it would be circular).
5. **The library's style is `Eq.trans` chains**, 188 theorems and 1,202 lines, written before
   `calc` and `rewrite` existed. About half of those I read are arithmetic.

### 1.3 Two samples, read by hand

**A random sample.** 15 AoC theorems with at least three body lines, drawn with Python's
`random.sample`, seed 374 **[run]**; my judgement of what the recommended stages would remove
**[inferred]**:

| theorem | lines | what would change | lines removed |
|---|---:|---|---:|
| Day 4 `parsedCell` | 15 | `rewrite` lists lose their explicit arguments | 2 |
| Day 2 `part2Correct` | 6 | `sumByCong` under a binder, `toIntSumBy`: one `simp` | 4 |
| Day 8 `countWithout` | 6 | case split inside a rewrite: none | 0 |
| Day 6 `answer1` | 5 | `rewrite` arguments inferred | 2 |
| Day 8 `anyOfMem` | 6 | case analysis: none | 0 |
| Day 9 `keyLinesHas` | 6 | membership: none | 0 |
| Day 2 `idWeight` | 9 | three `Eq.cong` motives, `toIntMul`: `simp` | 5 |
| Day 2 `repeatedZero` | 7 | case split and `omega`: none | 0 |
| Day 9 `largestInList` | 5 | none | 0 |
| Day 8 `countedMoved` | 21 | one `occurrencesCongMem` under a binder | 2 |
| Day 8 `oneCircuitOfCount` | 9 | none | 0 |
| Day 6 `answer2` | 6 | `rewrite` arguments inferred | 2 |
| Day 7 `notMemHeads` | 5 | none | 0 |
| Day 2 `templatesAsGrid` | 22 | two nested `mapCong`s under binders | 12 |
| Day 8 `lastJoinFinds` | 25 | case analysis: none | 0 |
| **total** | **153** | | **29 (19%)** |

Seven of fifteen change; eight don't. Two thirds of what goes is congruence under binders.

**A library sample** (12 theorems, seed 374): `Map.Spec.lookupSkip`, `List.runsFromEdge`,
`Omega.combineHolds`, `List.mergeAppend`, `List.subsequenceTail`, `Omega.stepHolds`,
`Vec.getOrShiftLeftLt`, `List.countFromFilter`, `Omega.dotAllZero`, `Map.getDifference`,
`Mod.zeroAdd`, `Set.containsPresent`: 61 lines, of which about 3 would go (`dotAllZero`'s
`Eq.cong` and `Int.zeroMul`, `Mod.zeroAdd`'s `Eq.trans`) **[inferred]**. Library proofs are
mostly case analysis and structural recursion.

**Estimate** **[inferred]**: AoC, 150 to 300 of 2,093 body lines (7 to 14%), from the
buckets (under-binder steps −90 to −110, `Eq.cong` steps −20, ring −20 to −30, inferred
`rewrite` arguments shortening lines more than removing them) and the random sample's 19% of
multi-line theorems. Library: about 5% of 4,732 by the sample, more in `List/Sort.sw`,
`Nat/Digits.sw` and `Mod/Mod.sw`, where the `Eq.trans` chains are arithmetic.

**Lines are not the whole story.** As `omega.md`'s stage 2 found (lines 3,494 → 3,477, but 79
lemma mentions gone), the larger effect is on what a proof *says*. `weightedIds` writes the
same triple sum four times; after, it writes it zero times. A proof that names only the facts
that matter (`termIds`, the IH) survives edits to the program better than one that restates
every intermediate term, which is the robustness argument for automation that the Lean
community makes too ([§4](#4-how-other-systems-do-it)).

**For comparison** (`comparisons/aoc-day02-general/README.md`, **[checked]**): the Lean 4
prototype of Day 2 part 2 is about 325 proof lines against Stitchwort's port of 700 to 1,000;
it used `omega` 138 times, `simp` 93 times, `grind` twice (for two ring identities) and
`decide` 10 times. `omega` has since landed in Stitchwort; `simp` and ring normalisation are
the rest of that gap.

### 1.4 Eight proofs, before and after

Chosen as the trigger cases and the clearest examples of each kind, **not at random**: §1.3
is the unbiased sample. Line counts are body lines **[run]**; the "after" forms are sketches
in the proposed syntax, not checked **[inferred]**.

**1. `writeTimesMul`** (`aoc/src/Aoc/Day02/Proofs/Repeated.sw:67`), ring. 10 lines → 2.

```
-- before
theorem writeTimesMul (k: Nat) (b: Nat): (n: Nat) -> writeTimes k b n = b * multiplier k n
  | Zero => Eq.sym (Nat.mulZero b)
  | Succ n =>
    calc writeTimes k b n * Nat.pow 10 k + b
      _ = b * multiplier k n * Nat.pow 10 k + b := rewrite writeTimesMul k b n
      _ = b * (multiplier k n * Nat.pow 10 k) + b := rewrite Nat.mulAssoc b (multiplier k n) (Nat.pow 10 k)
      _ = b * (Nat.pow 10 k * multiplier k n) + b := rewrite Nat.mulComm (multiplier k n) (Nat.pow 10 k)
      _ = b + b * (Nat.pow 10 k * multiplier k n) := Nat.addComm (b * (Nat.pow 10 k * multiplier k n)) b
      _ = b * 1 + b * (Nat.pow 10 k * multiplier k n) := rewrite Nat.mulOne b
      _ = b * (1 + Nat.pow 10 k * multiplier k n) := rewrite Nat.mulDistribLeft b 1 (Nat.pow 10 k * multiplier k n)
      _ = b * multiplier k (Succ n) := rewrite multiplierSucc k n

-- after
theorem writeTimesMul (k: Nat) (b: Nat): (n: Nat) -> writeTimes k b n = b * multiplier k n
  | Zero => ring
  | Succ n => rewrite writeTimesMul k b n, multiplierSucc k n in ring
```

After the two rewrites the goal is `b * m * p + b = b * (1 + p * m)` with three atoms
(`b`, `m` = `multiplier k n`, `p` = `Nat.pow 10 k`): a polynomial identity. The proof names the
two facts that matter and nothing else.

**2. `multiplierSucc`** (`Repeated.sw:56`), simp under a binder. 9 lines → 1.

```
-- before
  calc multiplier k (Succ n)
    _ = Nat.pow 10 (k * 0) + List.sumBy (i => Nat.pow 10 (k * i)) (List.rangeFrom n 1)
      := List.sumByCons (i => Nat.pow 10 (k * i)) 0 (List.rangeFrom n 1)
    _ = 1 + List.sumBy (i => Nat.pow 10 (k * i)) (List.rangeFrom n 1) := rewrite Nat.mulZero k
    _ = 1 + List.sumBy (i => Nat.pow 10 (k * Succ i)) (List.range n) := rewrite List.sumByRangeShift (i => Nat.pow 10 (k * i)) n 0
    _ = 1 + List.sumBy (i => Nat.pow 10 k * Nat.pow 10 (k * i)) (List.range n)
      := rewrite List.sumByCong (i => Nat.pow 10 (k * Succ i)) (i => Nat.pow 10 k * Nat.pow 10 (k * i))
        (List.range n) (i => Eq.trans (Eq.cong (t => Nat.pow 10 t) (Nat.mulSucc k i)) (Nat.powAdd 10 k (k * i)))
    _ = 1 + Nat.pow 10 k * multiplier k n := rewrite List.sumByMulLeft (Nat.pow 10 k) (i => Nat.pow 10 (k * i)) (List.range n)

-- after
  simp [multiplier, List.sumByRangeSucc, Nat.mulZero, Nat.mulSucc, Nat.powAdd, List.sumByMulLeft]
```

`Nat.mulSucc` and `Nat.powAdd` apply inside `i => …`, which is the step that needs
`List.sumByCong` today. `multiplier` in the list means "unfold it" (both sides).

**3. `weightedIds`** (`aoc/src/Aoc/Day02/Proofs/Part2.sw:395`), the review's trigger. 15
lines → 1, plus a three-line library lemma.

```
-- before (abridged: each of the three steps restates the whole triple sum)
  calc weighted w r
    _ = List.sumBy (k => List.sumBy (n => List.sumBy (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids) (List.rangeFrom (size - 1) 2)) (List.rangeFrom size 1)
      := List.sumRangeCongr (k => List.sumBy (n => if Nat.leq (k * n) size then … else 0) (List.rangeFrom (size - 1) 2))
        (k => List.sumBy (n => List.sumBy (x => …) r.ids) (List.rangeFrom (size - 1) 2)) size 1
        (k k1 k2 => List.sumRangeCongr (n => if … then … else 0) (n => List.sumBy (x => …) r.ids) (size - 1) 2
          (n n1 n2 => termIds w r k k1 n n1))
    _ = List.sumBy (k => List.sumBy (x => List.sumBy (n => …) (List.rangeFrom (size - 1) 2)) r.ids) (List.rangeFrom size 1)
      := List.sumByCong (k => …) (k => …) (List.rangeFrom size 1) (k => List.sumBySwap (n x => …) r.ids (List.rangeFrom (size - 1) 2))
    _ = List.sumBy (x => idTerms w size x) r.ids
      := List.sumBySwap (k x => List.sumBy (n => …) (List.rangeFrom (size - 1) 2)) r.ids (List.rangeFrom size 1)

-- after
  simp [termIds w r, idTerms] in List.sumByRotate _ _ _ _
```

`termIds` needs `1 <= k` and `2 <= n`. `simp` goes under `k =>` and `n =>` by
`List.sumRangeCongr`, whose premise gives `s <= x` and `x < s + c` for the bound variable, so
those facts are in scope there and discharge the conditions (§6.3). The two swaps become one
library lemma `List.sumByRotate` (a sum over k, n, x is the sum over x, k, n; three lines from
`List.sumBySwap`, proved once). `sumBySwap` itself is not a `simp` rule: applied twice it gives
back what it started with.

**4. `divisorWeightsTop`** (`Part2.sw:65`). 9 lines → 1.

```
-- after
  simp [divisorWeights, List.rangeFromSuccEnd, List.sumByAppend, Int.zeroAdd, Nat.dividesSelf]
```

The first step of today's `calc` exists only to turn `Succ j` into `j + 1` so that
`List.rangeFromAppend` matches; a `List.rangeFromSuccEnd` (`rangeFrom (Succ n) s = append
(rangeFrom n s) [s + n]`, one line from `rangeFromAppend`) is the better rule.

**5. `blockColumns`** (`aoc/src/Aoc/Day06/Proofs/Correct.sw:42`). 2 lines → 1.

```
-- before
  Eq.trans (List.mapMap (column => readNumber column.init) (column lines) cs)
    (List.mapCong _ _ cs (c => Eq.cong readNumber (List.initMap (line => charAt line c) lines)))
-- after
  simp [List.mapMap, List.initMap, column]
```

Day 6 was hand-shortened on 24 October (SW-426, SW-427: `_` for `mapCong`'s functions).
`simp` is the next step: the `mapCong` goes.

**6. `List.gaussSum`** (`crates/elab/src/std/List/Sort.sw:68`). 9 lines → 2.

```
-- before (the Succ case)
    Eq.trans (Eq.cong (t => t + t) (List.sumCons x (List.rangeFrom (Succ d) (Succ x))))
      (Eq.trans (Nat.addSwap x (List.sum (List.rangeFrom (Succ d) (Succ x))) x (List.sum (List.rangeFrom (Succ d) (Succ x))))
        (Eq.trans (Eq.cong (t => (x + x) + t) (List.gaussSum d (Succ x)))
          (Eq.trans (Eq.cong (t => (x + x) + Succ d * Succ (x + t)) (Eq.sym (Nat.addSucc x d)))
            (Eq.trans (Eq.cong (t => (x + x) + t) (Nat.mulSucc (Succ d) (x + (x + Succ d))))
              (Eq.trans (Eq.sym (Nat.addAssoc (x + x) (Succ d) (Succ d * (x + (x + Succ d)))))
                (Eq.cong (t => t + Succ d * (x + (x + Succ d))) (Nat.addAssoc x x (Succ d))))))))
-- after
  | Zero, x => ring
  | Succ d, x => rewrite List.sumCons x (List.rangeFrom (Succ d) (Succ x)) in ring [List.gaussSum d (Succ x)]
```

`ring [h]` with `h: l = r` proves `a = b` by checking `a + r = b + l` as polynomials and
cancelling (§6.2): the induction hypothesis's sum `S + S` appears in the goal only after
regrouping, which is exactly what `ring` does.

**7. `List.pairsStep`** (`Sort.sw:125`). 3 lines → 1: `ring [h]`.

**8. `List.sumByMulLeft`** (`Sort.sw:44`). 5 lines → 2.

```
  | Nil => ring
  | Cons x xs => simp [List.sumByCons, List.sumByMulLeft c f xs] in ring
```

**Total: 62 body lines (5,275 characters) → about 12 lines**, with two small new library
lemmas. **[run]** for the "before" counts, **[inferred]** for the "after".

**Cost of these proofs today [run]** (`STITCHWORT_TIMINGS=decls stitchwort check --no-cache` in
`aoc/`, one run; elaboration ms, kernel ms, evaluation steps): `weightedIds` 5.4, 0.5,
138,310; `writeTimesMul` 1.0, 0.5, 34,626; `List.gaussSum` 1.1, 0.5, 35,218;
`divisorWeightsTop` 1.1, 0.5, 34,398. Small: automation can't make them much faster or much
slower, but a `simp` that searched carelessly could make them slower ([§8](#8-risks)).

## 2. Words this note uses

- **Rewriting.** Replacing a part of the goal by something equal to it, using an equation
  `a = b` (a **rule**). Stitchwort's `rewrite p` does one rule, everywhere it matches.
- **Simplifier (`simp`).** A loop that applies a *set* of rules, each left to right, anywhere
  in the goal, again and again until none applies, then tries to close what's left by
  computation. Lean, Isabelle and Rocq's `autorewrite` are all this shape.
- **Under a binder.** Inside a lambda: in `List.sumBy (i => Nat.pow 10 (k * Succ i)) xs`, the
  `k * Succ i` is under the binder `i`. Rewriting there needs either function
  extensionality ("functions equal at every input are equal"), which Stitchwort has only as
  `Quot.funext` (it doesn't compute through `J`, so proofs built on it get stuck), or a
  **congruence lemma**: `List.sumByCong: ((x: a) -> f1 x = f2 x) -> List.sumBy f1 xs =
  List.sumBy f2 xs`, which needs no axiom.
- **Ring normalisation.** Putting an arithmetic expression with `+`, `*` and numbers into a
  standard form, a sum of products of atoms sorted in a fixed order with like terms collected
  (`2·b·m + b`). Two expressions are equal for every value of their atoms exactly when their
  standard forms are the same. (For `Nat` this is a *commutative semiring*: no subtraction.
  `Int` is a *commutative ring*.)
- **Atom.** A part of an expression the normaliser doesn't look inside: `List.length xs`,
  `Nat.pow 10 k`, `f x`. As in `omega`.
- **Proof by reflection.** Write the decision procedure (here, the normaliser) *as a
  Stitchwort function*, prove once that it is correct, and then prove each instance by
  running it: the kernel evaluates `norm lhs == norm rhs` to `True`. `omega` already works
  this way ([omega.md](omega.md), D545).
- **Proof-producing tactic.** The other way: the compiler (untrusted Rust) does the work and
  writes out a chain of lemma applications (`Nat.mulAssoc …`, `Eq.trans …`) that the kernel
  checks step by step. `rewrite` and `calc` work this way. Lean's `simp` does too.
- **Trusted computing base.** What has to be right for a checked proof to be right. In
  Stitchwort, the kernel (`crates/core`). Neither way above adds to it.

## 3. How Stitchwort proves things today

All **[checked]** at `06084471`.

- **No tactic language.** Proofs are terms. `calc`, `rewrite`, `omega` and `?` are expression
  forms, elaborated against the expected type like any other expression
  (`crates/elab/src/check.rs:1956-1958` dispatches `Expr::Calc`, `Expr::Rewrite`,
  `Expr::Omega`; `check.rs:676-678` for inference, where `omega` without a goal is an error).
  So any new automation is a term too: `simp [rules]`, not `by simp`. This matches what D546
  decided for `omega` ("`by omega` (no: there is no tactic language)").
- **The kernel's equality** is a built-in `Eq(A, a, b)` with `Refl` and `J`
  (`crates/core/src/term.rs:186-189`; `docs/core.md:135-141`): `rfl` checks `a ≡ b` by
  conversion, and `J P d rfl` computes to `d`. Axiom K holds. There is no built-in function
  extensionality; `Std.Quot.funext` is proved from `Quot.sound` (`docs/core.md:425`), and
  `J` on such a proof is stuck.
- **Conversion** (`crates/core/src/value.rs:1998`, `conv`) is normalisation by evaluation with
  a work list. Numbers are native (`docs/core.md:216`: `Nat.add`, `Nat.mul`, `Nat.leq`,
  `Nat.equal`, `Nat.decEq` and others run natively on literals), and `Succ`/literal/`k + x`
  forms compare by value (`value.rs`, `native::compare`). So a reflective normaliser's
  coefficient arithmetic is cheap, unlike Rocq's or Agda's unary naturals (§4).
- **`rewrite`** (`crates/elab/src/rewrite.rs`; design in [calc-rewrite.md](calc-rewrite.md)
  §6) searches the goal in pre-order for subterms with the rule's head (`key`, line 701),
  matches by syntax first and then by conversion within one shared budget, abstracts them
  into a motive, checks the motive and the round trip (`check_motive` line 746, `round_trip`
  line 818), and emits `J motive t (Eq.sym p)`. It **skips any occurrence that mentions a
  variable bound inside the goal** (`mentions_bound`, line 732), because `J` can't rewrite
  under a binder without extensionality; the error then points at `List.mapCongr`-style
  lemmas. `rewrite p, q in t` is one rule after another; `rewrite p at h` rewrites a
  hypothesis ([rewrite-hypothesis.md](rewrite-hypothesis.md)).
- **`calc`** (`crates/elab/src/calc.rs`) joins steps with `Eq.trans`, `J`, `Nat.leTrans`,
  `Nat.lessTrans` (`combine`, line 355); a step with no proof is `rfl` checked against the
  step (`by_computation`, line 237).
- **`omega`** (`crates/elab/src/omega.rs:115`, `check_omega`) reads the goal and facts into
  `Std.Omega` syntax (`NTerm`: variables, literals, `+`, `Succ`, multiplication by a literal;
  `crates/elab/src/std/Omega/Omega.sw:41`), searches for a certificate in Rust, and emits
  `Std.Omega.prove`/`proveEq` (`std/Omega/Sound.sw:348`, `:366`) applied to the syntax, the
  certificate and `rfl`. The kernel runs the checker. That is proof by reflection with an
  untrusted search, and the model for `ring` here.
- **`auto`** (`crates/elab/src/auto.rs:235`, `prove`) fills `[auto h: P]` arguments from a
  hypothesis or by running a `Decidable` instance at compile time (`fromYes d Trivial`, which
  the kernel re-runs). It's a decision search, not rewriting.
- **Congruence lemmas are already looked up by name.** `decreasing`'s generated "respects"
  lemma rewrites inside a call's function argument with that function's `FCong` lemma
  (`List.sumByCong`, `Bool.ifThenElseCong`, `Decidable.elimCong`), found beside the
  function's declaration and validated against its shape (`crates/elab/src/decreasing.rs:2189`,
  `cong_lookup`; `:2309`, `validate_cong`; described in `docs/core.md:174`). "No function
  extensionality is needed." This is exactly the mechanism rewriting under binders needs.
  The library's congruence lemmas are named unevenly today: `List.mapCong`, `sumByCong`,
  `filterMapCong`, `foldLeftCong` (`std/List/Toolkit.sw:834-858`), but `List.sumRangeCongr`
  (`std/List/Sort.sw:316`, which also gives the bound variable's range), `mapCongMem`
  (`Toolkit.sw:1401`, membership), `sumByCongrAll`.
- **Goals are shown folded.** Glued values (SW-257, [folded-calls.md](folded-calls.md)) keep
  calls like `multiplier k n` folded until something takes them apart, and the kernel checks
  unglued (`crates/elab/src/kernel.rs`, `unglued`). So a `simp` that matches on the goal *as
  shown* matches what the user reads.
- **Proof irrelevance is not built** (SW-93, backlog; [proof-irrelevance.md](proof-irrelevance.md)).
  An `auto` proof inside a term (`x % d` carries `d != 0`) is part of the term, which is why
  `rewrite` has `E-REWRITE-MOTIVE`. `simp` inherits that limit.
- **Goal display.** `?` shows the goal computed, with the names in scope (`crates/elab/src/goals.rs`;
  `docs/syntax.md` "Goals, `?`"). `simp … in ?` would show the goal after simplification:
  the cheapest way to make `simp` inspectable (§6.4).
- **Attributes** exist only for JavaScript names: a known attribute on a theorem is
  `E-ATTRIBUTE` (`docs/syntax.md:482`). A `@[simp]` would be the first attribute with a
  meaning inside Stitchwort.

## 4. How other systems do it

The sources were fetched on 24 October 2026 by a research sub-agent, which quoted what each
page says; the numbered sources are at the end. Where it couldn't confirm something from a
page it opened, it's marked **[unverified]**.

### 4.1 Summary

| system | simplifier | ring normalisation | how proofs are checked |
|---|---|---|---|
| Lean 4 | `simp`: a `@[simp]` default set, `simp only [..]`, `simp?`; conditional rules; congruence lemmas (`@[congr]`, also generated) | Mathlib `ring`: proof-producing, step by step; core `grind`'s ring solver: reflection | kernel checks terms; no reflection in `simp` |
| Rocq | `simpl` is *computation*, not rewriting; `autorewrite with base` is rule rewriting | `ring`/`field`: reflection (since Boutin 1997) | kernel checks terms; `ring`'s are small, conversion-heavy |
| Isabelle | `simp`: conditional, contextual, ordered rewriting for comm/assoc rules; simprocs | `algebra` (Gröbner), `arith`, `presburger` | LCF: a theorem can only be made by the kernel's rules; proof terms optional |
| Agda | `--rewriting`: user rules *in the definitional equality* (not `--safe`) | stdlib `Tactic.RingSolver`: reflection | kernel; the ring solver itself is `--safe` |
| Idris 2 | none built in; elaborator reflection (`%runElab`, `Elab`) to write your own | none built in | kernel |
| F* | none; goals go to the Z3 SMT solver; Meta-F* tactics for the rest | Z3 | Z3 is trusted |

### 4.2 Lean 4 `simp`

- **What it is**: "inside-out rewriting of terms based on a database of simplification rules"
  [S1]. An equation `l = r` rewrites `l` to `r`; a lemma that isn't an equation is used to
  rewrite the proposition to `True` [S2]. Only reducible definitions are unfolded unless
  listed [S1].
- **Sets**: `@[simp]` adds a lemma to the default set; priorities decide between rules; `↓`
  rules fire before the parts are simplified (the default is bottom-up); `registerSimpAttr`
  makes named sets [S3].
- **Forms** [S4]: `simp only [..]` ignores the default set; `simp [h]` adds `h` (a definition
  in the list is unfolded); `simp at h` simplifies a hypothesis; `simp?` records the rules
  used and suggests the equivalent `simp only [..]`; `dsimp` uses only rewrites that hold by
  computation.
- **Conditional rules** have their premises proved by a *discharger* (by default `simp`
  itself, to depth 2 by `maxDischargeDepth`; `(disch := tac)` replaces it) [S5][S6].
- **Proofs**: each step returns a new term and an optional proof `e = e'` (`none` means
  "by computation"); applications are rebuilt with `congrArg`/`congrFun`/`congr` and with
  congruence theorems, generated automatically or registered with `@[congr]` [S7][S8]. Lean
  has function extensionality, which `simp` can use to go under a `fun` without a special
  lemma **[unverified]**.
- **Loops**: a step budget (`maxSteps`, default 100,000; "maximum number of steps
  exceeded"); permutative rules like commutativity are applied only when the result is
  smaller in a fixed term order ("perm rejected"); since v4.22 a linter can look for looping
  rule sets, off by default because it is costly [S6][S5][S9].
- **Simprocs**: metaprograms that rewrite what can't be stated as equations (evaluating
  literals, for example) [S2].
- **Advice on robustness**: the Lean reference says to "avoid using simp without only unless
  it closes the goal"; the community page says code is easier to maintain "when every `simp`
  closes a goal completely", and to use `simp?` to get a `simp only` [S10][S11]. Mathlib's
  "flexible" linter flags a precise step that works on the output of a non-`only` `simp`
  [S12]. Reason: when someone adds a `@[simp]` lemma, every `simp` that isn't `only` may stop
  at a different place.

### 4.3 Lean and Mathlib arithmetic

- **Mathlib `ring` is proof-producing, not reflective**: "normalisation is guided by building
  a value in the type `ExSum` at the meta level, together with a proof … that the original
  value is equal to the normalised version"; commutativity is "by sorting the subterms"; it
  allows variable `ℕ` exponents [S13][S14]. It cites Grégoire and Mahboubi's paper [S15]
  (the identification is from course notes, **[unverified]** against the paper itself).
- **Lean core's `grind`** has a commutative ring solver that "uses proof-by-reflection": each
  step is a small theorem about a certificate, checked with `eagerReflBoolTrue` [S16][S17].
  So Lean now ships both ways.
- **`linarith`** finds coefficients with an untrusted simplex search, then checks the
  combination with `ring`; "the certificate checking step is *not* by reflection" [S18].
  **`norm_num`** evaluates numeric expressions with extensions plugged into `simp` [S19].
- **`omega`** (Lean core) builds its proof from a justification tree "once a contradiction is
  found" [S20]. Stitchwort's `omega` instead checks a certificate by reflection (D545).
- **`decide`** runs a `Decidable` instance in the kernel; `native_decide` "adds the entire
  lean compiler to the trusted part" [S21]. Stitchwort's `auto` decisions are the first kind.
- Lean's kernel computes on `Nat` literals with GMP [S22], as Stitchwort's does natively
  (§3).

### 4.4 Rocq

- **`simpl` is computation, not rewriting**: it "reduces a term to something still
  readable" [S23]. Rewriting with a set of lemmas is `autorewrite with base`, built with
  `Hint Rewrite`, which "may loop if you build non-terminating rewriting systems" [S24].
- **`ring` is reflection**, and the manual says why. The first ring tactic rewrote, and made
  proof terms "too big for Coq's type checker … At each step of rewriting, the whole context
  is duplicated in the proof term". The reflective version's terms "are linear in the number
  of ⊕ and ⊗ operations. Type checking those terms requires some time because it makes a large
  use of the conversion rule, but memory requirements are much smaller" [S25]. Reflection
  also folds constants: `34 + 2*x − x + 12` becomes `x + 46`. The same page says procedures
  that *backtrack* (like `auto`) are a poor fit for reflection [S25].
- Grégoire and Mahboubi, "Proving equalities in a commutative ring done right in Coq"
  (TPHOLs 2005): one reflective tactic for rings and semirings [S15]. Coefficients and
  variable indices are binary numbers (`positive`, `N`, `Z`) [S26], because Rocq's kernel
  doesn't accelerate unary `nat`.
- **`lia`** (micromega): an untrusted oracle finds a certificate, which is normalised by
  `ring` and checked [S27]. Stitchwort's `omega` copied this.
- **ssreflect `rewrite`** has occurrence selection (`{2}rule`), multipliers (`!rule`: as
  often as possible), patterns (`[pattern]rule`), and `//`, `/=` switches that tidy up after
  each step [S28]: a compact *explicit* style, a middle way between `rewrite` and `simp`.
- Rocq also has experimental user rewrite rules in the definitional equality, which "will
  lead to … inconsistencies" if ill-typed [S29].

### 4.5 Isabelle

- The Simplifier does "conditional and unconditional rewriting and uses contextual
  information"; premises are proved recursively before a rule fires; modifiers are
  `simp add: / del: / only: / cong: / split:` [S30].
- **Ordered rewriting**: a permutative rule (comm) is applied only if it makes the term
  smaller in a fixed order; with associativity, commutativity and left-commutativity this
  sorts sums, "imitates bubble-sort" [S30]. That is how a simplifier can do AC
  normalisation, at the cost of the reader not being able to predict the order.
- **Trust** is LCF style: a theorem is an abstract type that only the kernel's rules can
  build; storing full proof terms is optional [S31]. Reflection still pays: a reflective
  Presburger procedure was reported 10 to 100 times faster than a proof-producing one [S32].

### 4.6 Agda

- `--rewriting` with `{-# REWRITE #-}` "extend[s] Agda's evaluation relation with new
  computation rules"; termination of rules is not checked, and it is not allowed under
  `--safe` because it "turns any equation into one that holds definitionally" [S33][S34].
  That is a kernel change, which this note rules out.
- The standard library's ring solver is reflective (`Tactic.RingSolver`, "a solver that uses
  reflection"), works over almost-commutative rings, uses a sparse Horner normal form, and is
  itself `--safe` [S35]; it came from Kidney's solver [S36].

### 4.7 Idris 2 and F*

- **Idris 2**: elaborator reflection (`%language ElabReflection`, `%runElab`, an `Elab` monad
  over its syntax) lets a library write proof search in Idris [S37][S38]. No built-in
  simplifier or ring tactic. Its builtin `Natural` speeds up run time, not compile-time
  evaluation [S39].
- **F\***: proof obligations go to the Z3 SMT solver, so Z3 is trusted ("one needs to also
  trust the combination of F* and Z3") [S40]. The known cost is brittleness: "a small change in
  a query … can cause it to take a different search path, perhaps causing a proof to not be
  found at all" [S41]; there's an option, `--quake`, that repeats queries to test robustness
  [S42]. Meta-F* adds tactics for what Z3 can't do [S43].

### 4.8 Reflection against proof-producing tactics

| | reflection (Rocq `ring`, Agda solver, Stitchwort `omega`) | proof-producing (Lean `simp`, Mathlib `ring`, Stitchwort `rewrite`) |
|---|---|---|
| proof size | small: syntax, one theorem, one `rfl` | grows with the number of steps |
| kernel work | evaluation, by conversion | type-checking each step |
| trust | the normaliser is proved once in the library | each step is a lemma the kernel re-checks |
| what fits | procedures that *compute* | procedures that *search* or backtrack |
| failure | "the normal forms differ": opaque unless the tool explains | the step that failed |
| proof needed | yes, once, in the language | no, but the generator is more code |

Boutin introduced reflection for rings because it is "more efficient than an LCF-like
approach" [S44]; Chlipala's chapter shows the naive proof growing super-linearly and the
reflective one linearly, and notes the classic failure mode: a reflective tactic that fails
shows the user only an opaque mismatch [S45]. That last point is a design requirement for
`ring` here (§6.2): the error must show the two normal forms.

### 4.9 What to take

1. **`ring` by reflection**, as Rocq and Agda do and as Stitchwort's `omega` already does:
   small terms, nothing new trusted, and Stitchwort's native numbers make the evaluation
   cheap (the reason Rocq needs binary numbers doesn't apply).
2. **`simp` as a proof-producing rewriter**, as Lean and Isabelle do: rewriting is a search
   over the term, and reflection fits search badly (Rocq's own advice). Stitchwort's
   `rewrite` already produces `J` terms; `simp` repeats it.
3. **Congruence lemmas for going under binders**, as Lean's `@[congr]` and Isabelle's
   `cong:`. Stitchwort has no function extensionality that computes, so this isn't optional:
   it's the only way, and `decreasing` already does it.
4. **The robustness lesson from Lean**: a `simp` whose rule set can grow behind your back
   makes proofs fragile; `simp only [..]` and `simp?` are the cure. Stitchwort can start with
   only the cure.
5. **Not**: rewrite rules in the definitional equality (Agda `--rewriting`, Rocq's rewrite
   rules) or an SMT solver in the trusted base (F*). Both change what the kernel trusts.

## 5. Options

### (A) A controlled simplifier, `simp [rules]`

A proof term that rewrites the goal with the listed equations, each left to right, anywhere
(under binders through congruence lemmas), until none applies, then closes it by `rfl`. Its
output is the chain of `J`/`Eq.trans` terms `rewrite` would write, plus congruence lemma
applications. **Fit**: the same shape as `rewrite` (`simp [..] in t`, `simp [..] at h`), so
nothing new to learn about where it can go. **Trust**: kernel unchanged; every step is
checked. **Predictability**: good if the rules are listed in the proof (§9 Q2); the rewriting
order is fixed (inside out, left to right). **Performance**: each rule is a `rewrite`-style
search; the risk is many rules times a large goal (§8). **Errors**: when it can't close the
goal, show the goal it reached and the rules it used, as `?` shows a goal.

### (B) `ring` by reflection

A normaliser for commutative semiring expressions (`Nat`) and ring expressions (`Int`), in
the library (`Std.Ring`), proved correct once. `ring` reads both sides of the goal into its
syntax with atoms (as `omega` reads into `Omega.NTerm`), and its proof is `Ring.prove env lhs
rhs rfl`: the kernel evaluates `norm lhs == norm rhs`. **Fit**: a term, like `omega`; also
`(ring: a = b)` as a `rewrite` rule. **Trust**: kernel unchanged; one soundness proof in the
library. **Predictability**: total for its fragment: it either proves the identity or says
the sides differ, and it never depends on a lemma set. **Performance**: the prototype checks
`writeTimesMul`'s goal in 4,708 steps, `gaussSum`'s in 22,806, a degree-3 identity with 20
monomials in 461,305 (11.5 ms), a degree-4 one with 126 monomials in 20 million (574 ms; the
prototype's sort is quadratic) **[run]**. **Errors**: show both normal forms and their
difference.

### (C) Extend `omega`

`omega` already proves linear equations, so `(omega: i + (p + q) = (i + p) + q)` works today;
it treats `x * y` as an atom and knows `x * y = y * x` (stage 2). Extending it with
monomial normalisation (so `(x * y) * z` and `x * (y * z)` are one atom) is cheap once (B)
exists: `omega` would call `ring`'s normaliser on its atoms. `Int` support for `omega` is a
separate, already-planned item (omega.md, "Not built"). **Not** an alternative to (B):
`omega` is linear; `b * m * p + b = b * (1 + p * m)` is not.

### (D) `rewrite` under binders

The smallest change with the largest measured win: when an occurrence mentions a bound
variable, instead of skipping it, rewrite inside the function argument with the function's
congruence lemma, found as `decreasing` finds them. No new syntax: `rewrite Nat.mulSucc` on a
goal containing `List.sumBy (i => Nat.pow 10 (k * Succ i)) xs` just works. It's also the
first half of (A): `simp` needs exactly this.

### (E) Ring normalisation by proof-producing rewriting (Mathlib's way)

The compiler normalises in Rust and writes the chain of `Nat.addAssoc`/`mulComm`/… steps.
No soundness proof to write, but long proof terms (Rocq's manual: "too big for Coq's type
checker"), and more proof-generating code in the elaborator. Stitchwort chose the other way
for `omega` (D545) for the same reasons; nothing here argues differently.

### (F) Isabelle-style ordered rewriting

Put `addComm`, `addAssoc` and `addLeftComm` in a `simp` set and let a term order decide when
to apply them. One mechanism instead of two, but the reader can't predict the order, it's
slow for products, and it can't do distributivity well. (B) is better for arithmetic.

### (G) A tactic language, or elaborator reflection

Idris 2's route: expose the elaborator to Stitchwort code, and write `simp` and `ring` as
library metaprograms. Much more general, a large design, and a second language to learn.
Not justified by this measurement.

### (H) Rejected: kernel rewrite rules (Agda `--rewriting`) or an SMT solver (F*)

Both change what is trusted. Out of scope by the ticket.

### Side by side

| | trusted base | AoC lines (est.) | std lines (est.) | new syntax | cost to build |
|---|---|---:|---:|---|---|
| (D) `rewrite` under binders | unchanged | −90 to −110 | small | none | small: reuse `cong_lookup` |
| (B) `ring` | unchanged (+1 library proof) | −20 to −40 | −100 or more | `ring`, `ring [h]` | medium: library + reader |
| (A) `simp [rules]` | unchanged | −40 to −150 more | −100 to −200 | `simp [..]`, `in`, `at` | medium-large |
| (C) `omega` monomials | unchanged | a few | a few | none | small, after (B) |
| (E) Mathlib-style `ring` | unchanged | as (B) | as (B) | as (B) | medium, larger terms |

The line estimates are **[inferred]** from §1 and overlap (a step (D) shortens can't also be
counted for (A)).

## 6. The proposal in detail

### 6.1 Stage 1: `rewrite` under binders

- **Where it applies.** During `rewrite`'s pre-order search (`rewrite.rs`), when a candidate
  occurrence mentions a variable bound inside the goal, today it is skipped (`mentions_bound`).
  Instead: find the innermost enclosing application `F … (x => body) …` whose function
  argument binds the variable, and look up `F`'s congruence lemma with `decreasing`'s
  `cong_lookup`/`validate_cong` (moved to a shared module). If there is one, rewrite inside
  `body` with the bound variable as a local, recursively, and wrap the result in the
  congruence lemma: `List.sumByCong f1 f2 xs (x => <proof of f1 x = f2 x>)`. If there isn't,
  skip as today, and the "nothing found" message names the missing lemma
  (`List.windowsCong`).
- **Which lemmas.** The `FCong` convention `decreasing` uses: shape checked once per function.
  The library's irregular names get fixed: `sumRangeCongr` and `mapCongMem` are *contextual*
  congruence lemmas (they give a fact about the bound variable, `s <= x`, `List.Mem x xs`);
  they are registered under a second convention, `FCongRange`/`FCongMem`, or with an
  attribute (a build detail; I'd use the name convention, as `decreasing` does, and rename
  `sumByCongrAll` and friends to fit). When a contextual lemma exists, the rewriting inside
  has its facts in scope, which is what conditional rules need (§6.3).
- **Motive and checks.** Unchanged: the motive for the outer `J` is built after the inner
  rewrite, and the round trip is checked as now.
- **Cost.** One lookup per enclosing call; the search inside the body uses the same shared
  budget.
- **Acceptance**: the 33 AoC `calc` steps of §1.2 that use a congruence lemma under a binder
  are rewritten with `rewrite`; at least 25 lose their congruence lemma, and AoC proof lines
  drop by at least 60; no kernel change; `stitchwort test` in `aoc/` passes; AoC check time
  changes by less than +5%.

#### As built (stage 1, 24 October 2026, SW-374)

- **Mechanism.** `rewrite` (`crates/elab/src/rewrite.rs`, `rewrite/under.rs`) first looks for
  *sites*: calls `F … (x => body) …` in the goal with an occurrence of the rule's left side
  inside a function argument that uses its variable. For each, it looks up `FCong` with the
  lookup `decreasing` uses (moved to `crates/elab/src/congruence.rs`, one cache per check),
  walks the lemma's statement to pair each function parameter with its premise
  `(x…) -> f1 x… = f2 x…`, binds the variables named as in the lambda, elaborates the rule
  again there and rewrites the body (recursively: sites inside first, then ordinary
  occurrences that use the new variables). The proof is `FCong args… f1 f2 … (x => proof)`;
  the outer step is an ordinary `J` along that equation, so the motive and round-trip checks
  are unchanged. Then the ordinary pass rewrites what uses no bound variable. No new syntax,
  no kernel change.
- **Unknowns once per function.** Inside each function the rule is elaborated afresh, so `_`
  (and implicit arguments) are solved per function: `rewrite Nat.mulSucc k _` is `k * Succ i`
  in one function and `k * Succ j` in the next. A rule with no unknowns of its own doesn't
  look inside functions (it couldn't name the variable); that gate also keeps the cost of
  ordinary rewrites where it was (it fixed two `E-REWRITE-BUDGET` regressions on Day 9).
- **Partial applications** count as functions: `List.map (column lines) cs` with a rule
  about `column lines _` is rewritten as `x => column lines x`.
- **Which lemmas.** Only the plain `FCong` shape (§6.1's first convention), beside `F`;
  effect rows are skipped as `decreasing` skips them. The search sees calls unfolded, so
  `List.sumBy f xs` is met as `List.foldLeft (acc x => acc + f x) …` and rewritten through
  `List.foldLeftCong` (the goal shown afterwards is unfolded too, as it was before).
  Contextual lemmas (`mapCongMem`, `sumRangeCongr`) are not used and the library lemmas were
  not renamed: both wait for the conditional rules of stage 3, which are what need the facts.
- **Errors.** `E-REWRITE-CONG` when an occurrence is there only inside a function passed to
  `F` and there is no `FCong`: it names the lemma and shows its statement for `F`, e.g.
  `theorem totalCong (f1: Nat -> Nat) (f2: Nat -> Nat) (arg2: List Nat) (ef: (x: Nat) -> f1
  x = f2 x): total f1 arg2 = total f2 arg2`. Compiler-made functions (`Each.%elim`) are never
  named. `E-REWRITE-NOTHING`'s note for occurrences under binders now says to write `_`, or,
  when the rule has unknowns already, that a variable bound by the goal (`(y: Nat) -> …`)
  must be introduced first.
- **Tests.** Unit tests in `rewrite/under.rs`; `examples/accept/rewrite-inside-function.sw`
  (named for what it does: `reject/rewrite-under-binder.sw` already exists, for the goal's
  own binder, and still fails); `examples/reject/rewrite-inside-function-no-lemma.sw`.
- **AoC.** 36 steps on Days 2, 4, 5, 6 and 8 were converted. Non-blank, non-comment lines
  in the 12 changed proof files: 1552 → 1489 (−63); `Cong`/`Congr` mentions in them 64 → 18.
  The acceptance bar (−60) is met; §5's estimate (−90 to −110) is not, because most of the
  remaining mentions are contextual (`sumRangeCongr`, `…CongMem`: Day 2 Parts 1 and 2, Day 8,
  Day 9), which stage 1 doesn't use. Day 7 was being edited by another lane and wasn't
  touched; its candidates are `Proofs/Part1.sw` (about lines 321 and 352) and
  `Proofs/Distinct.sw`.
- **Check time.** `stitchwort check --no-cache` in `aoc/`, median of five, alternating: 4.95 s
  on main, 5.16 s with this stage (+4.2%, inside the +5% bar). The cost is the search for
  sites, which runs only for rules with unknowns of their own.

### 6.2 Stage 2: `ring`

**Surface** (all proof terms, like `omega`):

| form | proves |
|---|---|
| `ring` | `a = b` at `Nat` or `Int`, when `a` and `b` are equal as polynomials in their atoms |
| `ring [h1, h2]` | `a = b` from equations `h1: l1 = r1`, …: checks `a + r1 + r2 = b + l1 + l2` by `ring`, then cancels (`Nat.addCancelLeft`; for `Int`, subtraction) |
| `(ring: a = b)` | the same, as a rule for `rewrite`/`simp` |

- **Fragment.** `+`, `*`, numbers, `Succ`, and `Nat.pow e n` for a literal `n` (stage 2a); at
  `Int`, also `-` and negation (stage 2b). Anything else is an atom, chosen exactly as
  `omega` chooses atoms (same term, or quickly convertible). Truncated `Nat` subtraction is an
  atom: `(a - b) + b = a` needs `b <= a`, which is `omega`'s job. Variable exponents
  (`Nat.pow 10 (k + 1)`) are atoms in the first version; Mathlib allows them [S14], and Day 2
  has some (`Nat.powAdd`), so it's a candidate for later, measured first.
- **The library** (`Std.Ring`): syntax `Ring.Expr` (atoms by index, literals, `+`, `*`,
  `Succ`, powers by a literal), a normal form (a list of monomials, each a coefficient and a
  sorted list of atom indices, sorted, like terms merged, zero coefficients dropped), `norm`,
  `eval`, and `Ring.sound: eval env (norm e) = eval env e`, so `Ring.prove env a b (ok: norm a
  == norm b = True): eval env a = eval env b`. The proof uses the ring laws already in
  `Std.Nat` (`addComm`, `mulDistribLeft`, …), proved once. A faster normal form (sparse
  Horner, as Agda and Rocq use [S35][S25]) is a build detail to decide on measurements; the
  prototype's sorted monomial lists are enough for AoC-sized goals.
- **The elaborator** reads the goal's sides into `Ring.Expr` with an environment of atoms
  (reusing `omega.rs`'s reader where it can), runs `norm` in Rust (or not at all: the kernel
  will), and emits `Ring.prove env a b rfl`. The kernel checks that `eval env a` and `eval
  env b` convert to the goal's sides and that `norm a == norm b` evaluates to `True`.
- **Errors.** When the normal forms differ, `E-RING` shows them, over the atoms by name, and
  their difference:

  ```
  error[E-RING]: the two sides are different polynomials
    left:  b·m·p + b
    right: b·m·p + 2·b
    the left side has 1·b less (writing m = multiplier k n, p = Nat.pow 10 k)
  ```

  This is the opposite of the classic reflective failure ("doesn't unify", [S45]): the
  compiler runs `norm` itself before emitting the proof, so it knows both forms. When an atom
  looks like it should have been arithmetic (`a - b`, `x / 2`), a note says it was treated as
  an unknown.
- **Acceptance**: `Std.Ring` with its soundness theorem and no assumptions (`stitchwort
  axioms` lists none); `ring` and `ring [h]` close the six arithmetic proofs of §1.4
  (`writeTimesMul`, `gaussSum`, `pairsStep`, `sumByMulLeft`'s `Cons` step after its rewrites)
  and `Nat.addSwap`; at least 30 ring-law lemma
  mentions in AoC and 60 in the library outside `core/Arith.sw` and `Int/Int.sw` are gone;
  per-proof check time no worse than the hand proof's, or within 2 ms.

### 6.3 Stage 3: `simp [rules]`

**Surface** (proof terms, like `rewrite`):

| form | meaning |
|---|---|
| `simp [r1, r2]` | rewrite the goal with `r1`, `r2` until none applies, then close it by computation (`rfl`) |
| `simp [r1, r2] in t` | the same, then `t` proves what's left (as `rewrite … in t`) |
| `simp [r1, r2] at h` | the hypothesis `h`, simplified (as `rewrite … at h`) |
| `simp [r1, f]` with `f` a definition | also unfold `f` |
| `simp [<- r]` | use `r` right to left |
| `simp [(ring: a = b)]`, `simp [(omega: …)]` | any proof of an equation is a rule |

- **Rules** are exactly those listed (no default set; §9 Q2). Each is an equation `l = r`
  whose left side has a known head, as for `rewrite` (`E-SIMP-RULE` otherwise). A rule with
  premises (`termIds … (hk: 1 <= k) …` or `Nat.modSmall … (h: a < b)`) is *conditional*: it
  fires only when its premises are found, in this order: a hypothesis in scope (including
  those a contextual congruence lemma provides, §6.1), `auto`'s decision procedures, then
  `omega` with a small budget (as D547 planned for `auto`). A premise not found means the rule
  doesn't fire there; nothing is guessed.
- **Order.** Inside out (arguments before the call, as Lean and Isabelle do by default
  [S3][S30]), left to right, the rules tried in the order listed; repeat until nothing
  changes. Then unfold the listed definitions and compute (the goal is shown computed, as
  `?` shows it).
- **Termination.** A step budget (as `rewrite`'s, larger); exceeding it is `E-SIMP-BUDGET`,
  which shows the goal at that point and the last rules applied, so a loop (`r`, then `<- r`)
  is visible. A rule whose right side is its left side with arguments permuted
  (`Nat.addComm`, `List.sumBySwap`) is refused with a note: "this rule can be applied
  forever; use `ring` for arithmetic, or `rewrite` once". That gives up Isabelle's ordered
  rewriting (§5, F) for predictability.
- **The proof.** Each rewrite is a `J`, as `rewrite` writes it; steps are joined by
  `Eq.trans`; under binders by congruence lemmas (§6.1). Steps that hold by computation get
  no term. For the eight proofs of §1.4 that is tens of `J`s, which is what the hand proofs
  have now.
- **Matching** follows `rewrite`'s rules (key, syntax, then conversion within the budget),
  with one change for speed: rules are indexed by their left side's head, so each subterm is
  compared only with rules that could match it. Lean indexes its simp lemmas in a similar way
  (a discrimination tree) **[unverified]**.
- **Explaining itself (`simp?` in spirit).** Two ways, both cheap:
  1. `simp [..] in ?` shows the goal after simplification with the usual goal display.
  2. The language server offers "expand `simp`": it replaces `simp [rules]` by the explicit
     chain it found, as a `calc` with one `rewrite` per line, or as `rewrite a, b, c in rfl`
     where every step is outside binders. So the owner can keep the short form or commit the
     long one; the proof is the same either way.
  The rules `simp` *didn't* use are a warning ("`Nat.mulZero` was never applied"), so lists
  stay minimal, which is what `simp?` gives Lean users [S4].
- **Acceptance**: the eight proofs of §1.4 (with stage 2's `ring`) at about the lengths shown;
  at least 20 further AoC theorems shortened, AoC proof lines down a further 60 or more; AoC
  check time within +5%; every `simp` in AoC expands, by the code action, to a proof that
  checks.

### 6.4 What stays as it is

- `rewrite`, `calc`, `omega`, `auto` and `?` are unchanged in meaning; stage 1 makes
  `rewrite` succeed where it used to say "nothing found".
- Case analysis (a quarter to a half of all proof lines, §1.2) and lemmas applied directly
  are untouched. A `cases`-like automation would be a different note.
- The kernel, its conversion, and what `stitchwort axioms` reports.

### 6.5 Interactions

- **Glued values.** `simp` and `ring` read the goal folded (SW-257), so `multiplier k n` is an
  atom for `ring` and a match target for `simp` without unfolding it; listing `multiplier` in
  `simp` unfolds it on purpose.
- **Proof irrelevance (not built).** As for `rewrite`: a term containing an `auto` proof
  (`x % d`) can make a motive ill typed. `simp` reports `E-REWRITE-MOTIVE`'s explanation, with
  the rule's name.
- **`auto` and `omega`.** `simp`'s discharger uses them, with a small budget; neither calls
  `simp` (no recursion between them).
- **Caching** (`crates/elab/src/cache`): proofs are cached by content hash as now; a `simp`'s
  result depends only on its rules and the goal, so it caches like any term.

## 7. Staged plan and acceptance tests

Each stage is one lane, merges on its own, and has its own measurement; the next is decided
on that measurement.

| stage | what | acceptance | kernel |
|---|---|---|---|
| 0 | Convert the 28 AoC `Eq.cong (t => …) lemma` steps to `rewrite lemma` (no new feature) | about −20 AoC lines; same check time ±2% | unchanged |
| 1 | `rewrite` under binders through congruence lemmas (§6.1); rename the library's congruence lemmas to one convention | ≥25 of the 33 under-binder steps lose their lemma; AoC lines −60 or more; `examples/accept/rewrite-under-binder.sw` and `reject/` cases for a missing lemma | unchanged |
| 2a | `Std.Ring` (normaliser + soundness proof) and `ring` at `Nat` | `stitchwort axioms Std.Ring.prove` lists nothing; the §6.2 proofs close; ring-law mentions −30 in AoC, −60 in the library (outside the files that prove the laws) | unchanged |
| 2b | `ring [h]`, `Int`, `(ring: …)` as a rule | `gaussSum`, `pairsStep` by `ring [h]`; Day 2's `Int` steps (`weightsOne`, `idWeight`) | unchanged |
| 3 | `simp [rules]`, `in`, `at`, conditional rules, the expand code action | §1.4's eight proofs; ≥20 more AoC theorems; AoC lines −60 more; every `simp` expands to a proof that checks | unchanged |

Stage 0 is a tidy-up any lane can do now. Stages 1 and 2 don't depend on each other and can
run in parallel. Stage 3 needs stage 1.

Each stage reports, as omega's stage 2 did, per day: lines before and after, lemma mentions
before and after, and `STITCHWORT_TIMINGS=1 stitchwort check --no-cache` check time (median of
five).

## 8. Risks

- **The estimates are from reading proofs, not from converting them.** The `omega` stages
  showed how far that can be off: lines barely moved while lemma mentions fell by 59%. The
  acceptance tests measure both, and stage 3 is decided on stages 1 and 2's numbers.
- **`simp` can make checking slower.** Each rule is a search over the goal, and conversion
  checks cost evaluation steps. Mitigations: index rules by head; syntax before conversion
  (as `rewrite`); one budget; refuse permutative rules. The acceptance test caps AoC's check
  time at +5%.
- **`simp` can make proofs fragile.** That is Lean's experience with non-`only` `simp` [S10].
  With explicit lists only, a library change can still break a `simp` whose rule stops
  matching, but no more than it breaks the `rewrite` it replaces, and the error shows where
  it stopped.
- **`ring`'s cost grows fast with degree** (the prototype's degree-4, six-atom identity took
  574 ms). AoC's identities are degree 2 or 3 with three or four atoms; a better normal form
  (sparse Horner) is the fix if one appears. `ring` could also refuse above a size, with a
  message, rather than run long.
- **The soundness proof is real work.** `Std.Omega`'s took a lane (SW-314, about 370 lines).
  `Std.Ring`'s is about a list-based polynomial type: commutativity of the merge and of
  monomial sorting are the hard lemmas, and `List/Sort.sw` already has merge-sort
  permutation facts to build on **[inferred]**.
- **`ring` can't be used below itself.** `Std.Ring`'s proof uses `Std.Nat`'s ring laws and
  some list lemmas, so those files can't use `ring` (it would be circular, and the module
  order forbids it anyway). That is why the stage 2 targets exclude `core/Arith.sw` and
  `Int/Int.sw`, and why `Std.Ring` should depend on as little of `List/Sort.sw` as it can:
  `Nat.addSwap` and `List.gaussSum` live there.
- **Under-binder rewriting and `decreasing`'s lookup must agree.** Moving `cong_lookup` to a
  shared module keeps one validator; a lemma accepted by one is accepted by the other.
- **Readability is a matter of taste.** A one-word `ring` or `simp [..]` says less about *why*
  than a `calc`. Where the why matters, a `calc` with `ring` steps keeps the shape and drops
  the regrouping (`_ = (x + x) + (s + s) := ring`).

## 9. Decisions for Matt

Implementation details (data structures, where code lives, the normal form, the congruence
naming convention, budgets, error wording) are mine to decide and are decided above. These
four are about what proofs look like and in what order the work comes.

**Q1. Order: stage 1 (`rewrite` under binders) and stage 2 (`ring`) first, in parallel, and
`simp` (stage 3) only after their numbers are in?** Recommendation: **yes**. Stage 1 is the
largest measured win in AoC and is half of `simp` anyway; `ring` is independent and is what
the ticket's Day 2 trigger needs. Alternatives: `simp` first (largest eventual effect, largest
build, and it would need stage 1 inside it anyway); `ring` only (smallest; leaves the
under-binder restating, the review's other trigger).

**Q2. `simp`'s rules: listed in each proof only (`simp [a, b, c]`), or also a default set
marked with an attribute (`@[simp] theorem …`, then `simp` alone, plus `simp only [..]`)?**
Recommendation: **listed only, for now**. Every proof says which facts it uses, nothing
changes behind its back when a library lemma is added, and the "unused rule" warning keeps
lists short. This is what Lean's own advice converges on (`simp only`, `simp?`) [S10][S11].
Revisit after stage 3 if the lists turn out long and repetitive (a named set, `simp
[List.mapLaws]`, would be the middle way). Alternative: Lean's model (`@[simp]` default set):
shorter proofs, but a proof's meaning depends on which lemmas are marked anywhere in its
imports.

**Q3. `ring` with hypotheses: `ring [h1, h2]` (each equation added once to the other side,
then cancelled), or keep `ring` closed and write the hypothesis in by `rewrite` or a `calc`
step?** Recommendation: **`ring [h]`**, in stage 2b. It is what closes `gaussSum` and
`pairsStep` in one line, it matches `omega [facts]`'s look, and it is cheap (one more
cancellation lemma). Mathlib's nearest tactic is `linear_combination`, which (as I recall it) also
allows a multiplier on each hypothesis **[unverified]**; I'd leave multipliers out until a
proof needs one.

**Q4. When `simp` has done its work, should the committed proof keep the short `simp [..]`,
or should `simp` be a drafting tool whose result is expanded (by the code action) into
explicit `rewrite`/`calc` steps before commit?** Recommendation: **keep the short form**;
the expanded form is always one code action away for reading, and the kernel checks the same
term either way. Alternative: expand before commit (proofs read step by step with no
automation, at the price of the length this note is trying to remove); or a lint that flags
`simp`s whose expansion is short enough to write out.

## Sources

Fetched on 24 October 2026 by a research sub-agent, which quoted each page.

- [S1] Lean reference, The Simplifier: https://lean-lang.org/doc/reference/latest/The-Simplifier/
- [S2] Lean reference, Rewrite Rules: https://lean-lang.org/doc/reference/latest/The-Simplifier/Rewrite-Rules/
- [S3] Lean reference, Simp sets: https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/
- [S4] Lean reference, Invoking the Simplifier: https://lean-lang.org/doc/reference/latest/The-Simplifier/Invoking-the-Simplifier/
- [S5] Lean source, `Simp/Rewrite.lean`: https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Meta/Tactic/Simp/Rewrite.lean
- [S6] Lean reference, Configuring Simplification: https://lean-lang.org/doc/reference/latest/The-Simplifier/Configuring-Simplification/
- [S7] Lean source, `Simp/Types.lean`: https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Meta/Tactic/Simp/Types.lean
- [S8] Lean source, `SimpCongrTheorems.lean`: https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Meta/Tactic/Simp/SimpCongrTheorems.lean
- [S9] Lean v4.22.0 release notes: https://lean-lang.org/doc/reference/stable/releases/v4.22.0/
- [S10] Lean reference, Terminal vs Non-Terminal Positions: https://lean-lang.org/doc/reference/latest/The-Simplifier/Terminal-vs-Non-Terminal-Positions/
- [S11] Lean community, simp: https://leanprover-community.github.io/extras/simp.html
- [S12] Mathlib flexible linter (third-party mirror of the docs): https://florisvandoorn.com/LeanCourse25/docs/Mathlib/Tactic/Linter/FlexibleLinter.html
- [S13] Mathlib `Ring/Common.lean`: https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Tactic/Ring/Common.lean
- [S14] Mathlib `Ring/Basic.lean`: https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Tactic/Ring/Basic.lean
- [S15] Grégoire and Mahboubi, "Proving equalities in a commutative ring done right in Coq", TPHOLs 2005, LNCS 3603: https://doi.org/10.1007/11541868_7
- [S16] Lean source, `Init/Grind/Ring/CommSolver.lean`: https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Grind/Ring/CommSolver.lean
- [S17] Lean source, `Grind/Arith/CommRing/Proof.lean`: https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Meta/Tactic/Grind/Arith/CommRing/Proof.lean
- [S18] Mathlib `Linarith/Frontend.lean`: https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Tactic/Linarith/Frontend.lean
- [S19] Mathlib `NormNum/Core.lean`: https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Tactic/NormNum/Core.lean
- [S20] Lean source, `Elab/Tactic/Omega/Core.lean`: https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Elab/Tactic/Omega/Core.lean
- [S21] Lean reference, Tactic Reference (`decide`, `cbv`, `grind`): https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
- [S22] Lean reference, Natural Numbers: https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/
- [S23] Rocq 9.2 reference, equality and `simpl`: https://rocq-prover.org/doc/V9.2.0/refman/proofs/writing-proofs/equality.html
- [S24] Rocq 9.2 reference, `autorewrite`: https://rocq-prover.org/doc/V9.2.0/refman/proofs/automatic-tactics/auto.html
- [S25] Rocq 9.2 reference, `ring` and `field`: https://rocq-prover.org/doc/V9.2.0/refman/addendum/ring.html
- [S26] Rocq source, `BinNums.v`: https://raw.githubusercontent.com/rocq-prover/rocq/master/theories/Corelib/Numbers/BinNums.v
- [S27] Rocq 9.2 reference, micromega (`lia`): https://rocq-prover.org/doc/V9.2.0/refman/addendum/micromega.html
- [S28] Rocq 9.2 reference, ssreflect: https://rocq-prover.org/doc/V9.2.0/refman/proof-engine/ssreflect-proof-language.html
- [S29] Rocq 9.2 reference, rewrite rules: https://rocq-prover.org/doc/V9.2.0/refman/addendum/rewrite-rules.html
- [S30] Isabelle/Isar reference manual (§9.3, §12): https://isabelle.in.tum.de/doc/isar-ref.pdf
- [S31] Isabelle implementation manual (§2.3, §2.5): https://isabelle.in.tum.de/doc/implementation.pdf
- [S32] Chaieb and Nipkow, JAR 2008: https://www.proof.cit.tum.de/~nipkow/pubs/jar08.html (which method the shipped `presburger` uses is **[unverified]**)
- [S33] Agda docs, rewriting: https://agda.readthedocs.io/en/latest/language/rewriting.html
- [S34] Agda docs, safe Agda: https://agda.readthedocs.io/en/latest/language/safe-agda.html
- [S35] Agda stdlib `Tactic/RingSolver.agda`: https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Tactic/RingSolver.agda
- [S36] Kidney, agda-ring-solver (archived): https://github.com/oisdk/agda-ring-solver
- [S37] Idris 2 docs, pragmas: https://raw.githubusercontent.com/idris-lang/Idris2/main/docs/source/reference/pragmas.rst
- [S38] Idris 2 `Language/Reflection.idr`: https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Language/Reflection.idr
- [S39] Idris 2 docs, builtins: https://raw.githubusercontent.com/idris-lang/Idris2/main/docs/source/reference/builtins.rst
- [S40] F* book, introduction: https://fstar-lang.org/tutorial/book/intro.html
- [S41] F* book, SMT under the hood: https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html
- [S42] F* source, options (`--quake`): https://raw.githubusercontent.com/FStarLang/FStar/master/src/basic/FStarC.Options.fst
- [S43] Meta-F*, ESOP 2019: https://arxiv.org/abs/1803.06547
- [S44] Boutin, "Using reflection to build efficient and certified decision procedures", TACS 1997, LNCS 1281: https://doi.org/10.1007/BFb0014565
- [S45] Chlipala, CPDT, "Proof by Reflection": http://adam.chlipala.net/cpdt/html/Reflection.html

Stitchwort sources, at `06084471`: as cited inline. Scratch programs (not committed): the
`ring` prototype (about 75 lines: `RExpr`, sorted monomial lists, `norm`,
`polyEq`, four `rfl` theorems and a test that a false identity is refused), and the
measurement scripts (`measure.py`, `calcsteps.py`, `chains.py`, `sample.py`).
