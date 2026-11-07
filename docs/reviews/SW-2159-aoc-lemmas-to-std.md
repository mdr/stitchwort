# SW-2159: generic lemmas in the AoC solutions that belong in std

Survey, 7 Nov 2026 (Opus, read only). Matt's goal: "if they are reasonably
generic facts that might have wider utility than just Advent of Code ...
move them there and have a really rich standard library with a lot of
proven facts about the functions."

This builds on the std review's S3 (`docs/reviews/code-review-std.md:104`),
gap 5 of `docs/research/aoc-friction-synthesis.md:85`, and SW-2003 (std
lane C), which the lanes below absorb.

## Summary

The AoC tree has 3,018 theorems (2,841 in `aoc/src/Aoc`, 177 in
`games/rogue`). I read every theorem whose statement names no type,
function or constructor of its own day: 272 came through a mechanical
filter. About 130 of them are facts about std types only. They fall into
three groups:

- **About 30 restate something std already has**, often under another
  name (`leBoth` is `Nat.leAntisym`, `boolOfIff` is `Bool.eqOf`,
  `natEqAbove` is `Nat.equalOfLess`, `foldMinLe` is `List.foldMinLeStart`
  at `Nat.min`). The fix is to delete them, not to move them.
- **About 25 are one-word proofs** (`omega`, `cases`, `rfl`) of a
  particular arithmetic or `Bool` shape. They don't earn a std name. The
  use sites should say `omega` or `cases` themselves.
- **About 75 are genuinely missing from std.** These are the lemmas to
  move, grouped below by std module.

Every S3 item is still missing except the head half of `List.consInjective`
(now `List.consInjectiveHead`, `List/Lemmas.sw:1193`).

The biggest single item is not in S3. `runsAsValue` (a `Parse.Runs` with
the value rewritten by an equation) is defined word for word in **8 days**
and used 27 times. It's a one-line `rewrite`, so std either gets
`Parse.runsValueEq` or the days inline it. The next biggest are
`Option.somePairInjective` (2 days, 12 uses), `natEqSelf` (2 days plus
rogue, 12 uses, already `Nat.equalRefl`), and the decimal-split cluster
from 2024 day 11, which nearly every digit puzzle needs.

**Top five recommendations**

1. **Lane D0 (DeepSeek, 45 min, can start now):** delete the ~30
   restatements and the ~25 one-word proofs, pointing each use at std or
   writing the tactic. It has no std edits, so it can't clash with
   anything.
2. **Lane L1 (Sonnet, 60 min):** `List` filterMap, map, distinct and index
   lemmas: `countFilterMap`, `lengthFilterMapLe`, `mapConcat`,
   `distinctOfMap`, a `Distinct` snoc, `withIndexFrom*`, `memTails`. This
   is the core of S3 and SW-2003.
3. **Lane N2 (Sonnet, 60 min):** `Nat` digits and bits: splitting a
   number's decimal digits at `k` (2024 day 11), `testBit` of small
   numbers and of a sum (2024 day 24). These are the most reusable new
   facts here.
4. **Lane P (Sonnet, 45 min):** `Parse` and `Text`: `runsValueEq`,
   `spaceNotDigit`, `digitNotEq`, `stripPrefixCharsDiffer`, and the
   `joinReads`/`stepValues` snoc lemmas. Eight 2020 days get shorter.
5. **Sequence around in-flight work.** Lane O (`Option`/`Map`/`Set`) waits
   for SW-2138, which is editing `Map`/`Set` now. Lane F (folds and
   `iterate`, which is SW-1486) waits for SW-2147, which touches
   `Nat/Iterate`.

Seven lanes in all, about 6.5 hours of lane time. The lane briefs are
under "Migration lanes".

## Method

- I listed every `theorem` under `aoc/src/Aoc` and `games/rogue/src`, took
  each statement (up to `:=` or the first clause), and dropped those
  mentioning a `def`, `type` or constructor declared in the same day
  folder (or in `Aoc.Common`, treated separately). Binder names and names
  std also declares weren't counted as local. 272 statements came through.
  The script is in the scratchpad, not committed.
- I read all 272, and every remaining statement with one or two local
  names, looking for near-generic lemmas.
- For each candidate, I grepped std (`crates/elab/src/std/`, 4,108
  `theorem`/`def` names) for the name and for the shape, and read the
  signature where one looked equivalent. For example, std's
  `List.distinctSnoc` turned out to be about the dedup *function*
  `List.distinct`, not the `List.Distinct` proposition.
- I checked the open tickets named in the brief, every open "Std:" ticket,
  and SW-2001 to SW-2007 (the std review's lanes) against the candidates.
- I didn't build or run anything. Day and use counts are `grep -w` counts
  over `aoc/src` and `games`, so a common name can be over-counted a
  little.

The 1 Nov whole-codebase review (`docs/research/rust-codebase-review.md`)
is about the Rust code. None of its findings are in this survey's scope.

## S3 and the synthesis, item by item

| S3 item | Status today | Where it goes |
| --- | --- | --- |
| `Nat.lcm`, coprime, Euclid, congruences | missing | SW-1493 stays its own lane (new definitions, not a move) |
| Count by a proposition linked to `List.count` | missing; 2020 d19 `numberWithCount` (`Proofs/Proofs.sw:87`) is exactly it | SW-1577 stays; it should take `numberWithCount` as its proof |
| `List.countFilterMap` (two forms) | missing | L1 |
| `takeWhile` step lemmas | missing | L2 (absorbs SW-1468's half) |
| Non-empty collection has a member | missing for `Set` (2020 d20 `Monsters.sw:157`); the `List` one (2024 d19 `Possible.sw:54`) is about a local `hasSome` | O for `Set`; `List` skipped (domain) |
| `Set.min` is least | in SW-2138 | left out (brief) |
| `lengthFilterMapLe`, `mapConcat` | missing | L1 |
| `Result.getOr`, `Result.isErr` | missing | SW-2005 (std lane E): definitions, not lemmas |
| Division monotone, `Nat.mulNeZero` | both missing | N1 (SW-957's division item; `mulNeZero` from 2024 d14) |
| `withIndexFromMap`, `indexFromAbove`, `pairExt`, `somePairInjective` | missing | L1 (`withIndex*`), O (`somePairInjective`, `pairExt`) |
| `testBitSmall`, `testBitAbove` | missing | N2 |
| Fuelled "iterate until stable" | SW-2147 | left out (brief) |
| Heap, union-find | design work | not in scope |

The synthesis's open tickets are covered as follows:

- Lane L2 absorbs SW-1468 (takeWhile) and SW-1588's `last`/`reverse` half.
- Lane F is SW-1486.
- SW-1577, SW-1493 and SW-1467 stay separate.
- SW-1215's `consInjectiveHead` is done; its `Nat.choose` half stays.
- SW-1608 (`distinctFilterMap`) fits lane L1 and is absorbed there.
- SW-1271 (`Text.splitOn` and friends) and SW-1656 (`Each` to text) have
  no AoC copy to move. They stay separate.
- SW-1351 (a proof-indexed `List.get`) is a new definition, not a move. It
  stays separate.

## Candidates by std home

"Days" is the number of day folders (plus `Common`, plus rogue) that
define or use the name, followed by its total uses. Std names follow std's
conventions (`Intro`/`Elim`, `Of`, the operation first).

### A. Already in std: delete the AoC copy (lane D0)

| AoC lemma | File:line | Std equivalent | Days/uses |
| --- | --- | --- | --- |
| `leBoth` | 2024/Day22/Proofs/Part2.sw:17 | `Nat.leAntisym` (Nat/Arith.sw:17) | 1/2 |
| `natEqSelf` | 2025/Day07/Proofs/Part1.sw:33, rogue Proofs/Position.sw:8 | `Nat.equalRefl` (core/Equality.sw:56) | 2/12 |
| `natSound` | rogue Proofs/Position.sw:10 | `Nat.equalSound` | 1 |
| `natEqAbove` | 2025/Day07/Proofs/Part1.sw:37 | `Nat.equalOfLess` (Nat/Arith.sw:604) | 1/3 |
| `boolEqSelf`, `eqTrue`, `equalOf` | 2021/Day08/Proofs/Proofs.sw:158, 2024/Day12/Proofs/Steps.sw:16, Common/Proofs/Grid.sw:31 | `DecEq.refl` (with `rewrite` for the `x = y` forms) | 3/12 |
| `boolOfIff` | 2024/Day06/Proofs/Part2.sw:132 | `Bool.eqOf` (Bool/Bool.sw:63) | 1/2 |
| `blockLengthLeProduct`, `copiesLeProduct` | 2025/Day02/Proofs/Templates.sw:120,123 | `Nat.leMulPos` (Nat/Arith.sw:73) | 1 |
| `maxAtLeast` | 2024/Day24/Proofs/Lemmas.sw:66 | `Nat.leMaxLeft`, `Nat.leMaxRight` | 1/3 |
| `digitCountNonZero`, `digitListNonZero` | 2025/Day02/Proofs/Part2.sw:216,218 | `Nat.digitCountPos`, `Nat.digitsNonEmpty`, `Nat.digitCountLength` | 1/17 |
| `nearSelf`, `absDiffFixed` | 2025/Day04/Proofs/Window.sw:187, 2021/Day05/Proofs/Proofs.sw:145 | `Nat.absDiffSelf` | 2/6 |
| `foldMinLe`, `foldMinLeMember` | 2021/Day07/Proofs/Proofs.sw:76,81 | `List.foldMinLeStart`, `List.foldMinLeMember` (List/Lemmas.sw:1517), once SW-2001 adds `Ord.minNat` | 1/7 |
| `findMapAny` | 2024/Day22/Proofs/Keys.sw:37 | `List.memOfFindMap` (List/Lemmas.sw:1938) | 1/3 |
| `filterMapNotNil` | 2021/Day10/Proofs/Part2.sw:89 | `List.memFilterMapIntro`, then `≠ []` from membership | 1/3 |
| `zipNext` | 2021/Day01/Proofs/Proofs.sw:24 | `List.zipWithNextZip` (List/Lemmas.sw:54); the tail is `xs` here | 1/3 |
| `memSort` | 2020/Day05/Proofs/Proofs.sw:96 | `List.memPerm` with `List.sortPerm` (or a new `List.memSort` in L2) | 1/7 |
| `sizeWithin` | 2024/Day23/Proofs/Part2.sw:46 | `Set.sizeSubset` (Set/Spec.sw:645) | 1 |
| `containsInsertEither` | 2024/Day06/Proofs/Loops.sw:29 | `Set.containsInsertElim` (Set/Spec.sw:383) | 1 |
| `containsFromList` | 2020/Day06/Proofs/Parse.sw:23 | `Set.containsFromListIff` (Set/Spec.sw:291), plus `List.memContains` | 1 |
| `containsInsertAll` | 2024/Day12/Proofs/Regions.sw:20 | `Set.containsFoldInsert` (thin wrapper) | 1 |
| `orFalse`, `andTrueLeft` | 2021/Day04/Proofs/Proofs.sw:20, 2025/Day04/Proofs/Rounds.sw:110 | `Bool.orFalse`, `Bool.andFalseElim` | 2 |
| `memAppendLeft`, `memAppendRight` | rogue Proofs/Apart.sw:17,22 | `List.memAppendLeft`/`Right` (core/Finite.sw:10) | rogue |
| `positionExt` (copy), `positionEta` | 2024/Day06/Proofs/Sightlines.sw:60, Part2.sw:91 | `Aoc.Common.Proofs.positionExt` (Common/Proofs/Offset.sw:15) | 1 |
| `nextIs` | 2020/Day08/Proofs/Run.sw:25 | `Aoc.Common.Proofs.toNatCheckedSome` today, `Int.toNatCheckedSome` after N1 | 1/2 |
| `memOfEq`, `memEq` | 2024/Day22/Proofs/Keys.sw:28, 2020/Day20/Proofs/Orientations.sw:213 | `rewrite same at member` | 2/7 |
| `getOrSome`, `flatMapSome` | 2024/Day22/Proofs/Part2.sw:12, 2024/Day21/Proofs/Lemmas.sw:47 | `rewrite found in rfl` | 2 |
| 2024 day 12 `total` and its 12 lemmas | 2024/Day12/Proofs/Corners.sw:18-266 | `(List.range 0 n).sumBy f` with `List.sumByRangeSucc`, `sumByAdd`, `sumBySwap`, `sumByCongRange`, `sumByZero`; `totalRange` (Sides.sw:146) already bridges | 1, ~60 lines |

The 2024 day 12 `total` swap is larger than the rest (about 60 lines in
two files, and a `telescope` proof to restate). It goes in its own Sonnet
lane, D1, not DeepSeek's. Everything else in this table is mechanical.

### B. One-word proofs: use the tactic, add nothing (lane D0)

These are shapes `omega`, `cases` or `rfl` close directly, so a std name
would only be something to remember. Delete them, and have each use site
write the tactic.

- **Arithmetic:** `ltSucc`, `ltSelfSucc`, `shift` (2025/Day07/Proofs/Part1.sw:39,107,109); `natEqBelow` (Part1.sw:35); `slideCompare` (2021/Day01:52); `halfAtMost`, `zeroPlus`, `rollBound` (rogue; `rollBound` is `Nat.modLt`); `rangeEnd`, `rangeIn` (Common/Proofs/Range.sw:10,13); `notBelow` (2021/Day10/Proofs/Middle.sw:11); `thisTurn`, `laterTurn` (2021/Day04:62,65); `stepsFixed*`, `stepsDiagonal`, `productZero*` (2021/Day05); `undoAdd` (2024/Day07:26); `pastIff`, `thirdBack` (2024/Day08/Proofs/Part1.sw:54,63).
- **Bool:** `andOr` (2025/Day07:29); `orShift` (2024/Day06/Proofs/Sightlines.sw:43); `secondOf` (2021/Day05:109); `andShape`, `andIsSome` (2020/Day04/Proofs/Rules.sw:13,23); `splitSelf`, `andKeep` (2025/Day04/Proofs/Window.sw:173,182); `shapeOffRoute` (2024/Day06/Proofs/Part2.sw:158).
- **Lists:** `sum3`, `product3` (2020/Day01:109,111); `firstOfTwo`, `secondOfTwo` (2024/Day23/Proofs/Lemmas.sw:7,9).

Check each one as you go. If the tactic needs a hint list longer than the
lemma, keep the lemma local, and note it on SW-2159 as an `omega` gap.

### C. `List`: filterMap, map, distinct, index (lane L1, `List/Lemmas.sw`, `List/Index.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `List.countFilterMap` | `(xs.filterMap f).count p = xs.count (x => (f x).any p)` | 2020/Day11/Proofs/Sight.sw:17 | 2/8 |
| `List.countFilterMapEq` | `(xs.filterMap f).count (== y) = xs.count (x => f x == Some y)` (a corollary of the above) | 2024/Day14/Proofs/Lemmas.sw:19 | (with above) |
| `List.lengthFilterMapLe` | `(xs.filterMap f).length ≤ xs.length` | Common/Proofs/Grid.sw:147 | 1/3 |
| `List.lengthFilterMap` | `(xs.filterMap f).length` as two counts (generalise 2021 d3 `columnLength`, Proofs.sw:25, from `Bits` to `a`) | 2021/Day03 | 1 |
| `List.mapConcat` | `xss.concat.map k = (xss.map (.map k)).concat` | Common/Proofs/GridCells.sw:97 | 1/3 |
| `List.distinctOfMap` | `Distinct (xs.map key) → Distinct xs` | Common/Proofs/Grid.sw:141 | 1/3 |
| `List.distinctSnocIntro` | `y ∉ xs → Distinct xs → Distinct (xs ++ [y])` (std's `distinctSnoc` is about the function `List.distinct`, hence `Intro`) | 2020/Day08/Proofs/Run.sw:36, rogue Proofs/Apart.sw:38 | 2/6 |
| `List.distinctSwapMiddle` | replacing one element of a distinct list by a fresh one keeps it distinct | rogue Proofs/Apart.sw:27 | rogue |
| `List.distinctFilterMap` | SW-1608's statement | (SW-1608) | (2020 d20) |
| `List.withIndexDistinct` | `Distinct xs.withIndex` (the `fallback` argument is unused; drop it) | 2020/Day20/Proofs/Monsters.sw:173 | 1/2 |
| `List.withIndexFromMap` | `withIndexFrom s (map (withIndexFrom s xs) h) = …` | Common/Proofs/GridCells.sw:90 | 1/4 |
| `List.indexFromAbove` | `p ∈ withIndexFrom t xs → t ≤ p.fst` | Common/Proofs/GridCells.sw:149 | 1/4 |
| `List.distinctWithIndexFromPaired` | `Distinct ((withIndexFrom t xs).map (p => (s, p.fst)))` | Common/Proofs/GridCells.sw:157 | 1 |
| `List.memOfMemTails` | `later ∈ xs.tails → x ∈ later → x ∈ xs` | 2024/Day22/Proofs/Keys.sw:31 | 1/3 |
| `List.allZipWithSelf` | `List.All (holds …) (xs.zip (xs.zipWith ys g))` from a pointwise fact | 2024/Day09/Proofs/Part2.sw:43 | 1/3 |
| `List.allLengthMem` | `AllLength n rows → row ∈ rows → row.length = n` | 2020/Day20/Proofs/Orientations.sw:80 | 1/4 |
| `List.allLengthReverseOnto` | `AllLength` survives `reverseOnto` | 2020/Day20/Proofs/Orientations.sw:118 | 1 |

### D. `List`: takeWhile, last and reverse, counts, sums (lane L2, `List/Lemmas.sw`, `List/SortLemmas.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `List.takeWhileConsTrue`, `List.takeWhileConsFalse` | SW-1468's step lemmas | 2020/Day10/Proofs/Part2.sw:33,35 | 1/4 |
| `List.lastCons` | `rest.last = Some l → [x, ..rest].last = Some l` | 2024/Day16/Proofs/Paths.sw:46 | 1/3 |
| `List.lastReverse`, `List.headReverse`, `List.lastReverseOnto` | `xs.reverse.last.getOrElse d = xs.headOr d` and the converse (SW-1588) | 2020/Day20/Proofs/Orientations.sw:12-20 | 1/10 |
| `List.reverseEqNil` | `xs.reverse = [] → xs = []` | Orientations.sw:122 | 1/3 |
| `List.lastDrop`, `List.consHeadDrop` | dropping one from a list of length ≥ 2 keeps `last`; `[xs.headOr d, ..xs.drop 1] = xs` for non-empty `xs` | Orientations.sw:56,97 | 1/4 |
| `List.lengthPos` | `xs ≠ [] → 1 ≤ xs.length` | 2020/Day19/Proofs/Complete.sw:20 | 1/3 |
| `List.containsCons`, `List.containsTakeMono` | `[x, ..r].contains w = (x == w ∨ r.contains w)`; `take` is monotone for `contains` | 2024/Day18/Proofs/Lemmas.sw:6,9 | 1/6 |
| `List.countReplicate` | `(replicate n x).count p = n * (p x).toNat` | 2021/Day06/Proofs/Proofs.sw:18 | 1/3 |
| `List.countSplitOn` | `xs.count (not ∘ q) + xs.count q = xs.length` (generalise 2021 d10 `countSplit`, Middle.sw:60, from `a < _` to any `q`) | 2021/Day10 | 1/3 |
| `List.countPointwiseAdd` | `count p = count q + count r` when `p` splits pointwise | 2021/Day06/Proofs/Proofs.sw:24 | 1/3 |
| `List.countBelowSorted`, `List.countAboveSorted` | in a sorted list, at most `k` are below the `k`th | 2021/Day10/Proofs/Middle.sw:14,26 | 1/6 |
| `List.sortedHeadLeMem` | `Sorted Nat.leq [first, ..rest] → x ∈ … → first ≤ x` (check `List.sortedHeadLe` first; it may only need a `Nat` corollary) | 2020/Day05/Proofs/Proofs.sw:26 | 1/5 |
| `List.getMapRange`, `List.getMapRangePast` | `(range 0 n).map f` at `i` is `Some (f i)` when `i < n`, `None` otherwise | 2021/Day13/Proofs/Picture.sw:11,18 | 1/8 |
| `List.sumByConst` | `xs.sumBy (x => c) = c * xs.length` (generalises `sumByThree`, Common/Proofs/Grid.sw:245) | Common | 1/3 |
| `List.sumByLeMem` | `sumByLe` with the bound only on members (SW-957) | 2021/Day07/Proofs/Proofs.sw:96 | 1/3 |
| `List.existsOfSumByPos` | `0 < xs.sumBy f → ∃ x ∈ xs, 0 < f x` | 2021/Day14/Proofs/Spread.sw:13 | 1/3 |
| `List.allTake` (Bool `all`) | `xs.all p = True → (xs.take k).all p = True` | 2025/Day08/Proofs/Part1.sw:51 | 1/4 |
| `List.allPairs`, `List.allMapPairWith` | `xs.all q → xs.pairs.all (both q)` | 2025/Day08/Proofs/Part1.sw:60,67 | 1/6 |
| `List.memPairsRangeFrom` | `a < b` inside the range → `(a, b) ∈ (rangeFrom c s).pairs` | 2025/Day08/Proofs/Part2.sw:240 | 1/2 |
| `List.memMinOfMem` (Nat) | `u, v ∈ xs → Nat.min u v ∈ xs` | 2025/Day09/Proofs/Compress.sw:171 | 1/3 |
| `List.filterAllKept` | the filter kept everything if its length isn't smaller | 2024/Day24/Proofs/Complete.sw:29 | 1/3 |

### E. `List.occurrences` over ranges (lane L2, `List/Toolkit.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `List.occurrencesRangeOne` | one `v < n` satisfies `q` → `(range 0 n).occurrences q = 1` | 2025/Day08/Proofs/Part2.sw:29 | 1/3 |
| `List.occurrencesRangeWithout` | taking one satisfying `v` out of the count | Part2.sw:35 | 1/3 |
| `List.occurrencesRangeUnique` | count 1 → the two satisfying values are equal | Part2.sw:45 | 1/2 |
| `List.countRangeOnce` | `(range 0 n).count (i => c ∧ i == k) = c.toNat` | 2021/Day05/Proofs/Proofs.sw:94 | 1/2 |
| `List.sumByRangeFromKeepIf` | `(rangeFrom (to+1-from) from).sumBy (x => x.keepIf (y == x)) = y.keepIf (from ≤ y ≤ to)` | 2025/Day02/Proofs/Repeated.sw:335 | 1/2 |
| `List.rangeFromSplitFirst` | `rangeFrom (hi - lo) lo = [lo, ..rangeFrom (hi - Succ lo) (Succ lo)]` when `lo < hi`; `range 1 (n+1) = rangeFrom n 1` | 2025/Day06/Proofs/Correct.sw:69, 2025/Day02/Proofs/Templates.sw:59,61 | 2/6 |

### F. `List.allSome` (lane L2, `List/Lemmas.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `List.allSomeMap` | `f x = Some (g x)` on members → `allSome (xs.map f) = Some (xs.map g)` | 2024/Day24/Proofs/Complete.sw:115 | 2/3 |
| `List.allSomeElim` | `allSome (xs.map f) = Some ys → x ∈ xs → ∃ v, f x = Some v` | 2020/Day07/Proofs/Depth.sw:120 | 1/3 |
| `List.allSomeIntro` | the converse | Depth.sw:134 | 1/3 |
| `List.allSomeKeeps` | a weaker `g` that agrees wherever `f` succeeds gives the same list | 2020/Day07/Proofs/Part2.sw:38 | 1/3 |

Std has only `List.allSomeNone` today. These four make `allSome` usable.

### G. `Nat` and `Int` arithmetic, `Bool.toNat` (lane N1, `Nat/Arith.sw`, `Int/Lemmas.sw`, `Bool/Bool.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `Nat.mulNeZero` | `a ≠ 0 → b ≠ 0 → a * b ≠ 0` | 2024/Day14/Proofs/Lemmas.sw:30 | 1/2 (S3) |
| `Nat.divMonoLeft` | `a ≤ b → a / d ≤ b / d` (new proof, SW-957) | NOTES-2021:1684 | (S3) |
| `Nat.mulAddDivMatch` | `r < d → (v * d + r == t) = (t % d == r && v == t / d)` | 2024/Day07/Proofs/Undo.sw:11 | 1/3 |
| `Nat.mulAddDivSmall` | `c < w → (r * w + c) / w = r` | 2024/Day06/Proofs/Bound.sw:109 | 1/3 |
| `Nat.subModSelf` | `w ≤ c → (c - w) % w = c % w` | 2020/Day03/Proofs/Proofs.sw:12 | 1/2 |
| `Nat.modSuccEqZero` and `Nat.divSuccStep` | the dial-wrap facts of 2025 d1 (`isZeroNeg`, `stepRight`) | 2025/Day01/Proofs/Part2.sw:74,102 | 1 (near-generic; read first) |
| `Bool.toNatEqZero` | `b.toNat = 0 → b = False` | 2025/Day04/Proofs/Rounds.sw:90 | 1/2 |
| `Bool.toNatAnd` | `(a ∧ b).toNat = b.toNat.keepIf a` | 2025/Day04/Proofs/Window.sw:164 | 1/3 |
| `Bool.toNatOdd` | `(c.toNat % 2 == 1) = c` | 2024/Day24/Proofs/Sums.sw:22 | 1/3 |
| `Int.toNatCheckedSome`, `Int.toNatCheckedNone` | `x.toNatChecked = Some n → x = n.toInt`; `= None → x < 0` | Common/Proofs/Offset.sw:29,33 | 2/10 |
| `Int.modNatOfLt` | `x < size → x.toInt.modNat size = x` | Common/Proofs/Offset.sw:163 | 2/5 |
| `Int.modNatSuccWrap`, `Int.modNatPredWrap` | `(if x + 1 == size then 0 else x + 1) = (x + 1).modNat size`, and back | 2024/Day14/Proofs/Lemmas.sw:9,36 | 1/4 |
| `Int.modNatPeriodic` | adding `size * laps` steps doesn't move a wrapped position | 2024/Day14/Proofs/Moves.sw:58 | 1/2 |
| `Int.natAbsSign` | `x.natAbs.toInt = x.sign * x` | 2024/Day08/Proofs/Part2.sw:28 | 1/3 |
| `Int.signCases` | the three sign cases with their order facts | 2021/Day17/Proofs/Motion.sw:34 | 1/3 |
| `Int.natAbsSubLtOfLt` | `p, a < n → (p.toInt - a.toInt).natAbs < n` | 2024/Day08/Proofs/Part2.sw:97 | 1/2 |
| `Int.mulNonnegSucc` | `0 ≤ d * (d + 1)` | 2021/Day17/Proofs/Peak.sw:15 | 1 |
| `Int.mulKeepIf` | `v * (x.keepIf b).toInt = x.toInt * (if b then v else 0)` | 2025/Day02/Proofs/Part2.sw:98 | 1 |
| `Int.divExact` | `value.natAbs = t * Succ b → Succ b * (value / Succ b) = value` | 2024/Day08/Proofs/Part2.sw:16 | 1 |

`Int.modNat*` should land in `Int/`, where std review S4 / SW-2004 wants
the `modNat` lemmas moved anyway. If SW-2004 hasn't run yet, put them
next to the existing ones in `Mod/Mod.sw` and leave the move to SW-2004.

### H. `Nat` digits and bits (lane N2, `Nat/Digits.sw`, `Nat/Bits.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `Nat.fromDigitsTakeDrop` | `fromDigits (ds.take k) * 10^(ds.drop k).length + fromDigits (ds.drop k) = n` for `ds = n.digits` | 2024/Day11/Proofs/Split.sw:14 | 1/5 |
| `Nat.divPowTenDigits`, `Nat.modPowTenDigits` | `n / 10^k` and `n % 10^k` as `fromDigits` of the first and last digits (the day's `digitCount / 2` becomes any `k ≤ digitCount`) | Split.sw:44,51 | 1/7 |
| `Nat.digitsOfLeading` | `digits (fromDigits (xs.take c)) = xs.take c` when `xs` are digits with a non-zero head | Split.sw:70 | 1/2 |
| `Nat.digitsDivPowTen` | the digits of `n / 10^k` are the first `digitCount - k` digits | Split.sw:80 (generalised) | 1 |
| (none) | `rightHalfSmall` (Split.sw:27) is `Nat.fromDigitsBound` (Nat/Digits.sw:124) applied to the dropped digits: use std, delete | Split.sw:27 | 1 |
| `Nat.fromDigitsReplicate` | `fromDigits (concat (replicate n p)) = fromDigits p * repunit`, with a small `Nat.repunit k n` (2025 d2's `multiplier`/`writeTimes`, Repeated.sw:58-68,197) | 2025/Day02 | 1/10 (near-generic) |
| `Nat.testBitZero` | `n.testBit 0 = (n % 2 == 1)` | 2024/Day24/Proofs/Sums.sw:20 | 1/7 |
| `Nat.testBitOfLtPow` | `n < 2^b → b ≤ i → n.testBit i = False` (one lemma for `testBitSmall`/`testBitAbove`) | 2024/Day24/Proofs/Lemmas.sw:10,14 | 1/6 (S3) |
| `Nat.testBitAddZero` | bit 0 of `x + y + c` is `xor` of the three | 2024/Day24/Proofs/Sums.sw:27 | 1/2 |
| `Nat.testBitAdd` | bit `i` of `x + y` is `x_i xor y_i xor carry_i`, with `Nat.carryInto` defined in std (2024 d24's `carryInto`, `carryFrom` and `sumBit`, Sums.sw:32-69) | 2024/Day24 | 1 (near-generic) |
| `Nat.fromBitsLowFirst*` | bit lemmas of `Nat.fromBits` low-first lists (2024 d24's `fromBitsLow`/`High`, Lemmas.sw:30,33, through `Bits.fromLowFirst`; restate on std's `Nat.fromBits` of the reversed list) | 2024/Day24 | 1/4 (near-generic) |

### I. `Option`, `Pair`, `Map`, `Set` (lane O, after SW-2138: `Option/Lemmas.sw`, `Map/Map.sw`, `Set/Spec.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `Option.somePairInjective` | `Some (x1, y1) = Some (x2, y2) → x1 = x2 ∧ y1 = y2` (a convenience over `Option.someInjective` with `Pair.mkInjectiveFst`/`Snd`; 12 uses justify it) | Common/Proofs/BitReader.sw:10 | 2/12 |
| `Pair.ext` | `x.fst = y.fst → x.snd = y.snd → x = y` (generalise `pairExt`, GridCells.sw:109, from `(Nat, Nat)`) | Common | 1/2 |
| `Option.getOrElseMergeAdd` | `(x.merge y Nat.add).getOrElse 0 = x.getOrElse 0 + y.getOrElse 0` | 2024/Day22/Proofs/Totals.sw:9 | 1/2 |
| `Option.mergeElim` | from `x.merge y f = Some v`, either side's value proves the goal | 2024/Day22/Proofs/Keys.sw:87 | 1 |
| `Option.flatMapSomeRight` | `x.flatMap Some = x` | 2024/Day21/Proofs/Lemmas.sw:51 | 1/2 |
| `Option.getOrElseMap2And` | `(map2 (x y => (x ∧ y).toNat) a b).getOrElse 0 = (a.getOrElse False ∧ b.getOrElse False).toNat` | 2024/Day04/Proofs/Part2.sw:22 | 1 |
| `Option.isSomeNotNone` | `o.isSome = True → o = None → Void` | 2021/Day08/Proofs/Proofs.sw:160 | 1 |
| `Map.getOrUnionWithAdd` | `(a.unionWith b Nat.add).getOr k 0 = a.getOr k 0 + b.getOr k 0` (2024 d22's `unionGetOr`, Totals.sw:16, with `Changes` replaced by `k`) | 2024/Day22 | 1/2 |
| `Map.lookupLastMem`, `Map.lookupLastOfMem` | `lookupLast k ps = Some v → (k, v) ∈ ps`, and existence from membership | 2024/Day24/Proofs/Lemmas.sw:18, Complete.sw:78 | 1/6 (coordinate with SW-1577's `List.lookup` bridge) |
| `Map.lookupLastIdentityRange` | `lookupLast b ((rangeFrom c s).map (x => (x, x)))` is `Some b` inside, `None` below | 2025/Day08/Proofs/Labels.sw:79,90 | 1 |
| `Map.containsCountsAtLeast` | `(Map.counts xs |> .filter (_ n => m ≤ n)).contains x = (m ≤ xs.count (== x))`, from 2021 d5's `containsTwice` (Proofs.sw:49) with `Point → k` and `2 → m`, and its `NumberWith` form `countedTwice` | 2021/Day05 | 1/4 |
| `Map.Spec.sameKeyRefl` | `sameKey k k = True` | 2024/Day23/Proofs/Lemmas.sw:11 | 1/3 |
| `Set.memberOfSizePos` | `0 < set.size → ∃ k, set.contains k` (S3) | 2020/Day20/Proofs/Monsters.sw:157 | 1/2 |
| `Set.containsUnionElim` | the `Or`-elimination form of `containsUnion` (generalise 2024 d23's `unionElim`, Part2.sw:57, from `Computer`; its `insertElim` duplicates `Set.containsInsertElim` and goes) | 2024/Day23 | 1 |
| `Set.containsFromListThree` | skip: one use; `Set.containsFromListIff` with `List.Mem` cases does it | 2024/Day23/Proofs/Lemmas.sw:15 | — |
| `Set.sizeOfPopMinNone` | `s.popMin = None → s.size = 0` (2024 d23 `sizeNone`, Part2.sw:81; check SW-2142's `missingOfMinNone` first) | 2024/Day23 | 1 |

SW-2138 is editing `Map.sw` and `Set/Spec.sw` now, so lane O starts after
it merges. SW-2142 (after SW-2138) also touches 2024 day 23. Have lane O
absorb SW-2142, or run after it.

### J. Folds and `Nat.iterate` (lane F, SW-1486, after SW-2147: `List/Lemmas.sw`, `Nat/Iterate.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `List.foldLeftRelate` | a map commuting with each step commutes with the fold | 2020/Day12/Proofs/Parts.sw:13 | 1/4 |
| `Nat.iterateMod` | a period-`p` map iterated `n` times is iterated `n % p` times | Common/Proofs/Plane.sw:22 | 2/6 |
| `Nat.iterateCycles` | iterating `times * period` is the identity | Common/Proofs/Plane.sw:17 | 1/3 |
| `Nat.iterateModNat` | iterating a step that is `x ↦ (x + d).modNat size` `t` times is one jump `(x + t·d).modNat size` (2024 d14 `iterateWrap`, Lemmas.sw:45) | 2024/Day14 | 1 |
| `List.foldMinByKeeps` | a fold by `minBy` keeps a property all inputs have (2024 d21 `minByStepPasses`, Lemmas.sw:56) | 2024/Day21 | 1 |
| `List.foldMaxGeStart` | `z ≤ rs.foldLeft z (m r => Nat.max m (f r))` (2025 d5 `topGe`, Part2.sw:33, with `Range.to` replaced by `f`) | 2025/Day05 | 1 |

### K. `Parse` and `Text` (lane P, `Parse/Runs.sw`, `Text/Basics.sw`)

| Std name | Statement | From | Days/uses |
| --- | --- | --- | --- |
| `Parse.runsValueEq` | `v = w → Runs p read rest v → Runs p read rest w` | 2020 days 4, 6, 7, 8, 13, 16, 19, 20 (`Proofs/Complete.sw:11` and so on) | **8/27** |
| `Parse.spaceNotDigit` | `isSpace c = True → isDigit c = False` | 2020/Day16/Proofs/Complete.sw:21, Day19/Proofs/ParseComplete.sw:17 | 2/4 |
| `Parse.digitNotEq` | `isDigit c = True → isDigit d = False → (c == d) = False`, which replaces `digitNotX` (2020 d13:15) and `digitNotQuote` (2020 d19:84) | 2 days | 2/4 |
| `Text.stripPrefixCharsDiffer` | first characters differ → `stripPrefixChars [f, ..fs] [c, ..cs] = None` | 2020/Day17/Proofs/Complete.sw:17, Day20/Proofs/Complete.sw:26 | 2/7 |
| `Parse.joinReadsSnoc`, `Parse.stepValuesSnoc` | `joinReads`/`stepValues` of `steps ++ [(read, v)]` (both functions are std's) | 2020/Day18/Proofs/Complete.sw:248,253 | 1 |
| `Parse.cannotStartAtBlankBreak` | a parser that can't start at `\n`/`\r` can't start at a blank-line break | 2020/Day19/Proofs/ParseComplete.sw:171 | 1 |
| `Char.digitValueSpaces` | `(replicate k ' ').filterMap Char.digitValue = []` | 2025/Day06/Proofs/Grid.sw:36 | 1 |

`runsAsValue` could also just be written inline: it's `rewrite same at
runs in runs`. Std is still the better home: the shape is so common that
`search` should find it, and eight days found it worth naming.

### Near-generic lemmas (need a small generalisation first)

These name a day's helper, but the helper is a generic idea. Each needs the
helper moved too, so they're for lanes with judgement (Sonnet), and only
after the plain moves.

- **`isBetween` either way round** (2025 d9 `isBetween`/`isBetweenHalfOpen`,
  Day09.sw:69,72; 2021 d5 `between`, Spec.sw:28). This is
  `Nat.min a c ≤ b ≤ Nat.max a c`, needed by two days; `betweenBound` and
  `halfOpenBetween` come with it. Std home: `Nat/Arith.sw`, as
  `Nat.isBetween`. Lane N1, if time allows.
- **2024 day 12 `total`**: already std (table A), in lane D1.
- **2025 day 9 `largest`** (`foldLeft 0 Nat.max`): use `List.maximum` or
  the `List.foldMax*` lemmas; `largestInList` is `List.foldMaxMem`. Lane D0.
- **2024 day 21 `lastFrom`, `sumByPairs`**: a sum of costs over
  `zipWithNext` equals a fold, which is generic in `cost`. It would be
  `List.sumByZipWithNext` in L2, if a second day wants it. One day today,
  so it waits.
- **2021 day 1 `slidingWindows`** duplicates std's `List.windows`
  (List/Toolkit.sw:726). Rewriting the spec onto `List.windows` would
  remove `windowsLong`/`windowsShort`, but it changes the day's spec, so it
  belongs to an AoC follow-up lane, not this batch.
- **2024 day 2 `removals`/`anyRemoved`** (every list with one element
  dropped). Std has `List.removeAt` but no "all removals". One day: file
  only.
- **2021 day 6 `oneTimer`** and **2020 day 17 `window`/`windowAnd`**:
  counting indicator sums over a small window. These are `omega`/`cases`
  candidates, not std.
- **2024 day 8's `Int` cross-product lemmas** (`crossOnLine`,
  `onLineOfCross`, `twiceAsFar*`): plane geometry. Their home is
  `Aoc.Common.Plane`, not std, if a second day needs them.
- **`Common/PrefixSums.sw`** (a summed-area table with its proof
  `PrefixSums.blockSum`) is a generic data structure. Std could take it
  whole, as `List.Grid.PrefixSums`. That's a module move, not a lemma move,
  so it's left out of these lanes (see "Calls I made").

## Std gaps the days kept running into

These are functions with few or no lemmas, which several days had to
prove things about themselves:

- **`List.allSome`**: one lemma (`allSomeNone`); two days proved four
  (section F).
- **`List.filterMap`**: membership is covered, but length and count are
  not (`lengthFilterMapLe`, `countFilterMap`, 2021 d3 `columnLength`).
- **`List.last`, `List.reverse` together**: no `last (reverse xs)` or
  `head (reverse xs)` lemmas (SW-1588); `List.lastCons` is missing too.
- **`List.takeWhile`**: no cons step lemmas (SW-1468).
- **`Int.toNatChecked`**: only `toNatCheckedToInt`; the inverse direction
  is in `Aoc.Common`.
- **`Nat.testBit`**: lemmas for `and`/`or`/`xor`/`div`, none for `+`, `% 2`,
  or small numbers.
- **`Nat.digits` with `/` and `%` by powers of ten**: std has
  `fromDigitsAppend` but nothing linking `n / 10^k` to the digit list.
- **`Option.merge`**: only `mergeFlip`.
- **`Map.unionWith` with `getOr`**: only `getUnionWith` (on `get`).
- **`List.Distinct` and append**: `distinctAppend` exists, but there's no
  snoc form, and the name `List.distinctSnoc` is taken by the function
  `List.distinct`'s lemma. That `Distinct`/`distinct` clash will catch
  others. SW-2006 (one name per operation) should look at it.
- **`Parse.Runs` congruence in the value**: none (`runsAsValue`, 8 days).

## Migration lanes

All lanes put new std lemmas under full API docs (std requires them), use
std's naming, and replace each AoC copy with a use of std. If a day's
proof gets shorter by using std directly (rather than renaming the call),
it takes the shorter proof. No lane changes a theorem's statement in
`aoc/`, except to delete a local lemma.

Tests, for every lane that edits std:

- `task snap:hashes` (std changes run it without `NAME`);
- `task test:one -- hash_stability`;
- `task audit:touched -- <each changed AoC namespace>`;
- `stitchwort fmt` on the touched `.sw` files.

None of the lanes edits `std/core/`, so extract's `bound_to_the_prelude`
tests aren't needed. A lane that finds it must touch `core/` (for example
`core/Equality.sw`) adds `task test:one -- bound_to_the_prelude`.

Order and clashes:

- D0 is AoC-only and can run at any time.
- L1 and L2 both edit `List/Lemmas.sw`, so they run one after the other.
- N1 and N2 touch different files and can run side by side.
- P is independent.
- O waits for SW-2138 (and absorbs or follows SW-2142).
- F waits for SW-2147.
- D1 touches only 2024 day 12.

| Lane | Model | Est. | Std files | Depends on |
| --- | --- | --- | --- | --- |
| D0, deletions and tactic swaps | DeepSeek | 45 min | none | none |
| D1, 2024 d12 `total` onto std `sumBy` | Sonnet | 45 min | none | none |
| L1, List filterMap/map/distinct/index | Sonnet | 60 min | List/Lemmas.sw, List/Index.sw | none (absorbs SW-2003's list half, SW-1608) |
| L2, List takeWhile/last/count/sum/allSome/occurrences | Sonnet | 60 min | List/Lemmas.sw, List/SortLemmas.sw, List/Toolkit.sw | after L1 (absorbs SW-1468's takeWhile half, SW-1588's reverse half) |
| N1, Nat/Int/Bool arithmetic | Sonnet | 60 min | Nat/Arith.sw, Int/Lemmas.sw, Bool/Bool.sw (Mod/Mod.sw if SW-2004 hasn't run) | none (absorbs SW-957's lemma items) |
| N2, Nat digits and bits | Sonnet | 60 min | Nat/Digits.sw, Nat/Bits.sw | none |
| P, Parse and Text | Sonnet | 45 min | Parse/Runs.sw, Text/Basics.sw | none |
| O, Option/Pair/Map/Set | Sonnet | 60 min | Option/Lemmas.sw, Map/Map.sw, Map/Spec.sw, Set/Spec.sw | after SW-2138 (and SW-2142) |
| F, folds and iterate | Sonnet | 45 min | List/Lemmas.sw, Nat/Iterate.sw | after SW-2147 and L2 (this is SW-1486) |

That's 7 std lanes plus D0 and D1, about 8 hours of lane time.

### Brief paragraphs

**D0 (DeepSeek, 45 min).** Delete AoC lemmas that std already has or that
a tactic proves, and point their uses at std. The list is
`docs/reviews/SW-2159-aoc-lemmas-to-std.md`, sections A (every row except
the 2024 day 12 `total` row) and B. For each lemma, replace every use in
its day with the std name in the table (watch argument order: read the std
signature), or with `omega`/`cases`/`rfl` for section B. Then delete the
local theorem. If a tactic swap fails, or needs more than a short hint
list, keep that lemma and list it in your report. Don't edit
`crates/elab/src/std`. Tests: `task audit:touched -- <namespace>` for each
namespace you change (for example `Aoc.Year2024.Day22.Proofs`), and
`stitchwort fmt` on the files. Never run a command in the background: wait
for each to finish. Run every test you add and show it passing. Finish with
a report: what you changed, each command you ran and its result, and what
you were unsure of.

**D1 (Sonnet, 45 min).** 2024 day 12's `Proofs/Corners.sw` defines
`total n f`, `f 0 + … + f (n-1)`, with twelve lemmas (`totalCong` to
`totalAdd4`, `telescope`, `startsEqualEnds`). `Sides.sw:146`'s
`totalRange` shows it equals `(List.range 0 n).sumBy f`. Restate the
day's uses on `List.sumBy (List.range 0 n)` with std's `sumByRangeSucc`,
`sumByAdd`, `sumBySwap`, `sumByCongRange` and `sumByZero`, and delete
`total` and its lemmas. Keep `previous` and `telescope`, restated on
`sumBy`. If `telescope` is generic once restated (it is a telescoping sum
of `b i ∧ ¬ b (i-1)`), propose it for std in your report, but don't move
it. Tests: `task audit:touched -- Aoc.Year2024.Day12.Proofs`.

**L1 (Sonnet, 60 min).** Move the `List` lemmas of section C into std,
with full API docs: `countFilterMap` (and the `== y` corollary),
`lengthFilterMapLe`, `lengthFilterMap`, `mapConcat`, `distinctOfMap`,
`distinctSnocIntro`, `distinctSwapMiddle`, `withIndexDistinct`,
`withIndexFromMap`, `indexFromAbove`, `distinctWithIndexFromPaired`,
`memOfMemTails`, `allZipWithSelf`, `allLengthMem` and
`allLengthReverseOnto`. Also add SW-1608's `List.distinctFilterMap`.
Filter and map lemmas go in `List/Lemmas.sw` near `memFilterMap`; index
lemmas go in `List/Index.sw`. Generalise as the table says (drop the
unused `fallback`; `(Nat, Nat)` → `a`). Then replace the copies in
`Aoc.Common.Proofs` (Grid.sw, GridCells.sw), 2020 days 8, 11 and 20, 2024
days 9, 14 and 22, and rogue's `Proofs/Apart.sw` with the std names, and
delete them. Tests: `task snap:hashes`, `task test:one -- hash_stability`,
`task audit:touched` on `Aoc.Common.Proofs`, `Aoc.Year2020.Day08.Proofs`,
`Aoc.Year2020.Day11.Proofs`, `Aoc.Year2020.Day20.Proofs`,
`Aoc.Year2024.Day09.Proofs`, `Aoc.Year2024.Day14.Proofs`,
`Aoc.Year2024.Day22.Proofs` and the rogue proofs namespace.

**L2 (Sonnet, 60 min, after L1).** Move sections D, E and F into std, with
full API docs:

- `takeWhile`: `takeWhileConsTrue`/`False` (SW-1468's first half).
- `last` and `reverse`: `lastCons`, `lastReverse`, `headReverse`,
  `lastReverseOnto`, `reverseEqNil`, `lastDrop`, `consHeadDrop`
  (SW-1588's reverse half).
- `lengthPos`, `containsCons`, `containsTakeMono`.
- Counts: `countReplicate`, `countSplitOn`, `countPointwiseAdd`,
  `countBelowSorted`/`countAboveSorted`, `sortedHeadLeMem` (check
  `List.sortedHeadLe` first).
- `getMapRange`/`getMapRangePast`.
- Sums: `sumByConst`, `sumByLeMem`, `existsOfSumByPos`.
- `all` and pairs: `allTake`, `allPairs`/`allMapPairWith`,
  `memPairsRangeFrom`, `memMinOfMem`, `filterAllKept`.
- Ranges (`List/Toolkit.sw`): the `occurrencesRange*` lemmas,
  `countRangeOnce`, `sumByRangeFromKeepIf`, `rangeFromSplitFirst`.
- `allSome`: `allSomeMap`, `allSomeElim`, `allSomeIntro`, `allSomeKeeps`.

Replace the copies in 2020 days 5, 7, 10, 19 and 20, 2021 days 5, 6, 7,
10, 13 and 14, 2024 days 16, 18 and 24, and 2025 days 2, 6, 8 and 9, and
delete them. Tests: `task snap:hashes`, `task test:one --
hash_stability`, and `task audit:touched` on each changed namespace. This
list is long: if it won't fit, do D and F first and report E as left over.

**N1 (Sonnet, 60 min).** Move section G into std, with full API docs:

- `Nat/Arith.sw`: `Nat.mulNeZero`, `Nat.divMonoLeft` (a new proof, from
  SW-957), `Nat.mulAddDivMatch`, `Nat.mulAddDivSmall`, `Nat.subModSelf`.
- `Bool/Bool.sw`: `Bool.toNatEqZero`, `Bool.toNatAnd`, `Bool.toNatOdd`.
- `Int/Lemmas.sw`: `Int.toNatCheckedSome`/`None`, `Int.natAbsSign`,
  `Int.signCases`, `Int.natAbsSubLtOfLt`, `Int.mulNonnegSucc`,
  `Int.mulKeepIf`, `Int.divExact`.
- The `Int.modNat` ones (`modNatOfLt`, `modNatSuccWrap`/`PredWrap`,
  `modNatPeriodic`) go next to the existing `Int.modNat*` lemmas.
- If time allows, add `Nat.isBetween` (either order) and move 2025 day 9's
  and 2021 day 5's `between` onto it.

Replace the copies in `Aoc.Common.Proofs` (Offset.sw), 2020 days 3 and 8,
2021 day 17, 2024 days 6, 7, 8 and 14, and 2025 days 2 and 4, and delete
them. Before adding each lemma, check whether `omega` proves it at the use
site; if it does, use `omega` there and don't add the lemma. Tests: `task
snap:hashes`, `task test:one -- hash_stability`, and `task audit:touched`
on each changed namespace.

**N2 (Sonnet, 60 min).** Move section H into std, with full API docs:

- `Nat/Digits.sw`: the decimal split. `Nat.fromDigitsTakeDrop`,
  `Nat.divPowTenDigits`, `Nat.modPowTenDigits`, `Nat.digitsOfLeading` and
  `Nat.digitsDivPowTen`, generalised from 2024 day 11's half-split
  (`Proofs/Split.sw`) to any `k ≤ digitCount`. `rightHalfSmall` becomes a
  use of `Nat.fromDigitsBound`.
- `Nat/Bits.sw`: `Nat.testBitZero`, `Nat.testBitOfLtPow` (one lemma for
  `testBitSmall` and `testBitAbove`) and `Nat.testBitAddZero`.

Then restate 2024 day 11's `splitLeft`/`splitRight`/`recombine` as
corollaries at `k = digitCount / 2`, or delete them where std suffices.
Point 2024 day 24 at the bit lemmas.

Stretch, only if the plain moves are done: `Nat.carryInto` with
`Nat.testBitAdd` (2024 day 24's `Proofs/Sums.sw`), and `Nat.repunit` with
`Nat.fromDigitsReplicate` (2025 day 2's `multiplier`/`writeTimes`).

Tests: `task snap:hashes`, `task test:one -- hash_stability`, and `task
audit:touched -- Aoc.Year2024.Day11.Proofs Aoc.Year2024.Day24.Proofs` (add
`Aoc.Year2025.Day02.Proofs` for the stretch).

**P (Sonnet, 45 min).** Move section K into std, with full API docs:

- `Parse/Runs.sw`: `Parse.runsValueEq`, `Parse.spaceNotDigit`,
  `Parse.digitNotEq`, `Parse.joinReadsSnoc`, `Parse.stepValuesSnoc` and
  `Parse.cannotStartAtBlankBreak`.
- `Text/Basics.sw`, next to `stripPrefixChars`:
  `Text.stripPrefixCharsDiffer`.
- `Char.digitValueSpaces`.

Replace `runsAsValue` in 2020 days 4, 6, 7, 8, 13, 16, 19 and 20, and the
other copies in 2020 days 13, 16, 17, 18, 19 and 20, and 2025 day 6, and delete them. Tests: `task snap:hashes`, `task test:one --
hash_stability`, and `task audit:touched` on each changed namespace (12 or
so; run them in one call).

**O (Sonnet, 60 min, after SW-2138 merges).** Move section I into std,
with full API docs:

- `Option/Lemmas.sw`: `Option.somePairInjective`, `Option.getOrElseMergeAdd`,
  `Option.mergeElim`, `Option.flatMapSomeRight`, `Option.getOrElseMap2And`
  and `Option.isSomeNotNone`.
- `Pair.ext`, next to `Pair`'s other lemmas.
- `Map/Map.sw`: `Map.getOrUnionWithAdd`, `Map.lookupLastMem`/`OfMem`,
  `Map.lookupLastIdentityRange` and `Map.containsCountsAtLeast`, with its
  `NumberWith` form.
- `Map/Spec.sw`: `Map.Spec.sameKeyRefl`.
- `Set/Spec.sw`: `Set.memberOfSizePos`, `Set.containsUnionElim` and
  `Set.sizeOfPopMinNone` (check SW-2142's `missingOfMinNone` first).

Generalise `Changes`, `Computer`, `Point` and `2` as the table says.
Coordinate `lookupLast*` with SW-1577: if SW-1577 has merged, use its
names. Replace the copies in `Aoc.Common.Proofs` (BitReader.sw,
GridCells.sw), 2020 day 20, 2021 days 5 and 8, 2024 days 4, 21, 22, 23
and 24, and 2025 day 8, and delete them. If SW-2142 hasn't run, absorb it.
Tests: `task snap:hashes`, `task test:one -- hash_stability`, and `task
audit:touched` on each changed namespace.

**F (Sonnet, 45 min, after SW-2147 and L2).** This is SW-1486. Move
section J into std, with full API docs:

- `List.foldLeftRelate`, `List.foldMinByKeeps` and `List.foldMaxGeStart`,
  near the other fold lemmas in `List/Lemmas.sw`.
- `Nat.iterateMod`, `Nat.iterateCycles` and `Nat.iterateModNat`, in
  `Nat/Iterate.sw`, next to `Nat.iterateAdd`. SW-2147's `iterateCongOn`
  will be there by then.

Replace the copies in `Aoc.Common.Proofs` (Plane.sw), 2020 day 12, 2024
days 14 and 21, and 2025 day 5, and delete them. Tests: `task
snap:hashes`, `task test:one -- hash_stability`, and `task audit:touched`
on each changed namespace.

## Calls I made

- **One-word proofs get no std name.** If `omega`, `cases` or `rfl`
  proves a lemma directly, the use site says so, and std doesn't grow a
  name nobody will search for. This keeps std rich in facts that take
  work, not in restated arithmetic.
- **AoC domain modules stay in `Aoc.Common`.** That covers `Position`,
  `Direction`, `Offset`, `Range`, `Bits`, `Plane` and `GridGraph`. Only
  their lemmas about std types move.
- **`PrefixSums` stays out of these lanes.** It's a whole data structure
  and needs its own small design call. I'd file it as a backlog ticket:
  "Std: `List.Grid.PrefixSums` from `Aoc.Common`".
- **Std names follow the existing conventions,** even where the AoC name
  was clearer for the day (`distinctSnocIntro`, because `distinctSnoc` is
  taken).
- **Statement changes in `aoc/` are limited to deleting local lemmas.**
  2021 day 1's `slidingWindows` → `List.windows` changes a spec, so it
  goes to an AoC follow-up, not this batch.
- **SW-2003 is absorbed by L1, L2, N1 and O.** I'd close it as superseded
  when those lanes are filed.

## D questions

- **D3130:** should std take whole generic structures from `Aoc.Common`,
  starting with `PrefixSums` (the summed-area table with its block-sum
  proof), or only lemmas? [rec: lemmas now; `PrefixSums` as one backlog
  ticket, moved when a non-AoC example wants it.]

## Tickets to file

- The nine lanes above: D0, D1, L1, L2, N1, N2, P, O and F. Close SW-2003
  into L1, L2, N1 and O. Close SW-1486 into F. Note on SW-1468, SW-1588,
  SW-1608, SW-957 and SW-2142 which lane absorbs them.
- SW-1577 should take 2020 day 19's `numberWithCount` (`Proofs.sw:87`) as
  its proof, and 2024 day 24's `lookupLast*` should line up with its
  bridge.
- The `List.Distinct` / `List.distinct` name clash (`distinctSnoc` names a
  lemma about the function), for SW-2006's naming sweep.
- "AoC follow-up: 2021 day 1's spec onto `List.windows`" (Sonnet, 30 min).
- "Std: `List.Grid.PrefixSums` from `Aoc.Common`" (backlog, per D3130).
