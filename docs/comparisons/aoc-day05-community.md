# AoC 2025 day 5: community solutions in other languages

**Date:** 22 October 2026. **Our version:** `aoc/src/Aoc/Day05/Day05.sw` (program: sort the
ranges by start, fold them into a list of merged ranges, add up the sizes), and
`aoc/src/Aoc/Day05/Proofs/Part2.sw` (for every database, `solvePart2 db = countFresh db`, where
`countFresh` counts the ids from 0 to the largest end that some range holds, as the puzzle
reads). `docs/aoc-2025.md` §7 and "Day 5 (October 2026)" describe the program and the proof. This
note looks at what other people wrote for 2025 day 5, in the wild, and asks what that suggests for
Stitchwort. It follows the shape of [aoc-day01-community.md](aoc-day01-community.md),
[aoc-day02-community.md](aoc-day02-community.md) and
[aoc-day03-community.md](aoc-day03-community.md).

Labels, as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day5-community/sw/`,
run with the main checkout's `target/release/stitchwort` (built 22 Oct 2026, 09:03). Fetched
solutions are in `gh/` beside it, the megathread data in `arctic/`, and the scripts in `scripts/`.

## 1. Summary

I fetched day 5 files from 56 authors on GitHub (one per author): 16 in Lean 4, 3 in Idris 2,
1 each in Agda and Dafny, 8 in Haskell, 6 in OCaml, 5 each in Scala and Gleam, 4 in F#, 3 in
Clojure, 2 in Elixir, and one each in Koka and Roc. I read about 40 closely and classified the
rest by what they sort, fold and take the maximum of (§2 says which). I then read the r/adventofcode Day 5 megathread through the Arctic Shift archive (§2.2):
559 top-level comments, 551 not deleted, 94 language tags before merging spellings, 182 with code
inline. 67 comments are in functional or proof-oriented languages (15 Haskell, 8 Elixir, 7
Gleam, 6 F#, 5 each Common Lisp and OCaml, 4 each Scala, Clojure and Scheme, 3 Racket, and one
each Prolog, Emacs Lisp, Dafny, Admiran and Janet), about a dozen are in array languages (Uiua,
APL, J, BQN, K, Q, Goal). I read all of the 67; 27 have code inline. No Lean, Idris, Agda,
Coq/Rocq, Koka, Roc, Unison or Effekt comment is in the thread, and code searches for Coq, Rocq,
Isabelle, Idris, Agda and Dafny found no day 5 file beyond those above **[checked]**.

The main findings:

1. **Almost nobody proved anything about day 5, and nobody else proved the count.** Of the 16
   Lean authors, one (kim-em) states three theorems about merging and leaves all three as
   `sorry` ("requires proving qsort is a permutation and fold invariants"); sdiehl writes the
   non-overlap claim as an `axiom` ("The proof is nontrivial and requires reasoning about the
   fold invariant"); jorendorff states the full theorem (`solve2` equals the cardinality of a
   `Set.Finite`) in a comment, with `sorry`; acarapetis puts the invariant in a type and closes
   its side goals with `grind`, but proves nothing about which ids are covered. The one complete
   argument is Hath995's Dafny, which proves the answer equals the size of the set of covered ids
   (`assert answer == |original|`) **with** a `{:axiom}` for the order's totality and `decreases *`
   (permission not to terminate) on the method and its loop. Ours proves the same statement with no
   axiom and no `sorry`, total, over every database including empty and inverted ranges
   **[checked: read all of them; not run, so "it verifies" is each author's claim]**.
2. **The method families are the day 2 and 3 pattern again: one big family and a few clever
   ones.** About 60% of the GitHub files sort by start and fold into a list of merged
   ranges (ours). The clever ones: a **running high-water mark with a count and no list at all**
   (jorendorff in Lean, PP6464 in Haskell, junpls in Koka, r_so9 in F#, vanshjangir in Lean,
   and the array languages' running maximum); a **sweep over sorted start and end events**
   (ngrislain, tenthmascot and shnarazk in Lean, KacperKopiec in OCaml, mestar12345 in F#, K,
   J, APL, Uiua); **sorting by end and folding from the right**, which needs neither `max` nor
   `+ 1` (RossPaterson); and **interval-set libraries** (about a dozen: data-interval, Racket's
   `integer-set`, OCaml's `ISet`, F#'s FRange, glguy's `Box`, Mathematica's `IntervalUnion`).
3. **Stitchwort writes the shorter shapes today, first try, and they agree with ours.** The
   running-mark fold is four lines against our twelve (`merge` and `absorb`); the end-sorted fold
   is six; the sweep is seven. All four give 333892124923577 on the real input and 14 on the
   example, and on all 4,096 lists of three ranges with ends in 0 to 3 the mark fold, the
   end-sorted fold and ours equal the brute force, **inverted ranges included**; the sweep fails
   on inverted ranges and matches on all 1,000 well-formed lists **[checked: `variants.sw`,
   `exhaustive.sw`]**.
4. **The Lean authors reach for `omega` and `grind` exactly where our proof is longest.** The
   arithmetic bookkeeping in `Proofs/Part2.sw` (`topGe`, `coveredTop`, `mergedContains`,
   `absorbLo`, `absorbStacked`) is 55 of its 162 non-comment lines, a third; each is a case
   split plus `Nat.leTrans`, `Nat.leMaxLeft`, `Nat.addOne` and `Nat.leqFalse` steps. In the
   community files the same kind of side goal is `omega` (kim-em: two, one line each) or `grind`
   (acarapetis: 18 uses closing the sortedness invariants of `RangeSet.ofRanges`)
   **[checked: line ranges, grep]**. This is SW-101's case, already parked; day 5 gives it a concrete
   acceptance example.
5. **The two proof frictions recorded in `aoc-2025.md` are gone; one small tidy is left.** A
   lambda whose later arguments depend on it (`List.sortBySorted (a b => Nat.compare a.from b.from)
   …`, `List.anyPerm (r => r.contains id) …`) was `E-CANNOT-INFER`; both check now, so the three
   `Range.from a` / `Range.contains r id` spellings in `Part2.sw` (lines 112, 116, 123) are stale. And `Range` has a
   derived `Ord` (from, then to): `ranges.sort` runs, and `List.sortSorted` accepts it, so the
   comparison lambda written on ten lines (one in `Day05.sw`, nine in `Part2.sw`) can go
   **[checked: `p_lambda.sw`, `p_lambda2.sw`, `variants.sw`]**. The community leans on the same
   thing in other languages: Idris's `sort` on pairs "sorts lexographically, so this works out",
   Elixir's "tuples have built-in comparison" (kitaz0s_), where Lean's acarapetis writes `Ord
   Range` by hand with three `grind` lemmas.
6. **The traps are about touching and duplicate ranges, and our proof rules them out.** People
   lost time on `<` against `<=` ("wasted half an hour", runnerx4), singleton ranges
   (MyEternalSadness), a shorter range with the same start wiping a longer one (flwyd), duplicate
   ranges (RalfDieter), one range inside another (Daniikk1012) and overflow (Prolog, Scala's
   `NumericRange`, 15-digit ids). `Nat` is unbounded, and all of these are in the theorem's
   scope. Our unit tests cover touching, nested and gap; three more one-liners would name the
   rest (same start, duplicate, singleton), all passing today **[checked: `edge.sw`]**.
7. **Interval-set libraries are the most "other language" thing about day 5.** About a dozen
   solutions import one and have part 2 as `sum . map width . toAscList`. Stitchwort has no such
   library, and for this task the merge function is the thing to be proved, so I don't propose one
   (D436).

The ranked candidates are in §5 and the decisions in §6 (D430–D438). The cheapest useful ones:

- sort with the derived `Ord` and drop the stale workarounds (D430);
- three edge-case tests from the community's bugs (D431);
- one proof lane on the shorter programs, the running mark and the end-sorted fold (D432);
- day 5's arithmetic lemmas as the acceptance example for SW-101 (D434);
- `List.flatMap` into the SW-235 batch (D435).

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker; block comments are
counted, so files with long doc comments are inflated. "Proofs" means theorems in the file, not
tests. The table lists the solutions that add something; the others (listed after it) repeat
the patterns.

| # | Language | Author / link | Lines | Method | Notable | Proofs? |
|---|---|---|---|---|---|---|
| 1 | Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/5/Problem5.dfy) | 319 | sort by **end**, then merge a neighbouring overlapping pair until none is left (a `while` with `decreases *`) | the specification is a set: `rangeSet(r) = set x \| r.0 <= x <= r.1`, `Union(rs)`; `RangeSizeEqual` (`rangeSize(r) == \|rangeSet(r)\|`, induction on the upper bound); loop invariant `Union(sortedRanges) == original`; parse uses `expect` | **yes**: part 2's answer equals `\|original\|` (16 lemmas, 61 `assert`s); one `{:axiom} IsTotalOrder`; part 1 not verified; touching ranges (`hi + 1 == lo`) are not merged |
| 2 | Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day05/Basic.lean) | 91 | `qsort` by start, fold; touching merged (`last.hi + 1 >= r.lo`) | `Range.size_eq` and `Range.contains_max` by `omega`; `inAnyRange_iff` by `simp` | 8 theorems; `mergeRanges_preserves_coverage`, `_disjoint`, `_sorted` are `sorry` ("proof requires qsort reasoning") |
| 3 | Lean 4 | [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day5.lean) | 69 | `qsort`, fold with a running range | `NonOverlapping`, `SortedByStart` as recursive Props | `axiom mergeRanges_nonOverlapping`: "The proof is nontrivial and requires reasoning about the fold invariant" |
| 4 | Lean 4 | [jorendorff](https://github.com/jorendorff/advent-of-code/blob/HEAD/2025/day05/Day05/Basic.lean) | 48 | **running mark**, half-open ranges (`stop := last + 1`): `(max mark stop, total + (stop - min stop (max start mark)))` | the theorem `solve2_correct` (answer = cardinality of `{id \| ∃ r ∈ fresh, r.start ≤ id ∧ id < r.stop}`) sits in a comment | stated, `sorry`, commented out |
| 5 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day5_2.lean) | 75 | `Range` with a proof field `lower <= upper`; a `RangeSet` whose type says `ranges.Pairwise fun a b => a.upper < b.lower`; a recursive `build` threading the invariants as arguments | `instance : Ord Range` by hand with `Range.le_lower`, `lt_lower`, `le_lt`, each by `unfold … ; grind`; `List.sorted_mergeSort`; 18 uses of `grind` | invariants by construction (no `sorry`, no `axiom`); coverage is not stated |
| 6 | Lean 4 | [ianclement](https://github.com/ianclement/aoc-2025/blob/HEAD/Day05.lean) | 79 | `insertionSort`, then a recursive `union` that takes `h : List.Sorted RangeStartLe ranges` as an **argument** | the proof is only used to prove the recursive call's argument sorted; `IsTotal`/`IsTrans` instances written by hand | no theorem about the result |
| 7 | Lean 4 | [natewhite345](https://github.com/natewhite345/aoc25/blob/HEAD/day5/Day5/Basic.lean) | 70 | `mergeSort` by start, fold; **binary search** on the merged ranges, total through `termination_by haystack.length` | `#guard` tests for exactly the edge cases: touching `[(3,4),(4,9)]`, reversed order, nested | no |
| 8 | Lean 4 | [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day5.lean), [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day05.lean), [shnarazk](https://github.com/shnarazk/advent-of-code/blob/HEAD/Lean4/Y2025/Day05.lean) | 31–83 | **sweep** over sorted events: ngrislain `ranges.flatMap Range.toBounds` and a hand-written insertion sort of bounds; tenthmascot `[(start, 1), (stop, -1)]` with `mergeSort`, `adj_pairs`, `scanl` | ngrislain classifies each line as `Range ⊕ Nat` (as we do); shnarazk a `HashMap` of event counts and a running `level`; tenthmascot a `Decidable (i ∈ r)` instance for `Std.Range` | no |
| 9 | Lean 4 | [dupuisf](https://github.com/dupuisf/aoc25/blob/HEAD/Aoc25/Day05.lean), [vanshjangir](https://github.com/vanshjangir/AoC/blob/HEAD/2025/day05.lean) | 48–55 | running range or running mark in a `for` loop over the sorted array | dupuisf: `Parsec` parser rejecting `d < l`, `for hi : i in 1...<n` for safe indexing, `checkThat n (0 < ·)`; vanshjangir: `partial def`, a `let mut last` | no |
| 10 | Lean 4 | [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day5.lean), [frutjus](https://github.com/frutjus/aoc2025/blob/HEAD/day5/part2.lean), [stonarini](https://github.com/stonarini/AoC-2025/blob/HEAD/AoC2025/Day05.lean), [adomani](https://github.com/adomani/advents/blob/HEAD/Advents/AoC2025/day05.lean), [josephmate](https://github.com/josephmate/AdventOfCode2025/blob/HEAD/AdventOfCode2025/Day05.lean) | 32–108 | recursive `combineIntervals` (`Except ParseError` parse with messages, bjornestol); insert one range at a time into a disjoint list or `HashSet` (frutjus, adomani); in-place O(n²) pairwise merge with `[]` as "deleted" (stonarini); fixpoint over a `HashSet` with `partial def` (josephmate) | adomani: a line with one number is an id, two a range (`s.getNats`) and `#assert part1 atest == 3`; `panic` on other lines | no |
| 11 | Idris 2, Agda | [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day5/Solution.idr), [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day5.idr), [Pengler38](https://github.com/Pengler38/AoC-2025/blob/HEAD/src/Day5.idr), [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day05.agda) | 43–70 | sort then merge; Pengler38 inserts one range at a time with four cases | spikedoanz: "default Ord for (Int, Int) sorts lexographically, so this works out"; BrianNormant's library `merge` returns `Left`/`Right`; jpyamamoto sorts pairs through `×-decTotalOrder`, `{-# TERMINATING #-}` on `mergeRanges`, and merges only when `l₂ ≤ᵇ r₁` | no |
| 12 | Haskell | [glguy](https://github.com/glguy/advent/blob/HEAD/solutions/src/2025/05.hs), [mstksg](https://github.com/mstksg/advent-of-code/blob/HEAD/2025/AOC2025/Day05.hs) | 38, 39 | **interval-set libraries**: glguy's `unionBoxes` over half-open `Dim lo (hi + 1) Pt`; mstksg `foldMap (IVS.singleton …)` from data-interval | glguy parses with `[format\|2025 5 (%u-%u%n)*%n(%u%n)*\|]`, doctests with the example and answers; mstksg: "just a straightforward application of the data-interval library" **[cited]** | no |
| 13 | Haskell | [RossPaterson](https://github.com/RossPaterson/advent-of-code/blob/HEAD/2025/Day05.hs) | 53 | sort by **end** (`sortOn snd`), `foldr addrange []`; "a range with a smaller upper bound added to disjoint ranges ordered by their upper bounds" | no `max`, no `+ 1`: `\| hi1 < lo2 = new : rs \| otherwise = (min lo1 lo2, hi2) : rs` | no (a comment) |
| 14 | Haskell | [PP6464](https://github.com/PP6464/AoC-2025-Haskell/blob/HEAD/src/Day05.hs), [beefyhalo](https://github.com/beefyhalo/aoc/blob/HEAD/src/2025/05.hs), [stanosphere](https://github.com/stanosphere/advent-of-code/blob/HEAD/src/2025/Day5.hs) | 28–51 | PP6464: running mark in `State`; beefyhalo: sort, fold, **binary search** over a `Vector`; stanosphere: guard that falls through | PP6464: `(max m h, tot + max 0 (min (h + 1 - l) (h - m)))`; guards `\| currStart > prevEnd + 1 = …` / `\| otherwise` | no |
| 15 | Haskell | [nicuveo](https://github.com/nicuveo/advent-of-code/blob/HEAD/2025/haskell/src/Day05.hs), [GuillaumedeVolpiano](https://github.com/GuillaumedeVolpiano/adventOfCode/blob/HEAD/2025/days/Day5.hs) | 109+ | nicuveo: own `RangeSet` (`S.spanAntitone` to find the overlap); GuillaumedeVolpiano: an `IntMap` with `lookupLE`, "part 2 was actually solved with part one" **[cited]** | nicuveo also wrote `Day05TypeLevel.hs`: day 5 at the type level, in Peano numbers (161 lines, not read in full) | no |
| 16 | OCaml | [KacperKopiec](https://github.com/KacperKopiec/advent-of-code/blob/HEAD/2025/day5/part2.ml), [mbottini](https://github.com/mbottini/AOC2025/blob/HEAD/lib/day05.ml), [lukaskollmer](https://github.com/lukaskollmer/advent-of-code/blob/HEAD/src/2025/day_05/solution.ml), [mbacarella](https://github.com/mbacarella/ocaml-aoc2025/blob/HEAD/lib/day5.ml), [FizzyElt](https://github.com/FizzyElt/ocaml_aoc_2025/blob/HEAD/bin/day5/q2.ml), [aguluman](https://github.com/aguluman/advent-of-code-ocaml/blob/HEAD/2025/day05/day05.ml) | 31–112 | sweep over `(pos, tag)` events (KacperKopiec, 31 lines); merge into a balanced tree for part 1 (mbottini, whose `when` guard is the fold's first case); a `RangeSet` module (lukaskollmer) | KacperKopiec: `(l, 0) :: (r + 1, 1)` sorted with the tag as the tie-break | no |
| 17 | Scala 3 | [sim642](https://github.com/sim642/adventofcode/blob/HEAD/src/main/scala/eu/sim642/adventofcode2025/Day5.scala), [bishabosha](https://github.com/bishabosha/advent-of-code-2025/blob/HEAD/scala/2025_day05.scala), [lupari](https://github.com/lupari/aoc2025/blob/HEAD/src/main/scala/assignments/Day05.scala), [jelaby](https://github.com/jelaby/advent-of-code-2025-scala/blob/HEAD/src/main/scala/uk/co/mealor/aoc2025/Day5.scala), [Casper-Guo](https://github.com/Casper-Guo/AoC-Language-Exploration/blob/HEAD/2025.scala/day05.scala) | 21–178 | sim642 reuses `mergeIntervals` from his 2016 day 20; lupari 21 lines (`@tailrec merge`, `sortBy(_.start)`); bishabosha a queue-driven fixpoint | bishabosha: "Scala NumericRange[Long] requires that the diff from start to end is representable as an Int, so doesnt support the kind of wide ranges we need here" **[cited]**; the parse is `case s"$i-$j"` and a `r"…"` interpolator | no |
| 18 | F# | [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day05.fs), [spencerwi](https://github.com/spencerwi/AdventOfCode2025/blob/HEAD/day5/Lib.fs), [mattgallagher92](https://github.com/mattgallagher92/advent-of-code/blob/HEAD/2025/Day05.fs), [jrmcnair](https://github.com/jrmcnair/advent-of-code/blob/HEAD/2025/Day5.fs) | 15–70 | lboshuizen: sort, `fold` with a `when` guard, 15 lines; spencerwi: `tryMergeWith` with six overlap cases written out; a type `MergedRangesPuzzleInput` "to let the compiler ensure that we merge before running parts 1 or 2" | lboshuizen: `\| (alo, ahi) :: rest when lo <= ahi + 1L -> …`; `_.startInclusive` property shorthand | no |
| 19 | Koka, Roc | [junpls](https://github.com/junpls/aoc25/blob/HEAD/day05.kk), [arnemart](https://github.com/arnemart/aoc/blob/HEAD/2025/05/5.roc) | 38, 45 | Koka: **running mark with `var res` and `var largest`** over `ranges.sort()`; Roc: a `List.walk` that clips each range to start after the previous end | Koka `sort()` on pairs is the default order; Roc `Str.to_u64 s ?? 0` (a bad line becomes 0) | no |
| 20 | Gleam, Elixir, Clojure | [tilltheis](https://github.com/tilltheis/adventofcode-2025-gleam/blob/HEAD/src/day05.gleam), [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day05/day05.gleam), [bmatcuk](https://github.com/bmatcuk/adventofcode2025/blob/HEAD/day05/src/day05.gleam), [lasseebert](https://github.com/lasseebert/advent_of_code_2025/blob/HEAD/lib/advent/day_05.ex), [narimiran](https://github.com/narimiran/aoc2025/blob/HEAD/clojure/src/day05.clj), [genmeblog](https://github.com/genmeblog/advent-of-code/blob/HEAD/src/advent_of_code_2025/day05.clj) | 24–83 | sort and fold | tilltheis: `range_inclusive` returns `Error(Nil)` for `from > to`; genmeblog merges with `(<= a na b)`, so touching ranges stay apart (the count is the same) | no |
| — | Stitchwort | `aoc/src/Aoc/Day05/Day05.sw` + `Proofs/Part2.sw` | 25 (program) + 23 (tests); 162 (proofs; 214 lines, 20 theorems) | sort by start, fold into merged ranges, latest first | parse by classifying each line; `Range` from `Aoc.Common`; `solvePart1` is the puzzle's sentence | **yes**: `solvePart2Correct`, for every database, against a puzzle-literal brute force; no axiom, total |
| — | Stitchwort, community shapes | scratch `variants.sw`, `exhaustive.sw`, `edge.sw` | 4–7 per shape | running mark, end-sorted fold, sweep, derived-`Ord` merge | §4 | no (agree with the brute force on 4,096 small lists) |

Also in the count, and not in the table because they repeat these patterns: Lean ianclement's
sibling files and acarapetis's part 1; the Clojure CodeFarmer (a pairwise merge to a fixpoint
with `count` as the check) and genmeblog; Elixir ryoung786; Gleam houli (a `range` module with
`merge_list`) and bucsi. Classified only by counting sorts, maxima and folds, not read through:
mbacarella, FizzyElt, aguluman, jelaby, Casper-Guo, jrmcnair, Zenor27, bmatcuk, ryoung786 and
GuillaumedeVolpiano. I did not use devcordde's Day-05 folder (several unrelated languages, other
people), and Dessertion, benjaminfjones, a2435191, andorp, DavidMazarro, mfornet, joek13 and
yshui have no day 5 file in their repositories **[checked: tree listings]**.

All rows are **[checked]**: fetched and read, except cells marked **[cited]** and the files named
above as only classified. I ran none of them.

**Correctness notes from reading** **[inferred, not run]**:

- Hath995's `lteRange` compares the **end** (`left.1 <= right.1`), and `problem5_2` merges
  neighbours with `IsOverlapping`, which is false for touching ranges, so its merged list can
  hold ranges that touch; the count is unaffected. It marks the method `decreases *`, so the
  loop is not proved to terminate; the author says "Not quite sure how to prove the existence of
  a fix point to dafny yet" **[cited]**.
- kim-em's `Range.size_eq` proves `r.hi - r.lo + 1 = r.hi + 1 - r.lo` for `r.lo ≤ r.hi`, the
  same truncated-subtraction fact our `Nat.addOne` calls work around.
- sdiehl's `NonOverlapping` is `r1.stop < r2.start` and its merge joins touching ranges
  (`next.start <= current.stop + 1`), so the output does satisfy it: the axiom is plausible, not
  wrong, only unproved.
- tenthmascot's `Range` is half-open and its sweep subtracts with `Nat` ("intentional Nat
  subtraction"); jorendorff's solution is half-open too (`last + 1`).
- The standard `Range` and `NumericRange` types were the reason for detours in Scala (lluque8,
  TheScown, bishabosha: "Using proper range objects didn't work at all with these particular
  ingredients so had to use tuples of Long&Long" **[cited]**); a range type that can't hold the
  ends is the same trap as a list of ids.

### 2.1 What I couldn't find

- **Unison, Coq/Rocq, Isabelle, F\*, Effekt, PureScript:** none in GitHub repository and code
  searches or the megathread. Repository searches by language returned no Coq, Isabelle or
  Dafny (language-tagged) repository for 2025; code searches with the words "fresh ingredient",
  "cafeteria" and "ranges ingredient" in `.v`, `.thy`, `.idr`, `.agda`, `.dfy`, `.kk` and `.roc`
  files returned nothing **[checked: `gh/search2.txt`, `gh/repos.txt`]**. Code search is
  rate-limited and not exhaustive.
- **Lean theorem searches** ("mergeRanges theorem", "overlap ranges sorted pairwise theorem
  fresh") found nothing beyond the files above.
- **Day 5 from some earlier authors:** DavidMazarro, mfornet and joek13 stop before day 5;
  Dessertion, benjaminfjones and a2435191 stop at day 3 or 4; andorp's repository stops at day 4.
- **Reddit itself:** not contacted; the megathread came from the Arctic Shift archive. Linked
  pastes (topaz) weren't decoded.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** Two requests to [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift): a
post search by time window (5 Dec 2025, 03:00–06:00 UTC), and
`/api/comments/tree?link_id=t3_1pemdwd&limit=25000` (1.9 MB). No requests to reddit.com
**[checked: saved in `arctic/`]**. Terms as in the day 1 note.

**What it holds.** "-❄️- 2025 Day 5 Solutions -❄️-" (post `1pemdwd`, recorded `num_comments` 764).
The tree has 844 comments in all: **559 top-level**, 8 of them `[deleted]`/`[removed]`, 529 of
the 551 live ones with a language tag and 22 without. 182 of the 551 have code inline
**[checked: `scripts/langs.py`]**.

**The landscape.** Tags counted once per comment and language; spelling variants merged:

| Language | Comments | | Language | Comments |
|---|---|---|---|---|
| Python | 134 | | Elixir, R, Zig | 8 each |
| Rust | 52 | | Gleam | 7 |
| C++ | 29 | | F#, Perl | 6 each |
| Java | 24 | | OCaml, Swift, Raku, Common Lisp | 5 each |
| Go | 19 | | Scala, Clojure, Awk, SQL | 4–5 each |
| JavaScript | 18 | | Scheme, Racket, Julia, Dart, PHP, Lua | 3–4 each |
| C# | 17 | | Uiua, Dyalog APL, J, Goal, Factor, Odin, Nim, Bash | 2 each |
| TypeScript | 16 | | BQN, K, Q, Dafny, Prolog, Janet, Emacs Lisp, Admiran, Nix, … | 1 each |
| Haskell | 15 | | | |
| C | 14 | | | |
| Ruby | 13 | | | |
| Kotlin | 12 | | | |

The functional or proof-oriented tags add up to 67 comments, 12% of the live ones (day 1: 82,
day 2: 66, day 3: 76). The count is lower than the recorded thread size (764) because the
archive's tree holds fewer top-level comments than Reddit's counter, which includes replies
**[inferred]**.

**Methods, megathread-wide** (regular expressions over all 551 live comments; "with code" means
the comment has code inline; the patterns are loose, so read these as rough) **[checked:
`scripts/methods5.py`]**:

| Pattern | Comments | With code |
|---|---:|---:|
| mentions sorting | 223 | 118 |
| merge, collapse, combine, union, consolidate | 234 | 89 |
| binary search or bisect | 48 | 11 |
| brute force, "expand", memory, "too big" | 57 | 22 |
| 64-bit, big integers, overflow | 39 | 24 |
| inclusive, adjacent, touching, singleton, off by one | 25 | 13 |
| duplicate, nested, "fully contained", same start | 26 | 10 |
| a sweep or "events" | 11 | 4 |
| says "wrong answer", "too low", "too high" | 8 | 1 |

**What I read.** All 67 functional comments (27 with code inline), and every array-language and
Dafny comment. The ones that add to §2:

| # | Language | Author / link | Notable |
|---|---|---|---|
| 21 | F# | [r_so9](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdn2qf/) | the running mark as a fold on `(count, prevHi)` with three cases and no merged list: `\| true, true -> count, prevHi`, `\| true, false -> count + hi - prevHi, hi`, `\| false, false -> count + hi - lo + 1L, hi` |
| 22 | F# | [mestar12345](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsglxh2/) | the sweep: `(st, 1) :: (en, -1)` events sorted by `(x, -y)`, a running sum, `List.pairwise`; classifies each line by `split.Length` (2 a range, 1 an id, 0 the separator), as we do |
| 23 | Haskell | [mstksg](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdon8x/), [MyEternalSadness](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdub9u/), [Foldzilla](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nse71v0/), [sondr3_](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsete3j/) | data-interval, `Data.Range` ("had to fix a small bug in Part 2 where I did not account for singleton ranges"); Foldzilla `foldl' mergeOverlapping [] . sortOn fst` with guards; sondr3_'s recursive `mergeOverlap` with `inside a b` and a guard, 23 µs for part 2 **[cited]** |
| 24 | Haskell | [danvk](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsfeb67/), [NeilNjae](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nserw3h/), [G_de_Volpiano](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nseg53y/), [vanZuider](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsg5szt/) | danvk splits every range at every endpoint and dedupes (`splitRange edges`, half-open "to make the split easy"); NeilNjae a pair of `foldr`s with `partition (overlaps range)`; vanZuider: "two bugs in my code that just so happened to cancel out in the example" |
| 25 | Clojure | [minikomi](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdpakx/), [darren](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdq2pl/) | an instaparse grammar for the two sections; `loopr` carrying `[cur-start cur-end]` and a total, i.e. the mark fold; darren: "Had a couple of edge cases it took me a while to think through" |
| 26 | OCaml, Racket, Scheme | [continuouslypenguin](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nseubby/), [raevnos](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsh92ly/), [pinoaffe](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsel9pk/), [runnerx4](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsduq5n/) | library-backed: Batteries' `ISet.add_range` ("almost feels like cheating"), Racket `data/integer-set` with `is-union` and `is-count`, a Guile "diet" tree (the paper "Diets for Fat Sets"); runnerx4: "wasted half an hour on < vs <=" |
| 27 | Dafny, Elixir, Gleam | [Hath995](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nselsa7/), [Chungus1234](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdzrw5/), [Dense-Virus-1692](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdxq0c/), [Chemical_Chance6877](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdrrao/) | Hath995: "A couple of interesting things left to prove or improve"; Chungus1234: "Holy based chunk_while"; Dense-Virus-1692: tried to expand every range into a set "but that just seemed to give up without any output", wrote `collision` and `union` instead; Chemical_Chance6877: "iterating over neighbours recursively in a language that doesnt support indexed lookups on array broke my brain" |
| 28 | Factor, Janet | [molochwalk](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsiguw8/), [Porges](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsvlnrb/), [veydar_](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nvq60ef/) | molochwalk: "union of ranges output a regular sequence which overflows the memory"; Porges: "`merge-into` has a very bad cond"; veydar_'s PEG `(sub (to :sep) (group (split "\n" (group :range))))` to cut the input at the blank line |
| 29 | Array languages | [ap29600 (K)](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsebcw1/), [0rac1e (J, Raku)](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nseynld/), [voidhawk42 (APL)](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsgxoss/), [Andreasnl (Uiua)](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nsdvm6f/), [anaseto (Goal)](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nseadmb/), [Daniikk1012 (BQN)](https://www.reddit.com/r/adventofcode/comments/1pemdwd/2025_day_5_solutions/nserfpy/) | K: "classic trick of sorting begins and ends together, takes 600μs" (a sweep as `0<+\1-2*grade<#begins`); J: `>./\ , /:~ 0 1 +"1 fresh` (a **running maximum** over the sorted endpoints); APL `⌈\`, Raku `.produce(&max)`; the answers are 3 to 5 lines |

Megathread comments outside the functional group that matter here, all **[cited]**: flwyd (Awk)
"a shorter range with the same start point could occur later in the input, wiping out my bigger
range"; RalfDieter (SQL) "I made the mistake of assuming things about the input and didn't
expect it having duplicate ranges from the start"; TheScown (Scala) "I intended to use the built
in NumericRange, but it can only store Int.MaxValue values (even for a range of Longs)";
_rabbitfarm_ (Prolog) "the large numbers were causing GNU Prolog to overflow"; tymscar (Gleam)
used `bigi` for part 1 "just to not have that as an issue"; Salusa (MUMPS) and gyorokpeter (q)
fold sorted ranges in a few lines.

**Notes from the megathread**:

- **As on days 1 to 3, several authors say they are learning the language** (woond3r on OCaml
  parsing, marconisdev, ___ciaran, FCBStar-of-the-South "feedback absolutely solicited"), so
  style is weak evidence; complaints are stronger.
- **The complaints:** `<` against `<=` (runnerx4); singleton, duplicate and enclosed ranges
  (MyEternalSadness, RalfDieter, Daniikk1012: "sometimes when computing an intersection of two
  ranges, one can be fully contained within another"); standard-library range types that cannot
  hold the values (Scala, Prolog); expanding the ranges into sets or lists (Gleam, Factor);
  vanZuider's `read` annotation: "Is there a more elegant way to parse a number than defining an
  anonymous function `(\s -> read s ::Int)` every time?"
- **Speed is not an issue** for the merge in any language: 23 µs (sondr3_, Haskell part 2),
  0.23 ms (Elixir), 0.79 ms (Common Lisp), 0.86 to 1.6 ms (Gleam), 2.2 ms (G_de_Volpiano), 3 ms
  (lboshuizen, F#), 4.58 ms (Elixir, part 1) **[cited]**.

## 3. Themes

### 3.1 Reading the two sections

| Approach | Who | Example |
|---|---|---|
| Split the text at `"\n\n"` and each half at `"\n"` | most Python, Lean, Elixir, Clojure, Scala, Racket | `input.split("\n\n")`; `splitOn "\n\n"` |
| Cut the lines at the first blank | Haskell (`break null`, `span`), Lean (`span (·.length > 0)`), OCaml, Scala `takeWhile` | `(rangeLines, _ : numLines) = break B.null ls` |
| Parser combinators or a grammar | Haskell (megaparsec), Lean (`Parsec`), Koka, Clojure (instaparse), Janet (PEG), Idris (`Text.Parser`) | `sepBy1 (match NewLine) rangeGrammar` |
| A format string, interpolator or pattern | glguy, Scala | `[format\|2025 5 (%u-%u%n)*%n(%u%n)*\|]`; `case s"$i-$j"` |
| **Classify each line by what it is** | us, adomani, ngrislain, mestar12345, tilltheis (as a second step) | `if split.Length = 2 then range else id` |

**Stitchwort today.** `parseDatabase` is two `filterMap`s: a line is a range if `Range.parse`
reads it, an id if `Text.toNat` does, and is skipped otherwise. The blank line needs no
special case and there is no splitting helper, which is the shape four other solutions also
arrived at. The cost is leniency: a malformed line vanishes instead of failing, where bjornestol
returns an `Except` with "Interval … of wrong form!", adomani panics and Roc's `?? 0` makes it a
zero. Days 1 to 4 here are equally lenient (D437). The example is a `"""` text block
`.lines`, which is how the tests read it **[checked]**.

### 3.2 The methods

| Method | How it works | GitHub (of 56) | FP megathread (of 67) |
|---|---|---:|---:|
| Sort by start, fold into a merged list | extend the latest range or start a new one | ~30 | ~15 |
| Running mark, no list | keep the largest end so far and a count; add what is new | ~5 | ~3 |
| Sweep over events | sort `(start, +1)` and `(end + 1, -1)`; add the lengths where depth is positive | ~4 | 1 |
| Interval-set library or own set | `union` or `insert` into a structure that keeps ranges disjoint | ~6 | ~8 |
| Insert one range at a time, or merge pairs to a fixpoint | pairwise overlap tests, `partition`, repeat until stable | ~7 | ~4 |
| Sort by end, fold from the right | only the head can overlap; no `max` | 1 | 0 |
| Split at every endpoint | disjoint pieces, deduplicated | 0 | 1 (danvk) |

**[checked: counted by hand from the files and comments; approximate, and the boundaries between
rows are mine, e.g. a "running range" in a loop counts as the mark when it keeps no list. The
megathread column counts only comments whose method I could see; the rest link to code, and a
few files I only classified by grep are in the GitHub column]**

The array languages (about a dozen comments) mostly write the mark or the sweep without naming
it: sort the starts and ends, take a running maximum or a cumulative sum, subtract.

**The mark, as a program.** It is the only method here that is shorter than ours and has no data
structure to explain. Its correctness argument is, in words, "sorted by start, so everything
below the largest end so far is already counted; add what lies above it". Four people (jorendorff,
PP6464, junpls, r_so9) wrote it in four languages without saying why it works; RossPaterson's
comment on his end-sorted fold is the only one-sentence invariant on a short program.

**Stitchwort today.** All four shapes ran first time **[checked: `variants.sw`]**:

```
-- the running mark: jorendorff, PP6464, junpls, r_so9 (4 lines)
def markStep (st: (Nat, Nat)) (r: Range): (Nat, Nat) :=
  let (mark, total) := st
  (Nat.max mark (r.to + 1), total + (r.to + 1 - Nat.max r.from mark))

def markCount (ranges: List Range): Nat := (ranges.sort |> .foldLeft markStep (0, 0)).snd
```

```
-- RossPaterson: sort by END, foldr; no max, no + 1 (6 lines)
def addByEnd (r: Range) (rest: List Range): List Range :=
  match rest with
    | Nil => [r]
    | Cons h t => if r.to < h.from then Cons r rest else Cons { from = Nat.min r.from h.from, to = h.to } t

def byEndCount (ranges: List Range): Nat :=
  ranges.sortBy (a b => Nat.compare a.to b.to) |> .foldRight addByEnd [] |> .sumBy Range.size
```

The mark is one pass with a state of two numbers and no `Range` rebuilt; the end-sorted fold
works because the new range's end is at most every end already merged, so it can only reach the
head. Both are right on all lists of three ranges with ends in 0 to 3, including inverted ranges
(`from > to`) **[checked: `exhaustive.sw`, 4,096 lists against `brute`]**. The sweep is right
only for well-formed ranges: with an inverted range the depth goes negative. Our theorem is over
every database, so a replacement has to keep the inverted case, and the mark fold's step is where
that is delicate (an inverted range still raises `mark` to `to + 1`, which is harmless because
`mark <= from` for every later range, but the proof has to say so) **[inferred]**.

### 3.3 Where people lost time

| Trap | Who | Ours |
|---|---|---|
| `<` against `<=` on touching ranges (`4-6` after `1-3`) | runnerx4 ("wasted half an hour"); genmeblog, Hath995 and jpyamamoto decided not to merge touching ranges, which leaves the count unchanged | `r.from <= last.to + 1`: merged; test "touching ranges merge"; any count agrees |
| singleton range `5-5` | MyEternalSadness | in scope; no test names it (`edge.sw`: passes) |
| shorter range with the same start after a longer one | flwyd (Awk), a bug that "wiped out my bigger range" | `Nat.max last.to r.to`; no test names it (`edge.sw`: passes) |
| duplicate ranges | RalfDieter | in scope; no test names it (`edge.sw`: passes) |
| one range inside another | Daniikk1012, spencerwi (six overlap cases written out), Foldzilla | test "nested range" |
| a range whose `from` is above its `to` | tilltheis (`Error(Nil)`), jorendorff (`h : lower <= upper` in the type), Hath995 (`expect 0 < start <= end`), dupuisf (`failure`) | `Range.size` is `to + 1 - from` truncated, 0 for an inverted range; in the theorem's scope; no test |
| ids and answers above `Int` | Scala (`NumericRange` and `Int.MaxValue`), GNU Prolog, bigi in Gleam, `Long` in Scala and F# (`1L` everywhere) | `Nat` is unbounded |
| materialising the ids | Dense-Virus-1692 (Gleam), molochwalk (Factor) | `Aoc.Common.Range.ids` does exactly that (D438); `Day05.sw` doesn't use it |
| two bugs that cancel on the example | vanZuider; "assuming things about the input" (RalfDieter) | the real answers are tests (`Tests/Input.sw`), and the theorem |

The common thread is "the example doesn't show it": the puzzle's four ranges don't touch twice,
repeat, or start together. Our proof removes the need to think of each, but the tests are the
documentation a reader sees first, and natewhite345's `#guard` list (touching, reversed, nested)
is the model for what they should say.

### 3.4 Library breadth

| Helper | Seen in | Stitchwort |
|---|---|---|
| sort pairs or records by their natural order, start first | Idris (`sort l`), Koka (`sort()`), Haskell (`sort rs`), Elixir tuples, Julia | derived `Ord` on a record: `ranges.sort` **[checked: `variants.sw`]**, `List.sortSorted` proves it sorted |
| sort by a key (`sortOn fst`, `sort-by first`, `sortBy(_.start)`, `Seq.sortBy _.lower`) | about a dozen files and comments | `List.sortBy (a b => Nat.compare a.from b.from)`; `Ord.byKey` needs a key that tells values apart (an injectivity proof), which `from` does not |
| `foldLeft`, `foldRight`, `any`, `count`, `sumBy`, `scanLeft` | everyone | all present |
| `flatMap` / `concatMap` / `mapcat` | ngrislain, tenthmascot, jelaby, frutjus, shnarazk, danvk | **missing**: `List has no field or function flatMap`; `.map f \|> .concat` works **[checked: `sweep` in `variants.sw`]** |
| split the lines at the blank line (`splitOn`, `break`, `span`, `splitf-at`, `partition`) | most | `List.splitBy` exists; day 5 doesn't need it |
| tuple projections: `fst`/`snd`, `.1`/`.2`, `_1`, `.0` | everyone who didn't use a record | `.fst`/`.snd`; `.0` is `E-PARSE: expected a field name after .` **[checked]**; the parsed model uses a record |
| `min`, `max` on numbers | everyone | `Nat.min`, `Nat.max`, and `Ord.min`/`Ord.max` |
| an inclusive range type with `contains`, `size`, `disjoint?` | Elixir `Range`, Scala `NumericRange` (fails above `Int`), Raku `Range`, Lean `Std.Range` (half-open), Factor `[a..b]` | `Aoc.Common.Range` (ours; `ids` materialises a list) |
| interval sets (`IntervalSet`, `integer-set`, `ISet`, FRange, `IntervalUnion`, `Box`, `Diet`) | about a dozen | none; see D436 |
| binary search on a sorted array (`bisect`, `lookupLE`, a vector index) | natewhite345, beefyhalo, mvorber, aaronjw1, Raku, 11 megathread comments with code | none (`List` only, `List.get` is O(n)); day 5's part 1 is 190,000 `contains` calls, so no need |
| a running state in a `var` loop | junpls (Koka), vanshjangir (Lean `let mut`), Julia, Common Lisp, MUMPS | not now (D299); the mark fold is the recursion-free way to write it |

Pattern guards come up (8 files: lboshuizen, mbottini and FizzyElt's `when`, stanosphere,
beefyhalo and Foldzilla's `|`, FCBStar-of-the-South's `case … if`, nikola's Elixir), and every one
is the same merge test: `| (alo, ahi) :: rest when lo <= ahi + 1L -> …`. Our `absorb` matches
`Cons last earlier` once and puts the test in an `if`, with `Cons r merged` for the else branch,
so nothing is written twice and day 5 adds no evidence for SW-237. The `sortBy (a b => …)` lambda
is where Scala's `_.start`, F#'s `_.startInclusive` and Lean's `(·.1)` would show (SW-222); with
`ranges.sort` the need disappears. `solvePart1`'s `db.fresh.any (r => r.contains id)` is the other
spot (SW-228).

### 3.5 Proofs and automation

What the community proved for day 5:

- **Hath995 (Dafny): the count, over sets.** The statement is the method's own `assert answer ==
  |original|`, where `original = Union(sortedRanges)` is a ghost `set<nat>` and each range is
  `set x | r.0 <= x <= r.1`:
  ```dafny
  lemma RangeSizeEqual(r: (nat, nat))
      requires r.0 <= r.1
      decreases r.1 - r.0
      ensures rangeSize(r) == |rangeSet(r)|
  ```
  The loop merges one overlapping neighbour pair at a time under the invariant `Union(sortedRanges)
  == original`; `UnionLemma` shows the merge keeps the union; `SortedAreDistjoint` and `UnionSum`
  turn "no neighbour overlaps" into a sum of sizes. Most of the 319 lines are its 16 lemmas, and
  Dafny's solver fills in the arithmetic. It relies on `{:axiom} IsTotalOrder` and `decreases *`
  and leaves part 1 unverified, and the set comprehension and `|s|` come for free, which is what
  our `countFresh` (the ids from 0 to the largest end, counted) and `coveredTop` replace
  (16 lines) **[checked: read the file; not run]**.
- **kim-em, sdiehl, jorendorff (Lean): the statements, not the proofs.** `mergeRanges_preserves_coverage`
  is our `mergeCovers`; `mergeRanges_disjoint` is our `Stacked`; jorendorff's cardinality
  statement is our `solvePart2Correct`. All are `sorry` or `axiom`.
- **acarapetis (Lean): the invariant in the type.** `RangeSet` carries `Pairwise (a.upper <
  b.lower)`; `RangeSet.ofRanges.build` takes `h_rest`, `h1` and `h2` and discharges each recursive
  call with `grind` or `grind [List.pairwise_cons]`. It is the same bookkeeping as our `Stacked`,
  `LoAtMost` and `Fits`, written as function arguments (about 40 lines against our 17-line
  program), and the plain-program-plus-separate-proofs layout is the project's rule, so this is a
  contrast, not a gap.
- **ianclement (Lean): a proof as an argument for termination only**, `h : List.Sorted RangeStartLe
  ranges`, to justify the recursive call; the result has no theorem.
- **Totality without proofs:** natewhite345's `termination_by haystack.length` (binary search),
  bjornestol's `termination_by xs => xs.length`; against `partial def` in vanshjangir and
  josephmate, jpyamamoto's `{-# TERMINATING #-}`, and Dafny's `decreases *`.

**Where ours stands.** The statement is the strongest anyone wrote down and is the only one that
is proved without an axiom, over every database (empty and inverted ranges included),
total, in 162 lines and 20 theorems, which `aoc` checks in about 0.4 s. Its cost, as day 5's friction
notes said, shows in three places, re-checked now:

- **Arithmetic bookkeeping** (§1 item 4): `mergedContains` is 11 lines of a three-way case split
  with 13 lemma calls; `absorbStacked` is 19 with a `calc` through `Nat.addOne`. Lean's `omega`
  closes the same shape in one line (kim-em's `Range.contains_max` is `simp only […] at *; omega`).
  `Nat.addOne` appears three times, to move between `to + 1` and `Succ to`.
- **The `if` in `absorb`** still has to be spelled out in each lemma
  (`match e: Nat.leq r.from (last.to + 1) with | True => … | False => …`, three times), where
  Dafny's `if` is transparent to the solver.
- **The sort comparison** is written on ten lines (§1 item 5); the two friction items about lambda
  inference and about no rewriting are fixed (`calc … := rewrite …` is in use).

Nothing the community did removes these, except automation (D434) and a smaller program (D432).

### 3.6 Speed of the obvious programs

Times are wall-clock for the whole command, including checking (one run each, on a laptop that
was also running other work):

| Program | `stitchwort run` | `run --js` |
|---|---:|---:|
| Committed program (`Aoc.Day05.main`) | 0.30 s | 0.31 s **[checked]** |
| All four variants in one file (`variants.sw`, each part 2 once) | 0.15 s | 0.34 s **[checked]** |
| sondr3_, Haskell, part 2 | 23 µs (parser 417 µs, part 1 266 µs) **[cited]** | |
| lboshuizen, F# | 3 ms **[cited]** | |

None of the methods is slow at 190 ranges and 1,000 ids, and `run` is no slower than `--js` here,
unlike days 1 and 3's brute forces. The 190,000 `contains` calls of part 1 and the merge are
under the process's start-up cost **[inferred]**.

## 4. Side by side

The merge, as ours, as the shortest fold (lboshuizen, F#), and as the end-sorted fold
(RossPaterson, Haskell):

```
-- Stitchwort (Day05.sw)
def merge (ranges: List Range): List Range :=
  ranges
    |> .sortBy (a b => Nat.compare a.from b.from)
    |> .foldLeft absorb []
    |> .reverse

def absorb (merged: List Range) (r: Range): List Range :=
  match merged with
    | Nil => [r]
    | Cons last earlier =>
      if r.from <= last.to + 1
      then Cons { from = last.from, to = Nat.max last.to r.to } earlier
      else Cons r merged
```

```fsharp
// lboshuizen (F#)
let merge ranges =
    let fold acc (lo, hi) =
        match acc with
        | (alo, ahi) :: rest when lo <= ahi + 1L -> (alo, max ahi hi) :: rest
        | _ -> (lo, hi) :: acc
    ([], ranges |> List.sortBy fst) ||> List.fold fold
```

```haskell
-- RossPaterson (Haskell): sorted by upper bound, folded from the right
addrange :: Range -> [Range] -> [Range]
addrange r [] = [r]
addrange (lo1, hi1) ((lo2, hi2):rs)
  | hi1 < lo2 = (lo1, hi1):(lo2, hi2):rs
  | otherwise = (min lo1 lo2, hi2):rs
```

The three are the same program. Ours spells the order as a lambda where F# writes `fst` and
Haskell `sortOn snd`, and has the fallback in an `if` where they have a guard, with nothing
written twice either way. With `ranges.sort` the first line shrinks to `ranges.sort`
(D430).

The proof statements:

```dafny
// Hath995 (Dafny, proved with {:axiom} IsTotalOrder, decreases *)
assert answer == |original|;   // original = Union(sortedRanges), a set<nat>
```
```
-- Stitchwort (Proofs/Part2.sw, proved, total)
def countFresh (db: Database): Nat :=
  let top := db.fresh.foldLeft (m r => Nat.max m r.to) 0
  List.range (top + 1) |> .count (id => db.fresh.any (r => r.contains id))

theorem solvePart2Correct (db: Database): solvePart2 db = countFresh db
```
```lean
-- jorendorff (Lean, a comment, sorry)
theorem solve2_correct (freshRanges : Array Range) :
  let S := {id | ∃ r ∈ freshRanges, r.start ≤ id ∧ id < r.stop}
  ∃ hS : S.Finite, solve2 fresh = hS.toFinset.card
```

Ours and jorendorff's say the same thing; ours spells "finite" as "below the largest end". The
statement a shorter program would have to meet is the same one, `solvePart2 db = countFresh db`;
the mark fold is the candidate for it (§3.2, D432):

```
def markStep (st: (Nat, Nat)) (r: Range): (Nat, Nat) :=
  let (mark, total) := st
  (Nat.max mark (r.to + 1), total + (r.to + 1 - Nat.max r.from mark))
```

## 5. Candidate features, ranked by value over effort

Kinds: **sugar** (syntax only), **library**, **tooling**, **language** (elaboration or kernel),
**program** (a change to our day 5 code), **tests**.

| Rank | Candidate | Kind | Value | Effort | Evidence | Ticket |
|---|---|---|---|---|---|---|
| 1 | **Sort with the derived `Ord` (`ranges.sort`) and drop the stale `Range.from a` workarounds** in `Day05.sw` and `Proofs/Part2.sw` | program | small to medium: ten lines with one lambda gone; the proof says "sorted" once | small (one lemma: derived order implies `from <=`) | §1 item 5, §3.4: `p_lambda.sw`, `p_lambda2.sw`; Idris, Koka, Elixir, Haskell do the same with pairs | none; with the next Day05 touch (SW-224) |
| 2 | **Day 5's arithmetic lemmas as the acceptance example for SW-101** (linear `Nat` arithmetic: `omega`) | tooling | high for every AoC proof (55 of 162 lines here) | large (SW-101) | §3.5: kim-em, acarapetis (18 `grind`), natewhite345 | SW-101 (backlog): a note only |
| 3 | **Edge-case tests from the community's bugs**: same start (shorter second), duplicate, singleton | tests | low: the theorem covers them, the tests are the documentation | trivial | §3.3, `edge.sw` (12 tests, all pass); natewhite345's `#guard`s | none; fits SW-224 |
| 4 | **A proof lane on two shorter programs for part 2: the running mark and the end-sorted fold** | program, proof | medium to high if one proves shorter, zero if not | medium (one lane) | §3.2: 4 and 6 lines against 12; both match the brute force on 4,096 lists | none; one new ticket if approved |
| 5 | **`List.flatMap`** (into the SW-235 batch) | library | low: 6 files; `.map f \|> .concat` works | trivial | §3.4 | SW-235 |
| 6 | **A one-line warning on `Range.ids`** (it materialises every id; day 5's ranges hold 10^13) | docs | low | trivial | §3.3: two authors hit the expansion | none |
| — | Half-open `Range` in the parsed model | program | low: would remove three `Nat.addOne` and the `+ 1` **[inferred]**, but moves the puzzle's wording out of the spec | small | §3.5; jorendorff, tenthmascot, ianclement, glguy use half-open | **not now** (D433) |
| — | An interval-set type in `Std` | library | low: the merge is what we prove | large | about a dozen libraries | **no** (D436) |
| — | Reject lines that are neither range nor id (Abort) | program | low | small | bjornestol, adomani | **no** (D437) |
| — | Pattern guards (SW-237), `_` sections (SW-222), dot receiver (SW-228), `maxBy` and friends (SW-235) | language, library | unchanged | — | the guard in 8 files is always the merge test, which `absorb` doesn't duplicate; no `maxBy`, `dropWhile` or `tails` here | parked; no change |
| — | Local mutable variables (Koka `var`, Lean `let mut`) | language | low | large | junpls, vanshjangir, Julia | **not now** (D299) |

Why this order:

- **Rank 1 is cleanup with evidence from three sides**: the compiler can do it today, the
  community's pairs sort that way, and the lambda friction that justified the workaround is gone.
  It touches proofs, so it needs the lemma that the derived order implies `from <=` (about eight
  lines).
- **Rank 2 is the only large item and already exists as SW-101.** What day 5 adds is a
  small, concrete acceptance test: four lemmas whose proofs should shrink to a line each.
- **Rank 4 is the interesting speculation.** The running mark is the shortest program in the
  study and the end-sorted fold removes `max` and `+ 1` (three `Nat.addOne`, `Nat.leMaxLeft`,
  `Nat.leMaxRight`, `Nat.leqMaxAbove` and `mergedContains`'s `h2`). Whether either gives a shorter
  or clearer *proof* is unknown: I did not try, and the mark fold's invariant ("some range
  already held ends at `mark - 1` and starts no later than the next range") has an inverted-range
  corner (§3.2). Hence a lane, with the current program and proof kept unless one wins.
- **Ranks 3, 5 and 6 are trivial.**

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D430 | Sort with the derived `Ord` (`ranges.sort`) in `merge`, `stack` and the proofs, and drop the stale `Range.from a` workarounds? | [yes; small, with the next Day05 touch] |
| D431 | Add three unit tests named for the community's bugs (same start with a shorter second range, a duplicate range, a singleton range)? | [yes; three one-liners, they pass today] |
| D432 | Run one proof lane on a shorter part 2: the running-mark fold and the end-sorted `foldRight`, each proved equal to `countFresh`, keeping whichever reads and proves shorter (the current program stays if neither does)? | [yes, one small lane, after the higher-priority work; not now] |
| D433 | Move `Range` to half-open `[from, to)` in the parsed model? | [no for now; the puzzle says "both ends included" and the theorem is about the parsed model; revisit with D432's numbers] |
| D434 | Record Day 5's `mergedContains`, `absorbLo`, `absorbStacked`, `coveredTop` (55 of 162 lines) on SW-101 as the acceptance example for a first linear-arithmetic tactic? | [yes; a note on the ticket, no new work] |
| D435 | Add `List.flatMap` to the SW-235 list batch? | [yes] |
| D436 | Add an interval-set type (`IntervalSet`-style) to `Std`? | [no; the day's task is proving the merge, and no second ranges day needs it] |
| D437 | Make `parseDatabase` reject lines that are neither a range nor an id (with the Abort ability) instead of skipping them? | [no; days 1 to 4 are equally lenient, and the real answers are tests] |
| D438 | Add a one-line comment on `Range.ids` that it lists every id, so it is for small ranges only? | [yes] |

---

**Status** (short form, 22 October 2026): D430 derived-`Ord` sort, pending; D431 edge tests,
pending; D432 shorter-program proof lane, pending; D433 half-open ranges, not now; D434 SW-101
acceptance note, pending; D435 `flatMap` into SW-235, pending; D436 interval set, no; D437 strict
parse, no; D438 `Range.ids` comment, pending. Unchanged by day 5: D296 operator sections and
D297 text patterns not now, D299 local mutable variables not now, SW-101 backlog, SW-222, SW-228,
SW-235 and SW-237 parked.
