# AoC 2025 day 9: community solutions in other languages

**Date:** 29 October 2026. **Ticket:** SW-876 (D1610). **Our version:** finished before this
note: `aoc/src/Aoc/Year2025/Day09/` (SW-13, 24 October), both parts proved for every list of red
tiles. So unlike days 1 to 8, this note compares finished code: length, readability, speed, and
what is proved at what cost. The puzzle and our history are in `docs/aoc-2025.md` ("Day 9: movie
theatre rectangles" and "## Day 9"). In short: about 500 red tiles join, in order, into a closed
loop of straight green lines, and the tiles inside the loop are green too. Part 1 asks for the
largest rectangle with two red tiles as opposite corners. Part 2 asks for the largest one made
only of red and green tiles. The input is `aoc/inputs/2025/day09.txt`: 496 tiles, coordinates
1,579 to 98,471. The answers are 4,756,718,172 and 1,665,679,194. (`docs/aoc-2025.md` says
495 tiles, but `wc -l` misses the last line, which has no newline; `grep -c .` gives 496.)

The labels are as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Where things are:

- **Scratch area:**
  `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/day9/`.
  The fetched files are in `gh/files/`, the megathread JSON in `arctic/`, and the Stitchwort
  scratch project in `proj/`.
- **Committed copies:** the scripts and the Stitchwort scratch programs are in
  [aoc-day09-community/scripts/](aoc-day09-community/scripts/). The per-file method table for the
  functional files is [aoc-day09-community/classify-fp.tsv](aoc-day09-community/classify-fp.tsv).
- **Binary:** `target/release/stitchwort`, built from this worktree at `eda4edb4` with
  `nix develop -c cargo build --release -p stitchwort-cli`.
- **Timings:** wall-clock seconds from `scripts/rb.py`, one run each after one warm-up, on the
  machine that built the binary. They include process start-up, so treat them as rough, to a
  factor of about 1.5.

## 1. Summary

I fetched day 9 solutions from **104 GitHub authors**, one per author. 25 of them write in proof
or dependently typed languages: 16 in Lean 4, 2 in Idris 2, 2 in Roc, and one each in Agda,
Dafny, Koka, Admiran and Newt. The rest are Haskell, OCaml, Scala, F#, Gleam, Elixir, Clojure,
Elm, Racket, Common Lisp and Lily. I read the part 2 logic of 97 of them: I read the 25
proof-language files myself, and two reader agents read 72 functional ones against a fixed
rubric (§2.1). I also read the r/adventofcode Day 9 megathread through the Arctic Shift archive
(§2.2): 304 top-level comments, 31 of them in functional or array languages, plus one in Newt.
There was no Coq/Rocq, F\*, Isabelle or Unison solution in either source.

Stitchwort compared with them:

1. **We are the only ones who proved part 2, or even part 1's answer.** Of the 25
   proof-language authors, only kim-em has theorems: seven in all. Five are small facts
   (`rectangleArea_ge_one`, `rectangleArea_comm`, three about `isOnSegment`). The other two,
   `getSignificantYs_contains_minY` and `_maxY`, end in `sorry`. None of the seven says what
   the answer is. Hath995's Dafny proves two `ensures` for part 1's helpers, and its
   `problem9_2` is `return 4;`. jorendorff left two `bisect_correct` statements commented out
   with `sorry`. BrianNormant's Idris checks `intersection` on fixed segments by `Refl`. Six of
   the 25 have no part 2 at all **[checked: read every file; `grep` for theorem, lemma, ensures,
   sorry, Refl]**. Our `part1Correct` and `part2Correct` hold for every input. On this
   dimension Stitchwort is far ahead, with nobody near it.
2. **Most of the community's part 2s are not correct in general, and the authors mostly know
   it.** 30 of the 84 authors with a part 2 use the edge test alone (`EDGE`): a rectangle
   passes if no line of the loop crosses its open interior. 17 more add one inside test on a
   point (`EDGE+IN`). 4 more hard-code the input's shape (§3.1). On 5,000 random small loops,
   checked against a flood fill of the real tiles, `EDGE` gives a wrong answer on 354 and
   `EDGE+IN` on 57. Our method was wrong on 2, and those 2 come from how the spec reads the
   puzzle, not from the program (finding 5) **[checked: `scripts/methods9.py`]**. The puzzle
   input is shaped so that the shortcuts work: all three give 1,665,679,194 on it. Several
   authors say so: "assumption: green lines never touch (true for my input)" (nikola-benes),
   "that's not really lawful, there could be two adjacent parallel lines" (merlinorg),
   "Grid compression assumes no adjacent coordinates occur" (sim642) **[cited: files]**.
3. **Length: the shortcut programs are much shorter than ours; the general ones are not.**
   NerdyPepper's Haskell does both parts in about 15 lines with the edge test. Our program is
   54 code lines (141 with comments): about 14 for parsing and part 1, and about 40 for part 2. The edge test in
   Stitchwort is 10 lines (`sw/Edge.sw`), so the gap is the method, not the language. Among the
   general solutions, ours is the shortest I found. It is a little shorter than tenthmascot's
   Lean (88 lines) and well under khuepr123's Haskell (122 lines, the same method), but it
   leans on helpers that Std gained for day 9: `PrefixSums`, `List.dedup`, `List.indexOf` and
   `List.pairs`, about 25 lines between them (§4).
4. **Speed: we are slow, and the ranking is clear.** Our program takes **2.0 s** under `run`
   (2.9 s when run from `aoc/`) and **1.0 s** under `run --js`. Of that, about 0.6 s is
   start-up and loading the day 9 module and its imports, before any work. A
   CPython port of the same method takes 0.20 s, so CPython is about 7 times faster
   on the actual work. Compiled functional
   solutions report 6 ms (alex800121's Haskell sweep), 100 ms (Tnixc, OCaml), 300 ms (Newt,
   compiled to JS) and 644 ms (MyEternalSadness, Haskell). Some report seconds or minutes:
   lboshuizen's F# takes 5 s, TheScown's Scala about 200 s, and Philippus's Scala "around 1,5
   hr" **[checked: our timings; cited: theirs]**. So we are well behind compiled functional
   code and behind Python, but ahead of the brute-force solutions (§5).
5. **The proof is only as good as the spec's reading of "inside", and that reading is a
   choice.** The spec calls a tile inside when a ray from it crosses the loop an odd number of
   times: the interior of the polygon through the tile centres. Suppose two lines of the loop
   run side by side, one tile apart. A pocket of tiles can then be walled in by loop tiles
   (a flood fill can't reach it) and still lie outside that polygon. The spec calls such a
   pocket outside, and a flood-fill reading calls it inside. This happened on 2 of 5,000
   random loops. On the real input the two readings agree on every cell of the compressed floor
   **[checked: `scripts/spec9.py`, `scripts/pocket9.py`]**. The puzzle text doesn't settle the
   question **[inferred]**. Many community programs simply assume the case never arises (finding 2).
   We don't assume it, but the spec should say which reading it takes (D1620).
6. **The proof cost about 5 lines for each line of program.** The proof is 283 code lines
   (409 with comments) plus a 21-line spec, against a 54-line program. Std also gained 188
   lines of lemma files and about 30 lemmas in existing files. `check --no-cache` of the proofs
   takes 3.0 s. That is about a third of day 8's 840 proof lines. Nobody in the community paid
   that cost, so I can't compare it with another proof of the same thing **[checked:
   `scripts/classify9.py` on copies of our files; the Std figures are cited from
   `docs/aoc-2025.md`]**.
7. **Readability: ours explains itself best, but the code reads clumsier than the best
   Haskell.** Our comments explain why compression works, which no community file does as
   fully. jorendorff's Lean comes closest. Against that, our code has five small named helpers
   (`isBetween`, `isBetweenHalfOpen`, `touchesRow`, `crossesRightOf`, `Floor.outsideRow`), and
   it reaches into pairs with `line.fst.x` and `line.snd.y`. NerdyPepper's Haskell
   pattern-matches `away ([lx, ly], [lx', ly'])` in the argument. The `.fst`/`.snd` style is
   partly forced by the proofs, because pattern lambdas are opaque to them (day 8 gaps §5.1)
   **[inferred]**.

The ranked improvements are in §6.2, and decisions D1620 and D1621 in §7. The two with the most
value for the effort:

- Pin the spec's reading of "inside" with a comment and a test on a pinched loop (D1620).
- Find out why loading the day 9 module costs 0.4 s on every `run` (D1621).

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker (`scripts/classify9.py`).
None of the community programs was built or run. I ran my own ports of their methods (§3.1, §5).
The part 2 categories:

- **EDGE**: reject a rectangle if a loop line passes through its open interior, and accept it
  otherwise.
- **EDGE+IN**: EDGE, plus one point of the rectangle (its centre, a corner, or a tile just
  inside) tested by a ray cast.
- **COMPRESS-FILL**: compress the coordinates, classify each compressed cell by a flood fill or
  a ray, then check the rectangle's cells one by one or with a 2D prefix sum.
- **PERIM**: every perimeter tile of the rectangle (or every compressed one) is inside.
- **SWEEP**: a line sweep keeping intervals.
- **SHAPE**: uses the particular input shape, a large disc with a thin horizontal notch cut
  in. These solutions only try rectangles with a corner at the notch.
- **OTHER** and **NONE**: as named.

### 2.1 GitHub

**How I found them.** I took the 100 repositories cited in the day 5 to 8 notes, listed each
one's tree with `gh api`, and fetched the day 9 file (`scripts/find9.py`, `scripts/fetch.py`).
`gh search code` over 23 extensions with puzzle words found 8 more (`scripts/search9.py`), and
`gh search repos` by proof language found 4 more Lean authors (`scripts/repos9.py`). I fetched
the files that Reddit comments linked to as well. All 116 files came from
raw.githubusercontent.com.

**Proof and dependently typed languages (25 authors), read in full by me:**

| Language | Author / link | Lines | Part 2 method | Proofs |
|---|---|---|---|---|
| Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day09.lean) | 202 | OTHER: per rectangle, the "significant" rows (`getSignificantYs`), each row segment checked by a ray-cast `isInsidePolygon` | 7 theorems: area ≥ 1 and symmetric (by `omega`, `split`), three about `isOnSegment`, two `sorry`; none about the answer |
| Lean 4 | [jorendorff](https://github.com/jorendorff/advent-of-code/blob/HEAD/2025/day09/Day09/Basic.lean) | 197 | COMPRESS-FILL: `qsortOrd`/`eraseReps` key lines, ±1 strokes on vertical edges, then `columnPartialSums` and `partialSums` give the inside map, and a "skyline" stack finds rectangles | `bisect_correct` stated and commented out (`:= by sorry`); `Fin.wrappingSucc` carries "n is nonzero"; `panic! "diagonal line detected"` |
| Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day09.lean) | 88 | COMPRESS-FILL: compress, DFS from `(0, 0)` to remove the outside, then the rectangle's compressed boundary `.all (· ∈ inside)` | no |
| Lean 4 | [shnarazk](https://github.com/shnarazk/advent-of-code/blob/HEAD/Lean4/Y2025/Day09.lean) | 95 | COMPRESS-FILL: `HashSet` compression with no gap cells, then a flood fill | no |
| Lean 4 | [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day9.lean), [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day9.lean), [vanshjangir](https://github.com/vanshjangir/AoC/blob/HEAD/2025/day09.lean), [gyk](https://github.com/gyk/aoc2025-lean/blob/HEAD/Aoc2025/Day09.lean) | 79–116 | EDGE+IN: sdiehl tests the two other corners with `isInsideOrOnBoundary`, then `!segments.any (segmentCrossesRect …)` | no |
| Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day9_2.lean), [eutro](https://github.com/eutro/aoc2025/blob/HEAD/Aoc2025/Day09.lean) | 47, 58 | EDGE: acarapetis `cuts (rectangle p q) poly`; eutro `rects.find?` over a sorted list | no |
| Lean 4 | [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day9.lean), [frutjus](https://github.com/frutjus/aoc2025/blob/HEAD/day9/part2.lean) | 110, 108 | OTHER: bjornestol checks the turn direction at each corner (`checkInside`), then edge crossings; frutjus requires that no red tile lies strictly inside | `partial` (frutjus) |
| Lean 4 | adomani, josephmate, xcnwf, RussellEmerine | — | NONE: `def part2 … := sorry` (adomani), `let result := 0` (josephmate), `exact "0"` (xcnwf), `println! "Task: TODO"` (RussellEmerine) | — |
| Idris 2 | [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day9/Solution.idr), spikedoanz | 253, 8 | EDGE+IN: `Double` determinants for segment intersection, `pointInside`; spikedoanz is a stub | `intersection_T1 = Refl` and four more: tests run by the type checker |
| Agda | [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day09.agda) | 132 | COMPRESS-FILL: compress, `floodFill` under `{-# TERMINATING #-}`, then every compressed cell of the rectangle `member … inside`; comment: "This can be improved with a summed-area table" | no |
| Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/9/Problem9.dfy) | 71 | NONE: `method problem9_2 … { return 4; }` | `ensures \|AllPairs(xs, i)\| == ((\|xs\| * (\|xs\|-1))/2)` and `ensures \|xs\| > 0` for the parser |
| Roc | [charlespierce](https://github.com/charlespierce/advent-code-2025/blob/HEAD/Solutions/Day09.roc), [wiseodd](https://github.com/wiseodd/aoc-2025/blob/HEAD/roc/day_09.roc) | 132, 96 | EDGE+IN (`pointInPolygon` on the tile just inside a corner), EDGE | no |
| Koka | [junpls](https://github.com/junpls/aoc25/blob/HEAD/day09.kk) | 41 | EDGE: `intersects-any` over vertical and horizontal lines | no |
| Admiran | [taolson](https://github.com/taolson/advent-of-code/blob/HEAD/2025/day09.am) | 99 | OTHER: each side of the rectangle must extend inward from an "anchor" segment, and no segment may cross it | no |
| Newt | [dunhamsteve](https://github.com/dunhamsteve/newt/blob/main/aoc2025/Day9.newt) (Reddit ds101) | 79 | EDGE+IN: `isect` with strict `<`, then a winding count of the vertical lines right of `t + 1`; "I'm assuming the winner isn't a single row/column" | no |

**[checked: read each file's part 2]** Newt is Steve Dunham's dependently typed language in the
style of Idris. It compiles to JavaScript **[unverified: from its repository's description, not
checked here]**. Its author's experience matches ours (§5): "My original solution did a slow
qsort of the boxes (it's a functional language and the sort used lists) and took 1.8s. I changed
this to run through all of the possible boxes without sorting and it went down to 300ms"
**[cited: megathread]**.

**Functional languages (72 authors read).** Two reader agents classified them by the rubric
above, file by file. Their notes are in `classify-fp.tsv`; I spot-checked 6 against the files
(beefyhalo, merlinorg, sim642, khuepr123, rolandtritsch, danvk). I also fetched 7 more files
(FichteFoll, andete, anntnzrb, bbangert, bjorng, ryanbreen, scottbale) and only ran the regex
markers over them, so they are left out of the counts.

| Category | Proof langs (25) | Functional (72) | Total (97) | Examples |
|---|---:|---:|---:|---|
| EDGE | 4 | 26 | **30** | NerdyPepper's shape: beefyhalo, sondresl, lboshuizen, merlinorg, nikola-benes, narimiran, wisq, phibr0, tilltheis, … |
| EDGE+IN | 7 | 10 | **17** | Andrew-42, GuillaumedeVolpiano, TheScown, b-valdez, bjoli, devries, sdiehl, … |
| COMPRESS-FILL | 4 | 5 | **9** | with a 2D prefix sum: khuepr123, rolandtritsch, KacperKopiec, sim642, jorendorff; per cell: tenthmascot, shnarazk (Lean and OCaml), jpyamamoto |
| PERIM | 0 | 4 | 4 | danvk, miguel-negrao ("now with a really correct result checked by Z3"), albertdahlin, sreetamdas |
| SWEEP | 0 | 2 | 2 | mstksg (`IntervalSet`s per x interval), alex800121 |
| SHAPE | 0 | 4 | 4 | markpattison (notch indices 248/249), mtravers ("the data has a very particular shape"), Casper-Guo, arnemart |
| OTHER | 4 | 14 | 18 | a boundary offset one tile outward (JavadocMD, jelaby, gulllberg, tomas81508); libraries (DuckDB `ST_Within`, `java.awt` `Path2D`, SkiaSharp `SKRegion`); glguy's box algebra; chrg127 splits the polygon into rectangles |
| NONE | 6 | 7 | 13 | stubs and part 1 only |

**[checked: proof languages; cited: the reader agents' table, spot-checked]**

The general methods are COMPRESS-FILL, SWEEP, the outward-offset boundary (if it is traced
right), the libraries, and glguy's box algebra. They make up about 25 of the 84 authors with a
part 2 **[inferred: from the categories]**. Exactly our method is a compressed floor with a ray
parity per cell plus a summed-area table: khuepr123 (scanline parity, `cumulative sum mod 2`)
and rolandtritsch ("the usable region is exactly the polygon's filled interior including its
boundary", with gap blocks between key lines). glistering_knight on Reddit, who is khuepr123,
calls it a "Generalized O(n^2) solution using even (vertical) raycasting for closure detection
and 2d prefix sum for rectangle checking" **[cited]**.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** I made two requests to [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift).
The first was a post search for 9 December 2025, 04:50 to 05:20 UTC
(`/api/posts/search?subreddit=adventofcode&after=…&before=…`). It returned "-❄️- 2025 Day 9
Solutions -❄️-", id `1phywvn`, with `num_comments` 450. The second was
`/api/comments/tree?link_id=t3_1phywvn&limit=25000` (1.3 MB). I made no requests to reddit.com
**[checked: `scripts/arctic.py`, saved in `arctic/`]**. The terms are as in the day 1 note §2.2.

**What it holds.** 304 top-level comments; 299 are live and 293 carry a language tag. Only 65
have code inline, so most link out **[checked: `scripts/langs9.py`]**. The tags: Python 86,
Rust 39, C 27, C# 17, Go 13, JavaScript 12, Java 10, TypeScript 7, Haskell 7, Kotlin 6, Zig 5,
F# 4, R 4, Scala 3, Common Lisp 3, Uiua 2, and one each of Gleam, OCaml, Clojure, Scheme,
Racket, Lily, K, Q, BQN, Janet, Prolog, Lua, Newt and a few others. There is no Lean, Idris,
Agda, Dafny, Coq, Koka or Roc comment. The 31 functional, proof and array comments are 10% of
the live ones; day 8 had 52 of 380.

**Method words** across the 299 live comments, as upper bounds (a word can match in a comment
about something else) **[checked: `scripts/langs9.py` regexes]**:

- "intersect" or similar: 75;
- compress: 36;
- ray cast or parity: 26;
- flood fill: 24;
- doubts about generality ("not general", "only works because", "edge case", "concave"): 22;
- shapely or another geometry library: 19;
- point in polygon: 18;
- talk about the input's shape ("circle", "pac-man", "notch", visualise): 16;
- prefix sum or summed-area table: 11;
- sort by area: 11.

**What the functional comments add:**

| Author | Language | What they say |
|---|---|---|
| [NerdyPepper](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt2seri/) | Haskell | "managed a short solution": `p2 poly = maximum [area p p' \| p <- poly, p' <- poly, not (intersects p p' poly)]` with a 5-line `away` test. Foldzilla and JustinKasteleijn credit it. It is the EDGE method, and the most copied |
| [glistering_knight](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/ntv028u/) | Haskell | our method; "Spent hours wondering what went wrong (its the binary search... can't believe i screwed up binary search)" |
| [danvk](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt4x90s/) | Haskell | checks the perimeter only, "true for this problem because none of the xs or ys are exactly 1 apart". On our input 1 pair of columns and 2 pairs of rows *are* 1 apart, though the lines on them are far apart in the other direction **[checked: `scripts/pocket9.py`]** |
| [mvorber](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt6n13a/) | F# | "exploiting the fact that there are no 'touching' edges in the input data"; sorting by area first gave "around 2x-3x speed up" |
| [alex800121](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/ntafmlx/) | Haskell | a line sweep keeping y ranges; "Runs in 6ms" |
| [MyEternalSadness](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt31gtj/) | Haskell | part 1 7.22 ms, part 2 643.93 ms; descending sort, stop at the first valid one |
| [lboshuizen](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt33drb/) | F# | EDGE; "Runs in 5 secs, parallel version on github in ~ 1s" |
| [sim642](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt2kqak/) | Scala | compressed it first to *look* at it, then used the flood-filled compressed grid; "~8.5s" |
| [Daniikk1012](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/ntbrd12/) | BQN | "Initially I tried doing stuff with polygons/winding order, but that turned out to have way too many edge cases"; then 2D prefix sums |
| [RudeGuy2000](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/ntg5l0i/) | Racket | "took me two days", "a few seconds", "does 100% (well, maybe 99.9%) work with any kind of input" |
| [TheScown](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/ntiwc52/) | Scala | EDGE "allows lots of invalid rectangles", so a perimeter check too; "~200s and is a terrible solution" |
| [Andreasnl](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt2y48x/) | Uiua | part 1 in one line, `/↥≡(/×+1⌵/-)⧅<2 ⋕°csv`; part 2 "looked at the data and picked out two candidate rectangles by hand" |
| [ak-coram](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt76wdh/) | Common Lisp | "DuckDB with the spatial extension feels a bit like cheating" |
| [ap29600](https://www.reddit.com/r/adventofcode/comments/1phywvn/2025_day_9_solutions/nt3335e/) | K | compression and a flood fill in 8 lines, inline |

**[cited]** Paste links (topaz) for Q (gyorokpeter) and F# (r_so9) weren't decoded. The
Prolog author did part 2 in Perl instead ("Once again I found the second part to be easier in
Perl").

## 3. Which part 2s are right

### 3.1 The shortcuts, tested

`scripts/methods9.py` puts three checks next to a ground truth:

- **EDGE**: NerdyPepper's `away` test, as written.
- **EDGE+IN**: EDGE, plus a ray-cast test of the rectangle's centre.
- **COMPRESS**: our method, ported to Python: key columns and rows (each red one and the one
  after it), ray parity per cell, and a summed-area table.

The ground truth is a flood fill from outside on the real tiles, with no compression and no ray
rule: a tile the fill can't reach is red or green. The script runs these on 5,000 random
rectilinear loops (2 to 5 corners each way on a 10 by 10 floor, kept only when no tile is on two
lines that aren't neighbours) **[checked: run with seed 9]**:

| Check | Wrong on | Smallest wrong loop | It says | Truth |
|---|---:|---|---:|---:|
| EDGE | 354 of 5,000 | `(0,0) (2,0) (2,6) (6,6) (6,9) (0,9)`: an L; the rectangle from `(2,0)` to `(6,9)` lies outside the L, but no line crosses its interior | 35 | 30 |
| EDGE+IN | 57 of 5,000 | `(0,0) (1,0) (1,8) (2,8) (2,1) (8,1) (8,9) (0,9)`: two lines side by side at x = 1 and x = 2 cut every big rectangle, though the tiles between them are all on the loop | 63 | 81 |
| COMPRESS (ours) | 2 of 5,000 | `(1,0) (7,0) (7,2) (2,2) (2,8) (6,8) (6,3) (7,3) (7,9) (1,9)`: a pinched pocket, §3.2 | 21 | 70 |
| the spec, uncompressed | the same 2 | the same | 21 | 70 |
| COMPRESS against the spec | 0 of 5,000 | — | | |

So EDGE fails in two ways. It accepts a rectangle that lies outside a concave loop, which is
NerdyPepper's shape (and sim642 writes "Assumes largest area won't be outside"). It also rejects
a rectangle that a pair of side-by-side lines cuts through (merlinorg's "two adjacent parallel
lines"). EDGE+IN fixes the first failure but not the second. On the real input all three checks
give 1,665,679,194, because the loop is a large disc with a thin notch cut in, and the longest
lines are the notch's two sides, 92,258 and 92,472 tiles long **[checked]**. The input makes the
shortcuts work. The SHAPE solutions go further and use the notch directly: markpattison
"visualized in Excel first", and mtravers writes "the data has a very particular shape, so do a
special-purpose solution" **[cited]**. tenthmascot's general Lean solution says of itself: "does
not handle common would-be edge cases, but it should work for all AoC inputs" **[cited]**.

Our COMPRESS port agrees with the spec on all 5,000 loops. That is an independent check of what
`allKeysIsSpec` proves, that compression changes nothing. Our 2 failures are failures of the
spec's reading, not of the program.

### 3.2 What "inside" means: the pinched pocket

`scripts/spec9.py` draws a loop of the same kind: the first one found, in a run of 2,000 loops,
`(4,4) (3,4) (3,7) (5,7) (5,3) (9,3) (9,9) (0,9) (0,0) (4,0)`. The marks are `#` on the loop, `o`
inside by the spec, `.` outside, and `?` outside by the spec but walled in:

```
#####......
#ooo#......
#ooo#......
#ooo######.
#oo###ooo#.
#oo#?#ooo#.
#oo#?#ooo#.
#oo###ooo#.
#oooooooo#.
##########.
```

The line down column 4 and the line down column 5 run side by side in rows 3 and 4. The two
`?` tiles are walled in by loop tiles, so no tile path leads out. In the polygon through the
tile centres, though, they connect to the outside through the zero-width gap between columns 4
and 5. Our spec counts crossings of a ray, so it calls them outside. A rectangle that covers
them then fails, so the largest is 35 by the spec and 70 by the flood fill. The puzzle says "all of the tiles inside this
loop … are also green". That reads naturally either way, and its example has no such pocket
**[inferred]**. On the real input it doesn't matter. `scripts/pocket9.py` compresses with each
red column and row and its two neighbours, so that a one-tile gap is kept. On that 735 by 743
floor, the ray rule and the flood fill agree on every cell **[checked]**.

Who else meets this? Every EDGE solution and most EDGE+IN ones assume it away, and several say
so (§2.2). The COMPRESS-FILL solutions with no gap cells (KacperKopiec, khuepr123, shnarazk,
sim642) pick the flood or the parity reading without saying which **[cited: reader notes;
inferred]**. Our spec at least states a reading: it is in the spec's own comment ("A tile off
them is inside the loop when a ray from it to the right crosses the loop an odd number of
times"). What it doesn't say is that the reading differs from the walled-in one, or where they
differ (D1620).

## 4. Length and readability, side by side

Code lines, by the same rule for everyone:

| Solution | Lines | General? | Note |
|---|---:|---|---|
| NerdyPepper (Haskell, Reddit) | about 15, both parts | no (EDGE) | the most copied |
| lboshuizen (F#) | 15 | no (EDGE) | `Array.Parallel.choose` |
| Stitchwort, EDGE (`sw/Edge.sw`) | 10 for part 2 | no | reuses the program's part 1 and parser |
| tenthmascot (Lean 4) | 88 | yes **[inferred]**: it keeps a gap cell between key lines, and panics if two are 0 apart | "takes ~20s on my input!" |
| rolandtritsch (Scala 3) | 121 | yes | our method, with gap blocks |
| khuepr123 / glistering_knight (Haskell) | 122 | yes | our method |
| jpyamamoto (Agda) | 132 | yes | `TERMINATING` flood fill; no summed-area table |
| jorendorff (Lean 4) | 197 | yes **[unverified: the skyline step wasn't read in full]** | difference array and partial sums |
| kim-em (Lean 4) | 202 + 7 theorems | yes **[unverified]** | the only theorems, none about the answer |
| **Stitchwort** (`Day09.sw`) | **54** (141 with comments) | yes, and proved | Std has `PrefixSums` (about 18 lines), `dedup`, `indexOf`, `pairs` |

**[checked: `scripts/classify9.py`]** Counting Std's helpers as if written inline, we would be at
about 80 lines, still among the shortest general solutions **[inferred]**.

The core of each, as written:

```haskell
-- NerdyPepper (Haskell): EDGE, both parts in a dozen lines
p2 poly = maximum [area p p' | p <- poly, p' <- poly, not (intersects p p' poly)]
intersects [x, y] [x', y'] = not . all away . pairs
  where
    pairs (p : ps) = zip (p : ps) (ps ++ [p])
    away ([lx, ly], [lx', ly']) =
      (max lx lx' <= min x x') || (min lx lx' >= max x x')
        || (max ly ly' <= min y y') || (min ly ly' >= max y y')
```

```lean
-- tenthmascot (Lean 4): compress, DFS the outside away, test the compressed boundary
def part2 (points : Array Point) : Nat :=
  let new_points := part2.compress points
  let boundary := HashSet.ofList <| part2.boundary new_points
  let grid := part2.grid_without_boundary new_points
  let inside := boundary.insertMany (part2.DFS grid)
  points.zip new_points |>.all_pairs.filter (
    fun ((_, (x₁, y₁)), (_, (x₂, y₂))) =>
    (part2.boundary #[(x₁, y₁), (x₁, y₂), (x₂, y₂), (x₂, y₁)]).all (· ∈ inside)
  ) |>.map (…) |>.maxI
```

```
-- Stitchwort (Day09.sw): key lines, outside cells, a summed-area table
def isRedOrGreen (lines: List (Tile, Tile)) (tile: Tile): Bool :=
  lines.any tile.isOnLine ∨ lines.count (crossesRightOf tile) % 2 == 1

def keyLines (values: List Nat): List Nat := values.append (values.map Succ) |> .sort |> .dedup

def solvePart2 (tiles: List Tile): Nat :=
  let floor := Floor.of tiles
  tiles.map floor.corner |> .pairs |> .filter floor.allRedOrGreen |> .map cornersArea |> largest
```

How they read, in my judgement **[inferred]**:

- **Ours reads better at the top level.** `solvePart2` is one pipeline, and `isRedOrGreen` is
  the puzzle's own rule in one line. `keyLines` is shorter than any other compression I read:
  tenthmascot needs 8 lines with a `panic!`, jorendorff 3 plus `bisect`. It is also the only
  one that brings the "+1" column in with no special case. Our records (`Tile`, `Floor`,
  `Corner`) name things that the others pass around as tuples.
- **Ours reads worse in the small.** `Floor.allRedOrGreen` spends 9 lines on min/max bounds and
  the `+ 1`, because `List.between lo hi` and `PrefixSums.block` take half-open ends.
  `crossesRightOf` and `isBetweenHalfOpen` say with `.fst`/`.snd` what Haskell says with a
  pattern in the argument. Five helpers of one line each, every one with a signature, make the
  program longer to scan than tenthmascot's. And a reader has to know that `.pairs` means "each
  with each later one".
- **Ours explains itself far better.** Our 60 comment lines explain why the key columns are
  enough. No other file does that. jorendorff comes closest ("Our basic approach is to compress
  the grid…").

## 5. Speed

### 5.1 Our program and the alternatives, in Stitchwort

All on `aoc/inputs/2025/day09.txt` (scratch project `proj/`, with the `aoc` sources linked in),
one warm run each, wall-clock seconds **[checked: `scripts/rb.py`]**:

| Program | What it does | `run` | `run --js` | Answer |
|---|---|---:|---:|---|
| `Hello.sw` | read the input, print its length | 0.19–0.21 | | start-up only |
| `Load.sw` | the same, plus one call to day 9's `area` | 0.59–0.64 | | loads `Aoc.Year2025.Day09` and its imports |
| `Parts.sw` `mainParse` | parse the 496 tiles | 0.59–0.62 | | so parsing itself is cheap |
| `Parts.sw` `mainPart1` | part 1: 122,760 pairs | 0.62–0.64 | | part 1 costs nothing above the load |
| `Parts.sw` `mainFloor` | `Floor.of`: 495 × 490 cells, 120,226 outside | 1.27 | | the floor is about 0.65 s |
| **`Day09.main`** | **both parts, the committed program** | **2.02** (2.93 from `aoc/`) | **1.01** | 4756718172, 1665679194 |
| `Edge.sw` | part 2 by EDGE, every pair | 5.91 | 1.44 | 1665679194 |
| `Sorted.sw` `mainEdge` | EDGE, pairs sorted by area descending, first that passes | 3.38 | 1.15 | 1665679194 |
| `Sorted.sw` `mainOurs` | our test, sorted, first that passes | 2.49 | 1.15 | 1665679194 |
| `Sorted.sw` `mainSortOnly` | sort the 122,760 pairs by area, take the first | 1.49 | 0.90 | 4756718172 |

What this says:

- **The program spends a third of its time before it starts.** Loading the day 9 module and its
  imports (Parse, PrefixSums, the List files) costs about 0.4 s, on top of 0.2 s of start-up.
  The checked results are cached. Why loading costs this much is **[unverified]**, and no
  ticket covers it (D1621). The 0.9 s difference between running from `aoc/` and from the
  scratch project is unexplained too **[unverified: my guess is that the larger project is
  scanned or loaded at start]**.
- **The summed-area table is the fast choice in Stitchwort.** EDGE does 122,760 × 496 line tests
  and takes 5.9 s, 3× our program's time. The usual trick of sorting by area and stopping at
  the first rectangle that passes brings EDGE to 3.4 s. It makes ours slower (2.5 s), because
  sorting 122,760 pairs costs about 0.9 s on its own, which is more than all our pair tests.
  ds101 found the same in Newt (1.8 s with the list sort, 300 ms without) **[cited]**.
- **`run --js` is 2 to 4 times faster than `run` here.** The biggest gap is on EDGE's tight
  `List.all` loop (5.9 s against 1.4 s). That fits SW-813: the interpreter spends about 6.5 ns
  per instruction, 20 to 100 times slower than Python on generated inputs.

### 5.2 Against the community

| Who | Method | Reported or measured time |
|---|---|---|
| alex800121 (Haskell) | line sweep | 6 ms **[cited]** |
| MyEternalSadness (Haskell) | sort desc, EDGE-like | 7.22 ms + 643.93 ms **[cited]** |
| Tnixc (OCaml) | edge test with a `Hashtbl` cache | 100 ms **[cited]** |
| CPython, my port (`methods9.py`) | **our method** | **0.20 s**, without start-up **[checked]** |
| **Stitchwort native executable** (`build --native`) | **ours** | **0.34 s** (0.02 s of it start-up) **[checked]** |
| dunhamsteve (Newt, compiled to JS) | EDGE+IN, no sort | 300 ms **[cited]** |
| kneegma (Clojure, babashka) | AABB, short-circuit | 390 ms **[cited]** |
| sreetamdas (Elixir) | PERIM, compressed | 268 ms (1.70 GB) **[cited: file]** |
| python-b5 (Lily) | EDGE | "just under a second" **[cited]** |
| **Stitchwort `run --js`** | **ours** | **1.0 s** **[checked]** |
| **Stitchwort `run --native`** | **ours** | **1.2 s** **[checked]** |
| CPython, my port | EDGE, EDGE+IN | 1.5 s each **[checked]** |
| **Stitchwort `run`** | **ours** | **2.0–2.9 s** **[checked]** |
| blacai (F#) | edge counting | ~4 s **[cited]** |
| lboshuizen (F#) | EDGE | 5 s; ~1 s in parallel **[cited]** |
| miguel-negrao (Haskell) | PERIM, continuous | 5.6 s **[cited: file]** |
| sim642 (Scala) | compressed flood fill, per cell | ~8.5 s (first version) **[cited]** |
| tenthmascot (Lean 4) | compressed DFS + boundary | ~20 s **[cited: file]** |
| tomas81508, gulllberg (Clojure) | offset boundary | 21.8 s, 29.8 s **[cited: files]** |
| TheScown (Scala) | EDGE+IN + perimeter tiles | ~200 s **[cited]** |
| Philippus (Scala) | PIP on every tile | "around 1,5 hr" **[cited: file]** |

Compiled natively, it is a different picture. `stitchwort build --native Aoc.Year2025.Day09.main` compiles all 177 function bodies `main` reaches (154 ms), and the executable runs both parts in 0.34 s (four runs, 0.33 to 0.37 s; 67 MB peak memory). A native build of `Hello.sw` runs in about 0.02 s, so about 0.32 s is the program's own work: about 7 times faster than `run` (2.2 to 2.4 s in the same session) and 3 times faster than `run --js` (1.0 to 1.1 s), and within about 1.6 times CPython's 0.20 s for the same method. `run --native` takes 1.2 s, because it still loads the checked modules and compiles before running **[checked: 29 October 2026, release build at c611cc78, four runs each from `aoc/`; inferred: the split of `run --native`'s time]**.

The plain verdict: on speed, Stitchwort sits in the middle of the community only because the
community includes a lot of slow brute force. With the same method, CPython is about 7 times
faster than our compute (0.20 s against about 1.4 s), and compiled Haskell or OCaml is faster
again by one to two orders of magnitude **[inferred: from the rows above]**. Under `--js` we are
fast enough that nobody would notice, and our run time didn't come from a clever trick. It came
from choosing the summed-area table, which the proof wanted anyway.

## 6. Proofs: what we proved, what it cost, what to improve

### 6.1 What is proved, and by whom

| | Stitchwort | kim-em (Lean) | Hath995 (Dafny) | jorendorff (Lean) | BrianNormant (Idris) | everyone else |
|---|---|---|---|---|---|---|
| Part 1 answer is the largest rectangle | **yes, every input** (`part1Correct`) | no | no (`\|AllPairs\|` count only) | no | no | no |
| Part 2 answer is the largest all red-and-green one | **yes, every input** (`part2Correct`) | no | no (part 2 is `return 4`) | no | no | no |
| Compression is faithful | **yes** (`allKeysIsSpec`) | `getSignificantYs_contains_minY/maxY`, both `sorry` | — | `bisect_correct`, commented out | — | — |
| Small facts | `largestIsLargest`, `isRedOrGreenNear`, `cellAt`, `redOrGreenSame`, … | area ≥ 1, area symmetric, three `isOnSegment` facts | parser length | `Fin.wrappingSucc` nonzero | 5 `Refl` tests of `intersection` | doctests, `#assert`, `#eval` |
| Termination | total, checked | not checked by me | not checked by me | `partial def` for the stack | `partial` | Agda `TERMINATING` on the flood fill; tenthmascot's DFS has fuel and `panic!`s when it runs out |

**[checked]** The cost on our side:

- the program, 54 code lines;
- a spec of 21 code lines;
- proofs of 283 code lines (409 with comments: Part1 13, Floor 84, Compress 154, Part2 32);
- 188 lines of new Std lemma files and about 30 lemmas in existing ones;
- a 3.0 s `check --no-cache` of the proofs.

`docs/aoc-2025.md` predicted "Nothing deep" to prove for day 9. That was wrong: the faithfulness
of compression (`Compress.sw`) is half of the proof. Nobody in the community stated it, let alone
proved it. Can another language prove the same with less effort? I found no attempt to measure
against, so it is **[unverified]**. Lean's `omega` and `simp` would do what our `omega` did, and
Mathlib has no ready rectilinear polygon theory that I know of **[unverified]**.

So, against the brief's question "proves more with less effort": nobody here proves more, and so
nobody proves it with less effort. The honest qualifier is §3.2. Our proof is relative to a spec
that picks one of two readings of "inside", and it doesn't yet say that it does.

### 6.2 Candidate improvements, ranked by value over effort

| Rank | Candidate | Kind | Value | Effort | Evidence |
|---|---|---|---|---|---|
| 1 | **Pin the spec's reading of "inside"**: a comment in `Spec.sw` saying it is the even-odd interior of the polygon through tile centres, that walled-in pockets beside side-by-side lines count as outside, and a brute-force spec test on the 10-corner pinched loop of §3.2 (answer 35 by the spec, 70 by the flood fill) | spec, test | makes the proof's claim exact; the one place where "proved correct" could mislead | small (a comment and a test, no proof change) | §3.2, `spec9.py` |
| 2 | **Find out why loading costs 0.4 s per `run`**, for a module whose check is cached (and why running from `aoc/` adds 0.9 s) | runtime / driver | 20–30% of day 9's wall time, and likely of every small AoC day | small to investigate; the fix is unknown | §5.1 `Hello` 0.2 s, `Load` 0.6 s |
| 3 | **Add day 9's data points to SW-813** (interpreter speed): `run` is 4× slower than `run --js` on EDGE's `List.all` loop, and sorting 122,760 `Nat`-keyed pairs costs 0.9 s | runtime | sharpens an existing ticket; no new work item | trivial | §5.1 |
| 4 | **Patterns in lambda parameters that proofs can see through** (day 8 gaps §5.1) | language | `line.fst.x` becomes `((a, b)) => a.x`; day 9 is a second day that wants it | already a known gap; no new ticket | §4 |
| 5 | **Half-open `List.between`/`PrefixSums.block` helpers that take inclusive corners** | library | removes the `+ 1`s in `Floor.allRedOrGreen` and the `hi + 1 - lo` the proofs carry (`docs/aoc-2025.md` pain points) | small, but it touches proved code | §4 |
| — | `Array` (SW-112), a geometry or interval library, a heap, a line sweep | library | none needed: the general method fits in lists and `Map`, and runs in 1 to 3 s | large | §5.1 |
| — | Sorting by area with an early exit | program | makes our program slower (2.5 s against 2.0 s) | — | §5.1 |

## 7. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D1620 | Day 9's spec reads "inside" as the even-odd interior of the polygon through tile centres. A walled-in pocket beside two side-by-side lines counts as outside; a flood fill of the tiles would count it as inside. Keep that reading and document it (a comment in `Spec.sw` and a brute-force test on the pinched loop), or change the spec to the flood-fill reading (a new spec and proof of `redOrGreen`)? | [keep the reading and document it with the test; the real input is unaffected, and the even-odd rule is the standard one] |
| D1621 | Open a backlog ticket to find out why `run` spends about 0.4 s loading a cached module and its imports (and 0.9 s more from `aoc/`), separate from SW-813's per-instruction cost? Add §5.1's numbers to SW-813 either way. | [yes, backlog; investigate before more interpreter tuning, because it is a fixed cost on every run] |

---

**Status** (29 October 2026): SW-876, this note, is done once reviewed. D1620 (the spec's
reading of "inside") and D1621 (the per-run loading cost) are pending. Unchanged: SW-112
`Array` (backlog, not needed again), SW-813 interpreter speed (backlog; D1621 adds data).
