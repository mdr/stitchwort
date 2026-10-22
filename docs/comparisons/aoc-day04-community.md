# AoC 2025 day 4: community solutions in other languages

**Date:** 22 October 2026. **Our version:** `aoc/src/Aoc/Day04/Day04.sw` (program: the grid as a
`Vec` of `Vec` cells, so it is rectangular by its type; a round removes every accessible roll by
adding the three rows column by column and walking along the row, `peelRow`; part 2 is `sweep`,
which goes down the grid and only looks again at rows that changed) and `aoc/src/Aoc/Day04/Proofs/`
(both parts correct for every grid, against a spec stated by position). `docs/aoc-2025.md` §6 and
"Day 4 (October 2026)" describe the program and the proofs. This note looks at what other people
wrote for 2025 day 4, in the wild, and asks what that suggests for Stitchwort. It follows the shape
of [aoc-day01-community.md](aoc-day01-community.md), [aoc-day02-community.md](aoc-day02-community.md)
and [aoc-day03-community.md](aoc-day03-community.md).

Labels, as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day4-community/sw/`,
run with the main checkout's `target/release/stitchwort` (built 22 Oct 2026, 09:03). Fetched
solutions are in `gh/` beside it, the megathread data in `arctic/`, the scripts in `scripts/`.

## 1. Summary

I read 62 files from GitHub (about 55 authors): 16 in Lean 4, 3 in Idris 2, one each in Agda and
Dafny, and 41 in Haskell, OCaml, F#, Scala, Gleam, Clojure, Elixir, Elm, Roc, Koka and Admiran
(§2). They are the day 3 authors' repositories, found by changing the day number in the path,
plus four hits from a code search (0xmycf, kim-em, andorp, natewhite345); GitHub's code-search
rate limit stopped further searching, so the set is not exhaustive. I then read the r/adventofcode
Day 4 megathread through the Arctic Shift archive: 538 live top-level comments, 90 of them in
functional, array or proof-oriented languages (37 with code inline), which I read in full.

1. **Nobody proved the puzzle. Our proof is the only one.** Of the 21 proof-assistant files (Lean,
   Idris, Agda, Dafny), six state any theorem, and none says an answer is right. andorp (Lean)
   proves that a position has at most 8 neighbours; kim-em (Lean) has seven `sorry`s, including
   "removing accessible rolls decreases the count"; bjornestol (Lean) spends about 60 lines
   of lemmas proving that `Array.set` keeps every row the same length, then ends in `partial def`; acarapetis
   (Lean) proves the loop terminates (`removeAccessibleNonIncreasing`, by `grind`). In the
   megathread, Hath995 (Dafny): "I do not even know where to begin to prove anything about
   cellular automata" **[checked: read the files]**. Ours proves, for every grid, that part 1 counts
   the accessible rolls and that the swept, marked, in-place part 2 equals a plain
   repeat-until-stable spec (132 theorems in `Proofs/`, checked in about 0.9 s) **[checked]**.
2. **Three comments say the thing our proof is about, without proof.** Removing accessible rolls
   in any order, even in place while scanning, gives the same end state: bilgincoskun (numpy:
   "it does not matter for the result so the grid can be modified in-place"), lucariomaster2
   (C++: "you can in fact delete them while marking without messing things up"), Meamoria
   (Kenpali: "it doesn't matter exactly which order the rolls are removed in") **[cited]**. This
   is the fact `sweep` depends on, and `Proofs/Core.sw` proves it (`endsAgree`: both processes end at
   the largest stable set, the grid's 4-core). I found no one else who proves it.
3. **The commonest shape is a set of coordinates; ours is the array-language shape.** About 25
   of the functional files and comments I read (hand count) keep the rolls as a `Set` or `Map`
   of coordinates and rebuild it each round (mstksg, lboshuizen, r_so9, NeilNjae, RossPaterson,
   spikedoanz, glguy, ...). Our window trick (the 3 by 3 block includes the roll, so "accessible" is `5 <=
   window`) is the one the array languages use: Dyalog `5>+/,⍵` with `⌺3 3`, Raku `... < 5`,
   Radiadorineitor's `5>≢∘⍸`, Mathematica's convolution kernel with a 100 in the centre. 14
   megathread comments say they reused their own grid library **[checked: regex, then read]**.
4. **Stitchwort writes the set shape first try; it is correct, and slow in rounds.** `sets.sw`
   (mstksg's shape: `Set (Int, Int)`, `accessible rolls = rolls.filter (...)`, `peel` with
   fuel) passed the example on its first run and gives 1397 and 8758 on the real input, in 16.7 s
   under `run` and 3.5 s with `--js`. A worklist version (glguy's shape, `wl.sw`: a list of
   positions to look at, a roll is removed when it has fewer than 4 neighbours and its
   neighbours are queued) takes 1.65 s and 0.75 s. The committed program takes 0.61 s and
   0.45 s **[checked, one run each]**. So the library's `Set` and `Map` are enough for day 4, and
   the premise of SW-112 (a native array, because day 4 needs O(1) grid access) does not hold
   today.
5. **One real gap in `Set` literals.** `def s: Set Int := Set.fromList [1, 2, 3]` is
   `E-TYPE-MISMATCH` (it wants `Set Int` and finds `Set Nat`); so is `Set.fromList [0, 0, 0, 0, 0]`,
   and `[(3, 3)]` at `Set (Int, Int)`. Passing: `[3]` at `Set Int`, `[(0, 1), (1, 0), (1, 1), (1, 2)]`
   and `[(2, 2)]` at `Set (Int, Int)`, and the same long lists directly at `List Int`. I did not
   find the rule. The set-of-coordinates shape needs `Int` for the negative neighbour offsets, and
   my tests of it with literals hit this (`plus`, `block` in `worklist.sw`; I wrapped them in a
   helper `pts (xs: List Pos)`) **[checked: `lit.sw`, `worklist.sw`]**.
6. **Neighbour-window combinators are the library gap that shows in our own program.**
   POGtastic ("`triplewise` ... zip them all together"), the stencil languages, and
   G_de_Volpiano's first attempt ("a sliding-window solve as you parse") all use "each element
   with its left and right neighbours". Ours writes it twice by hand, `roundFrom` and `peelCells`. A `Vec.around`
   (`pad`, a function of left, element, right) replaces both: the scratch `around.sw` has the
   same answers and the example test passes **[checked]**. Day 7's `fall` has the same shape
   **[inferred]**.
7. **Everyone's part 2 is "repeat until nothing changes", and the Lean authors want a measure.**
   About 122 of the 168 megathread comments with code loop or iterate until stable (regex, so
   rough); three Lean files use `termination_by` the roll count (acarapetis, tenthmascot,
   kim-em), and nine of the 21 proof-assistant files give up on totality (`partial` in four
   Lean and Idris files, `TERMINATING`, `decreases *`) or use fuel (sdiehl, BrianNormant,
   0xmycf). Ours uses fuel = number of rolls
   plus a lemma that it is enough. This is SW-199 (well-founded recursion), already in the
   backlog, and day 4 is more evidence for it.

The ranked candidates are in §5 and the decisions in §6 (D420–D428). The cheapest useful ones:

- fix the `Set`/`Map` literal typing (D420);
- add `Vec.around` and use it in Day04.sw, if the proofs shrink (D421);
- add non-square tests (D426), refresh stale timings (D428);
- and raise SW-199 (D422).

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker. "Proofs" means theorems
in the file, not tests. The table lists the solutions that add something; the others repeat the
patterns.

| # | Language | Author / link | Lines | Method | Notable | Proofs? |
|---|---|---|---|---|---|---|
| 1 | Lean 4 | [andorp](https://github.com/andorp/Lea-r-n/blob/HEAD/AoC2025/Day04.lean) | 274 | part 1 only; `Grid h w` with `Vector (Vector Cell w) h`, positions `Fin h × Fin w` | `Position` classified corner/edge/interior; neighbours by `shift?` returning `Option` | 9 lemmas (≤ 8 neighbours, `foldl` monotone) by `omega`/`simp`; no `sorry` |
| 2 | Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day04.lean) | 126 | `Array (Array Char)`, `getAt` with `Int` coordinates returning `'.'` off the grid | `termination_by countRolls grid`, `decreasing_by` from a theorem | **7 `sorry`**: `removeRolls_decreases_count`, `findAccessible_spec`, ... |
| 3 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day4_2.lean) | 70 | `Vector (Vector Bool w) h`; `finalGrid` recurses while the count changes | `termination_by g.occupiedCount`, `decreasing_by grind only [!removeAccessibleNonIncreasing]` | `removeAccessibleNonIncreasing` proved (`grind`); the answer is not proved |
| 4 | Lean 4 | [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day4.lean) | 124 | `Map` of `Array`s with row and column counts as fields; `Index map` is a pair of `Fin`s | "This is not imperative. I promise."; `partial def removeAllRolls` | 3 lemmas, `Array.set_retains_property` about 40 lines, only to keep rows the same length |
| 5 | Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day04.lean) | 31 | `HashSet (Int × Int)`; `cycle` filters; `repeat_cycle` | `if _h : new.size < old.size then repeat_cycle new else ...`, `termination_by data.1.size`; `List.padj8.countP` from a shared library | no |
| 6 | Lean 4 | [0xmycf](https://github.com/0xmycf/Advent-of-code/blob/HEAD/2025/day04/Day04.lean) | 90 | `Std.HashMap Point Bool`; fuel `100_000` | `abbrev Neighbours p := { ls // ls.length = 8 ∧ is_all_neighbours p ls }` (unused) | two `simp` lemmas about `Point` zero; one commented `sorry` |
| 7 | Lean 4 | [dupuisf](https://github.com/dupuisf/aoc25/blob/HEAD/Aoc25/Day04.lean), [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day4.lean), [stonarini](https://github.com/stonarini/AoC-2025/blob/HEAD/AoC2025/Day04.lean), [vanshjangir](https://github.com/vanshjangir/AoC/blob/HEAD/2025/day04.lean), [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day4.lean), [josephmate](https://github.com/josephmate/AdventOfCode2025/blob/HEAD/AdventOfCode2025/Day04.lean), [benjaminfjones](https://github.com/benjaminfjones/advent-of-code-2025/blob/HEAD/AdventOfCode2025/D4.lean), [frutjus](https://github.com/frutjus/aoc2025/blob/HEAD/day4/part2.lean), [adomani](https://github.com/adomani/advents/blob/HEAD/Advents/AoC2025/day04.lean), [natewhite345](https://github.com/natewhite345/aoc25/blob/HEAD/day4/Day4/Basic.lean) | 31–103 | nested loops; dupuisf: a worklist with `while` and a `Vector₂` | sdiehl: `removeAllAccessible g total (fuel)` with fuel `height * width`; dupuisf: parsing refuses a non-rectangular grid; vanshjangir and josephmate `partial` | no |
| 8 | Idris 2 | [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day4/Solution.idr), [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day4.idr), [Pengler38](https://github.com/Pengler38/AoC-2025/blob/HEAD/src/Day4.idr) | 51–96 | `Vect n (Vect m Roll)` with `Fin` coordinates (BrianNormant); `SortedSet (Int, Int)` (spikedoanz); list of lists with a set of removed positions (Pengler38) | `MAX_ITERATION = 1000` and `untilSameResult'` (fuel); spikedoanz `partial`; Pengler38 marks most functions `total` | no |
| 9 | Agda | [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day04.agda) | 67 | `Data.Tree.AVL.Map` from coordinates to neighbour counts; each round recounts | `{-# TERMINATING #-} part2` | no |
| 10 | Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/4/Problem4.dfy) | 122 | `set<(int,int)>` of removed positions; `parseInput` ensures every row has length `n` | `while nRemoved > 0 decreases *` (no termination proof); a lemma `ThereIsAMinimum` to turn a set of offsets into a sequence | the parser's postcondition and one lemma; nothing about the answer |
| 11 | Haskell | [glguy](https://github.com/glguy/advent/blob/HEAD/solutions/src/2025/04.hs) | 40 | `Set Coord`; part 2 is a **worklist** over a `Queue`: pop a position, if it is a roll with fewer than 4 neighbours remove it and queue its neighbours | `part2' (x :<| q) rolls | notMember | length ns < magic | otherwise`; doctests with 13 and 43; answers 1540, 8972 | no |
| 12 | Haskell | [RossPaterson](https://github.com/RossPaterson/advent-of-code/blob/HEAD/2025/Day04.hs), [mstksg](https://github.com/mstksg/advent-of-code/blob/HEAD/2025/AOC2025/Day04.hs), [NeilNjae](https://www.reddit.com/r/adventofcode/comments/1pdr8x6/2025_day_4_solutions/ns8aeiq/) | 16–50 | `Set Position`; `whileJust`, `unfoldr`, `iterate` + `dropWhile` | `S.size . fold . takeWhile (not . S.null) . unfoldr (Just . go)` (mstksg); `neighbours p = Set.fromList [p .+. d \| d <- corners ++ unitVectors]` | no |
| 13 | Haskell | [beefyhalo](https://github.com/beefyhalo/aoc/blob/HEAD/src/2025/04.hs), [nicuveo](https://github.com/nicuveo/advent-of-code/blob/HEAD/2025/haskell/src/Day04.hs), [PP6464](https://github.com/PP6464/AoC-2025-Haskell/blob/HEAD/src/Day04.hs), [GuillaumedeVolpiano](https://github.com/GuillaumedeVolpiano/adventOfCode/blob/master/2025/days/Day4.hs), [sondr3_](https://www.reddit.com/r/adventofcode/comments/1pdr8x6/2025_day_4_solutions/ns8jkak/) | 20–60 | a comonad grid (`extend`, `experiment`, beefyhalo); a `Grid Bool` with `pmap` (nicuveo); `State`; an `IntSet` that prunes only the neighbours of removed rolls (GuillaumedeVolpiano, 955 µs) | beefyhalo: `extend (\c -> if forklift g (pos c) then Empty else extract c) g`; sondr3_: `Map.mapAccumWithKey` and 186 ms | no |
| 14 | OCaml | [POGtastic](https://www.reddit.com/r/adventofcode/comments/1pdr8x6/2025_day_4_solutions/ns7kr8t/) | — | no coordinates: pad each row with `None`, `triplewise` the rows, `triplewise` each triple and zip, filter the `None`s | "Coordinates? I HATE coordinates! ... ran this in Haskell and F# before" **[cited]**; then `Seq.iterate` | no |
| 15 | F#, Scala, Clojure | [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day04.fs), r_so9, [sim642](https://github.com/sim642/adventofcode/blob/HEAD/src/main/scala/eu/sim642/adventofcode2025/Day4.scala), [lupari](https://github.com/lupari/aoc2025/blob/HEAD/src/main/scala/assignments/Day04.scala), [tschady](https://github.com/tschady/advent-of-code/blob/HEAD/src/aoc/2025/d04.clj), [genmeblog](https://github.com/genmeblog/advent-of-code/blob/HEAD/src/advent_of_code_2025/day04.clj) | 9–35 | `Seq.unfold` of "remove the accessible ones, report how many"; `iterate`; `@tailrec` | lboshuizen: 12 lines, `Set.filter (neighbors rolls >> (>) 4)`; tschady: `(iterate forklift-step)` over `[total last grid]`, stopping when two totals are equal | no |
| 16 | Elixir, Gleam | [nikola-benes](https://github.com/nikola-benes/aoc2025elixir/blob/HEAD/04.exs), [lasseebert](https://github.com/lasseebert/advent_of_code_2025/blob/HEAD/lib/advent/day_04.ex), [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day04/day04.gleam), [bmatcuk](https://github.com/bmatcuk/adventofcode2025/blob/HEAD/day04/src/day04.gleam), tymscar | 20–95 | a map of **neighbour counts**, decremented as rolls are removed (nikola-benes, bmatcuk, onrustigescheikundig's BFS) | `removed \|> flat_map(&n8/1) \|> filter(&Map.has_key?(ns, &1)) \|> Enum.frequencies \|> Map.merge(ns, fn _, r, c -> c - r end)`; Gleam: "how are you supposed to do such a puzzle in a functional way? ... Part two ran in about 15 minutes" **[cited]** | no |
| 17 | Dyalog APL, K, Q, J, Goal, Uiua | [voidhawk42](https://www.reddit.com/r/adventofcode/comments/1pdr8x6/2025_day_4_solutions/ns7cd89/), light_switchy, Radiadorineitor, ap29600, gyorokpeter, 0rac1e, jpjacobs_, anaseto, oantolin, Andreasnl, lost_in_a_forest | 1–10 | stencil over 3 by 3 windows, `5>+/,⍵`, until stable | `f←{⍵-⍵∧{5>+/,⍵}⌺3 3⊢⍵}; +/,p-f⍣≡p` (voidhawk42, the whole of both parts); Uiua `F ← ×⊸⬚0⧈(≤4⧻⊚)[3_3 1_1 1_1]` (Andreasnl); Goal `nbsum:2{+(x+0,-1_x)+1_x,0}/`: a separable window sum, rows then columns, like ours **[cited]** | no |
| 18 | Mathematica, Julia, Raku | birdnardo, WolfRushHour, sauntcartas, Aspen138 | 5–30 | `ListConvolve` with kernel `{{1,1,1},{1,100,1},{1,1,1}}`: a cell is a removable roll when the sum is 100 to 103; Julia `OffsetArrays` | `NestWhile[f, {map, 0}, UnsameQ, 2]`; Raku `@board[(... max 0) .. (... min ...); ...].sum < 5` | no |
| 19 | Common Lisp, Scheme, Janet | dijotal, dzecniv, runnerx4, veydar_, onrustigescheikundig | 10–50 | lists of coordinates (20 s for part 2), a hash table, a `grid-directions-with-diagonals` library | veydar_ wraps the in-place removal in a **generator** and takes until zero: `(take-until \|(= 0 $) (extractor g))`; dijotal's one "fun" bug: a destructive `delete-if` "removing your nextdoor neighbor before asking you how many neighbors you have" **[cited]** | no |
| — | Stitchwort | `aoc/src/Aoc/Day04/Day04.sw` + `Proofs/` | 60 (program) + 28 (tests); 893 (proofs, 132 theorems; 1,262 lines with comments) | `Vec` grid, `peelRow` per row, `sweep` with per-row marks, fuel = rolls | `type Grid = { height, width, rows: Vec (Vec Cell width) height }`; parse refuses a ragged grid | **yes**: both parts, every grid, against a position-by-position spec; the order-independence core argument |
| — | Stitchwort, community shapes | scratch `sets.sw`, `wl.sw`, `worklist.sw`, `around.sw` | 25–45 | set rounds; worklist; fuel unfold; `Vec.around` | §4 | no |

Also read and not tabled: Haskell (MyEternalSadness, vitelaSensei, stanosphere, Mysterious_Remote584,
G_de_Volpiano, danvk, vanZuider), OCaml (lukaskollmer, mbacarella, FizzyElt, KacperKopiec,
aguluman), Scala (bishabosha, jelaby, Casper-Guo), Elm (albertdahlin, maxhille, caseyWebb),
Gleam (houli, bucsi, tilltheis), Roc (0xErwin1, arnemart), Koka (junpls, HeikoRibberink), Admiran
(taolson), F# (munchler, mestar12345, jrmcnair, mattgallagher92), Clojure (darren, CodeFarmer,
narimiran), Raku (mschaap), Common Lisp, Gleam and Elixir links without code. Day 4 files for
Dessertion, a2435191, ianclement, lambdam, devcordde, RossPaterson's alternative and
nikola-benes's `04lin.exs` do not exist at the guessed path **[checked]**.

All rows are **[checked]**: fetched and read, except cells marked **[cited]**. I ran none of
the community programs.

**Correctness notes from reading** **[inferred, not run]**:

- bjornestol's, vanshjangir's and josephmate's part 2 call `partial def`; spikedoanz's
  `applyUntilFixedPoint` is `partial`; Hath995's loop is `decreases *`; jpyamamoto's is
  `TERMINATING`. All terminate on real input, because each round removes a roll or stops;
  none says so to the compiler.
- kim-em's `removeAllAccessible` has `decreasing_by exact removeRolls_decreases_count ...`,
  with that theorem `sorry`, so the termination argument is assumed.
- Hath995's `ltFour` counts `grid[y][x]` with `multiset{...}['@'] < 4` and excludes removed
  positions, so a removed roll no longer counts: the same semantics as ours.
- G_de_Volpiano first read the grid as walled ("the outer bounds were not accessible"): the
  off-grid-is-floor rule is the one that cost somebody a wrong answer. Ours is in the spec
  (`cellsOf`: "floor off it").

### 2.1 What I couldn't find

- **Coq/Rocq, BQN, Koka (day 4), Roc (day 4 in the megathread), Effekt, PureScript:** none in the
  megathread or in my searches. Unison: toomyem, a link to Unison Share only.
- **Any Lean or Idris proof about the answer.** Code searches for "theorem" with the puzzle's
  words found nothing beyond the files above. GitHub's code search rate-limited after four queries,
  so this is not exhaustive.
- **Reddit itself:** not contacted. Linked pastes (topaz) were not decoded, so about half the
  comments with a paste link are known by their prose only.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** Two requests to [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift): a
post search for r/adventofcode between 4 Dec 2025 04:00 and 08:00 UTC, and
`/api/comments/tree?link_id=t3_1pdr8x6&limit=25000` (1.8 MB). No requests to reddit.com
**[checked: saved in `arctic/`]**.

**What it holds.** "-❄️- 2025 Day 4 Solutions -❄️-" (score 25, recorded `num_comments` 701). The
tree has 797 comments in all: **546 top-level**, 8 of them `[deleted]`/`[removed]`, 521 of the
538 live ones with a language tag and 17 without. 168 have code inline **[checked:
`scripts/langs.py`]**. Fewer people post inline code than on day 3 (286 of 670): more comments
are only a link.

**The landscape.** Tags counted once per comment and language:

| Language | Comments | | Language | Comments |
|---|---|---|---|---|
| Python | 135 | | Elixir | 10 |
| Rust | 53 | | R | 9 |
| C++ | 23 | | Gleam | 8 |
| Go | 21 | | Zig | 8 |
| C# | 20 | | Common Lisp, OCaml | 6 each |
| JavaScript | 18 | | F#, Swift | 5 each |
| Java | 17 | | Scala, Perl, Uiua, Lua | 4 each |
| TypeScript, Haskell | 14 each | | Dyalog APL, Racket, Tailspin, Julia, Raku, SQL, Awk, Bash, Google Sheets | 3 each |
| C | 13 | | J, Q, Goal, K, Clojure, Scheme, Nim, Odin, Jq, ... | 1–2 each |
| Kotlin, Ruby | 11 each | | Dafny, Unison, Janet, Elle, Io | 1 each |

My functional, array or proof-oriented list (Haskell, Elixir, Gleam, Lisps, ML family, Scala,
the array languages, Dafny, Unison, Julia, Raku, Mathematica, Tailspin, Elle) comes to 90
comments, 17% of the live ones (day 3: 11%), 37 with code. The jump is the array languages: Dyalog
APL 3, Uiua 4, J 2, Q 2, Goal 2, K 1, Mathematica 2 **[checked: `scripts/fp.py`]**. No Lean, Idris,
Agda, Coq/Rocq, Koka, Roc, Elm or BQN tag this time.

**Methods, megathread-wide** (regular expressions over the 538 live comments; the code column is
the 168 with code inline; rough) **[checked: `scripts/methods4.py`]**:

| Pattern | Comments | With code |
|---|---:|---:|
| the eight neighbours (offsets, directions, "neighbours") | 142 | 83 |
| repeat until nothing changes (until, while, fixpoint, loop) | 63 | 27 |
| a set or hash set of coordinates | 73 | 34 |
| a grid as a map or dict | 89 | 49 |
| convolution, stencil, kernel, `scipy`, `ndimage` | 25 | 19 |
| numpy | 18 | 13 |
| complex numbers as coordinates | 25 | 14 |
| a queue, worklist or BFS | 21 | 8 |
| degree, decrement, topological | 11 | 5 |
| padding, border or bounds | 28 | 20 |
| in place or mutation | 16 | 9 |
| a time or speed is reported | 86 | 31 |

**What I read.** All 90 functional-group comments. The ones that add to §2 are in the table
(rows 11–19). Megathread comments outside the functional group, all **[cited]**: bilgincoskun,
lucariomaster2 and Meamoria on order independence (§1); Teem0WFT (Julia): "Set operations on
binary tuples would have been much much more efficient, now that I see other people's
solutions" (5.2 s, 172 million allocations); tobega: a relational-algebra variant "much slower",
and a version that looks only at the neighbours of removed rolls "even slower" in Tailspin
(copy on write); stanosphere: "This is like Conway's game of life but things can only die. Game
of death if you like."

**Notes from the megathread**:

- **The functional authors say the same two things:** that part 2 is where having no mutation
  hurts (Chemical_Chance6877, Gleam: "suddenly changing a part of the puzzle becomes expensive,
  because no mutability lol ... I resorted to using glearray ... LOTS of mem copies"; marconisdev,
  Elixir: "I had a hard time not being able to mutate today"; aaronjw1, Elixir: "giving up and
  mutating"), and that they already had a grid library (14 comments, e.g. continuouslypenguin:
  "Spent time building up my own grid library since I know there will be a lot more coming").
- **Speed varies by a factor of 10^6 and nobody minds.** 955 µs (G_de_Volpiano, `IntSet` pruned
  to neighbours of removed rolls), 7 ms for part 1 and 186 ms for part 2 (sondr3_, `Map.mapAccumWithKey` of the whole grid each round), 20 s
  (dijotal, first version), 5 s (Teem0WFT), 15 minutes (Chemical_Chance6877, Gleam with an array
  copy per removal) **[cited]**.
- **The tie in day 3 has no analogue here, but the border does:** a solution's bug was usually
  the off-grid rule (G_de_Volpiano above; munchler: "it took me a while to get all the fiddly
  for-loops correct"; the Vim, Lisp and APL answers pad with floor instead).

## 3. Themes

### 3.1 How the grid is held

| Representation | Who | Example |
|---|---|---|
| a `Set` of roll coordinates | mstksg, lboshuizen, r_so9, NeilNjae, RossPaterson, glguy, spikedoanz, tenthmascot, Hath995 (as the removed set), and about 15 more | `Set.filter (accessible rolls)` |
| a `Map` from coordinate to cell, or to a neighbour count | danvk, sondr3_, jpyamamoto, nikola-benes, bmatcuk, tschady, ryoung786 | `Map.mapAccumWithKey go [] xs` |
| nested arrays or lists, with index arithmetic | kim-em, sdiehl, stonarini, PP6464, Pengler38, vanshjangir, munchler | `grid[r][c]` with bounds checks, or `getAt ... : Int -> Int -> Char` giving `'.'` off the grid |
| an array with `Fin` or size-indexed rows | andorp, acarapetis, BrianNormant, bjornestol, **ours** | `Vector (Vector Cell w) h`, `Vect n (Vect m Roll)` |
| shifted or stenciled whole-grid arrays | the APL family, Mathematica, numpy, Julia | `{5>+/,⍵}⌺3 3` |
| no coordinates: rows zipped with shifted rows | POGtastic, **ours** | `triplewise` rows, then triples of each row |

Our row (`Vec` of `Vec` with the width and height in the type) is shared by four proof-assistant
authors, and the cost of the alternative is visible: bjornestol's `Array` grid carries
`colsCorrect`, `rowsCorrect` and a 40-line `Array.set_retains_property` just so `removeRoll`
can say the new array is still a rectangle, and kim-em's `getAt` gives up on indexing and returns
`'.'` off the grid. Ours has neither, because `peelRow` takes three `Vec Cell w` and
returns one **[checked: read the files]**.

**Stitchwort today.** All five shapes except the comonad and the stencil run: `sets.sw`
(Set-based, `Int` coordinates), `wl.sw` (worklist), `worklist.sw` (the same, plus a fuel-bounded
`unfoldN`), and our own program. `Set.fromList` and `Set.filter` work; `Set.map`, `Set.any` and
`Set.count` don't exist; `List.concatMap` does. Parsing a grid into a set needs a with-index
view twice (`lines.zip (List.range lines.length)`, then the same for each line): SW-235's
`withIndex` would shorten it **[checked: `sets.sw`]**.

### 3.2 The stencil, and our window trick

The array languages say it in one line:

```
f←{⍵-⍵∧{5>+/,⍵}⌺3 3⊢⍵}      ⍝ voidhawk42: remove the rolls whose 3 by 3 window sums below 5
+/,p-f⍣≡p                    ⍝ part 2: apply until unchanged, count the difference
```

and ours is the same idea in five parts: the window includes the roll itself, so "fewer than 4
neighbours" is `window < 5` (`peelCells`: `if roll == Roll && 5 <= window`); the window sum is
separable (sum the three rows column by column, then each column with its two neighbours: Goal's
`nbsum:2{+(x+0,-1_x)+1_x,0}/` does it twice, rows then columns); and the edges are floor (APL's
`⌺` pads with zeros, Mathematica's `ArrayPad`, Uiua's `⬚0`, our `gap` row and `headOr 0`).
`Proofs/Window.sw` is the theorem that the program's window equals the spec's neighbours plus the
cell (`windowIsNeighbours`), for every grid, which the array languages leave to their primitive
`⌺`.

So the one stencil primitive the array languages have and we don't is "a function of each
element and its left and right neighbours, with a pad past the ends". We spell it out twice:
`roundFrom` (each row with the rows above and below) and `peelCells` (each column sum with its
neighbours). **Stitchwort today:** `Vec.zipWith3` exists; nothing like `around` does. A
scratch version, defined in the file because a user file can't add to `Vec`:

```
def around (pad: a) (f: a -> a -> a -> b) (v: Vec a n): Vec b n := aroundFrom pad f pad v

def aroundFrom (pad: a) (f: a -> a -> a -> b) (left: a): Vec a n -> Vec b n
  | VNil         => VNil
  | VCons x rest => VCons (f left x (rest.headOr pad)) (aroundFrom pad f x rest)

def Grid.round (grid: Grid): Grid :=
  { grid | rows = around (Vec.replicate grid.width Floor) peelRow grid.rows }

def peelRow (above row below: Vec Cell w): Vec Cell w :=
  let columns := Vec.zipWith3 (a r b => a.count + r.count + b.count) above row below
  Vec.zipWith (roll window => if roll == Roll && 5 <= window then Roll else Floor) row (around 0 (l h r => l + h + r) columns)
```

It replaces `roundFrom` (4 lines) and `peelCells` (6 lines) with a 6-line generic function, and
`sweep` is unchanged (it uses the already-swept row above, so it isn't an `around`). Answers
1397 and 8758 and the example test pass **[checked: `around.sw`]**. The gain in the program is
small; the possible gain is in the proofs, where `roundFromAt`, `peelCellsAt` and the
`RowIs` bookkeeping in `Window.sw` (31 theorems, 220 lines) prove "element i of the result is
`f` of elements i-1, i, i+1" twice, in two different shapes. One lemma (`getAround`) would do both
**[inferred: not tried]**. Day 7's `fall` has the same "left and right neighbour" shape
(`fromLeft`, `ss.headOr False && bs.headOr False`) **[inferred]**.

### 3.3 Part 2: until nothing changes

| Loop | Who | Termination |
|---|---|---|
| `unfold` / `unfoldr` / `iterate` + `takeWhile` | r_so9, lboshuizen, mstksg, stanosphere, tschady, genmeblog, sondr3_ | lazy list; nothing checks it |
| `while` / `recur` with a fixed-point test (size or `==`) | most imperative and Lisp solutions, Casper-Guo (`@tailrec`), sim642, Ross Paterson (`whileJust`) | none |
| a worklist | glguy, dupuisf, nikola-benes, bmatcuk, onrustigescheikundig (BFS) | none; glguy's queue grows |
| a measure | acarapetis, tenthmascot, kim-em (`termination_by` the roll count) | checked by Lean |
| fuel | sdiehl, BrianNormant (`MAX_ITERATION`), 0xmycf, ryoung786 (`0..99`), **ours** | by construction, not proved except ours |
| gives up | bjornestol, josephmate, vanshjangir, spikedoanz (`partial`), jpyamamoto (`TERMINATING`), Hath995 (`decreases *`) | none |

Every program that terminates does so for one reason: a round that changes something removes a
roll. Ours states it (`settleMarked ... grid.rolls`: "as many passes as there are rolls are
enough") and proves it (`settleEnds`, `roundsStable`). The three Lean authors state it as a
measure instead, which is shorter and checked by the compiler.

**Stitchwort today.** Fuel, as in `Nat.divFuel`, `Nat.digitsFuel`, `transposeN` and this day's
`settle`; each needs a "fuel is enough" and a "fuel doesn't matter" lemma (SW-199's wording).
`List.unfoldN` and a worklist are 4–5 lines each with fuel (`worklist.sw`). Neither `unfold` nor
`iterate until stable` exists in the library, and without `decreasing` they would need a fuel
argument every time.

### 3.4 Order independence

Three commenters say it in a sentence and rely on it. The others remove "all accessible at once"
and repeat, the puzzle's own wording, or process a worklist, and all of them get the same
number (1397 and 8758 are our input's answers; glguy's 1540 and 8972 are his own input's). That the removal order doesn't matter is what
makes that so. Ours proves it: a roll in a *stable* set (every member has at least 4
neighbours in the set) is never accessible, so any removal order ends at the largest stable
subset of the grid, the core (`stepKeeps`, `endsAgree`). That is the usual graph-theory 4-core, and
the same argument shows the worklist, the rounds and our in-place sweep agree, so the
`wl.sw` worklist could be proved correct by the same lemmas **[inferred: the lemmas are about
sets of cells, `Same`, `Keeps`, `Step`; not tried]**.

### 3.5 Proofs and automation

What the community did with proofs for day 4: nothing about the answer (§1). The techniques in
the files:

- **Size in the type** (andorp, acarapetis, BrianNormant, dupuisf's `Vector₂`): rows are
  `Vector _ w`, positions are `Fin h × Fin w`. Same idea as ours; ours also avoids `Fin` positions
  (the spec indexes by `Nat` and says "floor off the grid").
- **A termination measure** (acarapetis: `decreasing_by grind only [!removeAccessibleNonIncreasing]`):
  one monotonicity lemma and `grind`. The equivalent in Stitchwort is the fuel lemma
  (`roundCount`, `roundsFixed`), by hand.
- **`grind`, `omega`, `simp` for arithmetic** (andorp, acarapetis, kim-em's commented plan): our
  proofs are written without arithmetic automation (SW-101).
- **`Option` for bounds** (andorp's `shift?`, a proof that the neighbour is in range): the spec
  avoids it by letting positions be any `Nat` and cells off the grid be floor.

**Where ours stands.** 893 lines of proof (1,262 with comments) and 132 theorems, for two
statements: part 1 right, part 2 right. The cost is in `Window.sw` (the stencil equals the
neighbours: 220 lines), `Sweep.sw` (the marked sweep removes only accessible rolls and ends
stable: 239 lines) and `Core.sw` (the core argument: 172 lines). `check Aoc.Day04.Proofs`
takes 0.9 s; `test Aoc.Day04.Tests` takes 5.8 s, mostly the real input in the checking
evaluator **[checked]**.

### 3.6 Speed of the obvious programs

Times are wall-clock for the whole command on the real input (136 by 136, 1397 and 8758), one run
each, on a laptop that was also running other work **[checked: `scripts/r.sh`, `rc.sh`]**:

| Program | `stitchwort run` | `run --js` |
|---|---:|---:|
| Committed `Aoc.Day04.main` | 0.61 s | 0.45 s |
| `around.sw` (committed with `around`) | 0.38 s | 0.39 s |
| Set rounds (`sets.sw`, mstksg's shape) | 16.7 s | 3.5 s |
| Set worklist (`wl.sw`, glguy's shape) | 1.65 s | 0.75 s |
| glguy, worklist, Haskell | 1540 / 8972 on his input; no time given | |
| sondr3_, whole grid per round, Haskell | 6.95 ms, 186 ms **[cited]** | |
| G_de_Volpiano, `IntSet` pruned, Haskell | 958 µs, 955 µs **[cited]** | |
| dijotal, first version, Common Lisp | about 20 s **[cited]** | |

`docs/aoc-2025.md` says the program runs in 5.1 s; the same release binary now runs it in 0.6 s
(and `SW-112`'s text says "5 s"), so those numbers are stale **[checked]**. The Set-rounds
program is 27 times slower under `run` than the committed one, which matches what the community's
set solutions say about re-testing every roll every round. The worklist is 2.7 times slower than
the committed program and much shorter than `sweep` and its marks (`drain` is 8 lines;
`Marked`, `sweep`, `sweepFrom`, `sweepRow`, `settle` and `settleMarked` are about 25), but it has
no proof; the fuel `9 * rolls.size + 1` would have to be proved enough.

## 4. Side by side

The committed round against the set version and the array languages:

```
-- Stitchwort (Day04.sw): one row of a round, from the three rows around it
def peelRow (above row below: Vec Cell w): Vec Cell w :=
  peelCells 0 (Vec.zipWith3 (a r b => a.count + r.count + b.count) above row below) row
def peelCells (left: Nat): Vec Nat w -> Vec Cell w -> Vec Cell w
  | VNil,               VNil            => VNil
  | VCons here columns, VCons roll rolls =>
    let window := left + here + columns.headOr 0
    VCons (if roll == Roll && 5 <= window then Roll else Floor) (peelCells here columns rolls)
```

```haskell
-- mstksg (Haskell)
reachable pts = flip S.filter pts \pt -> S.size (fullNeighbsSet pt `S.intersection` pts) < 4
part2 = S.size . fold . takeWhile (not . S.null) . unfoldr (Just . go)
  where go pts = (removed, pts `S.difference` removed) where removed = reachable pts
```

```
-- Stitchwort, scratch sets.sw (mstksg's shape)
def accessible (rolls: Set Pos): Set Pos := rolls.filter (p => neighbourCount rolls p < 4)
def peel: Nat -> Set Pos -> Set Pos
  | Zero,   rolls => rolls
  | Succ f, rolls =>
    let gone := accessible rolls
    if gone.isEmpty then rolls else peel f (rolls.difference gone)
def part2 (rolls: Set Pos): Nat := rolls.size - (peel rolls.size rolls).size
```

```
f←{⍵-⍵∧{5>+/,⍵}⌺3 3⊢⍵}     ⍝ voidhawk42 (Dyalog APL), the whole round
```

The set version is as short as the Haskell and 27 times slower than ours under `run`; ours is
the one with a proof. The APL line has no proof and no `peelCells`: the stencil is a primitive.

```haskell
-- glguy (Haskell): the worklist
part2' (x Queue.:<| q) rolls
  | Set.notMember x rolls = part2' q rolls
  | length ns < magic     = part2' (Queue.appendList q ns) rolls'
  | otherwise             = part2' q rolls
```
```
-- Stitchwort, scratch wl.sw: the same, with a list as the work stack and fuel
def drain: Nat -> List Pos -> Set Pos -> Set Pos
  | Zero,   _,           rolls => rolls
  | Succ _, [],          rolls => rolls
  | Succ f, [p, ..rest], rolls =>
    if !rolls.contains p then drain f rest rolls
    else
      let ns := neighbours rolls p
      if ns.length < 4 then drain f (ns ++ rest) (rolls.remove p) else drain f rest rolls
```

glguy's three guards flatten into the nested `if` (SW-237, pattern guards). The fuel,
`9 * rolls.size + 1`, has to be worked out by hand: every roll is queued at most 8 more times
(once per removed neighbour) plus once to start. With `decreasing` (SW-199) it would be a
measure.

## 5. Candidate features, ranked by value over effort

Kinds: **sugar** (syntax only), **library**, **tooling**, **language** (elaboration or kernel),
**tests**.

| Rank | Candidate | Kind | Value | Effort | Evidence | Ticket |
|---|---|---|---|---|---|---|
| 1 | **`Set`/`Map` literals at `Int`: `def s: Set Int := Set.fromList [1, 2, 3]` is `E-TYPE-MISMATCH`** | language (elaboration) | medium to high: the commonest shape, a set of `(Int, Int)`, can't be written with a literal | small to medium (find why the expected type doesn't reach the list through the auto `ord`) | §1.5; `lit.sw`: fails for `[1, 2, 3]`, 5 zeros and `[(3, 3)]`; works for `List Int` and some short sets | none; new |
| 2 | **`Vec.around`** (a function of each element and its two neighbours, with a pad), a lemma `getAround`, and use it in `Day04.sw` and `Day07.sw` | library | medium: removes two hand-written recursions from the program and, if the lemma works, two index proofs | small for the function; medium for re-proving | §3.2; the array-language stencil, POGtastic's `triplewise`; `around.sw` | none; a lane after a design check |
| 3 | **Nat.iterate** (apply f n times; our spec's `rounds` is it) with `iterateSucc`, `iterateAdd` | library | low to medium | trivial | `Spec.sw` hand-writes `rounds`; 7 community loops are iterate | none |
| 4 | **Non-square tests in Day04.sw** (`["@@@@@"]`, a 5-row column of `@`) | tests | low: proofs cover it, but a width/height swap in `parseGrid` is the commonest silent bug | trivial | §2.2 notes; munchler's "fiddly for-loops" | with SW-224 |
| 5 | **`decreasing <measure>` (SW-199)**: day 4 adds the third evidence set | language | high but large | large | §3.3: 3 Lean files with `termination_by`, 9 of 21 proof-assistant files give up on totality or use fuel | SW-199 (backlog); raise to design-note next |
| 6 | **`List.cross`, `Set.map`, `Set.any`** (and an `Int` range) | library | low to medium: eight-neighbour offsets as a comprehension, in about 8 solutions; a set of rolls mapped to new positions | small | §3.1; `sets.sw` writes the offsets as a literal list of 8 | beside SW-235 |
| 7 | **Evidence for SW-112 (native array)**: day 4 doesn't need it | tooling (decision) | medium: avoids building a large item | none | §3.6: committed 0.61 s, `Set` worklist 1.65 s; bjornestol's `Array` bookkeeping | SW-112 |
| 8 | **Refresh the stale timings** in `docs/aoc-2025.md` Day 4 and SW-112 | docs | low | trivial | §3.6 | with SW-224 |
| 9 | **A shared `Grid` in `Aoc.Common` or `Std`** | library | low now: 14 megathread comments reuse their own library, but day 7's `Manifold` pads instead of refusing ragged rows | medium | §2.2 | wait for days 6–8 |
| — | Comonad grids (beefyhalo's `extend`/`experiment`) | language | low | large | one file | no change |
| — | A stencil primitive `⌺` / `ListConvolve` | library | covered by 2 | — | 11 array and numpy solutions | no new ticket |
| — | Local mutable variables, arrays | language | low | large | D299; 17 comments mention mutation | not now; SW-112 evidence |
| — | Arithmetic automation (`omega`, `grind`) | language/library | high for proofs | large | §3.5: acarapetis, andorp | SW-101; no change |

Why this order:

- **Rank 1 is a defect in the commonest shape, hit on the first run.** The coordinate set needs
  `Int` offsets; every attempt to write a test input as a literal failed until the list went
  through a helper with an annotated parameter (`pts [...]`). It is probably one elaboration
  rule (the expected type doesn't reach the elements of a list under a call that has an `auto`
  argument), so it is likely cheap to fix; but I haven't looked.
- **Rank 2 is the one idea from day 4 that touches our own program.** It also has a falsifiable
  test: if `getAround` doesn't make `Window.sw` shorter, don't merge.
- **Ranks 3 and 4 are trivial.** Rank 5 is already decided as backlog; day 4 is a third piece of
  evidence, with a concrete shape (`decreasing countRolls`).
- **Ranks 7–9 are decisions to *not* build something**, and say why.

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D420 | Make `Set Int`/`Set (Int, Int)` literals elaborate: `Set.fromList [1, 2, 3]` at `Set Int` is `E-TYPE-MISMATCH` today. Open a small ticket to find and fix it? | [yes, one small ticket (Sonnet lane): first find why the expected type doesn't reach the list elements through `Set.fromList`'s auto `ord` argument; add the failing cases of `lit.sw` as tests] |
| D421 | Add `Vec.around` (and `List.around`?) with a `getAround` lemma, use it in `Day04.sw` (`roundFrom`, `peelCells`), and check whether `Window.sw` shrinks; try Day 7's `fall` too? | [yes, `Vec.around` only; one lane, accepted only if the Day 4 proofs get shorter; Day 7 as a second step] |
| D422 | Treat day 4 as a third evidence set for SW-199 (`decreasing`), and move its design note ahead of other backlog design work? | [yes, raise it to "next design note"; no implementation yet] |
| D423 | Add `Nat.iterate` (f applied n times) with its two lemmas, and use it for the spec's `rounds`; do not add `unfold`/`until stable` yet (they would need fuel until SW-199)? | [yes for `Nat.iterate`; no for unfold/until] |
| D424 | Add `List.cross` (all pairs of two lists), `Set.map` and `Set.any` next to SW-235's batch 2? | [yes, small; with SW-235] |
| D425 | Start a shared `Grid` (rows of cells, neighbours, parse) in the library now? | [no; wait until days 6–8 show what is common; day 7's `Manifold` pads rows, day 4 refuses ragged ones] |
| D426 | Add non-square tests to `Day04/Tests/Examples.sw` (`["@@@@@"]` is (5, 5); the same as five rows of `@`)? | [yes; two lines, with SW-224] |
| D427 | Record on SW-112 (native `Array`) that day 4 doesn't need it (Set worklist 1.65 s, committed program 0.61 s) and that, if built, the array should carry its length in the type (`Array a n`), as bjornestol's Array bookkeeping shows? | [yes; add the note, keep the ticket in the backlog] |
| D428 | Refresh the stale day 4 timings (5.1 s) in `docs/aoc-2025.md` and SW-112 (now 0.6 s `run`, 5.8 s for `test Aoc.Day04.Tests`)? | [yes; with SW-224] |

Parked and relevant, not re-proposed: SW-235 (`withIndex`, `dropWhile`, ...) would shorten the
set parser in `sets.sw`; SW-237 (pattern guards) would flatten glguy's three-way `part2'` and our
`drain`; SW-222 (`_` lambdas) would shorten `rolls.filter (p => neighbourCount rolls p < 4)`;
SW-228 (dot receiver position) shows in `lines.zip (List.range lines.length) |> .concatMap`.

---

**Status** (short form, 22 Oct 2026): D420 `Set` literal typing, pending; D421 `Vec.around`,
pending; D422 SW-199 priority, pending; D423 `Nat.iterate`, pending; D424 `List.cross`/`Set.map`/
`Set.any`, pending; D425 shared `Grid`, pending (recommended no); D426 non-square tests, pending;
D427 SW-112 note, pending; D428 timings refresh, pending. Unchanged by day 4: D299 local mutable
variables not now, SW-101 backlog, SW-112 backlog.
