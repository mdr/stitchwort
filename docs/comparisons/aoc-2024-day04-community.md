# AoC 2024 day 4: community solutions in other languages

**Date:** 29 October 2026. **Ticket:** SW-892. **Our version:** finished before this note:
`aoc/src/Aoc/Year2024/Day04/`, with both parts proved equal to a position-by-position spec for
every grid, and the friction notes in `aoc/NOTES-2024.md` ("## Day 4"). The puzzle is a word
search. Part 1 counts every XMAS in any of eight directions, overlaps included. Part 2 counts
the "X-MAS": an `A` with a MAS, either way round, on both diagonals through it. The input is
`aoc/inputs/2024/day04.txt`, a 140 × 140 grid. The answers are 2524 and 1873.

This note follows the day 1–3 notes ([day 3](aoc-2024-day03-community.md)). Day 4 is the first
grid puzzle of 2024, so it looks at three things: how people represent the grid and the
directions, how they keep reads inside the grid, and whether anyone proves anything about a
grid search.

The labels are as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Where things are:

- **Scratch area:**
  `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/d2024-04/`.
  The fetched files are in `gh/files/`, the megathread JSON is in `arctic/`, and the Stitchwort
  scratch project is in `proj/`.
- **Committed copies:** the scripts are in
  [aoc-2024-day04-community/scripts/](aoc-2024-day04-community/scripts/), and the scratch
  programs and timing drivers are in `scripts/sw/`. The per-author table is
  [classify.tsv](aoc-2024-day04-community/classify.tsv), and the raw timings are in
  [timings.txt](aoc-2024-day04-community/timings.txt).
- **Binary:** the main checkout's `target/release/stitchwort`, rebuilt with `task build` at
  11:52 on 29 October (with native support).
- **Timings:** wall clock and peak memory from `scripts/time4.sh`, one to three runs each, on a
  laptop that was running other lanes. They include process start-up. Treat them as rough, to a
  factor of about 1.5.

## 1. Summary

I read day 4 files from **199 GitHub authors**, one file set per author. 21 are in Lean 4, 4
in Idris 2, and one each in Agda and Dafny. The rest are Haskell, Elixir, F#, Clojure, Scala,
OCaml, Gleam and Roc, plus a few others (§2.1). I also read the r/adventofcode "2024 Day 4
Solutions" megathread through the Arctic Shift archive: 762 live top-level comments, 91 of
them in functional or array languages (§2.2). **Thierry Martinez**, the Coq author who proved
a lot on days 1 and 2, **solved day 4 in Python only**. His 2024 folder has `.v` files for
days 1 and 2 and nothing in Coq after that **[checked: his repository's tree]**. There was no
Coq/Rocq, F\*, Isabelle, Koka or Unison day 4 in either source.

How Stitchwort compares:

1. **We are the only ones who prove the answer, and our proof covers the mistakes people
   actually made.** Nobody else has a theorem about either count. The nearest are these. A
   Lean theorem (shilangyu) shows that XMAS is in a reversed list exactly when SAMX is in the
   list. Two Lean authors (RussellEmerine, a2435191) index with `Fin` coordinates and build the
   bounds proofs as they go. Dafny's verifier (hath995) proves that every array index is in
   range, after an `assume {:axiom}` that the rows are equally long. main-- has four Lean
   `example`s about one 3 × 3 grid **[checked: §3]**. On the real input, the
   community's four common mistakes each change an answer. Python's negative indices wrap
   round: +19 on part 1. A non-overlapping regex `XMAS|SAMX` loses 182. A test for two Ms and
   two Ss among the corners takes `MAM`/`SAS`: +51 on part 2. Counting `+` shapes too adds 31
   **[checked: `pitfalls4.py`]**. Each mistake is reported in the megathread by someone who
   made it (§2.2). `part1Correct` and `part2Correct` rule out all four for every grid, ragged
   grids included. That holds so long as the 41-line spec is right, and the spec is written in
   the puzzle's own terms.
2. **The proof cost a lot.** It took 290 code lines and 40 theorems, on top of the general
   list lemmas that day 4 added to std (SW-715). The spec is 41 code lines and the program 30.
   Friction items 2 to 9 were all checker, library or syntax friction rather than hard
   mathematics. Some are still open: `c + 1` doesn't compute (SW-787) and `rewrite _` rewrites
   only one instance. Others are fixed: `let` inside parentheses (SW-788), `rfl`
   messages that hid the difference (SW-716), goals that printed proof terms (SW-717), and the
   missing lemmas (SW-715). A Lean user with Mathlib would have `simp` and
   `omega` for most of the index arithmetic **[inferred]**. Nobody in Lean did it, so this is
   a guess, not a comparison.
3. **Our program is short and safe by construction, but it is not the clearest version.**
   Every line of cells is read by zipping rows shifted against each other, for example
   `countXmas (first.drop 3) (second.drop 2) (third.drop 1) fourth` for the down-left
   diagonal. `zipWith4` stops at the shortest list, so no read can leave the grid. That is
   clever, and it is the same trick as ephemient's Haskell part 2. But a reader has to work out
   which diagonal each line is. The puzzle's own reading, "from each position, look along each
   of eight directions", is what our spec says, what `MapGrid.sw` says (§4), and what most of
   the community writes. At 30 code lines, we are a little longer than the shortest functional
   solutions: tromp's Haskell has 17, ephemient's Haskell 24, and mniip's Lean 30 (with a grid
   library of his own). We are well under the GitHub median of 63.
4. **Bounds handling: ours is among the safest, and the type system has little to do with
   it.** In Lean, 9 of 21 authors index with `xs[i]!` or `get!`, which return a default (and
   report a panic) when out of range. Two prove their indices. The rest use `Option` lookups
   or read rows as strings. In the functional languages, the common styles are an `Option` or
   `Map` lookup (Elixir and Gleam mostly use maps), explicit `0 <=` tests (F#, OCaml), and
   catching the exception (OCaml's `Invalid_argument`, Roc's `Result`). A few pad the grid
   with a border **[inferred: `classify4.py` tags, spot-read]**. Stitchwort has no indexing
   that can fail: `List.get` returns an `Option`. Our program doesn't index at all.
5. **Speed: fast on this day, and native is fast too.** On the real input, `run` takes
   0.20 s, `run --js` 0.28 s and native 0.01 s, against start-up times of 0.14 s, 0.31 s and
   0 s **[checked]**. On a 16× grid (560 × 560), native takes 0.15 s, against 0.70 s
   in-process for a plain Python version. Unlike day 3, native beats JS here (0.44 s). The
   program is pure list code, with no handlers in the loop. The slow route is a grid looked up
   by position: the spec run as a program takes 17 s natively on the 16× grid, and a
   `Map`-based version takes 3.5 s (§5). We have no random-access array (SW-112), so the
   puzzle-shaped program costs 23–110× more than the clever one natively.

## 2. The solutions

### 2.1 GitHub

Method **[checked: scripts]**:

1. I reused the day 3 lane's 344 repositories (`repos.tsv`, from `gh search repos` per
   language plus megathread links), with their cached trees, so day 4 needed no new search
   calls. I added `thierry-martinez/advent-of-code`.
2. `find4.py` kept the files that look like day 4 (256 paths), and `fetch4.py` fetched 257
   files from raw.githubusercontent.com.
3. `classify4.py` kept the files that mention XMAS (or `'X'` and `'M'`), one repository per
   author, and tagged them by method with regexes. `stats4.py` summarises the result. The tags
   are leads, not verdicts. For example, Clojure's `partial` function sets off the `partial`
   tag.

Authors by language: Haskell 27, Elixir 24, F# 24, Clojure 22, Scala 22, Lean 21, OCaml 20,
Gleam 16, Roc 11, Idris 4, Common Lisp 3, and one each in Agda, Dafny, Julia, Prolog and
Python (Martinez). That makes 199. The median is 63 code lines. By language, the medians are
Haskell 47, Lean 54, Scala 56, OCaml, F# and Clojure 58, Elixir 74, Idris 96, Roc 105 and
Gleam 106.

How the grid is held and read, from the tags (one author can have several):

| style | authors | typical languages |
|---|---|---|
| lines as strings: transpose, reverse, diagonals, then count substrings | 92 | Haskell, Lean, Agda, Elixir, Scala |
| a list of the eight directions as offsets | 94 | all of them |
| an array, vector or 2-D array, indexed | 84 | F#, OCaml, Clojure, Lean |
| an `Option`/`Map` lookup that misses off the grid | 80 | Gleam, Elixir, Clojure, Lean |
| explicit `0 <=` / `< width` tests | 50 | F#, OCaml, Elixir |
| a map from position to letter | 33 | Gleam (11 of 16), Elixir, Haskell |
| an exception caught or rescued | 19 | OCaml (8 of 20), Roc |
| padding with a border | 8 | a few in each |

I read all 27 proof-language files and Martinez's Python:

- **Lean (21).** 10 read the grid as strings (`transpose`, hand-written diagonals, then a
  `'X' :: 'M' :: 'A' :: 'S' :: rest` pattern). The others look up positions. 9 index with `!`
  (`grid[i]![j]!`, `get!`): jano-wol has 15 of them and dupuisf 8. mniip (30 lines) has the
  nicest direction model: `Dir8.list`, `d.advanceBy i`, and `Rect.index?`, which returns
  `Option`. Part 2 is a five-cell stencil, `('M', -1, -1) … ('S', 1, 1)`, rotated through
  `Dir4.list`. Proofs are in §3.
- **Matt's Lean (`mdr/aoc-2024`, 49 lines with its `#guard`s).** Part 1 reads the grid four
  ways (`id`, `transpose`, `diagonals`, `diagonals ∘ flipHorizontal`). `countXmasOccurrencesInRow`
  counts XMAS and SAMX in one pass, restarting from the last letter "as it could start a SAMX".
  Part 2 takes every 3 × 3 window, tries the four rotations, and matches the window against a
  pattern, `[['M', _, 'S'], [_, 'A', _], ['M', _, 'S']]`. That pattern is the most readable
  part 2 I found. The windows approach is the same nine-cell reading that our first part 2
  used (friction item 1). On a ragged grid it can lose a cross if `List.transpose` truncates
  the rows **[unverified: how Lean's `List.transpose` treats ragged rows]**. Puzzle inputs are
  rectangular, so the answers aren't affected.
- **Idris 2 (4).** BrianNormant is `%default total` and holds the grid as `Vect n (Vect n
  a)`, indexed by `Fin n`. So every read is in range by type, but only for square grids: rows
  of any other length are dropped by `toVect n`. The other three index lists with
  `Maybe`-returning lookups or test bounds by hand.
- **Agda (1).** aaronallen8455 writes `transpose` and `diags` with a `zipIt` that keeps the
  extra cells of longer rows, so it is right on ragged grids. Counting is a
  `'X' ∷ 'M' ∷ 'A' ∷ 'S' ∷ rest` pattern. There are no proofs.
- **Dafny (1).** hath995 holds the grid as `Matrix<char>`, with `requires isMatrix(m)` on each
  method. The verifier makes him guard every read (`if y + i < m.rows && x + i < m.columns`).
  He gets equal row lengths by `expect`, then `assume {:axiom}`. His `matrix.dfy` has verified
  `seqTranspose` postconditions and a lemma that transposing twice gives the same matrix.
  Neither count has a postcondition.
- **Martinez (Python, 24 lines).** He tests `0 <= x + 3 * dx < len(grid[0])` before reading,
  which avoids Python's negative-index trap. His part 2 checks `x >= len(grid) - 1`, using the
  row count for the width, so it assumes a square grid **[checked]**.

Two short functional solutions from outside the proof languages show the main styles:

- **tromp (Haskell, 17 lines).** `n = 140` is hard-coded. He lists every run of four
  positions, `[[(x,y),(x+1,y),(x+2,y),(x+3,y)] | x <- [0..n-4], y <- [0..n-1]]` and so on,
  with ranges that keep every read in bounds, then reads `Data.Array` with `!`. That is bounds
  by construction, like ours, but written as ranges instead of `drop`s. It fails on any
  non-140 grid.
- **ephemient (Haskell, 24 lines).** Part 1 counts `T.indices "XMAS"` and `"SAMX"` over rows,
  their transpose, and diagonals made by `splitAt`. Part 2 is ours in a list comprehension:
  `prev : line : next : _ <- tails`, then `zip3` of the middle row and the shifted corners
  (§4).

### 2.2 The Reddit megathread (via the Arctic Shift archive)

`arctic.py` made two requests. The post search for 4 December 2024 05:00 UTC found `1h689qf`,
"-❄️- 2024 Day 4 Solutions -❄️-" (1,135 comments). The second request fetched its comment tree:
776 top-level comments, 762 of them live, 730 with a language tag **[checked]**. By language:
Python 182, Rust 76, C 59, JavaScript 45, Go 42, … Haskell 14, Elixir 10, Scala 7, Dyalog APL
6, OCaml 5, Uiua 5, Clojure 4, F# 4, and one each in Lean, Dafny, Gleam, Prolog and BQN
(`langs4.py`).

Word counts over live top-level comments (upper bounds, from `words.txt`): eight-direction
lists in 109, transpose, rotate or diagonals in 96, a map or dictionary of positions in 48, a
regex in 41, padding or a border in 22, an exception for bounds in 22, and a convolution,
kernel or mask in 19.

Mistakes that people reported making, with what each costs on our input (`grepthread4.py`,
`pitfalls4.py`) **[checked]**:

| mistake | who says so | effect on our input |
|---|---|---|
| Python's `grid[-1]` wraps to the last row or column | yossi_peti ("an extraneous solution with a negative index wrapping over to the other side"), fallendeviL701b ("didn't consider that negative indices are valid in Python"), AllanTaylor314; __Abigail__ pads for the same reason in Perl | part 1: 2543, not 2524 |
| a non-overlapping regex or split misses `XMASAMX`'s second word | (none explicitly; 41 regex users) | part 1: 2342 (lookahead `(?=XMAS\|SAMX)` gives 2524) |
| two M and two S among the corners, which takes `MAM`/`SAS` | DatBoi247 and pred warn about it; AllanTaylor314 "didn't fall for SAS MAM" | part 2: 1924, not 1873 |
| `+` shapes counted as crosses | AllanTaylor314: "I assumed plusses counted as Xs" | part 2: 1904 |
| a typo in one of four hand-written patterns | G_de_Volpiano: "typed `[Just 'S', Just 'A', Just 'S']` instead of `[Just 'S', Just 'A', Just 'M']`" | — |

Our sabotage checks (NOTES item list, "Sabotage") are exactly this last kind of typo, and the
proofs catch them.

Comments about the method, in the functional and array languages:

- mstksg (Haskell): "Here we are matching 'stencils' across different windows, so it's always
  fun to use comonads for this." The stencils are data, `M.fromList [(i *^ step, x) | (i, x)
  <- zip [0 ..] "XMAS"]` for each of eight steps, and part 2 is the union of two diagonal maps
  plus `'A'` at the centre **[cited]**. It is the most declarative statement of the puzzle I
  found.
- marx38 (Lean, mfornet on GitHub): "take the corners clockwise … and check that M & S appear
  twice and that the first and third positions differ" **[cited]**. That last test is what
  rules out `MAM`.
- Porges (APL) uses the stencil operator `⌺` with the four rotations. oantolin (ngn/k) and
  chubbc (Uiua, four lines) solve both parts in five or fewer lines **[cited]**.
- WhiteSparrow (Prolog): part 2 is one clause with CLP(FD) constraints on the coordinates and
  a disjunction per diagonal; "A runtime of 11 seconds also attests to that" **[cited]**.

Nobody in the megathread mentions a theorem, a lemma or a proof about the counts. The few hits
on "verify" mean checking letters **[checked]**.

## 3. Proofs about grid search: who proves what

| who | what is proved or enforced | about the answer |
|---|---|---|
| **Stitchwort (ours)** | `solvePart1 grid = part1Spec grid` and `solvePart2 grid = part2Spec grid` for every grid, ragged ones included: no line counted twice or missed; no axioms | both parts, fully |
| shilangyu (Lean, 19 lines, no answer computed) | `infix_iff_rev_infix`: `p <:+: s ↔ p.reverse <:+: s.reverse`; so "XMAS" in a reversed row is "SAMX" in the row | the lemma behind searching both ways, not a count |
| RussellEmerine (Lean) | `Fin m × Fin n` coordinates, with `have hi : i.toNat < m` built from `Int.toNat_lt` at each step | none: in-range reads only |
| a2435191 (Lean) | the grid is `Coord h w → Char`, built under a proof that every line has width `w`; stencil reads carry `hy`/`hx` bounds proofs | none |
| hath995 (Dafny) | every array read is proved in range; transposing twice is the identity (`matTranspose`) | none; equal row lengths assumed by `assume {:axiom}` |
| BrianNormant (Idris) | `%default total`; `Vect n (Vect n a)` and `Fin n` make reads in range by type (square grids only) | none |
| main-- (Lean) | four `example`s that `isX_MAS` is right on a 3 × 3 grid; a "failed experiment" on diagonal lengths, commented out | none |
| brightlego (Lean) | four lemmas so a `Substring` scan terminates (`termination_by s.bsize`) | none |
| everyone else | `#guard` / `expect` / tests on the puzzle's example, at most | none |

So the proof-language community spends its proof effort on **index safety**, which
Stitchwort gets from `Option` without proof, and **none on the count**. That matches days 1–3.

What our proof is: the spec counts (position, direction) pairs whose letters spell XMAS. The
proof turns each `zipWith4` into a sum over indices, widens the spec's ranges by 3, and swaps
the sums so that directions come first. Each of the eight directions then equals one of the
program's eight readings. "No double counting" is not a separate theorem: equality with a
spec that counts each (position, direction) pair once makes it so. The symmetry theorems (the
same count with the word reversed, or the grid transposed) weren't attempted. shilangyu's
lemma is the first step towards one, and Dafny's `matTranspose` towards the other.

**What it cost, against what it would cost elsewhere.** 290 proof lines for a 30-line program
is about 10:1. Day 3's ratio was 87:37. The cost is in index bookkeeping (`sumShift`,
`programLines`), not in ideas. In Lean, Mathlib's `Finset.sum_comm`, `simp [List.getElem?_drop]`
and `omega` would probably do most of `programLines` **[unverified: nobody did it]**. Our
`cases` did well on the letter facts (friction item 10), but we have no `simp`, so each list
lemma is named and applied by hand.

## 4. Readability, side by side

Code lines, not counting blank or comment-only lines:

| solution | lines | grid / bounds | general? |
|---|---|---|---|
| chubbc (Uiua) | 4 | windows, rotations | yes **[unverified]** |
| tromp (Haskell) | 17 | `Data.Array`, index ranges chosen to stay inside | 140 × 140 only |
| ephemient (Haskell) | 24 | `Text` lines, transpose and `splitAt` diagonals; part 2 by `zip3` of shifted rows | rectangular |
| Martinez (Python) | 24 | `0 <=` tests | part 2 assumes square |
| mniip (Lean) | 30 | his own `Rect`, `Dir8`, `index?` (Option) | yes |
| **Stitchwort, `Day04.sw`** | **30** | **rows shifted by `drop`, read by `zipWith3`/`zipWith4`; no indexing** | **yes, ragged too, and proved** |
| `MapGrid.sw` (scratch, Stitchwort) | 40 | `Map Position Char`, eight `(Step, Step)` directions, Option | yes |
| Matt's Lean | 49 | transpose and diagonals; 3 × 3 windows, rotations and a pattern | rectangular |
| GitHub median, all 199 | 63 | | |

Part 2, ours and ephemient's, which have the same idea:

```stitchwort
def countCrosses (above: List Char) (middle: List Char) (below: List Char): Nat :=
  let downRight := List.zipWith3 above (middle.drop 1) (below.drop 2) spellsMas
  let downLeft := List.zipWith3 (above.drop 2) (middle.drop 1) below spellsMas
  List.zipWith downRight downLeft (one other => one ∧ other) |> .count (found => found)

def solvePart2 (grid: Grid): Nat :=
  let rows := grid.rows
  List.zipWith3 rows (rows.drop 1) (rows.drop 2) countCrosses |> .sum
```

```haskell
part2 input = length $ do
  prev : line : next : _ <- tails $ T.lines input
  ('A', x, y) <- zip3 (T.unpack $ T.drop 1 line) (T.zip prev $ T.drop 2 next) (T.zip next $ T.drop 2 prev)
  guard $ ok x && ok y
```

And the version a newcomer would write first, as `MapGrid.sw` does:

```stitchwort
def crossAt (letters: Map Position Char) (centre: Position): Bool :=
  let at := (down across => letterAlong letters centre down across 1)
  letters.get centre == Some 'A' ∧ mas (at Back Back) (at Ahead Ahead) ∧ mas (at Back Ahead) (at Ahead Back)
```

My judgement **[inferred]**: ours names its parts well (`above`, `middle`, `below`,
`downRight`, `spellsMas`). Its comments explain the trick, and nothing in it can go out of
range. ephemient's is tighter because a list comprehension does the zip, the pattern match on
`'A'` and the filter at once. Ours spells out a `zipWith` of booleans and a `count`. Part 1 is
where we read worst: `countThrough`'s three lines differ only in which list is dropped by how
much, and a reader has to draw the diagonal to check them. The proof checks them, which is the
point, but tromp's explicit coordinate lists and mniip's `Dir8` say "eight directions" more
directly. `MapGrid.sw` reads like the spec and like most community code, and it checked first
time. It is 25× slower (§5).

Two small things the comparison shows about the language **[checked: writing `MapGrid.sw`]**:

- `Map Position Char` works with a plain record key, with no instance to write.
  `rows.gridCells` (std/List/Grid.sw) gives the position of each cell. Day 4 didn't need
  either, but a reader coming from Elixir or Gleam would reach for them.
- There is no `(-1, 0, 1)` arithmetic on `Nat`, so the direction model is a three-way `Step`
  and `moved` returning `Option Nat`, as in the spec. mniip's `Dir8` and mstksg's `V2 Int`
  (with `Num`) are shorter. An `Int`-keyed version would need `Int` positions and a conversion
  at the edge. It is a small cost, paid every grid day.

## 5. Speed

Real input (140 × 140), wall-clock seconds, the middle of three runs:

| program | `run` | `run --js` | native |
|---|---|---|---|
| Hello (start-up) | 0.14 | 0.32 | 0.00 |
| **Day04 (`zipWith` over shifted rows)** | **0.20** | **0.28** | **0.01** |
| MapGrid (`Map Position Char`) | 0.91 | 0.71 | 0.15 |
| SpecRun (the spec, run as a program: `List.getOr` per letter) | 2.69 | 0.46 | 0.20 |

The input tiled 4 × 4 (560 × 560), one run each:

| program | `run` | `run --js` | native |
|---|---|---|---|
| Day04 | 0.75 | 0.44 | 0.15 (23 MB) |
| MapGrid | 13.8 | 2.18 | 3.51 (330 MB) |
| SpecRun | 131 | 20.3 | 17.1 |
| Python, positions and directions with bounds tests (`pitfalls4.py`, in-process) | | | 0.70 |

What this shows **[inferred from the tables]**:

- **Our program is fast, and native is fast on it.** It costs about 0.5 µs a cell natively,
  linear in the grid. That beats in-process Python by about 5× at 560 × 560 and doesn't depend
  on padding or bounds tests. Unlike day 3's handler-heavy `findAll`, there is no native/JS
  gap to explain, which fits day 3's finding that native is level with or ahead of JS on pure
  code.
- **The puzzle-shaped program pays for the missing array.** `MapGrid` does a `Map.get` at
  O(log n) per letter and is 23× slower natively. SpecRun does a list walk per letter, O(width
  + height), and is 110× slower. With an O(1) array, the direct version would probably be
  within a small factor of ours **[unverified]**. SW-112 (an `Array` type) has stayed in the
  backlog because "day 4 doesn't need a native array" (2025's day 4, D427). That is still true
  for this day, since our program avoids lookups. But every newcomer's first grid program will
  look like `MapGrid`.
- **The interpreter is the outlier on lookup-heavy code**: SpecRun takes 131 s with `run`
  against 20 s with JS and 17 s native. A spec that can be run is useful for tests (our
  `Tests/Spec.sw` runs it on the examples), but not on a real input under `run`.

## 6. Candidate improvements, ranked by value over effort

| Rank | Candidate | Kind | Value | Effort | Evidence |
|---|---|---|---|---|---|
| 1 | **Decide SW-787 (`Nat.add` recursing on its second argument)** | language | `c + 1` computing removes the `Nat.addComm` rewrites from 5 of 8 directions here and from days 12 and 15; Lean does it this way | medium (every `+` proof and hash to recheck), one lane | NOTES item 2; §3 |
| 2 | **Add day 4's numbers to SW-112 (Array)**: the direct position-lookup program is 23× (Map) to 110× (list) slower than the shifted-rows one natively, and 13.8 s / 131 s under `run` at 560 × 560 | runtime / library | sharpens an open decision; grid days recur | trivial | §5 |
| 3 | **A `rewrite`-every-instance form, or a note when `rewrite _` matched once and other instances remain** | proof tooling | the step that cost the most time after the `rfl` messages (now fixed) | small to medium | NOTES item 6 |
| 4 | **A short "grids in Stitchwort" section in the AoC or std guide**: shifted-row zips for fixed patterns, `gridCells` + `Map` for lookups, `Vec.around` for stencils, `Option` everywhere; and the 25× speed difference | docs | the three styles exist in std but no page puts them side by side; newcomers will write `MapGrid` | small | §4, §5 |
| 5 | **A symmetry lemma pair**: the count with the word reversed, and with the grid transposed (`transposeFill` already exists) | proof / library | the two facts the community does use informally (shilangyu, Dafny's `matTranspose`); reusable on later grid days | medium | §3 |
| 6 | ~~`let … in …` as an expression~~: already done before this note, as `(let x := e; body)` (SW-788) | syntax | — | — | NOTES item 8 |
| — | A `Dir8`/`V2 Int` direction type in std | library | shorter direction code (mniip, mstksg) | small, but wait for a second grid day that needs it | §4 |

## 7. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D1740 | SW-112 (an `Array` type) is in the backlog because no AoC day needs it: 2025's day 4 ran in 0.61 s on `Vec`. 2024's day 4 also doesn't need it, but only because our program avoids lookups; the lookup version a newcomer writes is 23× slower natively and 18× slower under `run` (13.8 s at 560 × 560). Does "a newcomer's natural grid program runs well" count as need, or only "a day can't be solved without it"? | [keep SW-112 in the backlog and add §5's numbers to it; take it up when a 2024 day's own program is slow (days 6, 16 and 20 are the likely ones), not for day 4] |
| D1741 | Day 4's spec counts (position, direction) pairs, so "no double counting" holds because the program equals the spec. Should grid days also prove the symmetry facts (reversed word, transposed grid), which the community uses informally but nobody proves? | [no, not as a standing rule: equality with a literal spec already covers correctness; prove symmetry only when a program relies on it, as Matt's Lean does (four transforms) and ours doesn't] |

---

**Status** (29 October 2026): SW-892, this note, is done once reviewed. D1740 (Array priority)
and D1741 (symmetry proofs) are pending.
