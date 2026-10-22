# AoC 2025 day 6: community solutions in other languages

**Date:** 22 October 2026. **Our version:** `aoc/src/Aoc/Day06/Day06.sw` (program: pad the lines,
transpose into columns, split at the blank columns; each block of columns is one problem with
both readings, its rows and its columns), with `Proofs/Spec.sw` (the puzzle read cell by cell
over the lines), `Proofs/Grid.sw` (padding and blocks) and `Proofs/Correct.sw` (both printed
answers equal the spec's grand totals, for every input). `docs/aoc-2025.md` §5 and "Day 6
(October 2026)" describe the program and the proof. Day 6 is the one day whose puzzle is about
the text layout itself, so its spec is over the lines and not over a parsed model; that was
accepted. This note looks at what other people wrote for 2025 day 6, in the wild, and asks what
that suggests for Stitchwort. It follows the shape of
[aoc-day01-community.md](aoc-day01-community.md), [aoc-day02-community.md](aoc-day02-community.md)
and [aoc-day03-community.md](aoc-day03-community.md).

Labels, as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day6-community/`
(`sw/` for programs, `proj/` for a scratch copy of `aoc/` with proof edits, `scripts/` for the
queries), run with the main checkout's `target/release/stitchwort` (built 22 Oct 2026, 08:57).
Fetched solutions are in `gh/proof/` and `gh/fp/` beside it, and the megathread data in `arctic/`.
I read the sources myself; no sub-agents.

## 1. Summary

I fetched the day 6 file of 55 GitHub authors: 19 in Lean 4 (27 files), 3 in Idris 2, 1 in Agda,
1 in Dafny, and 31 in Haskell, OCaml, Scala, F#, Gleam, Elixir, Clojure, Roc, Koka, Elm, BQN
and Common Lisp (one of them a stub). I read about 25 of them in full, and counted idioms in
the rest with `grep`; the table says which is which. I then read the r/adventofcode "2025 Day 6 Solutions" megathread through the
Arctic Shift archive (§2.2): 504 top-level comments, 499 not deleted, 93 distinct language tags.
77 comments are in functional or proof-oriented languages (the same list as day 3: 17 Haskell,
10 Elixir, 9 Common Lisp, 8 Clojure, 6 each OCaml and Gleam, 5 F#, 4 Scala, and a few more), and
13 more in array languages (Q, Dyalog APL, Uiua, Goal, J, BQN). I read all of them; 31 of the 77
have code inline. No Unison, Coq/Rocq, PureScript, F\* or Effekt solution turned up.

The main findings:

1. **Nobody else proved day 6 correct, and the one attempt that states the right theorem leaves
   it as `sorry`.** septract's two Lean files (`Aoc06-1.lean`, `Aoc06-2.lean`, in a repo named
   `aoc2025-ai-lean`) have the same architecture as ours: a `Spec` that reads the grid cell by
   cell (`charAt` is a space past the end, `isSpaceColumn`, problem boundaries from the blank
   columns), an `Impl`, and `theorem impl_eq_spec (grid : Grid) : Impl.solve grid = Spec.solve
   grid := by sorry`. Hath995's Dafny file has no lemma; its "proof" content is two `ensures`
   on the parser (`|ops| == length`, every row has `length` numbers) and nine runtime `expect`s,
   and the author's megathread comment is "Today I only proved that I do not like cephalopod
   parsing". kim-em's six Lean theorems are about `Problem.eval` (`rfl` and `simp`). The other
   21 Lean, Idris and Agda authors have no theorem at all **[checked: read the files; not
   run]**. So `part1Correct` and `part2Correct` (26 theorems over 333 lines of proof) have no
   community counterpart.
2. **Transposition is everywhere, and "transpose, split at the blank columns, read each group"
   is the commonest way to use it.** 33 of the 55 GitHub authors and 49 of the 107 comments in
   functional, array and similar languages transpose something (`grep` for `transpose`,
   `zip(*`, `zip_longest`, `apply map`); 21 of the 55 authors also split with a list helper or
   a blank-column test (`splitWhen (all isSpace)`, `chunk_by`, `groupby`, `chunk`). glguy's is
   five lines and is ours: split once, then part 1 transposes each block again and part 2 reads
   the block's columns. The others take the column boundaries from the operator row (about 8),
   run one pass over the columns with a stack or accumulator (about 10), or build a Lisp or
   Python expression and `eval` it (about 9) **[checked: `grep`, then read the hits; the counts
   are mine and approximate]**.
3. **The trap is the ragged input, and it is the day's most reported bug.** The real input's
   last line is one character shorter than the rest (3779 against 3780 **[checked]**), and
   editors, templates and `splitlines` trim trailing spaces off the example. Nine megathread
   comments describe it (TheZigerionScammer's "subscript out of range", darren, Rush_Independent,
   bakibol, Jadarma, s4uull's "my editor trimmed the test string, and I spent 20 minutes finding
   out what happened", eipi-10, marconisdev, Yorshex); four Python comments reach for
   `zip_longest(fillvalue=' ')`; the Haskell shapes avoid padding because
   `transpose` goes to the longest row. Ours pads, and the program and the spec are right on
   trimmed input by construction. **Stitchwort's `List.transpose` goes to the first row's
   width, not the longest**, so the unpadded Haskell shape written in Stitchwort is silently
   wrong when the first line is the one trimmed: the example's part 2 comes out as 3263823
   instead of 3263827 **[checked: `sw/haskell.sw`, `sw/p_trim.sw`]**.
4. **Stitchwort writes the Haskell shape in about 20 lines and gets the right answers.**
   cinx16's `splitWhen (all isSpace) . transpose` with `words`, written with `List.transpose`,
   `List.splitBy` and a one-line `words` (after fixing one precedence slip of mine:
   `words lines.last.getOrElse ""` needs brackets), printed 4722948564882 and 9581313737063 on
   the real input **[checked: `sw/haskell.sw`]**. What was missing was `words` (one line to write, used
   by about 18 of the 107 comments and 24 of 71 files in part 1), and the padding that a
   longest-row transpose would do for you.
5. **Nobody wrote a proof that the right-to-left reading doesn't matter, but six people
   asserted it.** python-b5 ("Addition and multiplication are commutative, so it doesn't matter
   what direction you do the puzzle in, right...?"), atweddle, graynk, Majestic_Coat_6832,
   chicagocode and Dullstar read part 2 left to right and say why. Ours states the spec
   right to left, as the puzzle does, and the program reads left to right; `evaluateReverse`
   (with `List.sumReverse` and `List.productReverse`) is the proof that the two agree
   **[checked: `Proofs/Correct.sw`]**.
6. **Our proof is shorter than it needs to be written, in one place.** The last two theorems
   restate a three-line sum three times. With `_` holes and `_ = _ :=` in `calc`, which the
   checker already accepts, `part1Correct` and `part2Correct` shrink from 33 lines to 9, and
   `Correct.sw` from 189 to 165 (169 with the two comments kept), with `check Aoc.Day06.Proofs`
   still passing **[checked: `proj/`; I also checked that a wrong term in the same place is
   rejected]**. This is tidying, not a language gap.

The ranked candidates are in §5 and the decisions in §6 (D440–D446). The cheapest useful ones:

- `List.transposeFill` (a transpose that goes to the longest row, filling the gaps), with its
  cell lemma, so that padding and its 65 lines of proof leave `Day06.sw` and `Proofs/` and live
  in the library once (D440);
- a test of the trimmed example (D441), and the `_`-hole tidy of `Correct.sw` (D442);
- two tiny helpers, `Text.words` and `List.findMap` (D443);
- document what plain `List.transpose` does on rows of different lengths (D444).

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker. "Proofs" means theorems
in the file, not tests. The table lists the solutions that add something; the others (listed
after it) repeat the patterns.

| # | Language | Author / link | Lines | Method | Notable | Proofs? |
|---|---|---|---|---|---|---|
| 1 | Lean 4 | [septract](https://github.com/septract/aoc2025-ai-lean/blob/HEAD/Aoc2025/Aoc06-2.lean) | 159, 172 | spec over the grid, then an `Impl` with `fuel` | `Spec.charAt` = `getD i ' '`; `findProblemBoundaries` from blank columns; `include_str` of the real input and `#guard` on its answer | **stated, not proved**: `impl_eq_spec ... := by sorry` in both files, and `solve_correct` rests on it |
| 2 | Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/6/Problem6.dfy) | 156 | split on spaces; part 2 slices by the operator positions | `function transpose(vals, columns, rows) requires forall d :: d in vals ==> \|d\| == columns`; 9 `expect`s | **no lemma**; `ensures \|ops\| == length` and "every row has `length` numbers" on the parser |
| 3 | Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day06/Basic.lean) | 140 + 16 | column scan with `fuel` (`numCols + 2`) | pads with `replicate`; `isSpaceCol` reads `grid[row]?.bind (·[col]?)` | 6 theorems about `Problem.eval` (`rfl`, `simp`): `eval_empty_mul`, `eval_singleton_add` |
| 4 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day6_2.lean) | 35, 41 | transpose, split at blank columns | `def Matrix (T) (height) (width) := Vector (Vector T width) height` and `transpose (x: Matrix T a b): Matrix T b a`; `sploot` splits by predicate | no |
| 5 | Lean 4 | [dupuisf](https://github.com/dupuisf/aoc25/blob/HEAD/Aoc25/Day06.lean) | 68 | `Parsec` for part 1; blocks split at `""` | `Array₂ Nat` with `transpose : Option` ("Rows not all the same length") | no |
| 6 | Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day06.lean) | 24 | transpose **the whole text** (`str_transpose`), blank columns become `""`, `splitOn "\n\n"` | part 1 is `str_transpose` of each block again | no |
| 7 | Lean 4 | [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day6.lean), [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day6.lean), [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day6.lean), [frutjus](https://github.com/frutjus/aoc2025/blob/HEAD/day6/part2.lean), and 10 more | 24–154 | mostly column scans or transposes; `padRows` + `getD col ' '` (sdiehl) | 22 of the 27 Lean files use `(· == ' ')`-style placeholders; 14 use `toNat!`; josephmate's part B prints `0` | no |
| 8 | Idris 2, Agda | [Pengler38](https://github.com/Pengler38/AoC-2025/blob/HEAD/src/Day6.idr), [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day6.idr), [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day6/Solution.idr), [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day06.agda) | 44–80 | transpose of `words`, transpose of characters, split at empty chunks | Pengler38 hand-writes `collect` and marks everything `partial`; spikedoanz hand-writes `splitOnNothing` ("really not proud of this one... brute force theorem proving"); jpyamamoto's Agda has `postulate transpose` compiled to Haskell's `Data.List.transpose` | no |
| 9 | Haskell | [glguy](https://github.com/glguy/advent/blob/HEAD/solutions/src/2025/06.hs), [cinx16 and mstksg (Reddit)](https://www.reddit.com/r/adventofcode/comments/1pfguxk/2025_day_6_solutions/nsjvhu0/) | 9–37 | `splitWhen (all (' ' ==)) (transpose input)`, then part 1 transposes each block, part 2 reads its columns | glguy's doctest of the example (`>>> :main`); no padding (Haskell's `transpose` goes to the longest row) | no |
| 10 | Haskell | [NukeyFox](https://github.com/NukeyFox/AdventOfCode2025/blob/HEAD/day6/solution.hs), [nicuveo (Reddit)](https://www.reddit.com/r/adventofcode/comments/1pfguxk/2025_day_6_solutions/nt12via/), [beefyhalo](https://github.com/beefyhalo/aoc/blob/HEAD/src/2025/06.hs) | 32–44 | parse twice; or one `foldl'` over the reversed columns with a buffer | `foldl1` with the operator as a function; `Either Int Char` per column | no |
| 11 | OCaml, F#, Scala | [p4bl0](https://www.reddit.com/r/adventofcode/comments/1pfguxk/2025_day_6_solutions/nsldl9w/), [munchler](https://www.reddit.com/r/adventofcode/comments/1pfguxk/2025_day_6_solutions/nsk4cuf/), [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day06.fs), [lupari](https://github.com/lupari/aoc2025/blob/HEAD/src/main/scala/assignments/Day06.scala), [bishabosha](https://github.com/bishabosha/advent-of-code-2025/blob/HEAD/scala/2025_day06.scala) and 5 more | 19–240 | transpose and split; or a fold with an option per column | munchler's `Array.foldBack` that starts a new chunk at each blank; lboshuizen reads token positions with `Regex.Matches` and never looks at columns; p4bl0 uses `ocamllex` for part 1 | no |
| 12 | Gleam, Elixir, Clojure, Elm | [tilltheis](https://github.com/tilltheis/adventofcode-2025-gleam/blob/HEAD/src/day06.gleam), [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day06/day06.gleam), [nikola-benes](https://github.com/nikola-benes/aoc2025elixir/blob/HEAD/06_2.exs), [lasseebert](https://github.com/lasseebert/advent_of_code_2025/blob/HEAD/lib/advent/day_06.ex), [tschady](https://github.com/tschady/advent-of-code/blob/HEAD/src/aoc/2025/d06.clj), [caseyWebb](https://github.com/caseyWebb/advent/blob/HEAD/2025/src/Day06.elm) and 10 more | 10–154 | transpose and `list.chunk` / `chunk_by` / `partition-by` | nikola-benes: `Enum.split(-1)` takes the operator line off, `fn "+" -> &Enum.sum/1; "*" -> &Enum.product/1 end`, 15 lines; tilltheis hand-writes `list_split_last` | no |
| 13 | Roc, Koka | [arnemart](https://github.com/arnemart/aoc/blob/HEAD/2025/06/6.roc), [charlespierce](https://github.com/charlespierce/advent-code-2025/blob/HEAD/Solutions/Day06.roc), [wiseodd](https://github.com/wiseodd/aoc-2025/blob/HEAD/roc/day_06.roc), [junpls](https://github.com/junpls/aoc25/blob/HEAD/day06.kk) | 39–138 | split off the operator line; a Koka loop with `var`s | arnemart's `[.. as n, o] -> (n, split_line o)` (a pattern for "all but the last, and the last"); Roc's `Str.split_last`; junpls's `var current-op := '+'` loop | no |
| 14 | BQN | [RubenVerg](https://github.com/RubenVerg/aoc2025/blob/HEAD/6.bqn) | 4 | partition by the blank columns | 3 lines for both parts | no |
| — | Stitchwort | `aoc/src/Aoc/Day06/Day06.sw` + `Proofs/` | 36 (program) + 23 (tests); 33 + 34 + 136 (proofs, 26 theorems) | pad, transpose, `splitBy` the blank columns; one block, two readings | `Operator` type; the spec is cell by cell over the lines; `Nat.isRun`, `List.splitByRuns` link the blocks to the spec's column numbers | **yes**: `part1Correct`, `part2Correct`, for every input |
| — | Stitchwort, community shape | scratch `sw/haskell.sw` (cinx16 and glguy) | about 20 | transpose the words / transpose the characters, split at blank columns | one-line `words`; no padding | no |

Also read, and not in the table because they repeat these patterns: Lean LeanSerra, RussellEmerine,
gyk, eutro, stonarini, vanshjangir, dominikmascherbauer, xcnwf, natewhite345 (four small files), the
Clojure and Common Lisp pair narimiran, the Scala jelaby and otobrglez, the OCaml SharieRhea,
Kazkans and mbacarella, the Gleam bmatcuk and houli, and the Haskell gustavnorens, BraeTroutman
and PP6464 (a three-guard `problems'`). FER-PUH's file is a stub ("TODO: implement Day 06").

All rows are **[checked]**: taken from the fetched files, except cells marked **[cited]**; for
the grouped rows (7, 11, 12) I read some and counted the rest by `grep`. I ran none of them.

**Notes from reading** **[inferred, not run]**:

- The solutions that do not pad (Haskell's `transpose` goes to the longest row; Lean's
  tenthmascot and acarapetis, who build a `Vector` from the first row's width) work on the real
  input for a simple reason: its first line is full length and only the last is short.
- lboshuizen's F# never reads the character columns: it tokenises each line with
  `Regex.Matches(s, @"\S+")` and checks whether the token starts line up (`aligned`). It is a
  different reading of the puzzle, and works on the real input.
- Part 2's order has no effect on the answer, and 6 comments say so (finding 5), so many
  solutions read the columns left to right. Ours reads left to right too; the spec is the
  one that says right to left.

### 2.1 What I couldn't find

- **Unison, PureScript, Coq/Rocq, F\*, Effekt:** none in GitHub repository searches or the
  megathread. Repository searches for Coq and Rocq 2025 solutions returned nothing. The GitHub
  search API rate-limited me once (I waited and retried); searches are not exhaustive.
- **Lean repositories with no day 6 file:** 12 of the 33 Lean repositories I found
  (Dessertion, yshui, benjaminfjones, DavidMazarro, mfornet, a2435191, ianclement, joek13,
  rubydusa, FayCarsons, ChiefArug, andorp) have no file whose name says day 6 **[unverified:
  I matched on path names, not file contents; some may stop before day 6, or call it something
  else]**. HeikoRibberink's Koka and mpizenberg's and TeaDrinkingProgrammer's Roc repositories
  likewise have none, and frectonz's repository wasn't readable.
- **Linked pastes:** about 15 solutions are in `topaz.github.io/paste` links, which I did not
  decode (Gleam, Haskell, F#, Clojure, Racket, Swift).
- **Reddit itself:** not contacted; the megathread came from the Arctic Shift archive.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** Arctic Shift: one post search (`subreddit=adventofcode`, `author=daggerdragon`,
a one-day window, which found "2025 Day 6 Solutions", `1pfguxk`, 620 comments), and one comment
tree (`comments/tree?link_id=1pfguxk`); the first request timed out once and worked on the
retry. The tree holds 504 top-level comments (687 with replies), 499 not deleted. Scripts:
`scripts/langs.py` (language tags, as on day 3), `fp.py`, `counts.py`, `grep_rows.py`.

**Languages.** 487 of the 499 carry a `[LANGUAGE: …]` tag, 93 distinct. The top: Python 118,
Rust 50, C# 20, JavaScript 17, Haskell 17, Java 16, C++ 16, Kotlin 15, Go 15, TypeScript 12,
Ruby 11, C 10, Elixir 10, Zig 9, Common Lisp 9, Clojure 8, R 7, OCaml 6, Gleam 6, F# 5.
**Functional or proof-oriented (the day 3 list):** 77 comments, 31 with code: Haskell 17,
Elixir 10, Common Lisp 9, Clojure 8, OCaml 6, Gleam 6, F# 5, Scala 4, Scheme 2, Racket 2,
Emacs Lisp 2, Prolog 2, and one each Dafny, Admiran, Factor and Janet. **Array languages:** 13
comments, 11 with code: Q 3, Dyalog APL 3, Uiua 2, Goal 2, J 2, BQN 1. No Lean, Idris, Agda,
Koka, Roc or Unison tag (the Roc and Koka solutions I read came from GitHub).

**What the comments say about ragged input** (finding 3), by name: TheZigerionScammer
("the last line had some whitespace stripped out so it wasn't as long as the others"), darren
("my editor is set to automatically strip spaces at the end of lines"), Rush_Independent ("my
template was stripping whitespace at the end of the lines"), bakibol ("`read().splitlines()`
removes trailing spaces"), Jadarma ("be careful with removing trailing spaces, I do this as a
'best practice'"), s4uull ("my editor trimmed the test string"), eipi-10 ("adding padding to each
column since my editor removed it"), marconisdev ("I white space padded the lines for part 2 and
did a double transpose"), Yorshex ("assumes the trailing spaces are there"); and four Python
comments name `zip_longest` (AlexTelon: "to ensure we got all the full numbers on the last
column"; K722003, the_cassiopeia, PM_ME_YER_SIDEBOOB) **[checked: `grep_rows.py`, then read]**.

**Clever ones.** dijotal (Common Lisp) moves the operator row to the top, transposes the text,
cuts at the operators and `eval`s each piece as a Lisp expression; onrustigescheikundig (Chez
Scheme) reverses the lines "to put the operators at the top", transposes, puts a `'+` in front
and calls `eval`; AtomPhys (q) builds the string `"(*/)2 4 5"` and `value`s it; carllom (Python)
`eval`s `row[0].join(row[1:])`. The array-language solutions are three to six lines; BQN's
`Split ← ((¬-˜⊢×·+`»⊸>)∘≠⊔⊢)` is from BQNcrate. sheshanaag's Haskell reverses and transposes
and groups by "does this column start with an operator".

## 3. Themes

### 3.1 Transposing a ragged grid

Everyone transposes. The question is what happens when the rows are not the same length, and
the languages differ:

| Library | Rows `[[1], [2, 3]]` | Used by |
|---|---|---|
| Haskell `transpose` | `[[1, 2], [3]]` (as wide as the longest) **[cited: base docs]** | glguy, cinx16, mstksg, danvk, nicuveo, ~8 more |
| Python `zip(*rows)` | `[(1, 2)]` (as short as the shortest) | most Python solutions pad first |
| Python `zip_longest(*rows, fillvalue=' ')` | `[(1, 2), (' ', 3)]` | 4 comments |
| Clojure `(apply map vector rows)` | as short as the shortest **[cited: the language]** | extractedtarball, gehenna0451; darren removes the short operator row before transposing |
| Stitchwort `List.transpose` | `[[1, 2]]` (as wide as the **first** row) **[checked: `sw/p_trim.sw`]** | `Day06.sw` pads first |
| Stitchwort padded, as `sw/fill.sw` | `[[1, 2], [0, 3]]` | stand-in for D440 **[checked]** |

The real input has a first line of 3780 characters and a last line of 3779, so the unpadded
Haskell shape works on it in Stitchwort too. It stops working when the first line is the one
that's short, which is what an editor does to the example's first line. `sw/haskell.sw` passes
the padded example and fails the trimmed one:

```
  ✓ example           ran
  ✗ example, trimmed  (`==` is False)
      left:  (4277556, 3263823)
      right: (4277556, 3263827)
```

(The tool I used to write the scratch file trimmed the trailing spaces of a text block
silently; I hit the day's bug myself, and wrote the example as a list of strings.)

The committed program is right on the trimmed example: the padding is exactly there for this,
and `proj/src/Aoc/Day06/Tests/Trimmed.sw` passes both parts on it **[checked]**. The spec reads a
missing cell as a space, so the theorem covers every input including trimmed ones.

What padding costs us today: `paddedGrid`, `gridWidth`, `widen` (5 code lines in `Day06.sw`),
`Fits`, `foldWidenGrows`, `foldWidenFits`, `paddedAllLength`, `paddedGridRectangular`,
`columnsKeepEveryCell` (about 35 lines of `Grid.sw`'s 54), and `paddedCells`, `columnsAre`,
`blankPast` (about 28 lines of `Correct.sw`) **[checked: line counts]**. Those proofs say one
thing, once: **column c of the padded transpose is the list of `charAt line c`**. A library
function `transposeFill` with that as its lemma would hold it for every grid day (days 4, 6 and
7 are grids) **[inferred]**. The program with it:

```
def transposeFill (fill: a) (rows: List (List a)): List (List a) :=
  let width := rows.foldLeft (w row => Nat.max w row.length) 0
  (rows.map (row => row.padRight width fill)).transpose

def blocks (lines: List Text): List (List (List Char)) :=
  transposeFill ' ' (lines.map Text.toList) |> .splitBy isBlank
```

**[checked: `sw/fill.sw`: it passes the trimmed example and prints 4722948564882 and
9581313737063 on the real input.]** The definition is `paddedGrid` with the width folded in;
the saving is the 65 lines of proof moving to the library once, not the three program lines.

### 3.2 Where the problems start and end

| Method | Seen in | Stitchwort |
|---|---|---|
| Transpose, split at blank columns, read each block | 21 of 55 GitHub authors (with a split helper or blank test; 33 transpose); 12 of the 107 comments name a split helper, 49 transpose | `blocks` (ours): `List.splitBy`, which also has its lemmas (`splitByGroups`, `splitByConcat`, `splitByRuns`) |
| Use the operator row for the boundaries (`+`/`*` start a block) | about 8: raevnos, RudeGuy2000, extractedtarball, argentcorvid, Chemical_Chance6877, becchar, nt0z5ad, runnerx4 | an index scan; not needed |
| One pass over the columns with a stack or accumulator | about 10: nicuveo, beefyhalo, MyEternalSadness, melochupan, alexbaguette1, p4bl0, munchler (`foldBack`), junpls (a `var` loop), Working_Way | `foldLeft`; same answers (not written) |
| Build an expression and `eval` it | about 9: dijotal, onrustigescheikundig, Illustrious-Idea6245, AtomPhys, carllom, gehenna0451, argentcorvid (first draft) | no `eval`; `Operator.apply` instead |
| Parser combinators or a grammar for part 1 | about 8: Foldzilla, NeilNjae, Stano95, nicuveo (Haskell), grainytokyo (Instaparse), molochwalk (Factor EBNF), gpacaci (Prolog DCG), p4bl0 (`ocamllex`), dupuisf (Lean `Parsec`) | `Text.split`, `words` by hand; no combinators |
| Read token positions, never the columns | lboshuizen (F#) | n/a |

**[checked: read; the counts are mine and approximate.]** Four people (spikedoanz, Pengler38,
NukeyFox, PP6464) hand-wrote the "split a list at the empty entries" helper that `List.splitBy`
already is; spikedoanz's comment on his is "really not
proud of this one. felt a lot like i was doing brute force theorem proving". Ours has the
function and its proofs.

### 3.3 One grid, two readings

glguy, cinx16 and ours all split once and read each block twice, because "the left/right
alignment of numbers within each problem can be ignored" is true for part 1 and false for
part 2 (onrustigescheikundig: "So that was a lie"). Most solutions parse twice. In Stitchwort
the reading is a field of `Problem` (`rowNumbers`, `columnNumbers`), so part 1 and part 2 are
`sumBy` over the same list, and the proof's `blockRows` and `blockColumns` are the two halves.

### 3.4 Reading a number from cells

| Idiom | Seen in | Stitchwort |
|---|---|---|
| strip the spaces, then `read`/`parse`/`toNat!` | most (Haskell `read`, Lean `toNat!`, Python `int`, Rust `parse().unwrap()`) | `readNumber` (ours): `Nat.fromDigits` of `filterMap Char.digitValue`; no partial function, and `readNumberWritten` proves a number with spaces around it reads back as itself |
| fold `acc * 10 + d` | lboshuizen's `fromDigits`; Python numeric loops | `Nat.fromDigits` |
| `eval` the text | 9 | none |

14 of the 27 Lean files use `toNat!`; Pengler38's Idris marks every function `partial`
**[checked: grep, then read]**. Ours has no partial function: an
operator-less block counts 0 (the puzzle never has one) and the spec says so.

### 3.5 Library breadth

| Helper | Seen in | Stitchwort |
|---|---|---|
| `transpose` | everyone | `List.transpose` (first-row width; D444) |
| zip-longest / pad to the longest | 4 Python comments, Lean sdiehl (`padRows`), kim-em, `ljust`/`PadRight` in about 9 comments | `List.padRight`; no fill-transpose (**D440**) |
| `splitWhen`, `chunk_by`, `groupBy`, `wordsBy` | 21 of 55 GitHub authors, 12 of the 107 comments | `List.splitBy` |
| `words` (split on runs of spaces) | about 18 of the 107 comments, 24 of 71 files | **missing**: `"a b".words` is `E-UNKNOWN-FIELD: Text has no field or function words`, and `"a  b".split ' '` is `["a", "", "b"]`; one line `(line.split ' ').filter (w => not w.isEmpty)` (**D443**) **[checked: `sw/p_missing.sw`, `sw/p_missing2.sw`]** |
| take the last line off (`last`/`init`, `unsnoc`, `Enum.split(-1)`, `.pop()`, `unclip-last`, `split_last`, a `[.. as n, o]` pattern) | 13 named: mstksg, cinx16, hopingforabetterpast, NeilNjae, nikola-benes, sauntcartas, molochwalk, arnemart, acarapetis, Zenor27, tilltheis, jpyamamoto, Pengler38 | `List.init`, `List.last` (both present; **D446** on a snoc pattern) |
| first `Some` of a mapped list (`find?` + `bind`, `listToMaybe . mapMaybe`, `collectFirst`) | septract; ours twice | `(xs.filterMap f).head`; **`List.findMap` missing** (`E-UNKNOWN-FIELD`, same files) (**D443**) |
| the operator as a function (`(+)`, `&Enum.sum/1`, `%op{…}`, `getfield(Base, …)`) | about 10 | `Operator.apply` over an `Operator` type; `(+)` is D296, not now |
| `foldl1`/`reduce` | Haskell, F#, Raku, Kotlin | `sum`, `product` through `Add`/`Mul` |
| `sum`, `product` | everyone | `List.sum`, `List.product` |
| `include_str` of the real input, as a compile-time check | septract (`#guard solve actualInput = …`) | `include "…"` in `Tests/Input.sw` (present) |
| a doctest of the example | glguy (`>>> :main`), beefyhalo | `test` beside the code |

**Placeholders.** 22 of the 27 Lean files use `(· == ' ')`, `(· * ·)` and the like, and four
Scala files use `_`; that is evidence for SW-222, already parked. **Guards.** NukeyFox's
`splitOnHelper` and PP6464's `problems'` use Haskell guards: few, and the shapes are not
essential (SW-237, parked). **List batch 2 (SW-235):** day 6 adds one use of `splitAt`
(jpyamamoto's Agda separates the last line with `splitAt (length ls ∸ 1) ls`) and none of
`maxBy`, `dropWhile`, `takeWhile`, `span`, `tails`, `findIndex`.

### 3.6 Right to left, and the commutativity

Six comments read part 2 left to right and say why (finding 5); the Lily, Elixir and Odin
authors are among them. Ours proves it:

```
theorem evaluateReverse: (op: Option Operator) -> (xs: List Nat) -> evaluate op (List.reverse xs) = evaluate op xs
  | None,          xs => rfl
  | Some Add,      xs => List.sumReverse xs
  | Some Multiply, xs => List.productReverse xs
```

It is used once, in `answer2`, together with `List.mapReverse`, to turn the spec's right-to-left
list of column numbers into the program's left-to-right one **[checked]**.

### 3.7 Proofs and automation

What the community proved for day 6:

- **septract (Lean): the right statement, `sorry`.** `Spec.solve grid` is the grand total read
  from the grid (`isSpaceColumn`, `findProblemBoundaries`, `extractNumbers` right to left,
  `extractOp`); `Impl.solve grid` is one pass with `fuel`; `impl_eq_spec` is `sorry`. It is
  our architecture without the proof. The spec reads the grid with `charAt` = a space past the
  end, as ours does.
- **kim-em (Lean):** `Problem.eval_mul`, `eval_add`, `eval_empty_mul`, `eval_empty_add`,
  `eval_singleton_mul`, `eval_singleton_add`, all `rfl` or `simp`; nothing about the parser.
- **Hath995 (Dafny):** no lemma. `parseInput` has `ensures |ops| == length` and `ensures
  forall d :: d in data ==> |d| == length`, `transpose` has `requires` that every row has
  `columns` entries, and `expect` checks the rest at run time.
- **Typed or checked grids:** acarapetis's `Matrix T height width := Vector (Vector T width)
  height` (so `transpose` swaps the indices in its type), dupuisf's `Array₂` whose `transpose`
  returns an `Option` ("Rows not all the same length"), Hath995's `requires`. All three put the
  rectangular-grid fact in the signature, which is what our `List.AllLength` hypotheses
  (`columnsKeepEveryCell`, `List.transposeTwice`) carry as a separate lemma.
- **Totality without proofs:** kim-em's and septract's `fuel` (`numCols + 2`, `mc + 2`),
  against `partial` in Pengler38 and `decreasing_by`/`termination_by` in none.

**Where ours stands.** 26 theorems, 333 lines (Spec 90, Grid 54, Correct 189), over the
whole puzzle read cell by cell. It is the only one that closes. What the community cannot show
us is a technique: nobody got through the transposition. What our proof shows is where the
effort goes: about 65 of the 333 lines are padding (§3.1), and about 24 lines of `Correct.sw`
were avoidable (finding 6). The `*Congr` lemmas (`sumByCongr` ×4, `mapCongr` ×2,
`filterMapCongr` ×1 in `Correct.sw`) are D37's answer to rewriting under binders, and with
`_` for the functions they cost one line each: no change to D37 is needed **[checked:
`proj/`]**.

### 3.8 Speed

| Program | `stitchwort run` | `run --js` |
|---|---:|---:|
| Committed `Aoc.Day06.main` | 0.15 s | 0.26 s **[checked]** |
| `sw/haskell.sw` (cinx16's shape) | 0.22 s | 0.25 s **[checked]** |
| onrustigescheikundig (Chez Scheme) | 890 µs, 380 µs **[cited]** | |
| G_de_Volpiano (Haskell) | 375 µs, 8.25 ms **[cited]** | |
| JarroVGIT (Rust) | 22 µs, 36 µs **[cited]** | |
| Chungus1234 (Elixir) | 0.60 ms, 2.36 ms **[cited]** | |
| MyEternalSadness (Haskell, with maps) | 7.5 ms, 492 ms **[cited]** | |
| Chemical_Chance6877 (Gleam) | 3 ms, 3657 ms (repeated string slicing) **[cited]** | |

The whole command, including checking, is under a second either way. The only slow report is
Gleam's part 2, from slicing the same long string repeatedly, which the author diagnoses. Day 6
is not a performance risk.

## 4. Side by side

glguy's whole solution and the committed program's core: the same split once, read twice.

```haskell
-- glguy (Haskell)
main = do
  input <- getInputLines 2025 6
  let problems = splitWhen (all (' ' ==)) (transpose input)
  print (sum (map solve1 problems))
  print (sum (map solve2 problems))

solve1 xs = finish (head (last xs')) (init xs') where xs' = transpose xs
solve2 (x:xs) = finish (last x) (init x : xs)
finish '+' xs = sum (map read xs)
finish '*' xs = product (map read xs)
```

```
-- Stitchwort (Day06.sw)
def blocks (lines: List Text): List (List (List Char)) := (paddedGrid lines).transpose.splitBy isBlank

def parseProblem (columns: List (List Char)): Problem :=
  let rows := columns.transpose
  { operator = (columns.filterMap (column => column.last.flatMap Operator.parse)).head
  , rowNumbers = rows.init.map readNumber
  , columnNumbers = columns.map (column => readNumber column.init) }

def Operator.apply: Operator -> List Nat -> Nat
  | Add,      numbers => numbers.sum
  | Multiply, numbers => numbers.product
```

The differences are the padding (`paddedGrid`), the total `readNumber` in place of `read`, and
the `Operator` type with a total `evaluate` (None counts 0) in place of `finish`'s missing
cases (a crash on any other character).

The padding, in Python, in Haskell (none) and in Stitchwort today and with D440:

```python
# PM_ME_YER_SIDEBOOB (Python)
cols = list(zip_longest(*rows, fillvalue=' '))
```
```
-- Stitchwort today (Day06.sw)
def paddedGrid (lines: List Text): List (List Char) :=
  lines.map (line => line.toList.padRight (gridWidth lines) ' ')
def gridWidth (lines: List Text): Nat := lines.foldLeft widen 0
def widen (width: Nat) (line: Text): Nat := Nat.max width line.length
-- ... and blocks = (paddedGrid lines).transpose.splitBy isBlank

-- with D440 (sw/fill.sw)
def blocks (lines: List Text): List (List (List Char)) :=
  transposeFill ' ' (lines.map Text.toList) |> .splitBy isBlank
```

Elixir writes the operator as a function and the whole part 2 as one pipeline:

```elixir
# nikola-benes (Elixir, 06_2.exs)
{nums, [ops]} = IO.stream(:line) |> Enum.split(-1)
ops = String.split(ops) |> Enum.map(fn "+" -> &Enum.sum/1; "*" -> &Enum.product/1 end)
nums
~> to_charlist
|> Stream.zip_with(& &1 |> to_string |> String.trim)
|> stream_chunk_only(& &1 != "")
~> Stream.map(&String.to_integer/1)
|> Stream.zip_with(ops, fn nums, op -> op.(nums) end)
|> Enum.sum
```

and the proof statements: septract's, which stops at `sorry`, and ours.

```lean
-- septract (Lean 4)
theorem impl_eq_spec (grid : Grid) :
    Impl.solve grid = Spec.solve grid := by
  sorry
```
```
-- Stitchwort (Proofs/Correct.sw)
theorem part1Correct (lines: List Text): solvePart1 (parseWorksheet lines) = part1Spec lines := …
theorem part2Correct (lines: List Text): solvePart2 (parseWorksheet lines) = part2Spec lines := …
```

And the tidy (finding 6): the last step of `part1Correct` today and with holes.

```
    _ = List.sumBy (lo => List.sumBy (hi => if isProblem lines lo hi then … else 0)
          (List.range (gridWidth lines + 1))) (List.range (gridWidth lines)) :=
        List.sumByCongr
          (lo => List.sumBy (hi => Nat.keepIf (blockAnswer1 (blockOf lines lo hi)) (isProblem lines lo hi)) (List.range (gridWidth lines + 1)))
          (lo => List.sumBy (hi => if isProblem lines lo hi then … else 0) (List.range (gridWidth lines + 1)))
          (lo => List.sumByCongr (hi => …) (hi => …) (hi => term1 lines lo hi) (List.range (gridWidth lines + 1)))
          (List.range (gridWidth lines))
```
```
theorem part1Correct (lines: List Text): solvePart1 (parseWorksheet lines) = part1Spec lines :=
  calc solvePart1 (parseWorksheet lines)
    _ = _ := List.sumByMap ((p: Problem) => evaluate p.operator p.rowNumbers) parseProblem (blocks lines)
    _ = _ := blocksTotal lines blockAnswer1
    _ = part1Spec lines := List.sumByCongr _ _ (lo => List.sumByCongr _ _ (hi => term1 lines lo hi) (List.range (gridWidth lines + 1))) (List.range (gridWidth lines))
```

(The first is abridged with `…`; the second is the checked scratch version.)

## 5. Candidate features, ranked by value over effort

Kinds: **sugar** (syntax only), **library**, **tooling**, **language** (elaboration or kernel),
**tests** and **proofs** (no feature).

| Rank | Candidate | Kind | Value | Effort | Evidence | Ticket |
|---|---|---|---|---|---|---|
| 1 | **`List.transposeFill`**: transpose to the longest row, filling the gaps, with the cell lemma (column c, row r is `getOr fill c` of row r) | library | medium: day 6's padding and 65 lines of proof become one library lemma; days 4 and 7 are grids too; and it closes the "ragged rows" trap | small to medium (the proofs exist for `Text`; they generalise) | §3.1: 4 `zip_longest`, 9 padding/trim comments, `sw/fill.sw`, `sw/p_trim.sw` | none; one ticket, then re-base Day 06 on it |
| 2 | **A test of the trimmed example** (every trailing space removed) in `Tests/Examples.sw` | tests | low to medium: it is the day's most reported bug, and the committed example depends on invisible trailing spaces | trivial (4 lines, passes today) | §3.1, 9 comments; `proj/.../Trimmed.sw` | none; fits SW-224 |
| 3 | **Tidy `Correct.sw` with `_` holes** and `calc … _ = _ :=` (and check the other AoC proofs for the same restating) | proofs | low to medium: 189 to 165 lines, and the proof reads as its argument | trivial (checked) | §3.7, finding 6; `proj/` | none; fits SW-224 |
| 4 | **`Text.words`** (split on runs of whitespace) and **`List.findMap`** (first `Some`) | library | low: both are one-liners today, but `words` is in about 18 of the 107 comments and 24 of 71 files | trivial | §3.5 | none; with SW-235 or alone |
| 5 | **Document `List.transpose` on rows of different lengths** (it takes the first row's width, as `[[1], [2, 3]]` shows) | docs | low to medium: Haskell, Python's `zip_longest` and Lean users will assume the longest | trivial | §3.1 | none |
| 6 | **`Vec.transpose`** and a typed grid `Vec (Vec a w) h` | library | low to medium: removes `AllLength` hypotheses from grid proofs; three proof-language authors do it | small to medium; wait for the grid days | §3.7 | none; revisit after days 4 and 7 |
| 7 | **A snoc pattern** `[..init, last]` (or `List.unsnoc`) | language/library | low: `init` and `last` exist; 13 sources take the last line off | medium (patterns, coverage, motives) | §3.5 | not now |
| — | Operator sections `(+)`, `(· * ·)`, Scala `_` | sugar | low | small to medium | about 10 operator-as-function uses; 22 of 27 Lean files use `·` | **parked** (D296, SW-222) |
| — | Pattern guards | language | low on day 6 (2 Haskell files) | medium | §3.5 | **parked** (SW-237) |
| — | List batch 2 (`maxBy`, `dropWhile`, `span`, `splitAt`, …) | library | day 6 adds only `splitAt` (1 file) | small | §3.5 | **parked** (SW-235) |
| — | Rewriting under binders (the `*Congr` lemmas) | language | none needed: `_` holes make each `Congr` one line | — | §3.7 | D37; no change |
| — | Local mutable variables (Koka `var`: junpls) | language | low | large | 1 file here | **not now** (D299) |
| — | Arithmetic automation (`omega`, `grind`) | language/library | none on day 6 | large | no community proof used it | SW-101; no change |

Why this order:

- **Rank 1 is the only candidate that comes from the puzzle.** The day is about a grid whose
  rows are not the same length; our answer (pad, then transpose) is right, but it is written and
  proved by hand for one day. The community's answers are the library's: Python's `zip_longest`,
  Haskell's `transpose`. A library function with its cell lemma turns our 65 lines into a
  citation and makes the unpadded shape (finding 4) safe to write. I did not build it; `sw/fill.sw`
  defines it locally and the day's tests and real answers pass on it **[checked]**. Its lemmas
  are `paddedCells`, `columnsAre` and `blankPast`, restated for any list of lists
  **[inferred]**.
- **Ranks 2 and 3 are trivial and close real gaps:** the trimmed example passes today (so
  nothing breaks, and the test records why the padding is there), and the proof's argument
  should not be buried under restated terms.
- **Rank 4 is two one-liners.** They come up in many programs and in our own (`findMap` in
  `parseProblem` and `operatorOf`).
- **Rank 5 is a note.** The trap is real (§3.1), and the library doc is the cheapest place to
  put it.
- **Ranks 6 and 7 wait.** `Vec.transpose` helps only if the grid days use `Vec`; a snoc pattern
  is a language feature for something `init` and `last` already do.

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D440 | Add `List.transposeFill (fill) (rows)` (every row padded to the longest, then transposed) with its cell lemma and length lemmas, and re-base `Day06.sw` and `Proofs/` on it? | [yes; one ticket: library function and lemmas first, then Day 06] |
| D441 | Add a test of the puzzle's example with every trailing space trimmed (`["123 328  51 64", …, "*   +   *   +"]`, answers 4277556 and 3263827) to `Tests/Examples.sw`? | [yes; four lines, with SW-224] |
| D442 | Tidy `Proofs/Correct.sw` with `_` holes and `calc … _ = _ :=` (189 to 165 lines, checked), and look for the same restating in the other AoC proofs? | [yes; Day 06 now, the others as a sweep] |
| D443 | Add `Text.words` (split on runs of whitespace) and `List.findMap` (first `Some` of a mapped list)? | [yes; two small definitions with an `rfl` example each] |
| D444 | Say in the docs what plain `List.transpose` does when the rows differ in length (it keeps the first row's width: `[[1], [2, 3]]` gives `[[1, 2]]`), and leave it as it is? | [yes, document only; D440 is the answer for ragged grids] |
| D445 | Add `Vec.transpose` and a typed-grid lemma (`Vec (Vec a w) h`)? | [not now; revisit after the day 4 and day 7 notes] |
| D446 | Add a snoc list pattern `[..init, last]`, or `List.unsnoc`, for "all but the last, and the last"? | [not now; `List.init` and `List.last` exist] |

---

**Status** (short form, 22 Oct 2026): D440 `transposeFill`, pending; D441 trimmed-example test,
pending; D442 `Correct.sw` tidy, pending; D443 `Text.words` and `List.findMap`, pending; D444
document `transpose`, pending; D445 `Vec.transpose`, pending; D446 snoc pattern, pending.
Unchanged by day 6: D296 operator sections, D297 text patterns and D299 local mutable variables
not now, SW-222 (`_`), SW-228 (dot receiver), SW-235 (list batch 2) and SW-237 (guards) parked,
SW-101 backlog, D37 rewriting under binders unchanged.
