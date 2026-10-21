# AoC 2025 day 1: community solutions in other languages

**Date:** 21 October 2026. **Our version:** `aoc/src/Aoc/Day01/Day01.sw` (program),
`aoc/src/Aoc/Day01/Proofs/Part2.sw` (part 2 proved for any dial). **Earlier comparison:**
[aoc-day01.md](aoc-day01.md) ported *our* proof to Lean 4, Agda and Idris 2. This note
looks at what other people actually wrote for 2025 day 1, in the wild, and asks what that
suggests for Stitchwort.

Labels, as in the earlier note:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day1-community/sw/`,
run with the main checkout's `target/release/stitchwort`.

## 1. Summary

I read 25 solutions from 21 authors on GitHub and blogs: 12 in Lean 4, 3 in Idris 2, 1 in
Agda, 3 in Haskell, and one each in OCaml, F#, Scala 3, Koka, Gleam and Roc (§2). I then read
the r/adventofcode Day 1 megathread through the Arctic Shift archive (§2.2): 636 top-level
comments, 609 of them not deleted, about 125 distinct language tags. 82 comments are in
functional or proof-oriented languages (25 Haskell, 8 Elixir, 6 each in Common Lisp, F# and
Gleam, 4 each in Scala, OCaml, Racket, Scheme and Emacs Lisp, 2 each in Lean and Clojure, and
one each in Dafny, Effekt, Prolog, Janet, Factor, Admiran and Ada). I read the 35 of those 82
with code inline, and 4 linked files (§2.2). No megathread comment is tagged Idris, Agda, Coq/Rocq, Koka,
Roc, Elm, PureScript, Erlang or Unison. I found no Unison solution anywhere, and couldn't
reach a Lean Zulip thread (§2.1).

The main findings:

1. **No community solution proves part 2 for a whole list of turns against a click-by-click
   specification.** The repository in the first set that says it has proofs (kim-em, Lean)
   proves the dial stays below 100 and restates each branch of its counting function (`rfl`,
   `unfold; simp`). Three solutions avoid the question instead: they compute the
   specification directly, expanding every turn into single clicks (tenthmascot in Lean,
   mstksg's write-up in Haskell, junpls's `part-two-sneaky` in Koka). **One megathread
   comment comes close:** Hath995's Dafny states, for one turn, that the closed-form zero
   count equals the number of multiples of 100 in the range the turn sweeps (two lemmas,
   each by induction on the turn length). It says nothing about the list of turns, and the
   loop over turns has no postcondition **[checked: read the file; not run, so "it verifies"
   is the author's claim, cited]**. Stitchwort's `turnCount` is the same kind of per-turn
   statement, and `zerosPassedCorrect`, for every dial size, start and list of turns, is the
   only list-level correctness proof I found **[checked: read all 25 and the 35 inline
   plus 4 fetched megathread files; the other megathread comments I read are programs without theorems]**.
2. **The short solutions get their length from four things:**
   - a number type that wraps at 100 by itself (Lean's `Fin 100`, Haskell's `Finite 100`);
   - signed turns (`L68` read as `-68`);
   - a scan (`scanl`) and a count;
   - part 2 written as brute force or as a single `divMod`.

   tenthmascot's Lean is 17 lines, lboshuizen's F# is 13, glguy's Haskell is 36 with
   comments. In the megathread, bramhaag's Haskell has the same shape (`scanl`,
   `filter (== 0)`, `zipWith zeros ps rs`) in 10 lines, and sim642's Scala is 30 lines with
   its parser. **Stitchwort can already be written that way.** A 13-line version with signed
   `Int`s, Euclidean `%`, `scanLeft`, `count` and `zipWith` prints the right answers on the
   real input **[checked: `run.sw`, 1076 and 6379, 0.56 s]**. Our committed Day01.sw is
   longer on purpose: it has a `Dial` type with a range proof, and a dial size parameter for
   the proof.
3. **Integer division is the puzzle's crux, and Stitchwort's choice matches the languages
   that had no trouble.** Lean, Koka and Stitchwort make `Int`'s `/` and `%` Euclidean, and
   Haskell's `divMod` floors. OCaml, F#, Scala and Gleam truncate, so their solutions add
   `((x % 100) + 100) % 100` or special cases for negative numbers **[checked: read; Lean and
   Koka cited]**.
4. **Where other languages are more convenient for this day, the differences are small and
   mostly library or syntax:**
   - **text patterns:** Scala's `case s"L$num"`, Gleam's and Elixir's `"L" <> n`, and Lean's
     `match s.take 1 with | "L"`. In the megathread, 9 comments with inline code use one (2
     Gleam, 2 Elixir, 2 Python and others), plus sim642's Scala file **[checked: regex over
     the 214 comments with inline code, then read the hits]**;
   - **operator sections and placeholders:** Haskell's `(== 0)`, Lean's `(· == 0)`, and Scala's
     `.count(_ == 0)` (sim642). 10 megathread comments with inline code have a section
     (half of them Haskell);
   - **early exit when parsing:** a `do` block over `Option`/`Except` in Lean, `?` in Roc,
     `use … <- result.try` in Gleam;
   - **multi-line text literals** for the example (Idris and Python-style `"""`, Roc's `\\`);
   - **list helpers:** `mapAccumL`, `unzip`, `divMod`. In the megathread, `divMod`, `quotRem`
     or an equivalent is in 20 comments with inline code, mostly Python and Rust, so it isn't
     an FP idiom; Haskell's `divMod` is in XamazingX5's snippet and in glguy's and
     G_de_Volpiano's files. `mapAccumL` or `map_fold` shows up in 4 FP comments (Gleam, F#
     and Factor, besides mstksg);
   - **test output:** Lean's `#guard_msgs` and glguy's doctests show the expected output
     beside the code.

   Stitchwort has no text patterns, operator sections or multi-line text **[checked:
   `p_textpat.sw`, `p_section.sw`, `p_multiline.sw` give `E-PARSE`]**, and none of those
   list helpers. A failed test says only "evaluated to False" **[checked: `p_fail.sw`]**. It
   can express the early exit with a user-defined ability, but the library has none to
   reuse **[checked: `p_abort.sw`]**.
5. **Proof automation barely appears in day 1 community code.** One `omega` (Hamberg:
   `newVal < 100` after `% 100`) and a handful of `simp`. Where automation matters is our
   kind of proof, as the earlier note measured (`omega`/`simp`/`grind` halved the Lean port).
   That is already SW-101.
6. **Brute force is a common first draft for part 2** (tenthmascot, junpls, mstksg's
   write-up). In the megathread 13 of the functional comments I read do it, usually saying so:
   sim642 ("silly but works"), munchler ("elegant but slow"), bread-dreams, raevnos ("it was
   like 4 AM"), danvk, itmuckel, statisticalnormality, runnerx4, molochwalk, geza42,
   Valuable_Leopard, Chemical_Chance and marvinborner's Effekt (a `Click` effect per click)
   **[checked: read each; counted by hand]**. In Stitchwort it gives the right answer, but slowly: expanding all 639,879
   clicks takes 5.5 s with `stitchwort run`, against 0.56 s for the closed form, and 0.95 s
   with `run --js` **[checked: `brute.sw`, `run.sw`]**.

The ranked candidates are in §5 and the decisions in §6. The megathread doesn't change their
order. The cheapest useful ones, with where each stands on 21 Oct 2026:

- a failed `a == b` test prints both values (SW-216, in progress);
- an `Abort` ability in the library for parsers (SW-217, in progress);
- a few `Text` helpers (SW-218, in progress) and `List`/`divMod` helpers (SW-219, backlog);
- multi-line text literals (SW-221, in progress);
- making `f().x` mean `(f()).x` (SW-220, backlog).

Operator sections (D296) and text patterns (D297) are "not now". SW-222 is a backlog design
note on Scala-style `_` placeholders.

## 2. The solutions

"Lines" counts non-blank lines that aren't whole-line comments (`--`, `//`, `#`). Doc
comments in `{- -}` are counted, so glguy's count is inflated **[checked: `grep` over the
fetched files]**. "Proofs" means theorems in the file, not tests.

| # | Language | Author / link | Lines | Notable | Proofs? |
|---|---|---|---|---|---|
| 1 | Lean 4 | [kim-em/AoC2025](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day01/Basic.lean) (+ [Day01.lean](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day01.lean)) | 93 | `structure Rotation`, `foldl` over `(pos, count)` pairs; left turn as `(pos + 100 - d % 100) % 100` on `Nat`. The README describes tooling for Claude to solve the puzzles autonomously | 8 theorems: result `< 100`, distances 0 and 100, and one restatement per branch of `countZeroCrossings` (`rfl`, `unfold; simp`) |
| 2 | Lean 4 | [sdiehl/aoc-2025-lean](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day1.lean) | 72 | `Option` `do` with `←` in the parser; separate left/right zero counters | no |
| 3 | Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day01.lean) | 17 | `l.scanl (· + Fin.intCast ·) (50 : Fin 100) \|>.count 0`; part 2 is `flatMap (List.replicate n d)`, brute force | no |
| 4 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day1.lean) ([part 2](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day1_2.lean)) | 17 + 26 | `abbrev Turn := Fin 100` with `-count` wrapping; part 2 uses `Rat.ceil` | no |
| 5 | Lean 4 | [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day1.lean) | 71 | `let mut` + `for` in `IO`; part 2's left turn is `((-pos) % 100 + d) / 100`, our formula | no |
| 6 | Lean 4 | [dupuisf](https://github.com/dupuisf/aoc25/blob/HEAD/Aoc25/Day01.lean) | 38 | `Std.Internal.Parsec` parser (`asciiLetter`, `digits`); `mapM` + `let some rots := … \| exitWithError` | no |
| 7 | Lean 4 | [joek13](https://github.com/joek13/aoc2025/blob/HEAD/Day1.lean) | 40 | `Option` `do`; `scanl act 50 \|>.count 0`; `reduceOption` | no |
| 8 | Lean 4 | [DavidMazarro](https://github.com/DavidMazarro/advent-of-code-2025/blob/HEAD/AdventOfCode2025/Day01.lean) | 52 | `Except String` errors, `sequence`; dial is `Fin 100`; comments on `Int.tdiv` rounding | no |
| 9 | Lean 4 | [benjaminfjones](https://github.com/benjaminfjones/advent-of-code-2025/blob/HEAD/AdventOfCode2025/D1.lean) | 67 | `#guard`, `#guard_msgs in #eval` pin the answers in the file; part 2 click by click with a `where` helper | no (tests only) |
| 10 | Lean 4 | [0xmycf](https://github.com/0xmycf/Advent-of-code/blob/HEAD/2025/day01/Day01.lean) | 88 | `def Lock := {n : Nat // n < 100}` with tactic blocks inside definitions, as our `Dial`; extra `% 100` "makes the proof easier" | range proofs inline |
| 11 | Lean 4 | [natewhite345](https://github.com/natewhite345/aoc25/blob/HEAD/day1/part2.lean) | 77 | `Except` `do` with `throw`; `#eval` checks after each function; click-by-click helper | no |
| 12 | Lean 4 | [Hamberg (blog)](https://hamberg.no/erlend/posts/2025-12-01-aoc-2025-day1.html) | about 38 | `Fin 100` dial; `⟨newVal, (by omega : newVal < 100)⟩`; writes his own `List.scanl` | one `omega` |
| 13 | Idris 2 | [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day1.idr) | 39 | defines `scanl` itself; `unpack` + list patterns `'L' :: rest` | no |
| 14 | Idris 2 | [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day1/Solution.idr) | 63 | contrib's `Text.Lexer`/`Text.Parser`; `\|\|>` pipelines; leaves a hole `?wja` | no |
| 15 | Idris 2 | [Zikoat](https://github.com/Zikoat/adventofcode/blob/HEAD/2025/idris/Day1.idr) (unfinished) | 80 | examples as `Refl` theorems; a `failing "Mismatch between: 18 and 19."` block checks a wrong claim is rejected; `"""` text | `Refl` examples |
| 16 | Agda | [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day01.agda) | 67 | `with … \| …` on two values; renames `_+ℤ_`/`_+ℕ_` to avoid clashes; `%ℕ` gives a `ℕ` from an `ℤ`, as our `Int.modNat` | no |
| 17 | Haskell | [mstksg](https://github.com/mstksg/advent-of-code/blob/main/2025/AOC2025/Day01.hs) ([write-up](https://github.com/mstksg/advent-of-code/wiki/Reflections-2025#day-1)) | 42 | parse by mapping `R`→space, `L`→`-` and `read`; `countTrue (== 0) . scanl' (+) 50 . map (modulo @100)`; part 2 `mapAccumL` + `divMod` | no |
| 18 | Haskell | [glguy](https://github.com/glguy/advent/blob/main/solutions/src/2025/01.hs) | 36 | `[format\|2025 1 (@D%u%n)*\|]` input parser; a left turn is a right turn on the negated dial, one `divMod` each; doctests `>>> :main` | no |
| 19 | Haskell | [PP6464](https://github.com/PP6464/AoC-2025-Haskell/blob/HEAD/src/Day01.hs) | 33 | `State` monad, `quotRem` then `mod` | no |
| 20 | OCaml | [FizzyElt](https://github.com/FizzyElt/ocaml_aoc_2025/tree/HEAD/bin/day1) | 36 + 42 | `Scanf.sscanf s "%c%d"`; truncating `mod`, so `if next_p < 0 then next_p + 100` | no |
| 21 | F# | [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day01.fs) | 13 | `Seq.scan dial 50 >> Seq.filter ((=) 0) >> Seq.length`; `((n + delta) % 100 + 100) % 100`; floor division via `float` | no |
| 22 | Scala 3 | [bishabosha](https://github.com/bishabosha/advent-of-code-2025/blob/HEAD/scala/2025_day01.scala) | 31 | `case s"L$num" => -num.toInt`; named tuples `(pos: Int, turn: Int)`; `foldLeft` with a `:` lambda block | no |
| 23 | Koka | [junpls](https://github.com/junpls/aoc25/blob/HEAD/day01.kk) | 52 | parser combinators (`many`, `one-of`, `pint`); local `var` in a pure function; `part-two-sneaky` = brute force | no |
| 24 | Gleam | [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day01/day01.gleam) | 79 | `case s { "L" <> n -> … }`; `use rotations <- result.try(…)`; truncating `%` handled by hand | no |
| 25 | Roc | [mpizenberg](https://github.com/mpizenberg/aoc-2025/blob/HEAD/roc/day01.roc) | 71 | `\\` multi-line example in the file; `var $pos` + `for`; `?` on parse failure; prints demo answers beside real ones | no |
| — | Stitchwort | `aoc/src/Aoc/Day01/Day01.sw` + `Proofs/Part2.sw` | 53 + 141 | `Dial` record with a range proof; `scanLeft`/`count`/`zipWith`/`sum` pipelines; tests on the example and the real input; full part 2 proof | yes, for any dial |
| — | Stitchwort, short | scratch `run.sw` | 13 | signed `Int` turns, Euclidean `%`, the same pipelines | no |

All rows are **[checked]**: I fetched and read each file (tarballs from GitHub, or `gh api`
for single files). The Hamberg row is from the blog post's code blocks **[cited]**.

**Correctness notes from reading** **[inferred, not run]**:

- FizzyElt's part 1 (`q1.ml`) returns `(p, count)` instead of `(next_p, count)` from its
  fold, so the dial never moves. It looks like a committed bug.
- BrianNormant's Idris file leaves the hole `?wja` in a type, so it isn't total as committed.
- mstksg's write-up shows a part 2 on unwrapped `Int`s that compares with `0`; his actual code
  uses `divMod` (the table follows the code).

### 2.1 What I couldn't find

- **Unison:** no 2025 day 1 solution in GitHub repository or code search, on the web, or in
  the megathread **[checked: `gh search repos/code`, two web searches, the megathread tags]**.
- **Dafny:** the GitHub search found none, but the megathread has one (Hath995, §2.2). The
  earlier "none" was a gap in the search, not in the world.
- **Reddit's own pages:** reddit.com and its mirrors weren't reachable from here (a "blocked
  by network security" 403 and a "Prove your humanity" challenge), and I did not try to get
  round them. The megathread came from the Arctic Shift archive instead (§2.2).
- **A Lean Zulip AoC 2025 thread:** none found by search.
- **The puzzle text** at adventofcode.com: not fetched. `docs/aoc-2025.md` §3 restates it.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift) is a public archive
of Reddit data with a keyless API. I made two requests, one for the post
(`/api/posts/ids?ids=1pb3y8p`) and one for the comment tree
(`/api/comments/tree?link_id=t3_1pb3y8p&limit=25000`, 2.4 MB), then 4 plain requests to
`raw.githubusercontent.com` for linked files (Dafny, Effekt, Scala, Haskell); a fifth, for the
Admiran file, returned 404. **[checked: the status page was up; the response bodies are saved
in the scratchpad `reddit/arctic/`]**

**Terms.** The repository README and `api/README.md` state no usage conditions beyond "No
uptime or performance guarantees", a note that excessive requests are rate limited (HTTP 429,
`X-RateLimit-Reset` headers; "this is a free service, so be considerate"), and a pointer to the
monthly dumps for bulk use. Two requests are well inside that. I found no `LICENSE` file at the
repository root **[checked: the READMEs; `LICENSE` returned 404]**. The archive holds public
comments and the authors' names as posted; this note quotes short snippets and names authors
the way the first part does, with a link to each.

**What it holds.** The post is "2025 Day 1 Solutions" (1 Dec 2025, score 68, archived on 2 Dec
2025). The tree has 1,139 comments in all: **636 top-level comments**, of which 27 are
`[deleted]`/`[removed]`, 585 carry a language tag, and 24 are untagged (questions, or a
language named in prose). The post's recorded `num_comments` was 871 when it was archived, fewer
than the 1,139 in the tree, so I have no sign that comments are missing, but I can't confirm
the archive is complete **[checked: counted in the JSON]**. 214 of the 609 live
comments include code inline; the rest link to GitHub or a paste site, so counts of code
patterns below are lower bounds.

**The landscape.** Tags counted once per comment and language (a comment tagged
`C, C++` counts for both); spelling variants merged by hand. About 125 distinct tags:

| Language | Comments | | Language | Comments |
|---|---|---|---|---|
| Python | 130 | | Zig | 6 |
| Rust | 52 | | Common Lisp | 6 |
| C++ | 27 | | Gleam | 6 |
| Haskell | 24 (+1 "type-level Haskell") | | F# | 6 |
| C | 23 | | Nim | 5 |
| Go | 19 | | Scala | 4 |
| Java | 18 | | OCaml | 4 |
| JavaScript | 18 | | Racket | 4 |
| C# | 17 | | Scheme (incl. Guile, Chez) | 4 |
| TypeScript | 16 | | Emacs Lisp | 4 |
| Ruby, Kotlin | 10 each | | Lean | 2 |
| Elixir, R | 8 each | | Clojure | 2 |
| Uiua, AWK, Lua | 7 each | | Dafny, Effekt, Prolog, Janet, Factor, Admiran, Ada | 1 each |

The functional or proof-oriented tags (Haskell, Elixir, Common Lisp, Gleam, F#, Scala, OCaml,
Racket, Scheme, Emacs Lisp, Lean, Clojure and the one-offs in the bottom right) add up to 82
comments, 13% of the 609 live ones. There is no Idris, Agda, Coq/Rocq, Koka, Roc, Elm,
PureScript, Erlang or Unison. Python, Rust and C-family languages make up well over half
**[checked: `langs3.py` over the archived JSON; the "FP" grouping is mine, and Kotlin, Swift and
Julia are not in it]**.

**What I read.** Of the 82 functional comments, 35 have code inline, and I read all of them
(arrays and Uiua aside, which I skipped). I opened 4 linked files; the rest are links I did
not follow. The table lists the ones that add something to §2's table; the
others repeat its patterns (a `scanl` plus a count in Haskell, a fold over a pair in F#,
Scala and OCaml, a floor or Euclidean `%` or a hand fix for a truncating one).

| # | Language | Author / link | Lines | Notable | Proofs? |
|---|---|---|---|---|---|
| 26 | Dafny | [Hath995](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nroam7m/) ([file](https://github.com/hath995/dafny-aoc-2025/blob/main/problems/1/Problem1.dfy)) | 148 | `rotateAndCount` returns `(position, zeros)`, with `ensures` that the zero count equals the size of `set x \| pos - n <= x < pos && x % 100 == 0` (and the right-turn analogue); two lemmas prove it by induction on `n`, with `calc` blocks | yes, per turn (set-cardinality specification); none for the list; the loop has `invariant pos < 100` only |
| 27 | Effekt | [marvinborner](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrp8gcs/) ([file](https://github.com/marvinborner/AdventOfCode/blob/main/2025/01/solve.effekt)) | 64 | effects and handlers: `Click(at)` for every single click, `Final(at)` for the end of a turn; a handler per part counts zeros; a streaming `Scan[Char]` parser; part 2 starts one low (`part2 - 1`) because the dial starts at 0 | no |
| 28 | Scala | [sim642](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nro5egi/) ([file](https://github.com/sim642/adventofcode/blob/master/src/main/scala/eu/sim642/adventofcode2025/Day1.scala)) | 30 | `case s"L$i" => -i.toInt`; `.count(_ == 0)`; his own `%+` for a non-negative modulo; part 2 is `flatMap(i => Seq.fill(i.abs)(i.sign))` then part 1 | no |
| 29 | Haskell | [G_de_Volpiano](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrosjsz/) ([file](https://github.com/GuillaumedeVolpiano/adventOfCode/blob/master/2025/days/Day1.hs)) | 56 | a `Streamly` byte fold with a strict state record; `total \`divMod\` 100` and a correction `delta` for landing on 0 or leaving it from a left turn | no |
| 30 | Haskell | [Foldzilla](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/ns2f2mm/) | inline | `newtype Dial = Dial Int` with `instance Num Dial` wrapping at 100 through `mkDial`; he says it did not make part 2 cleaner | no |
| 31 | Haskell | [XamazingX5](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nro20ik/) | inline | one `scanl` whose state is the `(quotient, remainder)` pair of `(acc + x) \`divMod\` 100`, then `sum . map (abs . fst)`; I did not run it, and a left turn that lands on 0 looks like it needs the extra correction G_de_Volpiano adds **[inferred]** | no |
| 32 | Haskell | [bramhaag](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrol4v2/) | 10 | `scanl`, `filter (== 0)`, `zipWith zeros ps rs`, a three-guard `zeros`; `parse ('L':n) = negate $ read n` | no |
| 33 | Haskell | [NeilNjae](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrrhtgt/) | inline | `Either Int Int` as the instruction type (`Left n` is a left turn); `foldl'` over `(here, count)`; `MultiWayIf` corrections | no |
| 34 | type-level Haskell | [nicuveo](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/ns9evsd/) | inline | Peano numbers, `Add`, `Sub`, `Mod` as type families, `Fold` over a type-level list; part 1 on the example only, the compiler computes the answer | no |
| 35 | Haskell | [statisticalnormality](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nry9q5j/) | inline | part 1 in the `State` monad; part 2 builds the list of every click (`getClicks`) and filters | no |
| 36 | Haskell | [itmuckel](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrrehyb/) | inline | part 2 is recursion one click at a time (`turnLeftFor iterator n`), `left`/`right` bump a counter | no |
| 37 | Haskell | [danvk](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrphfa2/) | inline | part 2: positions as a second `scanl (+)`, then `length . filter ((==) 0 . (\`mod\` 100)) $ [(a + 1) .. b]` per turn | no |
| 38 | F# | [munchler](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrpr692/) | inline | `Seq.scan`; part 2 with `seq { pos + sign .. sign .. pos + rot }`, labelled "elegant but slow" | no |
| 39 | F# | [r_so9](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrrf5yr/) | inline | part 1 a `scan`, part 2 a `fold` with `abs ((n + delta) / 100)` and one correction | no |
| 40 | OCaml | [POGtastic](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nroa3qa/) | file (link only) | splits turns into pieces of at most 99 so each makes at most one click; says the stdlib lacks a prelude (`Seq.pairwise`) | no |
| 41 | OCaml | [Saser](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrt3fth/) | inline | `Base`; `turn_right` once, and a left turn by mirroring the dial (`(100 - dial) % 100`), with a comment explaining it; about 250 µs **[cited]**; expect tests | no |
| 42 | Gleam | [SurplusSix](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrpn4ef/), [Chemical_Chance](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrobb47/), [tymscar](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrpng7b/) | inline | `list.map_fold` and `int.modulo` (SurplusSix); `"L" <> r -> int.parse("-" <> r)` and click-by-click recursion (Chemical_Chance); tymscar wants string interpolation and a `debug` that prints any value **[cited]** | no |
| 43 | Elixir | [Maximum_Expression](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrrkocw/), [daic0r](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrqiwo2/) | inline | `def rotate("L" <> clicks, pos)` as function heads (text prefix patterns); `Integer.mod`; 472 µs and 528 µs per part, on his machine **[cited]** | no |
| 44 | Lean 4 | [ecyrbe](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrxjfzt/), [vsaraph](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nru0fvr/) | inline | ecyrbe: `match s.data with \| 'L' :: rest`, `IO` errors with line numbers, part 2 as floor division over pairs (`hi / 100 - lo / 100`); vsaraph: `Except String Int` with `throw`, part 1 only | no |
| 45 | Common Lisp, Scheme, Racket, Emacs Lisp | [dijotal](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nron17f/), [CowImaginary3155](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nroodvl/), [Roberti42](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrqns7f/), [Valuable_Leopard_799](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrqz3l2/), [geza42](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nropzut/) | inline | dijotal: closed form `(floor (1- current) modulo) - (floor (+ current delta -1) modulo)`, reading `L68` as a Lisp symbol; Valuable_Leopard: `labels` helpers `up`/`down`, one click at a time; geza42: `-running-sum` and `make-list` per click | no |
| 46 | Factor, Janet, Prolog | [molochwalk](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrrm212/), [veydar_](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nrq6fdq/), [_rabbitfarm_](https://www.reddit.com/r/adventofcode/comments/1pb3y8p/2025_day_1_solutions/nro9kqq/) | inline (Prolog links to blog posts) | an `EBNF:` parser then `accumulate*` (Factor); a PEG parser (Janet); a DCG that threads the dial state (Prolog) | no |

All rows are **[checked]** (inline code or the fetched file), except where a cell says
**[cited]** or **[inferred]**. Permalinks are to the comments on reddit.com. I did not fetch
them, only the archive's copy, and the comment text could have been edited since it was
archived.

**Notes from the megathread**:

- **Several FP authors say they are learning the language.** XamazingX5, fegte, aocwgpl,
  loleik, vanZuider, FCBStar-of-the-South, bmatcuk, jenaro94 and maciek_glowka all say so, so
  the style reflects "first Haskell/Gleam/OCaml program" as often as idiom. I'm not reading
  design signals into those solutions beyond what the authors complain about.
- **What authors complain about is mostly the same four things:** the sign of `%` or `mod` on
  negatives (fegte: "From now I hate the mod operator"), a left turn that starts or ends on
  0, library gaps (POGtastic writing `Seq.pairwise`; tymscar's missing file I/O and string
  interpolation in Gleam), and off-by-ones in part 2.
- **Two solutions use effects.** marvinborner's Effekt uses a handler per part, which is the
  shape of our `State` ability example. Stitchwort has abilities and handlers
  (`examples/accept/abilities.sw`), so that program is expressible; I did not port it
  **[inferred]**.
- **A modular type appears once more.** Foldzilla's `instance Num Dial`, next to Lean's
  `Fin 100` (4 solutions) and Haskell's `Finite 100`, makes six, which is relevant to D298
  (§3.2).

## 3. Themes

### 3.1 Parsing a line like `L68`

| Approach | Who | Example |
|---|---|---|
| Pattern on a text prefix | Scala, Gleam, Elixir | `case s"L$num" => -num.toInt` / `"L" <> n -> #(Left, …)` / `def rotate("L" <> clicks, pos)` |
| Match on a one-character text | Lean (joek13, DavidMazarro, natewhite345) | `match str.take 1 with \| "L" => … (str.drop 1)` |
| First character, then the rest | Lean (most), Stitchwort | `line.front` + `line.drop 1 \|>.toInt!` |
| List of characters | Idris, Haskell (PP6464, bramhaag, danvk, NeilNjae), Lean (ecyrbe) | `case unpack str of 'L' :: rest => …`, `match s.data with \| 'L' :: rest` |
| Rewrite the text, then `read` | Haskell (mstksg) | `R`→space, `L`→`-`, `read` the whole input as `[Integer]` |
| Format parsers | OCaml, glguy | `Scanf.sscanf s "%c%d"`, `[format\|2025 1 (@D%u%n)*\|]` |
| Parser combinators | Koka, Lean (dupuisf), Idris (BrianNormant) | `one-of("LR")` then `pint()`; `asciiLetter` then `digits` |

How failure is handled differs more than how lines are split:

- **Crash on bad input:** `panic!`, `toNat!`, `error`, `failwith`.
- **`Option`/`Except` with a `do` block:** sdiehl, joek13, DavidMazarro, natewhite345:
  ```lean
  def Action.fromString? (s : String) : Option Action := do
    let dir <- Direction.fromString? (s.take 1)
    let amt <- (s.drop 1).toNat?
    return Action.mk dir amt
  ```
- **`?`** (Roc), and **`use … <- result.try`** (Gleam).
- **Megathread:** most FP comments either crash on bad input (`error`, `failwith`,
  `let assert Ok(...)` in Gleam) or ignore it; only ecyrbe and
  vsaraph (Lean) use `IO`/`Except` with messages, and veydar_ (Janet) and molochwalk (Factor)
  use a parsing library (PEG, EBNF) that fails as a unit.

**Stitchwort today.** `t.uncons` with character patterns gives the same shape as Lean's
"first character, then the rest", and one `match` covers bad input **[checked:
Day01.sw]**:

```
def Turn.parse (t: Text): Option Turn :=
  match t.uncons with
    | Some ('L', rest) => rest.toNat.map Left
    | Some ('R', rest) => rest.toNat.map Right
    | _                => None
```

What isn't there:

- **Text patterns.** `| "L" => …` and `| "L" ++ rest => …` are both `E-PARSE: expected a
  pattern` **[checked: `p_textpat.sw`, `p_misc.sw`]**. Number and character patterns exist.
- **Prefix and substring helpers.** The library has no `Text.drop`, `Text.take`,
  `Text.startsWith` or `Text.stripPrefix`, and `Text.split` takes a `Char`, not a `Text`
  **[checked: the list of `Text.` definitions in `crates/elab/src/std`]**.
- **A reusable early exit.** There's no `do` notation, but an ability does the same job.
  This works today **[checked: `p_abort.sw`, 2 tests pass]**:
  ```
  def turn (t: Text): {Abort} Int :=
    let (c, rest) := need t.uncons
    let n := need rest.toInt
    if c == 'L' then -n else if c == 'R' then n else fromEmpty (abort())

  def parse (t: Text): Option Int := toOption (() => turn t)
  ```
  The library has no such ability, though. The file declares `Abort`, `need`, `toOption`
  and its own `Empty: Type` (13 lines). `Void` can't be used, because it's a `Prop`, and an
  operation's result must be a `Type` (`E-UNIVERSE` **[checked]**). *Since SW-217 the
  library has one: `Std.Abort`, with `need`, `ensure`, `abort`, `toOption` and `orElse`
  (docs/syntax.md, "`Abort`").*

### 3.2 Integer and modular arithmetic: part 2's crux

Part 2 counts the multiples of 100 a turn passes through. Going right from `p` by `n`, that's
`(p + n) / 100`. Going left, either mirror the dial or use floor division.

| Language | `%` on negatives | What the solutions do |
|---|---|---|
| Lean 4 | Euclidean ("The Div Int and Mod Int instances implement Euclidean division" [Lean reference](https://lean-lang.org/doc/reference/latest/Basic-Types/Integers/)) **[cited]** | `(pos - d) % 100` directly. ngrislain's left count is `((-pos) % 100 + d) / 100` |
| Haskell | `mod`/`divMod` floor | glguy: `(zeros, neg -> loc') = (neg loc + n) \`divMod\` 100`, one line per direction |
| Koka | Euclidean ("always a non-negative number" [Koka docs](https://koka-lang.github.io/koka/doc/std_core_int.html)) **[cited]** | `(current - 100).abs % 100` mirror |
| Agda | `%ℕ` on `ℤ` gives `ℕ` | `newpos %ℕ 100`, as our `Int.modNat` |
| OCaml, F#, Scala, Gleam | truncating | `((x % 100) + 100) % 100`, or `if next < 0 then next + 100`. lboshuizen gets floor division through `float` and `floor`. Megathread: Scala `Math.floorMod` (Kevincav, FCBStar), Gleam `int.modulo` (SurplusSix), sim642's own `%+`; marvinborner's Effekt writes `a - floor(a.toDouble / b.toDouble) * b` |
| Elixir, Common Lisp, Scheme, Racket, Emacs Lisp, Clojure | `Integer.mod`/`div` floor; `mod`/`floor` floor; Scheme `modulo` floors, `quotient` truncates | `Integer.mod(pos - clicks, 100)` (Elixir); dijotal's `(floor (1- current) modulo)` differences; CowImaginary3155 uses `quotient` and an explicit `if` for the sign |
| Stitchwort | Euclidean (`crates/elab/src/std/core.sw:778`); also `Int.tdiv`/`tmod`, `Int.fdiv`/`fmod`, `Int.modNat` | committed: `Int.modNat` into `Dial`, and the mirror `((size - p) % size + n) / size`. Scratch: `(p + t) % 100` on `Int` **[checked]** |

The mirror trick that glguy documents ("a left turn is a right turn on a negated dial") is
the formula in our `Dial.zerosDuring`. ngrislain and junpls use it too. It's the simplest
correct closed form, and Stitchwort's `%` lets it be written directly:

```haskell
-- glguy (Haskell)
sim loc ((DL, n) : xs) = (loc', zeros) : sim loc' xs
  where (zeros, neg -> loc') = (neg loc + n) `divMod` locations
```
```
-- Stitchwort (scratch run.sw), checked against the real input
def hits (p: Int) (t: Int): Nat :=
  if t >= 0 then ((p + t) / 100).toNat
  else (((-p) % 100 - t) / 100).toNat
```

Missing next to Haskell: `divMod` (a quotient-and-remainder pair). Stitchwort writes
`let (q, r) := (x / 100, x % 100)` instead **[checked: syntax.md, patterns in `let`]**.

**Numbers that wrap by themselves.** Lean's `Fin 100` (tenthmascot, acarapetis,
DavidMazarro, Hamberg) and Haskell's `Finite 100` (mstksg) have `+` and `-` modulo 100. That
makes part 1 a one-liner with no `% 100` anywhere:

```lean
-- tenthmascot (Lean)
def solve_aux (l : List Int) : Nat :=
  l.scanl (· + Fin.intCast ·) (50 : Fin 100) |>.count 0
```

Foldzilla's Haskell wraps by hand instead, with `newtype Dial = Dial Int` and an `instance Num Dial`
whose `+` and `-` call `mkDial (… \`mod\` 100)`; he says it did not make part 2 cleaner,
which is the same split as our `Dial`: the type gives part 1, and part 2 still needs a count of
wraps.

Stitchwort's `Fin n` is the unary indexed type (positions in a `Vec`), with `ofNat`/`toNat`
and no arithmetic **[checked: `std/Fin/Fin.sw`]**. Our `Dial` record plays the part of
`Fin 100`, with the range proof `Int.modNatLt`, where Hamberg writes `by omega`.

### 3.3 Folds, scans and state

- **`scanl` then count:** most solutions (tenthmascot, joek13, mstksg, lboshuizen, Hamberg,
  spikedoanz). Hamberg and spikedoanz had to write `scanl` themselves.
- **`foldl` over a `(position, count)` pair:** kim-em, sdiehl, Scala, Gleam, OCaml, Agda.
- **`mapAccumL`** (mstksg), and **`unzip`** of a list of pairs (glguy).
- **Local mutable variables** in otherwise pure code:
  - Lean's `let mut` + `for` (ngrislain, dupuisf);
  - Koka's `var zeroes := 0` inside a pure `fun`;
  - Roc's `var $pos`.
- **A `State` monad** (PP6464, statisticalnormality in the megathread).
- **Effects and handlers:** marvinborner's Effekt emits a `Click` per click and handlers count
  them; a Prolog DCG threads the dial state (_rabbitfarm_).
- **Megathread counts** (comments with inline code): `scanl`/`scan`/`reductions` or a running
  sum in 14, 6 of them Haskell; a fold over a `(position, count)` pair in most of the rest.

**Stitchwort today** has `List.scanLeft`, `count`, `zipWith`, `sum`, `concatMap`,
`replicate`, `filterMap` and `foldLeft` **[checked: std listing]**. The committed part 1 and
part 2 are scan pipelines like mstksg's:

```
def zerosPassed (start: Dial highest) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move start
    |> .zipWith Dial.zerosDuring turns
    |> .sum
```

Missing: `List.mapAccumLeft` and `List.unzip` **[checked: not in the std listing]**. There
is no local mutable variable; a user-defined `State` ability does the job
(`examples/accept/abilities.sw`).

### 3.4 Syntax conveniences

| Convenience | Seen in | Stitchwort |
|---|---|---|
| Lambda shorthand on a method | Lean `(·.dial == 0)` | method sections `.isZero`, `.drop 1` **[checked: syntax.md]** |
| Operator sections and placeholders | Haskell `(== 0)` (5 megathread comments), F# `((=) 0)`, Lean `(· + ·)`, `(· == 0)`, Scala `.count(_ == 0)` (sim642) | not supported (D296 is "not now"; SW-222 is a backlog note on Scala-style `_`): `xs.count (== 0)` is `E-PARSE` **[checked: `p_section.sw`]**; write `(p => p == 0)` |
| Pipelines | Lean `\|>.`, F# `>>`, Idris `\|\|>`, Gleam `\|>` | `\|>` with method sections; no `>>` (SW-22, not now, D10) |
| `where` helpers | Lean (benjaminfjones), Haskell (glguy, mstksg), Agda | local `def`s in a block; `where` is `E-WHERE` by design (syntax.md) |
| Named tuples | Scala `(pos = …, turn = …)` | records; tuples are positional |
| Multi-line text | Idris `"""`, Roc `\\`, Lean (literal newlines in `"…"`), Guile (runnerx4's example is a string with literal newlines) | `"""…"""` text blocks (SW-221, docs/syntax.md); a newline inside `"…"` is still `E-PARSE`; `include` reads a file |
| Calling a unit function in a chain | Lean `(← IO.FS.lines input).mapM …` | `IO.readAllLines().filterMap parse` reads as `IO.readAllLines (().filterMap parse)`, giving ``E-UNKNOWN-FIELD: `Builtin.UnitType` has no field or function `filterMap` `` **[checked: first try at `run.sw`]**; write `(IO.readAllLines()).filterMap` |

### 3.5 Testing and tooling

- **In-file evaluation and pinned output.** benjaminfjones pins each answer under the
  function it checks:
  ```lean
  /-- info: (32, 6) -/
  #guard_msgs in
  #eval (do let ins ← p1_test; pure $ List.foldl foldDoRot2 (initDial, 0) ins.toList)
  ```
  natewhite345 leaves `#eval spin 0 (.mk .L 1) --99` lines after each function. glguy's
  doctest `>>> :main + "L68\nL30…"` shows `3` and `6`. Roc's `run!` prints the demo answers
  beside the real ones.
- **Megathread:** Saser (OCaml) mentions expect tests; I saw no doctests or pinned-output
  lines elsewhere in the FP comments with inline code, but most comments are code without tests.
- **Examples as theorems:** Zikoat's Idris `rotateDial_example2: rotateDial 19 (-19) = 0 =
  Refl`.
- **Checking that something is rejected:** Zikoat's
  `failing "Mismatch between: 18 and 19."` block.
- **Stitchwort today:**
  - `test "…" := …` and `theorem … := rfl` on the example. The scratch `p_rfl.sw` checks
    both parts by `rfl`, including the 600-click brute-force part 2, in 0.39 s
    **[checked]**.
  - `include` tests on the real input.
  - `stitchwort eval FILE EXPR` (it printed `6: Nat` for part 2 of the example
    **[checked]**) and `stitchwort repl`.
  - Rejected programs are tested by the `examples/reject` harness, not in the language.
- **A failed test doesn't show the values.** `test "…" := part1 [0, 1, 0] == 3` prints
  `✗ wrong on purpose ran (evaluated to False)`, not what `part1 [0, 1, 0]` was
  **[checked: `p_fail.sw`]**. Lean's `#guard_msgs` and glguy's doctests show both.

### 3.6 Proofs and automation

What the community proved for day 1:

- **kim-em:** `applyRotation_lt_100` (`unfold; cases rot.dir <;> simp [Nat.mod_lt]`), plus
  seven small lemmas: three about distances 0 and 100, and four that restate the branches of
  `countZeroCrossings`:
  ```lean
  theorem countZeroCrossings_right (pos dist : Nat) :
      countZeroCrossings pos ⟨Direction.right, dist⟩ = (pos + dist) / 100 := by
    rfl
  ```
  None of them links the arithmetic count to the clicks.
- **Hamberg:** `(by omega : newVal < 100)` where the value is `x % 100 |>.toNat`. The
  post says he is "being a bit hand-wavy" with proofs **[cited]**.
- **0xmycf:** range proofs inside definitions with `constructor`, `apply Nat.mod_lt`, and
  `trivial`. The code adds a redundant `% 100` with the comment "this just makes the proof
  easier".
- **Zikoat (Idris):** examples by `Refl`.
- **Brute force as its own specification:** tenthmascot, mstksg's write-up and junpls's
  `part-two-sneaky` compute part 2 by expanding every turn into clicks. That is our
  `zerosPassedSpec`. They run it rather than prove the closed form equal to it. So do the
  13 megathread comments in §1.
- **Hath995 (Dafny, megathread):** the specification is a set,
  `|set x | pos - n <= x < pos && x % 100 == 0|` for a left turn and
  `|set x | pos < x <= pos + n && x % 100 == 0|` for a right one, and `rotateAndCount` must
  equal its size. The lemmas run by induction on `n` with a `calc` chain per case (the new
  endpoint is a multiple of 100 or it isn't), the same two-case split as our `stepLeft` and
  `stepRight`. Dafny's solver handles the `x / 100` and `x % 100` steps; our version spends
  its length on the same arithmetic (`rightCount`, `leftCount`) **[inferred: I did not run
  Dafny; the line counts and structure are read from the file]**. What it doesn't have:
  a theorem over the list of turns, or one for the answer (the loop has `invariant pos < 100`
  and no `ensures`).

So the community gives no new evidence about automation for this day. The earlier note's
measurement stands: in our port, `omega`, `simp` and `grind` did the bookkeeping, and none of
them helps with `/` or `%` by a variable. One small point is new: Stitchwort checks the
brute-force specification on the example by `rfl` quickly (0.39 s for the whole file), as
Lean's `decide +kernel` did in the earlier note.

**Since the earlier note**, `calc` and `rewrite` have landed and are used throughout
`Proofs/Part2.sw` (items 1 of that note's ranking). Proof irrelevance (SW-93) and `ext`
lemmas (SW-95) are still open, and `dialExt`/`dialExtAt` remain the motivating example.

### 3.7 Speed of the obvious program

| Program | Command | Time |
|---|---|---|
| Closed form (scratch `run.sw`) | `stitchwort run` | 0.56 s **[checked]** |
| Brute force, 639,879 clicks (scratch `brute.sw`) | `stitchwort run` | 5.5 s **[checked]** |
| Same brute force | `stitchwort run --js` | 0.95 s **[checked]** |
| mstksg closed form, Haskell | criterion, parsing excluded | 229 µs **[cited]** |
| Saser, OCaml (closed form, mirror trick) | his timing, a 2021 laptop | about 250 µs **[cited]** |
| Maximum_Expression, Elixir (closed form) | his timing, Ryzen 7, JIT on | 472 µs and 528 µs per part **[cited]** |

The brute-force answer is right, and 5.5 s is usable. `--js` runs it about six times
faster. The Haskell figure is for a different method and input, so it only shows that brute
force isn't needed there.

## 4. Side by side: the shortest Stitchwort

This is the scratch `run.sw`, which prints 1076 and 6379 on `aoc/inputs/day01.txt`
**[checked]**. It follows mstksg and glguy, not our committed shape (it has no `Dial` type
and no `solvePart1`/`solvePart2`, so it isn't a proposal to change Day01.sw):

```
def parse (t: Text): Option Int :=
  match t.uncons with
    | Some ('L', rest) => rest.toInt.map (n => -n)
    | Some ('R', rest) => rest.toInt
    | _                => None

def hits (p: Int) (t: Int): Nat :=
  if t >= 0 then ((p + t) / 100).toNat
  else (((-p) % 100 - t) / 100).toNat

def main(): {IO} () :=
  let turns := (IO.readAllLines()).filterMap parse
  let positions := turns.scanLeft (p t => (p + t) % 100) 50
  IO.print "Part 1: ${positions.count (p => p == 0)}"
  IO.print "Part 2: ${(positions.zipWith hits turns).sum}"
```

With the candidates below, the parse could be `| "L" ++ rest => …`, the count
`positions.count (== 0)`, and the call `IO.readAllLines().filterMap parse`. Each is a
few characters, which is why they rank on cost more than on value.

## 5. Candidate features, ranked by value over effort

"Value" means for AoC-style programs and proofs; "effort" is a rough size. Kinds: **sugar**
(syntax only), **library**, **tooling**, **language** (elaboration or kernel).

| Rank | Candidate | Kind | Value | Effort | Evidence | Ticket |
|---|---|---|---|---|---|---|
| 1 | **A failed `a == b` test prints both sides** (`expected 3, got 2`) | tooling | medium: every day's tests | small | Lean `#guard_msgs`, glguy doctests, Roc demo lines (§3.5); `p_fail.sw`. The megathread adds one (Saser's expect tests), so little new | SW-216, in progress |
| 2 | **`Abort` ability in the library**, with `Option.need` (or `orAbort`) and a handler to `Option`, plus a `Type`-level empty type for operation results | library | medium: every parser | small | Lean `Option`/`Except` (sdiehl, joek13, natewhite345, DavidMazarro; three with `do`; the megathread adds ecyrbe and vsaraph), Roc `?`, Gleam `result.try`, Janet PEG and Factor EBNF parsers (§3.1); `p_abort.sw` works with 13 user lines | SW-217, in progress. SW-68 is the `IO` side (`Result` from `IO`), not this |
| 3 | **`Text` helpers:** `drop`, `take`, `startsWith`, `stripPrefix: Text -> Text -> Option Text`, and `split` on a `Text` separator | library | medium | small | 8 of 12 Lean solutions use `drop 1`/`take 1`; Gleam, Elixir and Scala prefix patterns (9 megathread comments with inline code, plus sim642's file) (§3.1) | SW-218, in progress |
| 4 | **`List.mapAccumLeft`, `List.unzip`, `Nat.divMod`/`Int.divMod`** | library | low to medium | small | mstksg `mapAccumL` + `divMod`, glguy `unzip` + `divMod` (§3.2, §3.3); the megathread has `divMod` or an equivalent in 20 comments with inline code (mostly Python and Rust) and `map_fold`/`mapAccumL` in 4 FP ones | SW-219, backlog |
| 5 | **`f().x` means `(f()).x`** when there's no space before `(`: a call with `()` followed by dot notation | sugar (parser) | low to medium: `main` bodies, effectful chains | small | `run.sw` first try (§3.4); not seen in the megathread, which is mostly languages without the issue | SW-220, backlog |
| 6 | **Multi-line text literals** (`"""…"""`, as Scala, Idris and Python write them) for examples in files | sugar (lexer) | low to medium | small | Idris (Zikoat), Roc, Lean (0xmycf, natewhite345) embed the example (§3.4); one more in the megathread (runnerx4's Guile); `include` covers real inputs | SW-221, in progress. SW-62 (long literals) is related, not the same |
| 7 | **Operator sections** `(== 0)`, `(+ 1)`, `(100 -)` | sugar | low to medium | small to medium (prefix `-` and tuples need care: is `(- 1)` a section or `-1`?) | Haskell, F#, Lean `·` (§3.4); Scala `_ == 0` and 5 more Haskell sections in the megathread | **not now** (D296); SW-222 is a backlog design note for Scala-style `_`. SW-22 (`>>`) is the neighbouring "not now" |
| 8 | **Text patterns:** first literal ones (`\| "L" =>`), then prefix ones (`\| "L" ++ rest =>`) | language (patterns) | medium for parsing generally, low for day 1 (character patterns already cover it) | medium (literal patterns can reuse the number-pattern route through `DecEq`; prefix patterns need a new desugaring and coverage rule) | Scala `s"L$num"`, Gleam and Elixir `"L" <> n`, Lean `match s.take 1 with \| "L"` (§3.1); in the megathread 9 comments with inline code use a text-prefix pattern, and none is in Lean or Idris | **not now** (D297) |
| 9 | **A modular number type** (`Mod n`, or arithmetic on `Fin n`) with `+`, `-`, `fromInt` and an `Add` instance | library (with laws) | low to medium: day 1 has `Dial` | medium (`Add` needs `zeroAdd`, `assoc` and `comm` proved modulo `n`) | Lean `Fin 100` (4 solutions), Haskell `Finite 100`, and Foldzilla's `instance Num Dial` in the megathread (§3.2) | none |
| 10 | **Local mutable variables** (`var x := 0` … `x := x + 1`, desugared to a `State` handler or a fold) | language | low: folds and abilities cover it | large | Lean `let mut`/`for`, Koka `var`, Roc `var $` (§3.3) | none |
| — | Term-level arithmetic automation (`omega`-like, by reflection) | language/library | high for proofs, none for day 1 programs | large | earlier note; Hamberg's one `omega` | SW-101 (backlog), no change suggested |
| — | Faster evaluator for brute-force specifications | tooling | medium | large | §3.7 (5.5 s against 0.95 s with `--js`) | evaluator performance (related: SW-84, SW-74); use `--js` meanwhile |
| — | In-language "must not check" tests (Idris `failing`) | tooling | low for AoC | medium | Zikoat (§3.5) | none; `examples/reject` serves the compiler's own tests |

Why this order:

- **Ranks 1 to 4 are cheap library or tooling work.** They make every later AoC day a
  little easier without touching the language. They're the same kind of work as the list
  toolkit that already exists.
- **Ranks 5 and 6 are lexer or parser changes with a clear precedent**, but they are
  surface syntax, so they are Matt's call. Rank 5 in particular changes how `f().x` reads.
- **Ranks 7 to 10 change the language's surface or semantics more.** Each has an easy way
  round today (a lambda, `uncons` with character patterns, the `Dial` record, folds), so day
  1 alone doesn't justify them. Ranks 7 and 8 are decided "not now".
- **The megathread didn't move the order.** It adds evidence to ranks 2, 3, 4, 7 and 8 and
  one more modular-type example to rank 9, and it shows that most functional programmers on
  day 1 wrote the same `scanl` or fold we can already write. The one new proof-shaped
  data point (Hath995's Dafny) is a per-turn statement like our `turnCount`, so it supports
  the list-level theorem being worth having rather than any new feature.

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D290 | Should a failed `test` whose body is `a == b` print both values (and the same for `!=`, `<`, `<=`)? | SW-216, in progress |
| D291 | Should `Std` get an `Abort` ability (an empty `Type` for its result, `Option.need`/`orAbort`, a handler to `Option`), so parsers can stop early without `match` ladders? | SW-217, in progress |
| D292 | Should we add `Text.drop`, `Text.take`, `Text.startsWith`, `Text.stripPrefix` and splitting on a `Text` separator? | SW-218, in progress |
| D293 | Should we add `List.mapAccumLeft`, `List.unzip`, `Nat.divMod` and `Int.divMod`? | SW-219, backlog |
| D294 | `f().x`: should it mean `(f()).x` (today it means `f (().x)` and fails)? | SW-220, backlog (`name()` with no space is a call, then dots apply) |
| D295 | Multi-line text literals, written `"""…"""` (Scala, Idris, Python)? | SW-221, in progress |
| D296 | Operator sections `(== 0)`, `(+ 1)`, `(100 -)`? | **Decided: not now; think about Scala-style `_` later** (Matt, 21 Oct 2026; SW-222) |
| D297 | Text patterns: literal (`\| "L" =>`) now, prefix (`\| "L" ++ rest =>`) later? | **Decided: not now** (Matt, 21 Oct 2026) |
| D298 | A modular number type (`Mod n` with `+`, `-` and laws), or arithmetic on `Fin n`? | [not now; revisit if another day needs it] |
| D299 | Local mutable variables (`var`, Koka/Roc style)? | [not now] |

---

**Status** (short form, 21 Oct 2026): D290 test failures show values, SW-216 in progress;
D291 `Abort` ability, SW-217 in progress; D292 `Text` helpers, SW-218 in progress; D293
list/`divMod` helpers, SW-219 backlog; D294 `f().x`, SW-220 backlog; D295 `"""` text, SW-221
in progress; D296 operator sections, not now (SW-222 backlog design note for `_`); D297 text
patterns, not now; D298 modular type, not now; D299 mutable locals, not now. No decision is
pending, and the megathread changes none of them.
