# AoC 2025 day 2: community solutions in other languages

**Date:** 21 October 2026. **Our version:** `aoc/src/Aoc/Day02/Day02.sw` (program: an
arithmetic series per block length and repeat count, with computed Möbius-style weights for
part 2), `aoc/src/Aoc/Day02/Proofs/` (both parts proved equal to the puzzle's own method for
every input). **Earlier comparison:** [comparisons/aoc-day02-general/](../../comparisons/aoc-day02-general/README.md)
is a Lean 4 prototype of *our* part 2 proof (SW-159), which the Stitchwort proof then followed
(SW-166). This note looks at what other people wrote for 2025 day 2, in the wild, and asks what
that suggests for Stitchwort. It follows the shape of [aoc-day01-community.md](aoc-day01-community.md).

Labels, as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day2-community/sw/`,
run with the main checkout's `target/release/stitchwort`. Fetched solutions are in `gh/proof/`
and `gh/fp/` beside it, and the megathread data in `arctic/`.

## 1. Summary

I read 56 solutions on GitHub and GitLab: 14 in Lean 4, 3 in Idris 2, 1 in Agda, 1 in Dafny,
13 in Haskell, 4 in OCaml, 3 in F#, 5 in Scala, 2 each in Elixir, Clojure and Elm, and one each
in Koka, Gleam, Roc, Effekt, Chez Scheme and Admiran (§2). Two Sonnet sub-agents fetched and
summarised them; I checked the claims the note relies on against the saved files. I then read
the r/adventofcode Day 2 megathread through the Arctic Shift archive (§2.2): 630 top-level
comments, 614 not deleted, about 95 distinct language tags. 66 comments are in functional or
proof-oriented languages (19 Haskell, 8 Scala, 6 F#, 5 each in Clojure, Elixir and Common
Lisp, 3 each in OCaml, Gleam and Scheme, 2 each in Emacs Lisp and Admiran, and one each in
Lean, Dafny, Prolog, Factor and Janet). I read all 66; 25 of them have code inline. No Unison,
PureScript, Coq/Rocq or F\* solution turned up anywhere.

The main findings:

1. **No community solution proves day 2 correct.** The one that states the theorems (kim-em,
   Lean 4) states exactly ours: the closed-form sum for one block length and repeat count
   equals walking the bases (`sumRepetitionsInRange_correct`, our `repeatedCorrect`), and each
   part equals a brute-force filter over the range (`sumInvalidInRange_correct`,
   `…Part2_correct`, our `part1Correct`/`part2Correct`). All five are `sorry`, with comments
   saying an automated prover "was unable to prove" the string-to-arithmetic steps and that a
   generated proof "times out". The proved lemmas there are about geometric and arithmetic
   series (`omega`, `nlinarith`, Mathlib's `Finset.sum_range_id`). Hath995's Dafny makes the
   specification and the program the same predicate (`exists k :: … n == repeat(n[..k], |n|/k)`)
   and verifies only loop bookkeeping. Others prove index bounds (a2435191) or carry a data
   invariant (jpyamamoto's Agda `evenDigits`, 0xmycf's subtype) **[checked: read each file]**.
   Stitchwort's `part2Correct` has no hypothesis and no digit limit; kim-em's statements
   assume `r.hi < 10 ^ 20`.
2. **Three method families, and brute force is the most common.** Of the 56 GitHub solutions,
   about 30 walk every id and test its digits; about 20 generate the repeated numbers (a base
   times `11`, `101`, `10101`, …) and keep those in range, deduplicating with a set or `nub`;
   6 add arithmetic series per block length (kim-em part 1, GuillaumedeVolpiano, jpyamamoto
   part 1, Casper-Guo part 1, beefyhalo's bounds, erickalkman). In the 66 functional megathread
   comments, at least 30 brute-force and say so ("Simple brute force", "horribly
   inefficient", "naive and slow") and about 12 generate candidates **[checked: counted by hand;
   the boundaries between families are mine]**.
3. **Part 2's double counting is everyone's snag, and our weights are the textbook fix.**
   sim642: "toSet because some IDs can be created multiple ways (2222 is 2-2-2-2 and 22-22)".
   Most fix it with a set. Two functional solutions and two megathread comments in other
   languages use inclusion–exclusion (a third, in C++, was considering it): erickalkman's Chez Scheme has a table to 20 with the
   comment "EDIT: apparently this is the negative of the Möbius function", GuillaumedeVolpiano
   hard-codes the 6- and 10-digit cases, and Key_Pack_9630 (C) and Akari_Takai (Rust) name
   Möbius inversion. Our `plus`/`minus` computes the same weights for every repeat count
   (the `weights` test is erickalkman's table) **[checked]**.
4. **The short solutions are short because of string helpers.** lupari's Scala is 12 lines:
   `s.take(s.length / 2) == s.drop(s.length / 2)` and
   `(1 to s.length / 2).exists(k => s.grouped(k).distinct.size == 1)`. tenthmascot's Lean part 2
   is `[1:s.length].toList.any (fun p => s == s.drop p ++ s.take p)` (some rotation equals the
   string). **Stitchwort can write the halves and the rotation today** with the new `Text.take`/`drop` and `++`: a
   19-line brute-force file gives the right answers **[checked: `brute.sw`, `probes.sw`]**.
   What is missing is a chunking helper (`chunksOf`/`grouped`/`sized_chunk`, in 26 megathread
   comments with code), a text repeat (`String.replicate`, `String.duplicate`,
   `concat . replicate`), `divisors`, and a list dedup **[checked: `p_chunks.sw`]**.
5. **Three new frictions came out of writing the community shapes in Stitchwort:**
   - `s |> .contains t` asks whether `s` occurs in `t`, because dot notation puts the receiver
     in the first `Text` parameter, which for `Text.contains` is the pattern. It's documented
     (Text.sw, docs/syntax.md), but my first brute force silently missed 111 **[checked:
     `p_contains_dot.sw`]**. This is a data point for D302 (the dot-notation receiver rule).
   - `n != 0 && len % n == 0` is `E-AUTO-STUCK: can't decide n != 0 here`: `&&` doesn't pass
     its left side to its right the way `if` does. Haskell's `len `mod` k == 0` guards are in
     most part 2 checks **[checked: `p_and_div.sw`]**.
   - The obvious brute force (`ranges.concatMap ids`, 1,917,096 ids, then `filter` and `sum`)
     fails under `stitchwort run` with `E-RESOURCE: … recursed more deeply than allowed` after
     3 s; `run --js` gives the right answers in 77 s, and summing one range at a time works under
     `run` in 295 s **[checked: `brute.sw`, `brute2.sw`]**. See §3.7.
6. **Big numbers are a non-issue for us and a small one elsewhere.** Lean, Agda, Koka, Elixir and
   Haskell's `Integer` have unbounded integers; most others use 64-bit ints, and FCBStar (Scala)
   "still fell for" overflow in part 2 before adding `toLong`. Stitchwort's `Nat` is unbounded,
   and the committed tests go to 20-digit ids **[checked: Day02.sw `long ids`]**.

The ranked candidates are in §5 and the decisions in §6 (D330–D335). The cheapest useful ones:

- a small library batch: `List.chunksOf`, `Text.repeat`, `Nat.divisors`, a list dedup
  (D332, beside SW-219);
- `&&` and `||` passing their left operand as a fact to the right one (D331);
- `Text.contains` and friends as a test case for the receiver rule research (D330, D302);
- the `run` resource failure on a 1.9-million-element list as evidence for SW-66 (D333).

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker; block comments are
counted, so files with long doc comments are inflated. "Proofs" means theorems in the file,
not tests. The table lists the solutions that add something; the other GitHub files (listed
after it) repeat the patterns.

| # | Language | Author / link | Lines | Method | Notable | Proofs? |
|---|---|---|---|---|---|---|
| 1 | Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day02/Basic.lean) | 173 | part 1 closed form (arithmetic series over bases, multiplier `(10^(d*k)-1)/(10^d-1)`); part 2 enumerates bases per divisor, then `eraseDups` | the specifications are "a filter over `List.range (hi-lo+1)`", as ours | 8 proved series lemmas (`omega`, `nlinarith`, `simp_all +decide`, Mathlib `Finset.sum_range_id`); 5 correctness theorems all `sorry`, "Aristotle was unable to prove the following two theorems" |
| 2 | Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day02.lean) | 20 | brute force | part 2 by rotation: `[1:s.length].toList.any (fun p => s == s.drop p ++ s.take p)`; `Slice` API for part 1 | no |
| 3 | Lean 4 | [natewhite345](https://github.com/natewhite345/aoc25/blob/HEAD/day2/Day2/Basic.lean) | 114 + 22 | brute force | about 35 `#guard` checks, ending with both example answers; part 2 as a small automaton over candidate patterns, with a proof field for safe indexing | one `simp` lemma for the field |
| 4 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day2_2.lean) | 35 + 51 | generate from rounded seeds | `Fin n → Nat` view of the chunks; "here's the dumb way, still runs plenty fast" **[cited]** | no |
| 5 | Lean 4 | [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day2.lean), [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day2.lean), [benjaminfjones](https://github.com/benjaminfjones/advent-of-code-2025/blob/HEAD/AdventOfCode2025/D2.lean), [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day2.lean) | 70–140 | generate, dedup with `eraseDups`, `Std.HashSet` or `Std.TreeSet` | `String.join (List.replicate k s)`; benjaminfjones pins answers with `#guard_msgs` and has a "TODO: make it a fold"; bjornestol uses `termination_by` | no |
| 6 | Lean 4 | [dupuisf](https://github.com/dupuisf/aoc25/blob/HEAD/Aoc25/Day02.lean) | 49 | brute force | the only Lean parser-combinator parse (`Std.Internal.Parsec`); part 2 caps the block count at 10 | no |
| 7 | Lean 4 | [a2435191](https://github.com/a2435191/advent-of-code-2025-lean/blob/HEAD/advent-of-code-2025/AdventOfCode2025/Day2.lean) | 51 | brute force on a digit `Array (Fin 10)` | array bounds proved with `calc` blocks; `dbgTraceIfShared` to check in-place updates | index bounds only |
| 8 | Lean 4 | [frutjus](https://github.com/frutjus/aoc2025/blob/HEAD/day2/part2.lean) | 50 + 74 | generate | defines `Monad List` itself and uses `do` with `guard` | no |
| 9 | Lean 4 | [0xmycf](https://github.com/0xmycf/Advent-of-code/blob/HEAD/2025/day02/Day02.lean) | 72 | brute force | `{ n : Nat // both_halfs_same n }` results; "I could not get this to work with termination checking" **[cited]** | subtype only |
| 10 | Lean 4 | [mfornet](https://github.com/mfornet/advent-of-code-2025/blob/main/AdventOfCode2025/Day2.lean) (megathread: marx38), [vanshjangir](https://github.com/vanshjangir/AoC/blob/HEAD/2025/day02.lean) | 24, 36 | brute force | `digits.toChunks k` and `all (· == x[0]!)` | no |
| 11 | Idris 2 | [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day2.idr), [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day2/Solution.idr), [Pengler38](https://github.com/Pengler38/AoC-2025/blob/HEAD/src/Day2.idr) | 55, 79, 54 | brute force | hand-written chunking; contrib's `Text.Lexer`/`Text.Parser` (BrianNormant) over a `LazyList`; a `Reader` monad for the predicate (Pengler38) | no |
| 12 | Agda | [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day02.agda) | 122 | part 1 closed form (`(10^d + 1) * sumFromTo lo hi`); part 2 generate + `deduplicateᵇ` | `Range` record with an `evenDigits` proof field; `{-# TERMINATING #-}` on the splitter | data invariant only |
| 13 | Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/2/Problem2.dfy) | 80 | brute force as a set comprehension | `predicate InvalidAll(n: string) { exists k :: 0 < k < \|n\| && \|n\| % k == 0 && n == repeat(n[..k], \|n\|/k) }`; the set is drained with `var id :\| id in invalid_ids` | loop invariants and 4 asserted examples; the predicate is both specification and program |
| 14 | Haskell | [mstksg](https://github.com/mstksg/advent-of-code/blob/HEAD/2025/AOC2025/Day02.hs) ([write-up](https://github.com/mstksg/advent-of-code/wiki/Reflections-2025#day-2)) | 30 | generate | `repDigits n = read . concat . replicate n . show`; ranges become `IS.fromRange` and are intersected with the `IntSet` of all repeats; 243 µs and 264 µs **[cited]** | no |
| 15 | Haskell | [glguy](https://github.com/glguy/advent/blob/HEAD/solutions/src/2025/02.hs) | 32 | brute force | format quasi-quote parser; `or [same (chunks i str) \| i <- [1 .. n `quot` 2], n `mod` i == 0]`; doctests with the example and real answers | no |
| 16 | Haskell | [beefyhalo](https://github.com/beefyhalo/aoc/blob/HEAD/src/2025/02.hs) | 37 | generate within ceiling/floor bounds | `factor = (10 ^ (k * m) - 1) `div` (10 ^ m - 1)`; doctests in comments; `Integer` | no |
| 17 | Haskell | [GuillaumedeVolpiano](https://github.com/GuillaumedeVolpiano/adventOfCode/blob/master/2025/days/Day2.hs) | 141 | arithmetic, no per-id work | per-length guards; subtracts the 1-digit overcount for 6 and 10 digits; under 100 µs per part **[cited: megathread]** | no |
| 18 | Haskell | [stanosphere](https://github.com/stanosphere/advent-of-code/blob/main/src/2025/Day2.hs), [nicuveo](https://github.com/nicuveo/advent-of-code/blob/HEAD/2025/haskell/src/Day02.hs) | 56, 65 | generate per same-length sub-interval, `nubOrd` | nicuveo: list monad with `guard`, `parMap rpar` | no |
| 19 | Haskell | [PP6464](https://github.com/PP6464/AoC-2025-Haskell/blob/HEAD/src/Day02.hs), [RossPaterson](https://github.com/RossPaterson/advent-of-code/blob/HEAD/2025/Day02.hs) and 6 more | 23–68 | brute force | PP6464 tests `s `mod` (10 ^ power + 1) == 0` arithmetically; RossPaterson `properFactors` + `allSame (takes f cs)` | no |
| 20 | OCaml | [mbacarella](https://github.com/mbacarella/ocaml-aoc2025/blob/HEAD/lib/day2.ml), [FizzyElt](https://github.com/FizzyElt/ocaml_aoc_2025/blob/HEAD/bin/day2/q2.ml), [lambdam](https://github.com/lambdam/advent-of-code-2025-ocaml/blob/HEAD/lib/day02.ml), [KacperKopiec](https://github.com/KacperKopiec/advent-of-code/blob/main/2025/day2/part2.ml) | 27–181 | brute force (first two), generate (last two) | `%expect_test` (mbacarella); `CCString.repeat`; `List.chunks_of`; `sort_uniq` | no |
| 21 | F# | [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day02.fs) | 18 | generate | `multiplier l = [0..t-1] \|> Seq.sumBy (fun i -> pow10 (i*l))` (our `m`); part 2 is all repeat counts then `Seq.distinct` | no |
| 22 | Scala 3 | [lupari](https://github.com/lupari/aoc2025/blob/HEAD/src/main/scala/assignments/Day02.scala) | 12 | brute force | `case s"$s-$e"`; `s.grouped(k).distinct.size == 1` | no |
| 23 | Scala 3 | [sim642](https://github.com/sim642/adventofcode/blob/HEAD/src/main/scala/eu/sim642/adventofcode2025/Day2.scala), [bishabosha](https://github.com/bishabosha/advent-of-code-2025/blob/HEAD/scala/2025_day02.scala), [jelaby](https://github.com/jelaby/advent-of-code-2025-scala/blob/HEAD/src/main/scala/uk/co/mealor/aoc2025/Day2.scala), [Casper-Guo](https://github.com/Casper-Guo/AoC-Language-Exploration/blob/HEAD/2025.scala/day02.scala) | 39–50 | generate (sim642, bishabosha), brute force (jelaby), part 1 closed form (Casper-Guo) | `.toSet.sum` with the 2222 comment; `Math.powExact`; ScalaTest on the example; `Double` digit counts | no |
| 24 | Koka | [junpls](https://github.com/junpls/aoc25/blob/HEAD/day02.kk) | 61 | generate | parser combinators; `linear-set` dedup | no |
| 25 | Gleam | [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day02/day02.gleam) | 98 | brute force | `list.sized_chunk`; one Erlang process per range in part 2 | no |
| 26 | Roc | [mpizenberg](https://github.com/mpizenberg/aoc-2025/blob/HEAD/roc/day02.roc) | 168 | generate per digit count | hand-written dedup, "Ideally we use a Set, but it's not available yet" **[cited]**; `var $x`, `for`, `while`; `U64` | no |
| 27 | Effekt | [marvinborner](https://github.com/marvinborner/AdventOfCode/blob/HEAD/2025/02/solve.effekt) | 73 | brute force | `Scan[Char]` parser emitting `Range`s; digit slices into a `Set`; `wrongFormat()` as an effect | no |
| 28 | Elixir | [nikola-benes](https://github.com/nikola-benes/aoc2025elixir/blob/HEAD/02.exs), [freddydumont](https://github.com/freddydumont/aoc2025-elixir/blob/HEAD/lib/02_gift_shop/gift_shop.ex) | 33, 54 | generate with `Stream.iterate` + `String.duplicate` + `Stream.uniq`; brute force with an interpolated regex | "Try to be clever in both parts" **[cited]** | no |
| 29 | Chez Scheme | [erickalkman](https://gitlab.com/erickalkman/aoc2025/-/blob/main/day02.sls) (megathread: onrustigescheikundig) | 64 | **closed form** with a Gauss sum per block size; part 2 by a correction table | `overcount-correction-factor` for block counts 2..20: `2 1 3 1 4 0 5 1 6 -1 …`; "apparently this is the negative of the Möbius function"; about 100 µs **[cited: megathread]** | no |
| 30 | Clojure, Elm, Admiran | [CodeFarmer](https://github.com/CodeFarmer/aoc-2025/blob/HEAD/src/aoc_2025/day_2.clj), [albertdahlin](https://github.com/albertdahlin/advent-of-code/blob/HEAD/elm/src/Y25/D02.elm), [caseyWebb](https://github.com/caseyWebb/advent/blob/HEAD/2025/src/Day02.elm), [taolson](https://github.com/taolson/advent-of-code/blob/master/2025/day02.am) | 21–92 | brute force (first three), generate with `nub` (taolson) | `(apply str (repeat …))`; Elm example in a `"""` string; `elm/parser`; taolson: "Went from 3.5s to 0.006s" after switching from brute force **[cited: megathread]** | no |
| — | Stitchwort | `aoc/src/Aoc/Day02/Day02.sw` + `Proofs/` | 28 (program) + 35 (tests); 873 (proofs) | **closed form**, computed weights | `repeated r k n` (one arithmetic series), `weighted`, `plus`/`minus`/`weightFuel`; brute force kept as a cross-check test; `include` tests on the real input | yes: `part1Correct`, `part2Correct` for every input; 99 theorems, checked in 1.1 s |
| — | Stitchwort, brute force | scratch `brute.sw` | 19 | brute force | `t.take half == t.drop half`; rotation test via `Text.contains` | no |

Also read, and not in the table because they repeat these patterns: Haskell glebec (part 1
only), Sammers21, marpasdev, RockRottenSalad, KevinNotDuringWork; F# blazpeterlin,
WoutervanDixhoorn; Clojure lambdam (part 1 only) **[checked]**.

All rows are **[checked]**: fetched and read (tarballs or `gh api`), except cells marked
**[cited]**. I didn't run any of them.

**Correctness notes from reading** **[inferred, not run]**:

- Casper-Guo's `count_digits` is `ceil(log10(num))`, which is one short for exact powers of
  ten; the real inputs may never hit one.
- junpls's Koka only considers the digit lengths of each range's two ends, so a range that
  spans three lengths (such as 95–1012) would lose the middle length's ids.
- dupuisf caps the block count at 10, and kim-em's statements assume `r.hi < 10 ^ 20`; ours
  has neither limit (the old SW-147 version had the 10-digit limit).
- Sammers21's part 2 predicate is named `isValid` and returns true for invalid ids.
- Hath995's parser `expect`s `start < end`, so a one-id range `5-5` would stop it.

### 2.1 What I couldn't find

- **Unison, PureScript, Coq/Rocq, F\*:** none in GitHub repository and code searches or the
  megathread. Two code searches (Dafny, Coq) hit the GitHub rate limit, so those are
  incomplete **[checked: the sub-agents' search logs]**.
- **Day 2 from some day 1 authors:** joek13 and DavidMazarro (Lean) stop at day 1, Zikoat's
  Idris has only day 1, and no day 2 post turned up on hamberg.no.
- **Reddit itself:** not contacted; the megathread came from the Arctic Shift archive.
- **The puzzle text:** not fetched; `docs/aoc-2025.md` §4 restates it.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** Three requests to [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift):
two post searches by time window (a title search timed out, "Maybe slow down a bit"), one
`/api/posts/ids?ids=1pbzqcx`, and `/api/comments/tree?link_id=t3_1pbzqcx&limit=25000` (2.2 MB),
which also timed out once and succeeded on a retry a minute later. No requests to reddit.com,
and none for linked files beyond what the sub-agents fetched from GitHub and GitLab **[checked:
saved in `arctic/`]**. Terms as in the day 1 note: be considerate, rate limited, no licence file.

**What it holds.** "-❄️- 2025 Day 2 Solutions -❄️-" (2 Dec 2025, score 32, recorded
`num_comments` 861). The tree has 1,006 comments in all: **630 top-level**, 16 of them
`[deleted]`/`[removed]`, 583 of the live ones with a language tag and 31 without. As on day 1,
the tree holds more comments than the recorded count, so I have no sign that comments are
missing, but can't confirm it. 214 of the 614 live comments have code inline **[checked:
`scripts/langs.py`]**.

**The landscape.** Tags counted once per comment and language; spelling variants and version
suffixes merged (by script, then a few by hand):

| Language | Comments | | Language | Comments |
|---|---|---|---|---|
| Python | 165 | | Swift, F# | 6 each |
| Rust | 59 | | Clojure, Elixir, Common Lisp, Perl, Bash, Lua | 5 each |
| C++, Java | 24 each | | SQL, Uiua | 4 each |
| TypeScript, C# | 22 each | | OCaml, Gleam, Scheme, Julia, Raku, MATLAB, PHP | 3 each |
| Haskell, C, JavaScript | 19 each | | Emacs Lisp, Admiran, Nim, Dart, Odin, J, … | 2 each |
| Go | 17 | | Lean, Dafny, Prolog, Factor, Janet, Ada, … | 1 each |
| Ruby, R | 9 each | | | |
| Scala, Kotlin, Zig | 8 each | | | |

The functional or proof-oriented tags add up to 66 comments, 11% of the live ones (day 1: 82,
13%). No Idris, Agda, Coq/Rocq, Koka, Roc, Elm, PureScript, Erlang, Effekt or Unison this time.

**Methods, megathread-wide** (regular expressions over all 614 live comments; "with code" means
the comment has code inline) **[checked]**:

| Pattern | Comments | With code |
|---|---:|---:|
| says "brute force" | 117 | 26 |
| a regex backreference `\1` | 52 | 44 |
| a set, `distinct`, `nub`, `unique` or dedup | 60 | 51 |
| chunking (`chunk`, `grouped`, `chunksOf`) | 33 | 26 |
| divisors or factors | 39 | 21 |
| 64-bit or big integers named (`u64`, `Int64`, `Long`, `BigInt`, overflow) | 64 | 46 |
| Möbius or inclusion–exclusion | 3 | 2 |
| Gauss, arithmetic series or triangular numbers | 3 | 1 |

**What I read.** All 66 functional comments (25 with code inline). The ones that add to §2:

| # | Language | Author / link | Notable |
|---|---|---|---|
| 31 | Haskell | [mstksg](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nruh0rd/) | "You can do this nicely using the `IntSet` type … `IS.fromRange`" **[cited]**; same as row 14 |
| 32 | Haskell | [G_de_Volpiano](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrx5a7n/) | the case analysis behind row 17: "length is prime, just compute 1-pattern … n == 6 or n == 10, truly compound numbers"; "debugging was hell" **[cited]** |
| 33 | Chez Scheme | [onrustigescheikundig](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/ns05une/) | "I saw the brute force solution but instead chose pain (number theory)"; blocked numbers are multiples of `1001001…`, summed by Gauss; "I was able to calculate manually the amount of overcounting" **[cited]**: our design, with a table |
| 34 | Haskell | [danvk](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrw3j4z/), [Althar93](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nry8bo2/), [leDragonir](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nry3z6l/), [icecoldgold773](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrz90eb/), [sondr3_](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrxykyp/) | brute force with `splitAt`, `concat (replicate (len `div` n) (take n str))`, `T.chunksOf`; sondr3_ benchmarks 643 ms and 859 ms **[cited]**; icecoldgold773 and SnooHesitations6473 write their own `splitOn` |
| 35 | Haskell | [sheshanaag](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrxa45i/) | generate via `take len $ cycle v'`, `bigFactors` from a prime factorisation, then `nub`, with the comment "nub is required for values such as 1111111111" |
| 36 | F# | [r_so9](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrubd06/), [mestar12345](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrzjt0l/), [munchler](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nruc3er/) | generate with `Seq.unfold` + `String.replicate` + `Seq.distinct`; `List.unfold` + `Set.ofSeq`; brute force with `Seq.chunkBySize` + `Seq.distinct` and a hand-written `getDivisors` |
| 37 | Clojure, Scheme, Emacs Lisp, Factor | [Negative-Machine4279](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrufy9l/), [darren](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nruavxu/), [valhesh](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrytnqo/), [CowImaginary3155](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrxx6k6/), [geza42](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrumbko/), [molochwalk](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrw74vp/) | regex backreferences do part 2: `{:part-1 (f #"^(.+?)\1$") :part-2 (f #"^(.+?)\1+$")}`; valhesh: "I was going to use Go for today, but … the regex package does not support backref" **[cited]**. 10 of the 66 use a backreference |
| 38 | Common Lisp | [dijotal](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrux5bm/), [argentcorvid](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/ns5d39n/) | generate to 10 digits, `remove-duplicates`, 0.05 s **[cited]**; part 1 by `(floor id (expt 10 (/ digits 2)))`, two values from one division |
| 39 | Scala | [blackzver](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nruxtff/), [FCBStar-of-the-South](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrx5wj2/) | ZIO streams with `BigInt` ids, `Either` for parse errors, `s == s.take(len) * (length / len)`; FCBStar: overflow in part 2 without `toLong` **[cited]** |
| 40 | Janet, Gleam | [veydar_](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrxn219/), [tymscar](https://www.reddit.com/r/adventofcode/comments/1pbzqcx/2025_day_2_solutions/nrvcohi/) | coroutine chunk iterator; tymscar wished Gleam lists had `.second` and had to install a regex library **[cited]** |

Megathread comments outside the functional group that matter here, all **[cited]**:
Key_Pack_9630 (C) "Happy that I could use the Moebius inversion formula for
inclusion/exclusion", with a hard-coded table; Akari_Takai (Rust) states the Möbius inversion
over periods and gives part 2 as `O(n * log^3 m)`; Appropriate-Corgi168 (C++) has part 1 as an
arithmetic series and is "fiddling around a bit with Möbius Inversion Formula".

**Notes from the megathread**:

- **Several authors say they are learning the language** (danvk, valhesh, vanZuider,
  Upstairs-League-5703, LtHummus, baboonbomba's polyglot run), so, as on day 1, I don't read
  design signals into style beyond complaints.
- **The complaints:** regex support (POGtastic: "utter confusion at how bad the OCaml stdlib's
  regex library is"; Go without backreferences); splitting strings (vanZuider: a split function
  is "a way more arcane and dangerous undertaking than Python would have us believe", citing the
  `split` package); overflow; and part 2's double counting.
- **Speed is rarely a problem for brute force in compiled languages** (POGtastic 0.6 s, blacai
  0.5 s, argentcorvid 2 s for part 2), and a reason to switch for others (Maximum_Expression's
  Elixir took 2.95 s and 8.54 GB for part 2; taolson's Admiran went from 3.5 s to 0.006 s).

## 3. Themes

### 3.1 Parsing `11-22,95-115,…`

| Approach | Who | Example |
|---|---|---|
| Split on `,` then `-` | most | `splitOn "," . splitOn "-"` (mstksg), `r.Split ','` (lboshuizen) |
| Text patterns | Scala 3 (lupari, sim642, bishabosha, Casper-Guo) | `case s"$s-$e" => s.toLong to e.toLong` |
| One regex for the pair | Clojure | `(re-seq #"(\d+)-(\d+)" input)` |
| Format/scanf | glguy, FizzyElt | `[format\|2025 02 (%u-%u)&,%n\|]`, `Scanf.sscanf s "%d-%d"` |
| Parser combinators | Koka, Lean (dupuisf), Idris (BrianNormant), Haskell (megaparsec, Parsec), Elm, Chez, Effekt, Factor (EBNF) | `sepBy (pchar ',') parseRange` |
| `Option`/`Except` with early exit | Lean (sdiehl, natewhite345, a2435191, bjornestol), Roc `?`, Scala `Either` (blackzver) | `let [fst, snd] := s.splitOn "-" \| none` |

**Stitchwort today.** `Aoc.Common.Range.parse` is a list pattern on the split, as Lean's
refutable `let`:

```
def Range.parse (t: Text): Option Range :=
  match (t.split '-').map Text.toNat with
    | [Some from, Some to] => Some { from, to }
    | _                    => None
```

The input is `t.trim.split ',' |> .filterMap Range.parse`. Nothing here is missing for day 2:
`Text.splitOn` takes a `Text` separator (SW-218), and the example can be a `"""` text block
over several lines (`probes.sw`, 11 ranges parsed after `trim` **[checked]**).

### 3.2 Testing an id: halves, chunks, rotations, regexes

| Check | Who | Code |
|---|---|---|
| Halves equal | almost everyone, part 1 | `s.take(s.length / 2) == s.drop(s.length / 2)` (lupari) |
| Chunks all equal | glguy, RossPaterson, lupari, mfornet, Gleam, OCaml, F#, Effekt | `same (chunks i str)`, `s.grouped(k).distinct.size == 1`, `Seq.chunkBySize size \|> Seq.distinct` |
| Repeat the prefix and compare | danvk, Dafny, OCaml, F#, Clojure | `str == concat (replicate (len `div` n) (take n str))` |
| Some rotation equals it | tenthmascot | `s == s.drop p ++ s.take p` |
| Regex backreference | 10 FP megathread comments, 52 overall | `^(.+?)\1+$` |
| Arithmetic | PP6464, argentcorvid | `s `mod` (10 ^ power + 1) == 0`; `(floor id (expt 10 …))` |

**Stitchwort today.** The halves and the rotation work as written (`probes.sw`, `brute.sw`
**[checked]**):

```
def rotates (x: Nat): Bool :=
  let s := x.toText
  List.rangeFrom (s.length - 1) 1 |> .any (p => s == s.drop p ++ s.take p)
```

Repeating the prefix needs a detour through characters, because there is no `Text.repeat`:

```
def repeatsAs (s: Text) (n: Nat): Bool :=
  let len := s.length
  if n != 0 then len % n == 0 && Text.fromList (List.concat (List.replicate (len / n) (s.take n).toList)) == s else False
```

Two things went wrong on the way **[checked]**:

- **`&&` doesn't carry the fact.** The first version was `n != 0 && len % n == 0 && …`, as in
  Haskell. `%` and `/` need a proof that the divisor isn't 0, and `&&` doesn't give its right
  operand the left one as a fact, so this is `E-AUTO-STUCK: can't decide n != 0 here … Note:
  establish it first, with if h: … then … else …` (`p_and_div.sw`). `if n != 0 then` works,
  and the note helps. The same happens with `maxLen / k` where `k` comes from
  `List.rangeFrom n 1`: the list's elements are at least 1, but nothing says so.
- **`.contains` reads backwards.** My first rotation test was
  `((t ++ t).drop 1).take (2 * t.length - 2) |> .contains t`, meaning "t occurs inside". Dot
  notation fills the first `Text` parameter, which for `Text.contains (p: Text) (t: Text)` is
  the pattern, so this asks whether the long text occurs in `t`. The test then printed
  `left: ([11, 22], [99])` against `right: ([11, 22], [99, 111])` (SW-216's both-values output
  made it quick to see). `|> Text.contains t` is right. Text.sw explains the order ("write
  `t |> Text.startsWith p`"), so this is documented, but it's an easy trap with `startsWith`,
  `endsWith`, `contains`, `stripPrefix` and `splitOn` alike. It belongs to D302's research.

No chunking helper: `List.chunksOf` is `E-ARITY: List needs 1 argument(s)`, and `Text.repeat`
and `Nat.divisors` are `E-NO-NAMESPACE: Text is a type, which has no namespace to look .repeat
up in` (`p_chunks.sw`). Both messages are hard to read as "no such function".

### 3.3 Generating the invalid ids instead

The middle family builds `base * multiplier`, where the multiplier is `11`, `101`, `10101`, …:

| Who | Multiplier | Dedup |
|---|---|---|
| lboshuizen (F#) | `[0..t-1] \|> Seq.sumBy (fun i -> pow10 (i*l))` | `Seq.distinct` |
| beefyhalo (Haskell), mpizenberg (Roc), kim-em (Lean) | `(10 ^ (k * m) - 1) `div` (10 ^ m - 1)` | `S.fromList`, hand-written, `eraseDups` |
| mstksg (Haskell), sim642 (Scala), Elixir, Lean (sdiehl) | string repetition, then `read` | `IntSet`, `.toSet`, `Stream.uniq`, `eraseDups` |
| sheshanaag (Haskell) | `take len $ cycle v'` | `nub` |

Our `repeated` uses lboshuizen's multiplier and then, instead of listing the bases, adds them
as one arithmetic series:

```fsharp
// lboshuizen (F#)
let multiplier l = [0 .. t-1] |> Seq.sumBy (fun i -> pow10 (i*l))
let candidates l = seq { pow10 (l-1) .. pow10 l - 1L } |> Seq.map ((*) (multiplier l))
```
```
-- Stitchwort (Day02.sw)
def repeated (r: Range) (k: Nat) (n: Nat): Nat :=
  let m := List.range n |> .sumBy (i => Nat.pow 10 (k * i))
  if m != 0 then
    let from := Nat.max (Nat.pow 10 (k - 1)) ((r.from + m - 1) / m)
    let to := Nat.min (Nat.pow 10 k - 1) (r.to / m)
    if from <= to then m * ((from + to) * (to - from + 1) / 2) else 0
  else 0
```

The generate-then-dedup shape works in Stitchwort today with `Set.fromList` (`probes.sw`: the
108 distinct repeated numbers of up to 4 digits **[checked]**), but is long-winded without a
`Text.repeat` (`(Text.fromList (List.concat (List.replicate n b.toText.toList))).toNat |>
.getOrElse 0`). A list dedup (`distinct`, `nub`, `eraseDups`, `deduplicateᵇ`, `sort_uniq`)
would be the shorter spelling; `Set.fromList` then `.size` or `.toList` does it today.

### 3.4 Part 2's overlap: sets, tables and Möbius

The ids with a proper period are counted once for each way of writing them (111111 = `1`×6 =
`11`×3 = `111`×2). The community's fixes, from most to least common:

1. **A set** (most generate-family solutions).
2. **Pick only the right repeat counts**, by hand per digit length: GuillaumedeVolpiano's guards
   ("length is prime … n is a power of a prime … n == 6 or n == 10"), PP6464 and sheshanaag
   using the largest proper factors.
3. **Inclusion–exclusion with a table**: erickalkman (2..20), Key_Pack_9630 (C).
4. **Möbius inversion stated in general**: Akari_Takai (Rust).

Our weights are (3) without a table, which is what (4) gives:

```scheme
;; erickalkman (Chez Scheme)
; EDIT: apparently this is the negative of the Möbius function
(define overcount-correction-factor
  (array-map 2 1  3 1  4 0  5 1  6 -1  7 1  8 0  9 0  10 -1 …
```
```
-- Stitchwort (Day02.sw): the same numbers, computed for every n
def plus (n: Nat): Nat := weightFuel (Succ n) True n
def minus (n: Nat): Nat := weightFuel (Succ n) False n

test "weights" := List.map (n => (plus n).toInt - (minus n).toInt) (List.rangeFrom 11 2) == [1, 1, 0, 1, -1, 1, 0, 0, -1, 1, 0]
```

The split into two natural-number weights exists for the proof (D82, the day 2 general note):
the sums stay in `Nat`, where the library has the lemmas. No community solution needed that.

### 3.5 Library breadth

| Helper | Seen in | Stitchwort |
|---|---|---|
| `take`/`drop`/`splitAt` on text | everyone | `Text.take`, `Text.drop` (SW-218); no `splitAt` (two calls) |
| chunks (`chunksOf`, `grouped`, `chunkBySize`, `sized_chunk`, `chunks_of`, `toChunks`) | glguy, sondr3_, lupari, munchler, Zenor27, mbacarella, mfornet; 26 megathread comments with code | **missing** **[checked]** |
| text repetition (`replicate`, `String.replicate`, `String.duplicate`, `CCString.repeat`, Scala `*`) | mstksg, danvk, r_so9, nikola-benes, FizzyElt, blackzver | **missing**: `Text.fromList (List.concat (List.replicate n t.toList))` |
| divisors (`getDivisors`, `properFactors`, `get_divisors`, `factor`) | munchler, RossPaterson, lambdam, spikedoanz, PP6464 | `Nat.divides` exists; no list of divisors |
| dedup (`distinct`, `nub`, `nubOrd`, `eraseDups`, `sort_uniq`, `uniq`) | most generate solutions | `Set.fromList`; no list function |
| integer sets with ranges (`IS.fromRange`, `intersection`) | mstksg | `Set` (balanced tree): `fromList`, `intersect`; no range constructor |
| digits | many (`show`, `Nat.toDigits`, `toNatDigits`) | `Nat.digits`, `Nat.toText`, `Nat.fromDigits`, with lemmas |
| regex with backreferences | 10 FP megathread comments, freddydumont | none (not proposed) |
| a `Set` where the language has none yet | Roc ("not available yet") | `Std.Set` |

### 3.6 Proofs and automation

What the community proved for day 2:

- **kim-em (Lean):** states five correctness theorems and proves none. The proved part is
  series algebra:
  ```lean
  theorem arith_sum_formula_doubled (a b : Nat) (hab : a ≤ b) : …  -- nlinarith
  ```
  and the open ones read like ours:
  ```lean
  theorem sumRepetitionsInRange_correct (r : Range) (d k : Nat) (hd : d > 0) (hk : k ≥ 2) :
      sumRepetitionsInRange r d k =
      ((List.range (10 ^ d - …)).filterMap (fun i => … if r.lo ≤ n ∧ n ≤ r.hi then some n else none)).foldl (· + ·) 0 := by
    sorry
  ```
  The comments say why they are open: the string-based `isInvalid` needs "reasoning about
  toString n and showing string equality matches numeric structure", and the generated proof of
  the series theorem "times out on v4.24.1".
- **Hath995 (Dafny):** the predicate is the specification and the program is a set
  comprehension over it, so there is nothing to prove between them; Dafny checks the loop that
  drains the set and four examples. The author: "Dafny's existential operator has made short
  work of several advent of code problems" **[cited]**.
- **Bounds and invariants:** a2435191's `calc` proofs of array indices; jpyamamoto's
  `evenDigits` field; 0xmycf's subtype; natewhite345's `safe : cur < pat.length` field.

**Where ours stands.** kim-em's two open string steps are our `Nat.digits` bridge
(`Repeated.sw`: `twiceDigits`, `fromDigitsRep`, the `Nat.digits*` lemmas in the library), and
their open series theorem is our `repeatedCorrect`. Part 2's periods argument (`Period`,
`periodDvd`, `smallestPeriod`, `copiesDivides`) has no counterpart anywhere I looked. The cost
on our side is the 873 lines of proof (`Proofs/`), with no arithmetic automation; the Lean
prototype in `comparisons/aoc-day02-general/` needed 138 `omega` and 93 `simp` for the same
argument, and that measurement still stands (SW-101). The community adds one data point: a
solver-backed attempt at exactly these theorems didn't finish.

### 3.7 Speed of the obvious program

| Program | Command | Time |
|---|---|---|
| Committed closed form (`Aoc.Day02.main`) | `stitchwort run` | 0.49 s **[checked]** |
| Same | `stitchwort run --js` | 0.53 s **[checked]** |
| Brute force, all 1,917,096 ids in one list (scratch `brute.sw`) | `stitchwort run` | `E-RESOURCE: … recursed more deeply than allowed` after 3.2 s **[checked]** |
| Same | `stitchwort run --js` | 77 s, right answers **[checked]** |
| Brute force, one range at a time (`brute2.sw`: `ranges.sumBy (r => ids r \|> .filter doubled \|> .sum)`) | `stitchwort run` | 295 s, right answers **[checked]** |
| mstksg, generate + `IntSet`, Haskell | criterion, parsing excluded | 243 µs, 264 µs **[cited]** |
| sondr3_, brute force, Haskell | his benchmark | 643 ms, 859 ms **[cited]** |
| GuillaumedeVolpiano, arithmetic, Haskell | his benchmark | 57 µs, 71 µs **[cited]** |

So the `E-RESOURCE` comes from holding all 1.9 million ids in one list, not from the work:
summing range by range (the largest range has 181,930 ids) runs to the end. That points at
the depth of a recursion over one long list (`concatMap`, `filter` or `sum`) **[inferred: not
profiled]**.

Day 1's brute force took 5.5 s (`run`) and 0.95 s (`--js`); day 2's takes 295 s and 77 s,
because each of the 1.9 million ids is turned into text and compared (twice), where day 1 did
one addition per click. Here the method matters more than the evaluator, and `--js` is about
four times faster. `docs/aoc-2025.md` §4 predicted "several minutes" for the brute-force port, and
the committed program chose the closed form for that reason.

## 4. Side by side: the shortest Stitchwort

The scratch `brute.sw`, 19 lines, follows lupari and tenthmascot. It is the puzzle's own method,
not a proposal to change Day02.sw:

```
type Range = { from: Nat, to: Nat }

def parse (t: Text): Option Range :=
  match (t.split '-').map Text.toNat with
    | [Some from, Some to] => Some { from, to }
    | _                    => None

def ids (r: Range): List Nat := List.rangeFrom (r.to + 1 - r.from) r.from

def doubled (x: Nat): Bool :=
  let t := x.toText
  let half := t.length / 2
  t.length % 2 == 0 && t.take half == t.drop half

-- t has a smaller period exactly when it occurs inside t ++ t
-- with the first and last characters removed.
def repeats (x: Nat): Bool :=
  let t := x.toText
  ((t ++ t).drop 1).take (2 * t.length - 2) |> Text.contains t
```

```scala
// lupari (Scala 3), the whole file is 12 lines; the two checks:
s.take(s.length / 2) == s.drop(s.length / 2)
(1 to s.length / 2).exists(k => s.grouped(k).distinct.size == 1)
```

With the candidates below, `repeats` could be `List.rangeFrom (n / 2) 1 |> .any (k =>
(t.chars.chunksOf k).distinct.length == 1)`, close to lupari's; the rotation version already
needs nothing new.

## 5. Candidate features, ranked by value over effort

Kinds: **sugar** (syntax only), **library**, **tooling**, **language** (elaboration or kernel).

| Rank | Candidate | Kind | Value | Effort | Evidence | Ticket |
|---|---|---|---|---|---|---|
| 1 | **`List.chunksOf`, `Text.repeat`, `Nat.divisors`, a list dedup (`List.distinct` on `DecEq`)** | library | medium: string-shaped AoC checks | small | §3.2, §3.3, §3.5: chunks in 26 megathread comments with code and 7+ GitHub files; repetition in 6; divisors in 5; dedup in most generate solutions | none; fits beside SW-219 |
| 2 | **`a && b` and `a \|\| b` give `b` the fact `a` (and `not a`) the way `if` does**, so `n != 0 && len % n == 0` checks | language (elaboration of `&&`/`\|\|`) | medium: every guard before a division | small to medium (on `Bool`s `a && b` is already `if a then b else False`, but as a `Bool` `if`, which gives `b` no fact; a decidable comparison on the left would need the `if _:` form, as an `if` condition already gets) | §3.2, `p_and_div.sw`; Haskell/Scala/Lean guards `n `mod` k == 0` in most part 2 checks | none |
| 3 | **Clearer message for a missing function in a type's namespace** (`List.chunksOf` says `E-ARITY: List needs 1 argument(s)`; `Text.repeat` says `Text is a type, which has no namespace`) | tooling | low to medium | small | `p_chunks.sw` | none |
| 4 | **`Text.contains`/`startsWith`/`stripPrefix` read backwards with dot notation** | design input | medium (a silent wrong answer) | none here: input to D302 | §3.2, `p_contains_dot.sw` | D302 research |
| 5 | **`stitchwort run` on a list of 1.9 million elements** fails with `E-RESOURCE` (range by range it works, in 295 s) | tooling (evaluator) | medium: brute-force specifications | unknown | §3.7, `brute.sw`, `brute2.sw` | SW-66 (`stitchwort run` out of resources); related SW-84 |
| 6 | **Text patterns** `case s"$a-$b"` | language | low for day 2 (`split` is enough) | medium | 4 Scala solutions | **not now** (D297); no change |
| 7 | **Scala-style `_` placeholders** (`.map(_.toLong)`, `exists(_.contains(id))`) | sugar | low to medium | small to medium | Scala rows, Lean `(· == x[0]!)` | SW-222 (backlog design note); no change |
| 8 | **Regular expressions with backreferences** | library (large) | low for Stitchwort's aims | large | 52 megathread comments, 10 in FP languages | none; not proposed |
| — | Arithmetic automation (`omega`-like) | language/library | high for proofs | large | §3.6: kim-em's open theorems; the Lean prototype's 138 `omega` | SW-101, no change |

Why this order:

- **Rank 1 is the same kind of work as SW-218/SW-219** and every item has three or more
  independent uses in the sample. Each has a one-line workaround today, so value is moderate.
- **Rank 2 is the one language change.** The `if` form works and the error note says what to
  write, so it's a convenience; but it hits the commonest guard in day 2 code, and `&&` already
  works on comparisons in `if` conditions (docs/syntax.md), so users will expect it.
- **Rank 4 costs nothing to record** and gives D302 a concrete case where the rule produced a
  wrong answer rather than an error.
- **Rank 5 is evidence, not a new ticket.** The committed program doesn't need it.
- **Ranks 6–8 are unchanged by day 2.** Day 2 is easier to parse than day 1.

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D330 | Record the `Text.contains`/`startsWith`/`stripPrefix` dot-notation reversal (`s \|> .contains t` asks whether `s` is in `t`) as a test case for the D302 receiver-rule research? | [yes; it gave a silent wrong answer, not an error] |
| D331 | Should `a && b` (and `a \|\| b`) elaborate `b` with `a` (with `not a`) as a known fact, as `if a then b else False` does, so `n != 0 && len % n == 0` checks? | [yes, as a small ticket after the D302 work; low risk, common guard] |
| D332 | Add `List.chunksOf`, `Text.repeat`, `Nat.divisors` and a list dedup (`List.distinct` on `DecEq`) to the library? | [yes; batch with SW-219] |
| D333 | Add the brute-force day 2 file (`E-RESOURCE` under `run` with one 1.9-million-element list; 77 s with `--js`; 295 s under `run` range by range) to SW-66 as a reproduction? | [yes; no new ticket] |
| D334 | Regular expressions in the library? | [no; not now] |
| D335 | Make "no function `chunksOf` in `List`" the error for an unknown function in a type's namespace, instead of `E-ARITY`/`E-NO-NAMESPACE`? | [yes, small] |

---

**Status** (short form, 21 Oct 2026): D330 contains receiver → D302 research, pending; D331
`&&` carries facts, pending; D332 chunks/repeat/divisors/dedup, pending (beside SW-219 backlog);
D333 brute force in SW-66, pending; D334 regex, recommend no; D335 namespace error message,
pending. Unchanged by day 2: D296 operator sections and D297 text patterns not now, SW-222
backlog, SW-101 backlog.
