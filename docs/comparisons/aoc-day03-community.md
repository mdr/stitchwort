# AoC 2025 day 3: community solutions in other languages

**Date:** 21 October 2026. **Our version:** `aoc/src/Aoc/Day03/Day03.sw` (program: the greedy
"leftmost largest digit in the window that still leaves room", for any k), and
`aoc/src/Aoc/Day03/Proofs/Best.sw` (for every k and every bank, the answer is a subsequence of
the bank with `min k (length)` digits, and no k digits taken in order make a larger number).
`docs/aoc-2025.md` §5 and "Day 3 (October 2026)" describe the program and the proof. This note
looks at what other people wrote for 2025 day 3, in the wild, and asks what that suggests for
Stitchwort. It follows the shape of [aoc-day01-community.md](aoc-day01-community.md) and
[aoc-day02-community.md](aoc-day02-community.md).

Labels, as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day3-community/sw/`,
run with the main checkout's `target/release/stitchwort` (built 21 Oct 2026, 22:46). Fetched
solutions are in `gh/proof/` and `gh/fp/` beside it, and the megathread data in `arctic/`.

## 1. Summary

I read 68 solutions on GitHub (one per author; about 85 files): 18 in Lean 4, 5 in Idris 2,
1 in Agda, 1 in Dafny, 8 in Haskell, 6 in OCaml, 5 each in Scala and Gleam, 4 in Clojure,
3 each in F#, Elixir and Elm, 2 each in Koka and Roc, and one each in Chez Scheme and Admiran
(§2). Two Sonnet sub-agents fetched and summarised them; I checked the claims the note relies
on against the saved files. I then read the r/adventofcode Day 3 megathread through the Arctic
Shift archive (§2.2): 682 top-level comments, 670 not deleted, about 100 distinct language tags.
76 comments are in functional or proof-oriented languages (24 Haskell, 9 Elixir, 6 each in F#,
Scala, Common Lisp and OCaml, 4 each in Scheme, Gleam and Clojure, 2 Prolog, and one each in
Emacs Lisp, Dafny, Admiran, Racket and Janet). I read all 76; 32 have code inline. No Unison,
PureScript, Coq/Rocq, F\* or Effekt solution turned up anywhere.

The main findings:

1. **One community solution proves day 3 optimal, in Dafny, and it is our argument.**
   Hath995's `Problem3.dfy` proves that the greedy pick is lexicographically at least every
   subsequence of the same length (`flsIsLexicographicMax`), with the same exchange argument
   as our `bestOptimal`: compare first digits, and on a tie use that the greedy took the
   *earliest* maximum, so the other choice's tail comes from a suffix of the greedy's
   (`assert f_idx <= s_idx`). The commit is "proved lexicographic max", the same day; the
   file has no `assume` or `{:axiom}` **[checked: read the file and `gh api` commits; not run,
   so "it verifies" is the author's claim]**. Two differences from ours: it stops at
   lexicographic order and never connects it to the number (`ToNat`), which is where our
   `Nat.fromDigitsHeadLess` and the "digits are below 10" hypothesis come in; and it requires
   `0 < count < |bank|`. The Lean attempts stop short: kim-em's two theorems are `sorry`
   ("difficult to prove for the imperative while loop"), natewhite345's part 1 optimality ends
   in `all_goals sorry` after `grind`, and andorp's specification has `allChoices := sorry`
   with the correctness theorems commented out **[checked]**.
2. **Four method families, and the greedy window is by far the most common.** Of the 68
   GitHub solutions, about 48 take the leftmost largest digit in the window that leaves room
   (ours); about 10 keep a stack or a k-digit register and drop a smaller digit when a larger
   one arrives; 5 do dynamic programming (glguy, RossPaterson, dupuisf, sim642's memo,
   KacperKopiec); and 3 search digits 9 down to 1 with backtracking (mstksg, erickalkman,
   Dessertion). In the 76 functional megathread comments, about 37 are greedy, 9 stack, 6 DP
   and 4 search; the rest only link to code **[checked: counted by hand; the boundaries
   between families are mine]**. Several people first tried all combinations and switched
   ("(100 choose 12) is ~1e15", danvk).
3. **The one trap is ties, and our proof would catch it.** The greedy must take the
   *leftmost* largest digit. Haskell's `maximumBy` and Clojure's `max-key` return the *last*
   maximum, and so does Rust's `max_by_key`, so people wrote `minimumBy` with `Down`
   (XamazingX5: "`maximumBy` returned the last maximum"), `lessOrFirst` (RossPaterson), a
   negated index (PP6464) or `.rev()` before `max_by_key` (DMonitor; 7 megathread
   comments reverse or use `Down` first) **[checked]**. Flipping our `if c < x` to `c <= x` gives wrong
   answers on the example's fourth bank and on the real input (17073 instead of 17263), and
   `docs/aoc-2025.md` records that the proof fails with that change **[checked: `p_tie.sw`;
   sabotage cited from aoc-2025.md]**. Our test named "leftmost wins" passes with either rule
   (`Bank.best 1 [3, 9, 9, 1]`); narimiran's `[2 7 5 7 3]` (77 against 73) tells them apart.
4. **Stitchwort writes all three common shapes today, first try.** sondr3_'s one-fold DP
   (`zipWith max prev (map (\b -> b*10+n) (0 : prev))`), danvk's greedy and bramhaag's stack
   each became a short scratch file that passed the example and printed the right answers
   **[checked: `dp.sw`, `greedy.sw`, `stack.sw`]**. What was missing were list helpers the
   community reached for: an arg-max (`maxBy`, `maximumBy`, `max_by`; in 15 GitHub files and 23
   megathread comments with code), "the rest after the first `x`" (`dropWhile`, `break`),
   "all but the last n" (`dropRight`, `dropLast`; in 12 files), `tails` (8), `findIndex`/
   `indexOf` (17) and a with-index view (`zipWithIndex`, `with_index`; 12). Each is a 2–4 line
   local function in Stitchwort.
5. **Pattern guards are the one syntax gap this day showed.** The stack shape is a pattern
   plus a condition that falls through to the next case: `step (t:ts, d) x | d > 0 && x > t =
   …`, `when top < cur` (Elixir), `if remains < remaining` (Gleam). About 11 GitHub files and 5
   functional megathread comments with code use one. Stitchwort has no guards, so the fallback
   body is written twice (`stack.sw`) **[checked]**.
6. **Big numbers matter more than on day 2.** Part 2's answers are about 1.7 × 10^14 and need
   64 bits: 50 megathread comments name 64-bit or big integers, sim642 had "a small trip-up
   leading to a switch from `Int` to `Long`", and kim-em, Lean and Agda use unbounded `Nat`.
   Stitchwort's `Nat` is unbounded **[checked]**.

The ranked candidates are in §5 and the decisions in §6 (D360–D364). The cheapest useful ones:

- `List.maxBy`/`minBy` that keep the **first** of equal elements, said in the docs (D360);
- a second list batch after SW-219: `dropWhile`, `takeWhile`, `span`, `dropRight`, `tails`,
  `findIndex`, `zipWithIndex` (D361);
- make Day03.sw's "leftmost wins" test distinguish the tie rule, and keep the
  every-choice brute force as a test (D363, D364);
- a design note on pattern guards (D362).

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker; block comments are
counted, so files with long doc comments are inflated. "Proofs" means theorems in the file,
not tests. The table lists the solutions that add something; the others (listed after it)
repeat the patterns.

| # | Language | Author / link | Lines | Method | Notable | Proofs? |
|---|---|---|---|---|---|---|
| 1 | Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/3/Problem3.dfy) | 408 | greedy window (`fls`), `MaxIndex` returning the earliest maximum | `MaxIndex`'s postcondition `forall i :: … xs[i] == MaxIndex(xs).0 ==> MaxIndex(xs).1 <= i`; the specification is `subsetSeqs`, every subsequence | **yes**: `flsInSet` (the answer is a subsequence of length k) and `flsIsLexicographicMax`; 17 lemmas, 64 `assert`s, no `assume`; lexicographic only |
| 2 | Lean 4 | [natewhite345](https://github.com/natewhite345/aoc25/blob/HEAD/day3/Day3/Basic.lean) | 179 | part 1 one-pass fold; part 2 "remove the leftmost digit lower than its right neighbour" after each new digit | a refined `Joltage` type (1 to 9); `#guard_msgs` checks that `mk 0` fails | `from_digits_cmp` proved (`simp_all; grind`); part 1 optimality `pf` ends in `all_goals sorry` and `cons hd tl ih => sorry` |
| 3 | Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day03/Basic.lean) | 49 | part 1 all pairs; part 2 greedy in a `while` loop | `if arr[i]! > bestDigit` (leftmost) | 5 `rfl` facts; `maxJoltage_le_99` and `maxJoltageK_greedy` are `sorry`: "This is difficult to prove for the imperative while loop" |
| 4 | Lean 4 | [andorp](https://github.com/andorp/Lea-r-n/blob/HEAD/AoC2025/Day03.lean) | ~232 | greedy, `pickMaxSubseq xs k (hk: k ≤ rest.length)` | specification first: `Choice`, `allChoices`, `bankMax`; the length proof makes the recursion total | `pairValue_lt_iff` proved (`omega`); `allChoices := sorry`; the correctness theorems are commented-out `sorry`s |
| 5 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day3_2.lean) | 32 | greedy | `{n: Nat // n ≠ 0}`, `termination_by n.val`, `decreasing_by omega`; `b.max?.get (by simp; grind)` | a `@[simp] theorem maxExists` for the side condition |
| 6 | Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day03.lean) | 21 | greedy, one function with k | `line.maxI start (line.size - n)`; `Array.findIdx?.loop … |>.get!` with the comment "i'm sorry" | no |
| 7 | Lean 4 | [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day3.lean), [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day3.lean), [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day3.lean), [josephmate](https://github.com/josephmate/AdventOfCode2025/blob/HEAD/AdventOfCode2025/Day03.lean), [ianclement](https://github.com/ianclement/aoc-2025/blob/HEAD/Day03.lean), [adomani](https://github.com/adomani/advents/blob/HEAD/Advents/AoC2025/day03.lean) | 31–52 | greedy | bjornestol: `(xs.take (xs.length - (n-1))).max?` and `xs.dropWhile (· < n) \|>.drop 1` in `Option`'s `do`; adomani: `#assert part2 atest == 3121910778619` | no |
| 8 | Lean 4 | [dupuisf](https://github.com/dupuisf/aoc25/blob/HEAD/Aoc25/Day03.lean) | 53 | DP: part 1 `10*prev + bank[i]` with a running `max prev`; part 2 a 12-row table | `Parsec` parser; `for hi : i in 1...<n` for safe indexing | index bounds only |
| 9 | Lean 4 | [Dessertion](https://github.com/Dessertion/advent-of-code-2025/blob/HEAD/AdventOfCode2025/D3.lean), [benjaminfjones](https://github.com/benjaminfjones/advent-of-code-2025/blob/HEAD/AdventOfCode2025/D3.lean), [vanshjangir](https://github.com/vanshjangir/AoC/blob/HEAD/2025/day03.lean), [frutjus](https://github.com/frutjus/aoc2025/blob/HEAD/day3/part2.lean), [stonarini](https://github.com/stonarini/AoC-2025/blob/HEAD/AoC2025/Day03.lean), [a2435191](https://github.com/a2435191/advent-of-code-2025-lean/blob/HEAD/advent-of-code-2025/AdventOfCode2025/Day3.lean) | 24–114 | search 9..1 with `firstM` (Dessertion); delete-a-digit to a fixpoint (benjaminfjones); stack (vanshjangir); greedy over `tails` (frutjus) | `termination_by l.length` + `decreasing_by simp_all; omega` (Dessertion); `partial def` (benjaminfjones, vanshjangir, frutjus), with "TODO: prove that sizeOf xs' < sizeOf xs"; benjaminfjones keeps a "this one is WRONG" attempt | no |
| 10 | Idris 2 | [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day3/Solution.idr), [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day3.idr), [Pengler38](https://github.com/Pengler38/AoC-2025/blob/HEAD/src/Day3.idr), [devcordde](https://github.com/devcordde/adventofcode-25/blob/HEAD/Day-03/idris2/duckulus/day03.idr) | 35–70 | `Vect 12` candidate with every removal tried (BrianNormant); greedy (others) | `%default covering`; `testH1 = Refl` (a second `Refl` commented out); Pengler38 marks every function `partial` | `Refl` tests only |
| 11 | Agda | [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day03.agda) | 41 | greedy, recursion on ℕ | `removeLastN n = reverse ∘ drop n ∘ reverse`; `dropWhileᵇ`; `Extrema.max` | no |
| 12 | Haskell | [glguy](https://github.com/glguy/advent/blob/HEAD/solutions/src/2025/03.hs) | 37 | **DP fold**, best value for every size at once | `solveLine = foldl addDigit (repeat 0)`; `[ max a (b * 10 + d) \| a <- prev \| b <- 0 : prev]` (parallel list comprehension); doctests with the example and real answers | no |
| 13 | Haskell | [RossPaterson](https://github.com/RossPaterson/advent-of-code/blob/HEAD/2025/Day03.hs) ([alt](https://github.com/RossPaterson/advent-of-code/blob/HEAD/2025/Day03alt.hs)) | 39, 44 | DP via `foldr`; the alternative is greedy | `zipWith max (best++[0]) (zipWith (+) (iterate (*10) d) (0:best))`; keeps the all-pairs part 1; `lessOrFirst`: "like compare, but EQ is treated as GT (so max chooses the first)", with a prose correctness argument | no |
| 14 | Haskell | [mstksg](https://github.com/mstksg/advent-of-code/blob/HEAD/2025/AOC2025/Day03.hs) | 36 | **search**, digits 9 down to 1, in `StateT String []` | `n <- lift "987654321"`; `[ xs' \| x : xs' <- tails xs, x == n ]`; `replicateM n nextDigit`; 287 µs and 4.35 ms **[cited]** | no |
| 15 | Haskell | [beefyhalo](https://github.com/beefyhalo/aoc/blob/HEAD/src/2025/03.hs), [nicuveo](https://github.com/nicuveo/advent-of-code/blob/HEAD/2025/haskell/src/Day03.hs) | 34, 40 | stack; k-digit register | guard `(x : xs) \| x < d && l + remaining >= k -> pop (l - 1) xs`; `parMap rpar` | no |
| 16 | Haskell | [PP6464](https://github.com/PP6464/AoC-2025-Haskell/blob/HEAD/src/Day03.hs), [stanosphere](https://github.com/stanosphere/advent-of-code/blob/main/src/2025/Day3.hs), [GuillaumedeVolpiano](https://github.com/GuillaumedeVolpiano/adventOfCode/blob/master/2025/days/Day3.hs) | 28–120 | greedy; bit-packed register (GuillaumedeVolpiano) | `maxWithIndex = second negate . maximum . flip zip [0,-1..]` (leftmost by negated index); stanosphere: "probably there's a splitAt or something?"; 1.27 ms and 1.90 ms **[cited: megathread]** | no |
| 17 | OCaml | [mbacarella](https://github.com/mbacarella/ocaml-aoc2025/blob/HEAD/lib/day3.ml), [FizzyElt](https://github.com/FizzyElt/ocaml_aoc_2025/blob/HEAD/bin/day3/q2.ml), [KacperKopiec](https://github.com/KacperKopiec/advent-of-code/blob/main/2025/day3/part2.ml), [lambdam](https://github.com/lambdam/advent-of-code-2025-ocaml/blob/HEAD/lib/day03.ml), [lukaskollmer](https://github.com/lukaskollmer/advent-of-code/blob/HEAD/src/2025/day_03/solution.ml), [aguluman](https://github.com/aguluman/advent-of-code-ocaml/blob/HEAD/2025/day03/day03.ml) | 13–109 | greedy (four); online DP by deleting one of 12 digits (KacperKopiec); every removal from a 13-digit window (lambdam) | `%expect_test` per example line (mbacarella); `when` guards (FizzyElt); hand-written `drop_end` and `max_idx` (lukaskollmer); `Int64` (aguluman) | no |
| 18 | F# | [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day03.fs), [jrmcnair](https://github.com/jrmcnair/advent-of-code/blob/HEAD/2025/Day3.fs), [mattgallagher92](https://github.com/mattgallagher92/advent-of-code/blob/HEAD/2025/Day03.fs) | 9–57 | greedy | lboshuizen is 9 lines: `seq {pos .. bn.Length - r - 1} \|> Seq.maxBy (fun i -> bn[i])` folded with `Seq.foldBack`; mattgallagher92: "furthest left wins", Expecto tests | no |
| 19 | Scala 3 | [lupari](https://github.com/lupari/aoc2025/blob/HEAD/src/main/scala/assignments/Day03.scala), [sim642](https://github.com/sim642/adventofcode/blob/HEAD/src/main/scala/eu/sim642/adventofcode2025/Day3.scala), [bishabosha](https://github.com/bishabosha/advent-of-code-2025/blob/HEAD/scala/2025_day03.scala), [jelaby](https://github.com/jelaby/advent-of-code-2025-scala/blob/HEAD/src/main/scala/uk/co/mealor/aoc2025/Day3.scala), [Casper-Guo](https://github.com/Casper-Guo/AoC-Language-Exploration/blob/HEAD/2025.scala/day03.scala) | 22–61 | greedy (four); memoised DP (sim642) | `.slice(from, …).zipWithIndex.maxBy(_._1)`; `helper(i - 1, digits) max (helper(i - 1, digits - 1) * 10 + bank(i).asDigit)` with `mutable.Map`; "part 1: 16769 - not right (combinations don't keep order)"; jelaby unrolls part 2 twelve times | no |
| 20 | Elixir | [nikola-benes](https://github.com/nikola-benes/aoc2025elixir/blob/HEAD/03lin.exs), [lasseebert](https://github.com/lasseebert/advent_of_code_2025/blob/HEAD/lib/advent/day_03.ex), [ryoung786](https://github.com/ryoung786/AdventOfCode/blob/HEAD/lib/aoc/years/2025/day_03.ex) | 21–61 | greedy and stack (nikola-benes has both); remove-lower-lead (lasseebert) | `Stream.drop(-n + 1) \|> Stream.with_index() \|> Enum.max_by(…)`; `when top < cur and b_len > empty`; `Integer.undigits` | no |
| 21 | Clojure | [narimiran](https://github.com/narimiran/aoc2025/blob/HEAD/clojure/src/day03.clj), [CodeFarmer](https://github.com/CodeFarmer/aoc-2025/blob/HEAD/src/aoc_2025/day_3.clj), [tschady](https://github.com/tschady/advent-of-code/blob/HEAD/src/aoc/2025/d03.clj), [genmeblog](https://github.com/genmeblog/advent-of-code/blob/HEAD/src/advent_of_code_2025/day03.clj) | 17–30 | greedy | narimiran: `max-key` "would pick the latter 7", so `[2 7 5 7 3]` gives 73 instead of 77 **[cited]**; `(apply max (drop-last (dec pos) bank))` + `.indexOf` (tschady) | no |
| 22 | Koka | [junpls](https://github.com/junpls/aoc25/blob/HEAD/day03.kk), [HeikoRibberink](https://github.com/HeikoRibberink/aoc25/blob/HEAD/day3/common.kk) | 33, 45 | greedy with local `var`s; a register that zeroes its tail | parser combinators; `foreach-indexed`; `Cons(digit, tail.map(to-zero))` | no |
| 23 | Gleam | [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day03/day03.gleam), [bmatcuk](https://github.com/bmatcuk/adventofcode2025/blob/HEAD/day03/src/day03.gleam), [tilltheis](https://github.com/tilltheis/adventofcode-2025-gleam/blob/HEAD/src/day03.gleam), [houli](https://github.com/houli/advent-of-code-2025/blob/HEAD/src/day3.gleam), [bucsi](https://github.com/bucsi/aoc/blob/HEAD/solutions_gleam/src/aoc_2025/day_3.gleam) | 48–95 | stack (Zenor27); greedy (others); `list.combination_pairs` for part 1 (Zenor27, bucsi) | `[#(_, remains), .._] if remains < remaining`; `undigits` vendored "Deprecated so I vendored it" **[cited]** | no |
| 24 | Roc, Elm, Admiran | [arnemart](https://github.com/arnemart/aoc/blob/HEAD/2025/03/3.roc), [0xErwin1](https://github.com/0xErwin1/advent-of-code/blob/HEAD/2025/day_3/main.roc), [albertdahlin](https://github.com/albertdahlin/advent-of-code/blob/HEAD/elm/src/Y25/D03.elm), [caseyWebb](https://github.com/caseyWebb/advent/blob/HEAD/2025/src/Day03.elm), [maxhille](https://github.com/maxhille/aoc-2025/blob/HEAD/days/Day03.elm), [taolson](https://github.com/taolson/advent-of-code/blob/HEAD/2025/day03.am) | 26–100 | greedy; look-ahead skip (taolson) | `List.drop_last` (Roc); `indexedFindLastMax` on the reversed list (caseyWebb); elm-test on 3121910778619; taolson: `= go r' n ds, if canSkip & hasBetter`, "The first version of this used memoization" **[cited]** | no |
| 25 | Chez Scheme | [erickalkman](https://gitlab.com/erickalkman/aoc2025/-/blob/main/day03.sls) (megathread: onrustigescheikundig) | 49 | **search** over a digit-to-positions map, 9 down to 1 | "the first successful result of which must be the maximum" **[cited: megathread]**; about 2 ms | no |
| — | Stitchwort | `aoc/src/Aoc/Day03/Day03.sw` + `Proofs/Best.sw` | 25 (program) + 9 (tests); 133 (proofs) | greedy window, leftmost largest (`if c < x`) | `pick` as a local definition; `Nat.fromDigits`; the example and real-input answers as tests | **yes**: `bestSub`, `bestLength`, `bestOptimal`, `joltageIsLargest`, numeric, for every k and line; 16 theorems, checked in about 0.5 s |
| — | Stitchwort, three community shapes | scratch `dp.sw`, `greedy.sw`, `stack.sw` | 16–22 | DP fold, greedy, stack | §4 | no |

Also read, and not in the table because they repeat these patterns: Lean frutjus part 1 and
Idris frectonz (part 1 only). Elixir ryoung786's pairwise window merge and Clojure genmeblog's
comparator merge (rows 20, 21) are variants of the stack. einarwh's Elm was not used, because
it embeds the puzzle input (the sub-agent deleted it), and erickalkman's file came through a
web fetch, so it isn't byte-exact **[checked]**.

All rows are **[checked]**: fetched and read, except cells marked **[cited]**. I ran none of
them.

**Correctness notes from reading** **[inferred, not run]**:

- kim-em's `maxJoltageK` returns 0 for a bank shorter than k, and its theorem
  `maxJoltageK_greedy` only says the result is positive unless the bank is all zeros, which is
  weaker than its doc comment ("each selected digit is maximal").
- Hath995's `problem3_2` uses `expect |banks[i]| > 12`, so a bank of exactly 12 digits would
  stop it; the theorem's `count < |bank|` is the same restriction. Ours has `min k (length)`.
- Several greedy solutions call `length` on the remaining list at every step (FizzyElt,
  albertdahlin, our `rest.length` once per digit chosen); harmless at 100 digits.
- Sorting the window to find its maximum (stonarini, dzecniv in the megathread) is correct
  only with a tie rule on positions; stonarini's comparator has one.

### 2.1 What I couldn't find

- **Unison, PureScript, Coq/Rocq, F\*, Effekt:** none in GitHub repository and code searches or
  the megathread. Code searches for `.v` "joltage" found only Verilog and V. The GitHub code
  search rate-limited both sub-agents once; they waited and retried, but searches are not
  exhaustive **[checked: the sub-agents' reports]**.
- **Day 3 from some earlier authors:** mfornet, joek13, DavidMazarro, Zikoat, 0xmycf and
  mpizenberg (Roc) have no day 3; freddydumont's Elixir stops at day 2; marvinborner's 2025/03
  is Python, not Effekt.
- **Lean theorem searches** ("joltage theorem", "greedy joltage", "bank digits subsequence
  lemma") found nothing beyond the files above.
- **Reddit itself:** not contacted; the megathread came from the Arctic Shift archive.
  Linked pastes (topaz) weren't decoded.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** Four requests to [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift): a
title search (timed out, "Maybe slow down a bit"), a post search by time window (3 Dec 2025,
03:00–07:00 UTC) after a pause, `/api/posts/ids?ids=1pcvaj4`, and
`/api/comments/tree?link_id=t3_1pcvaj4&limit=25000` (2.3 MB). No requests to reddit.com
**[checked: saved in `arctic/`]**. Terms as in the day 1 note.

**What it holds.** "-❄️- 2025 Day 3 Solutions -❄️-" (3 Dec 2025, score 37, recorded
`num_comments` 894). The tree has 1,014 comments in all: **682 top-level**, 12 of them
`[deleted]`/`[removed]`, 636 of the live ones with a language tag and 34 without. 286 of the 670
live comments have code inline **[checked: `scripts/langs.py`]**.

**The landscape.** Tags counted once per comment and language; spelling variants merged
(by script, then a few by hand, e.g. CPython into Python):

| Language | Comments | | Language | Comments |
|---|---|---|---|---|
| Python | 155 | | Swift, R | 7 each |
| Rust | 70 | | F#, Scala, Common Lisp, OCaml | 6 each |
| Go | 32 | | Perl, Uiua | 5 each |
| Java, C++ | 27 each | | Nim, Awk, Raku, Scheme, Julia, Gleam, Clojure, Google Sheets | 4 each |
| TypeScript | 27 | | Lua, SQL, Q, Dyalog APL, Bash, PowerShell | 3 each |
| Haskell, C# | 24 each | | Prolog, Dart, PHP, Smalltalk, jq, Odin, COBOL, … | 2 each |
| JavaScript | 21 | | Emacs Lisp, Dafny, Admiran, Racket, Janet, … | 1 each |
| C | 17 | | | |
| Ruby | 13 | | | |
| Kotlin | 11 | | | |
| Zig | 10 | | | |
| Elixir | 9 | | | |

The functional or proof-oriented tags add up to 76 comments, 11% of the live ones (day 1: 82,
day 2: 66). No Lean, Idris, Agda, Coq/Rocq, Koka, Roc, Elm, PureScript, Erlang, Effekt or
Unison tag this time.

**Methods, megathread-wide** (regular expressions over all 670 live comments; "with code" means
the comment has code inline) **[checked: `scripts/methods.py`]**:

| Pattern | Comments | With code |
|---|---:|---:|
| says "greedy" | 50 | 24 |
| a stack or "monotonic" | 25 | 14 |
| dynamic programming or memoisation | 36 | 11 |
| says "brute force" | 33 | 9 |
| combinations, "choose" or `itertools` | 24 | 13 |
| "window" | 34 | 11 |
| a maximum with its index (`max_by`, `maxBy`, `enumerate`, `indexOf`, `position`, …) | 141 | 119 |
| an arg-max helper by name (`maximumBy`, `maxBy`, `max_by`, `max-key`, …) | — | 23 |
| leftmost, first occurrence or ties | 20 | 11 |
| 64-bit or big integers (`u64`, `Int64`, `Long`, `BigInt`, overflow) | 50 | 46 |
| the fold `acc * 10 + d` | 67 | 65 |

The "maximum with its index" pattern is broad (Python's `enumerate` and `.index(` dominate), so
read it as "most solutions find a position", not as a precise count.

**What I read.** All 76 functional comments (32 with code inline). The ones that add to §2:

| # | Language | Author / link | Notable |
|---|---|---|---|
| 26 | Haskell | [bramhaag](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns0oukk/) | the whole stack solution in 8 lines: `(stk, _) = foldl' step ([], length s - k) s`, `step (t:ts, d) x \| d > 0 && x > t = step (ts, d-1) x` |
| 27 | Haskell | [sondr3_](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns2en8u/) | the DP as one line: `go prev n = zipWith max prev (map (\b -> b * 10 + n) (0 : prev))`; 602 µs and 3.83 ms **[cited]** |
| 28 | Haskell | [danvk](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns46rrw/) | "(100 choose 12) is ~1e15"; "taking the first instance of the max digit … gives you the most optionality, you can do this without loss of generality" **[cited]**: the exchange argument in one sentence; `(_, _ : rest) = break (== best) xs` |
| 29 | Haskell | [XamazingX5](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns0rqis/), [cinx16](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns2ah6u/), [SnooHesitations6473](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns4u29e/), [Foldzilla](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns2citu/) | `minimumBy` with `Down` because "`maximumBy` returned the last maximum"; `drop 1 (dropWhile (/= largest) xs)`; a hand-written `maxWithPos` fold |
| 30 | Haskell | [mstksg](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns0xu9z/), [Porges](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns7ok56/) | search in the list monad: Porges sorts `mapMaybe uncons . tails` by digit and takes `head` of the `do` block; "mostly imports" edition |
| 31 | Haskell, OCaml | [NeilNjae](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns2nlhi/), [Saser](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns3chwz/) | DP over a `Map` from count to best (`M.unionWith max`); Saser's bottom-up DP took 1.4 ms, the greedy 0.5 ms: "Glad I looked at Reddit after posting my first one" **[cited]** |
| 32 | Haskell, Admiran | [hopingforabetterpast](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns5j38r/), [icecoldgold773](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns32wj3/) | pattern guards: `\| m:ms <- mx , x > m = go (succ n) ms (x:xs) zs`; `\| canSkip && hasBetter = selectNDigits n xs` |
| 33 | Scala | [stewSquared](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns50ozz/), [dcss_addict](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns5ho1h/), [sim642](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns0sy3k/) | the indices as a `scanLeft`: `(batteries to 1 by -1).scanLeft(-1): case (i, b) => (i + 1 to bank.length - b).maxBy(bank)`; `batteries.dropRight(length-1).max`; sim642: `.combinations(2)` "forgets the order of elements" **[cited]** |
| 34 | F#, Clojure, Elixir | [r_so9](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns0pyio/), [munchler](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns0v45c/), [stalebit](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns1mr98/), [IvanMisustin](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns3tib7/) | `Seq.take … \|> Seq.max` then `Seq.findIndex`; `Array.indexed … \|> Seq.maxBy snd` with `seq { yield …; yield! … }`; Clojure `(map-indexed vector) reverse (apply max-key second)` (reversed for the tie); IvanMisustin builds the number with `:math.pow(10, idx)`, a float |
| 35 | Prolog | [bolusmjak](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns1azwc/) | a DCG that tries `countdown(0'9, 0'1, D)` and backtracks: the search family in 10 lines; 0.015 s and 0.112 s **[cited]** |
| 36 | Dafny | [Hath995](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns1t986/) | "with enough time I think it should be possible to prove that the results are the lexicographically largest possible subsequence"; the repository's commit "proved lexicographic max" followed that evening (row 1) |
| 37 | OCaml, Common Lisp, Emacs Lisp, Janet | [POGtastic](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns0xilg/), [dijotal](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns5hprb/), [geza42](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/ns1bll2/), [veydar_](https://www.reddit.com/r/adventofcode/comments/1pcvaj4/2025_day_3_solutions/nsg2ufz/) | POGtastic: "sidetracked … thinking that this was a dynamic programming problem"; dijotal records each digit's first position in a 10-slot array; geza42's whole solution is 6 lines (`(-max (butlast bank digits))`, `(cdr (member d bank))`) |

Megathread comments outside the functional group that matter here, all **[cited]**:
Alert_Bake_9026 (Rust) names the problem "the lexicographically maximum subsequence of length
k" and the monotonic stack; andrewsredditstuff (C#): "MAXBY does not necessarily return the
first one it finds (in my case, it was returning the last)"; DMonitor (Rust) reverses before
`max_by_key` "so we find the first one"; tonyganchev (C++) keeps it in a LeetCode repository.

**Notes from the megathread**:

- **As on days 1 and 2, several authors say they are learning the language** (fuxino, dijotal,
  Nemin32, baboonbomba's polyglot run), so style is weak evidence; complaints are stronger.
- **The complaints:** the tie rule of arg-max helpers (above); wanting an `argmax` (vanZuider:
  "Using an actual `argmax` functions would probably have been cleaner, but `dropWhile (<max)`
  does the job"); `Int` to `Long`; off-by-one window bounds (MyEternalSadness, G_de_Volpiano);
  and part 2's combinatorial explosion for those who started from combinations
  (SandPrestigious2317: "121 billion combinations … my computer glitched and shutdown").
- **Speed is not an issue for the linear methods** in any language: 0.004 s (dijotal, Common
  Lisp), 17–20 ms (Gleam), 0.67 ms (Elixir), 1–4 ms (Haskell) **[cited]**.

## 3. Themes

### 3.1 Parsing a line of digits

| Approach | Who | Example |
|---|---|---|
| `digitToInt` / `asDigit` per character | most Haskell and Scala | `map (map digitToInt) . lines` |
| Character code minus `'0'` | Lean, OCaml, Idris, Gleam, Scheme | `c.toNat - '0'.toNat`; `int_of_char c - 48` |
| A digit function that can fail | Lean (bjornestol's `Except`, a2435191's `Char.toDigit?` with `mapM`), Idris (spikedoanz), natewhite345's refined `Joltage` | `s.toList.toArray.mapM Char.toDigit?` |
| Parser combinators | Koka, Lean (dupuisf), Elm (maxhille), Prolog DCG, Haskell megaparsec | `many digit` |
| Keep the text, compare characters | mstksg, Gleam (houli), Lisp (dzecniv) | `lift "987654321"` |

**Stitchwort today.** `Bank.parse` is `t.toList |> .filterMap Char.digitValue`, and the library
proves it yields digits (`Char.mapDigitValueDigits`), which the proof uses to discharge "every
digit is below 10". Nothing is missing here, and the example can be a `"""` text block
(`dp.sw` **[checked]**).

### 3.2 The four methods

| Method | How it works | GitHub (of 68) | FP megathread (of 76) |
|---|---|---:|---:|
| Greedy window | for each of the k digits, the leftmost largest digit among those that leave enough after them | ~48 | ~37 |
| Stack / register | scan once; a larger digit pops smaller ones while drops remain | ~10 | ~9 |
| DP | best value for every size so far, updated per digit | 5 | ~6 |
| Search | try 9, 8, …, 1 as the next digit, backtrack when too few remain | 3 | ~4 |

**[checked: counted by hand from the files and comments; approximate]**

The DP and the stack are linear in the bank; the greedy is `O(k · n)`. At 100 digits and
k = 12 all are fast. The DP needs no tie rule and no index, which is why glguy's and sondr3_'s
are the shortest correct Haskell; the greedy is the one with a proof story, because "the
leftmost largest" is exactly the step the exchange argument needs.

**Stitchwort today.** All three of the common shapes ran first time **[checked]**:

```
-- dp.sw, after sondr3_ and glguy
def step (prev: List Nat) (d: Nat): List Nat :=
  List.zipWith Nat.max prev (Cons 0 prev |> .map (b => b * 10 + d))

def joltage (k: Nat) (line: Text): Nat :=
  line.toList |> .filterMap Char.digitValue |> .foldLeft step (List.replicate k 0) |> .last |> .getOrElse 0
```

```
-- stack.sw, after bramhaag
def push (x: Nat): List Nat -> Nat -> (List Nat, Nat)
  | [t, ..ts], Succ d => if x > t then push x ts d else (Cons x (Cons t ts), Succ d)
  | stk,       d      => (Cons x stk, d)
```

`push` recurses on the stack's tail, so it is structural with no fuel. glguy's `repeat 0` (an
infinite list) becomes `List.replicate k 0`.

### 3.3 Ties: leftmost or wrong

The greedy is correct only if, among equal digits in the window, it takes the leftmost: that
leaves the most digits for the rest. The library helpers people reached for disagree on ties:

| Helper | Returns on a tie | Who hit it |
|---|---|---|
| Haskell `maximumBy` | the last | XamazingX5 ("returned the last maximum"); RossPaterson wrote `lessOrFirst`, PP6464 negated the index |
| Clojure `max-key` | the last | narimiran (`[2 7 5 7 3]` → 73), stalebit reversed first |
| Rust `max_by_key` | the last | DMonitor and others reverse first |
| C# `MaxBy` | the first, but one author saw the last **[cited, not checked]** | andrewsredditstuff |
| Scala `maxBy`, F# `Seq.maxBy`, Elixir `Enum.max_by`, Kotlin `maxBy` | the first | lupari, lboshuizen, nikola-benes **[unverified for each library's documentation; inferred from working solutions]** |

Ours is `if c < x then pick … x … else pick … c …`: strict, so the earlier digit stays. Making
it `c <= x` gives `881911112111` instead of `888911112111` for the example's fourth bank and
17073 instead of 17263 on the real input, and `docs/aoc-2025.md`'s sabotage list records that the
proof then fails ("day 3 `if c < x` to `c <= x`") **[checked:
`p_tie.sw`, with the failed test printing both values]**. So the bug most people hit by
accident is one our proof rules out by construction. One small gap: the unit test named
"leftmost wins", `Bank.best 1 [3, 9, 9, 1] == [9]`, passes with either rule (`p_tie.sw`), since
the two 9s are equal and nothing follows the choice. narimiran's `[2, 7, 5, 7, 3]` with k = 2
(77 against 73) tells them apart.

### 3.4 Library breadth

| Helper | Seen in | Stitchwort |
|---|---|---|
| maximum of a list | everyone | `List.maximum` (an `Option`) |
| arg-max: the maximum with its position, or by a key (`maximumBy`, `maxBy`, `max_by`, `max-key`, `maxI`, `Extrema.max`) | 15 GitHub files, 23 megathread comments with code | **missing** **[checked: `p_missing.sw`, `E-ARITY: List needs 1 argument(s)` for `List.maxBy`]** |
| the rest after the first match (`dropWhile`, `break`, `span`, `member`) | danvk, cinx16, bjornestol, jpyamamoto (`dropWhileᵇ`), geza42 | **missing**: `[3, 9, 1].dropWhile …` is `E-UNKNOWN-FIELD: List has no field or function dropWhile` (a clear message) **[checked: `p_dot.sw`]**; a 3-line `after` in `greedy.sw` |
| all but the last n (`dropRight`, `dropLast`, `drop_end`, `butlast`, `Stream.drop(-n)`) | 12 GitHub files; jpyamamoto writes `reverse ∘ drop n ∘ reverse` | **missing**; `xs.take (xs.length - n)` works (ours) |
| `tails` | mstksg, Porges, RossPaterson, frutjus and 4 more | **missing** |
| index of the first match (`findIndex`, `indexOf`, `elemIndex`, `position`) | 17 GitHub files | **missing** |
| with index (`zipWithIndex`, `with_index`, `indexed`, `foreach-indexed`) | 12 GitHub files | `List.zip xs (List.range n)` |
| `splitAt` | natewhite345, Pengler38, stanosphere ("probably there's a splitAt or something?") | **missing** (two calls) |
| `zipWith`, `replicate`, `foldLeft`, `scanLeft`, `last` | glguy, sondr3_, stewSquared | all present |
| digits to a number (`undigits`, `foldl (\a d -> a*10+d)`, string then `read`) | everyone; Gleam's was "Deprecated so I vendored it" | `Nat.fromDigits` (with lemmas) |

Many solutions build a string of digits and parse it (`read`, `toLong`,
`Int64.Parse`, `parse-long`), which is where Pengler38 and IvanMisustin take a detour through
`show` and `:math.pow`. `Nat.fromDigits` avoids that, and it is what the proof reasons about.

### 3.5 Guards, and the shapes that want them

The stack and look-ahead solutions are a pattern plus a condition, falling through to the next
case when the condition fails:

```haskell
-- bramhaag (Haskell)
step (t:ts, d) x | d > 0 && x > t = step (ts, d-1) x
step (stk, d) x = (x:stk, d)
```
```elixir
# nikola-benes (Elixir, 03lin.exs)
{[cur | _], [top | tail]} when top < cur and b_len > empty -> …
```

**Stitchwort today** has no guards: alternatives are tried top to bottom, and a condition
belongs in the body (docs/syntax.md, `match`). So the fallback is written twice, once as its own
alternative and once in the `else` (`stack.sw`, above: `(Cons x (Cons t ts), Succ d)` repeats
what `| stk, d => (Cons x stk, d)` gives). About 11 GitHub files and 5 functional megathread
comments with code use a guard (Haskell `|`, OCaml and Elixir `when`, Gleam `if`, Admiran
`, if`) **[checked: grep, then read the hits]**. A guard interacts with coverage (a guarded
alternative doesn't cover its pattern) and, for proofs, with what a branch knows: `| p if c`
should give the branch `c` as a fact, as `if` does, and the later alternatives `not c`. That
makes it a design question, not a library one.

### 3.6 Proofs and automation

What the community proved for day 3:

- **Hath995 (Dafny): optimality, lexicographic.** The statement:
  ```dafny
  lemma flsIsLexicographicMax(bank: seq<nat>, count: nat)
      requires |bank| > 0
      requires 0 < count < |bank|
      ensures forall ss :: ss in subsetSeqs(bank) && |ss| == count ==> lexSort(fls(bank, 0, count), ss)
  ```
  The core lemma `TheoremFlsIsLexMax` compares heads, and on a tie uses `MaxIndex`'s
  postcondition (the earliest maximum) to show the other choice's tail lies in the suffix after
  the greedy's pick, then recurses; the boundary case (exactly `count - 1` digits left) is its
  own branch. Helpers cover subsequence membership (`LemmaSubsetsContained`,
  `LemmaHeadLocation`) and slicing (`LemmaFlsSliceEquivalence`). About 290 of 408 lines are
  lemmas; Dafny's solver fills in the arithmetic.
- **natewhite345 (Lean), andorp (Lean): part 1 comparisons.** Both prove that two-digit numbers
  compare lexicographically (`from_digits_cmp` by `simp_all; grind`; `pairValue_lt_iff` by
  `omega`), our `fromDigitsHeadLess` for k = 2. Both stop before optimality.
- **kim-em (Lean):** two `sorry`s with the comment that the imperative loop is the obstacle.
- **Totality without proofs:** acarapetis's `termination_by` + `decreasing_by omega`, andorp's
  `hk : k ≤ rest.length` argument, Dessertion's `decreasing_by simp_all; omega`; against
  `partial def` in benjaminfjones, vanshjangir, frutjus and adomani, and Idris's `partial`
  (Pengler38) and `%default covering` (BrianNormant).

**Where ours stands.** Hath995's proof and ours make the same argument; ours goes one step
further (to the number, `Nat.fromDigits`, with `Nat.fromDigitsHeadLess`), covers banks shorter
than k (`bestLength`'s `min`), and is stated for an input line (`joltageIsLargest`). It is 133
lines in 16 theorems, written without arithmetic automation, where Dafny's lemmas lean on the
solver. Our cost shows elsewhere: `pick`'s `if` is reasoned about by matching on
`Nat.leq (Succ c) x` and spelling out what the `if` became (`Decidable.elim (Bool.decTrue …)`
in `pickBestStep`'s statement), and recursive calls passed as hypotheses must be fully applied
(`c2 a2 g1 g2 g3 y2 s2 g4 g5 g6 => …`, SW-116). Both were noted in `docs/aoc-2025.md`; the
community adds no new friction here.

### 3.7 Speed of the obvious programs

Times are wall-clock for the whole command, including checking (one run each, on a laptop
that was also running other work):

| Program | `stitchwort run` | `run --js` |
|---|---:|---:|
| Committed greedy (`Aoc.Day03.main`) | 0.74 s | 0.55 s **[checked]** |
| DP fold (`dp.sw`) | 1.56 s | 0.49 s **[checked]** |
| danvk's greedy (`greedy.sw`) | 1.00 s | 0.50 s **[checked]** |
| bramhaag's stack (`stack.sw`) | 0.81 s | 0.51 s **[checked]** |
| Brute force, part 1 only, all pairs (`brute.sw`) | 5.21 s | 0.57 s **[checked]** |
| Brute force, part 2, every 12-subsequence | infeasible (about 10^15 per bank); runs as a test on the example **[checked: `brute.sw`]** | |
| sondr3_, DP, Haskell | 602 µs, 3.83 ms (parsing 874 µs) **[cited]** | |
| mstksg, search, Haskell | 287 µs, 4.35 ms **[cited]** | |

The linear methods don't matter at this size. The all-pairs brute force for part 1 (about a
million pairs) shows the evaluator gap again: 9× slower under `run` than with `--js`, in line
with day 1's brute force (5.5 s against 0.95 s) **[inferred]**. The DP's 1.56 s under `run` is
mostly `zipWith` over twelve-element lists per digit (200 × 100 × 12 updates) **[inferred: not
profiled]**.

## 4. Side by side

The committed `pick` against the community's most common greedy, and the shortest correct
program in each family:

```
-- Stitchwort (Day03.sw): the leftmost largest of the next w digits, and what follows it
def pick: Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)
  | Zero,   _,           c, after => (c, after)
  | Succ _, [],          c, after => (c, after)
  | Succ w, Cons x more, c, after =>
    if c < x then pick w more x more else pick w more c after
let (top, after) := pick (rest.length - k) rest d rest
Cons top (Bank.best k after)
```

```haskell
-- danvk (Haskell)
chooseWithMax n xs = best : chooseWithMax (n - 1) rest
  where
    best = maximum $ take (length xs - n + 1) xs
    (_, _ : rest) = break (== best) xs
```

```
-- Stitchwort, scratch greedy.sw (danvk's shape)
def after (x: Nat): List Nat -> List Nat
  | []         => []
  | [y, ..ys]  => if y == x then ys else after x ys

def choose: Nat -> List Nat -> List Nat
  | Zero,   _  => []
  | Succ n, xs =>
    let best := xs.take (xs.length - n) |> .maximum |> .getOrElse 0
    Cons best (choose n (after best xs))
```

danvk's version gets leftmost-on-ties for free: `break (== best)` stops at the first `best`.
Ours finds the maximum and its position in one pass, which is what the proof's `pickBest`
follows step by step. With D360 and D361, `greedy.sw` would lose `after` (`xs.dropWhile (y => y
!= best) |> .drop 1`, or a `List.maxBy` that returns the rest).

```scala
// stewSquared (Scala): the chosen indices as a scan
val indices = (batteries to 1 by -1).scanLeft(-1):
  case (i, b) => (i + 1 to bank.length - b).maxBy(bank)
indices.tail.map(bank).mkString.toLong
```

`List.scanLeft` exists; the missing piece for this shape is `maxBy` (with its first-on-ties
rule).

## 5. Candidate features, ranked by value over effort

Kinds: **sugar** (syntax only), **library**, **tooling**, **language** (elaboration or kernel).

| Rank | Candidate | Kind | Value | Effort | Evidence | Ticket |
|---|---|---|---|---|---|---|
| 1 | **`List.maxBy`/`minBy` (by a key) that keep the first of equal elements, documented and tested** | library | medium: the commonest helper in day 3 code, and the tie rule is the day's bug | small | §3.3, §3.4: 15 GitHub files, 23 megathread comments with code; XamazingX5, andrewsredditstuff and narimiran on last-wins; 7 megathread comments work around it | none; beside SW-219 |
| 2 | **`dropWhile`, `takeWhile`, `span`, `dropRight`, `tails`, `findIndex`, `zipWithIndex`, `splitAt`** | library | medium: each is short to write, but each turns up in several solutions | small | §3.4: 4–17 files each | none; a second batch after SW-219 |
| 3 | **A distinguishing "leftmost wins" test in Day03.sw** (`[2, 7, 5, 7, 3]`, k = 2, is 77) | tests | low to medium: the proof already covers it, but the test should mean what its name says | trivial | §3.3, `p_tie.sw` | none; fits SW-224 (AoC refresh) |
| 4 | **The every-choice brute force as a Day03.sw test** (`choices k ds`, on the example) | tests | low to medium: the theorem's statement as a runnable check, as day 2 keeps its brute force | trivial (8 lines, passes today) | `brute.sw`; memory "keep unit tests beside proofs" | none; fits SW-224 |
| 5 | **Pattern guards** (`\| p if c => …`, giving the branch `c` and later alternatives `not c`) | language | medium: stack and look-ahead shapes, recursive helpers generally | medium (coverage, motives, the `if`-fact rule) | §3.5: ~11 GitHub files, 5 FP megathread comments with code | none; design note first |
| 6 | **Evaluator speed on the all-pairs brute force** (5.2 s `run`, 0.57 s `--js`) | tooling | low for day 3 | — | §3.7 | evidence for the evaluator work (docs/evaluator-speed.md); no new ticket |
| — | Local mutable variables (Koka `var`, Lean `let mut`, Scala `mutable.Map`) | language | low | large | 8 files | **not now** (D299); no change |
| — | Arithmetic automation (`omega`, `grind`, a solver) | language/library | high for proofs | large | §3.6: the Lean pair lemmas, Dafny's solver | SW-101; no change |

Why this order:

- **Rank 1 is library work with a semantic choice inside it.** Which of equal elements wins is
  a design decision (§6, D360). "First" matches the greedy, Scala, F# and Elixir, and makes
  `maxBy` usable for the day's main step; Haskell's and Clojure's "last" caused the bugs above.
- **Rank 2 has no decisions inside it** beyond names. The missing-function message for
  `List.maxBy` (`E-ARITY`) is SW-227's case, already in progress; dot notation already says
  "has no field or function".
- **Ranks 3–4 are trivial and close a real gap:** the test named after the tie rule doesn't test
  it.
- **Rank 5 is the one language idea from day 3.** The `if` workaround costs one duplicated line,
  so it isn't urgent; it would also touch the D331/SW-226 rule (facts from conditions).
- **Rank 6 and the unranked rows are unchanged by day 3.**

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D360 | Add `List.maxBy` and `List.minBy` (by a key, returning `Option`), and decide their tie rule: the **first** of equal elements, stated in the docs and tested? | [yes, first-on-ties; with SW-219 or right after it] |
| D361 | Add a second list batch: `dropWhile`, `takeWhile`, `span`, `dropRight`, `tails`, `findIndex`, `zipWithIndex`, `splitAt`? | [yes, one small ticket after SW-219] |
| D362 | Write a design note on pattern guards in `match` and arms (`\| p if c => …`, the branch knowing `c`, later alternatives `not c`)? | [yes, backlog design note; not now as a feature] |
| D363 | Make Day03.sw's "leftmost wins" test distinguish the tie rule (`Bank.best 2 [2, 7, 5, 7, 3] == [7, 7]`)? | [yes; one line, with SW-224] |
| D364 | Keep the every-choice brute force (`choices k ds`, all k-subsequences) in Day03.sw as a test on the example, beside the proof? | [yes; with SW-224] |

---

**Status** (short form, 21 Oct 2026): D360 `maxBy`/`minBy` first-on-ties, pending; D361 second
list batch, pending; D362 guards design note, pending; D363 tie test, pending; D364 brute-force
test, pending. Unchanged by day 3: D296 operator sections and D297 text patterns not now, D299
local mutable variables not now, SW-101 backlog, SW-227 (missing-function message) in progress.
