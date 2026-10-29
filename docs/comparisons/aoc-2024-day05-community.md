# AoC 2024 day 5: community solutions in other languages

**Date:** 29 October 2026. **Ticket:** SW-893. **Our version:** finished before this note:
`aoc/src/Aoc/Year2024/Day05/`. Part 1 is proved for every print queue. Part 2 is proved for every
print queue whose rules strictly and totally order each update's pages. The friction notes are
in `aoc/NOTES-2024.md` ("## Day 5").

The puzzle: the input has 1,176 ordering rules (`47|53`: if an update has both pages, 47 comes
first), then 197 updates (lists of 5 to 23 pages). Part 1 adds up the middle pages of the
updates that break no rule. Part 2 puts each of the other updates in "the" right order and adds
up their middle pages. The answers are 4569 and 6456.

Day 5 is known for a shortcut. Most people do part 2 by sorting with a comparator built from the
rules. That works only because the rules happen to be a strict total order on each update's
pages, even though they are no order at all on the 49 pages taken together. This note asks who
relies on that, who checks it, what we prove, and what each shortcut does when the rules are
less kind.

The evidence labels are the same as in the earlier notes:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Where things are:

- **Scratch area:**
  `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/d2024-05/`.
  It holds the fetched files (`gh/files/`), the repository trees (`gh/trees/`, mostly reused from
  the day 3 lane), the megathread JSON (`arctic/`), the Stitchwort scratch project (`proj/`), and
  the outputs `adv5.out`, `bench.out` and `bench2.out`.
- **Committed copies:** the scripts and the Stitchwort scratch programs are in
  [aoc-2024-day05-community/scripts/](aoc-2024-day05-community/scripts/). The per-author tags are
  in [aoc-2024-day05-community/classify.tsv](aoc-2024-day05-community/classify.tsv).
- **Binary:** the main checkout's `target/release/stitchwort`, as rebuilt with `task build` at
  11:52 on 29 October.

## 1. Summary

1. **The input is a cyclic tournament.** Each of the 49 pages has a rule with every other page,
   in exactly one direction (1,176 = 49·48/2), and each page precedes exactly 24 others. So the
   rules as a whole are full of cycles (96|95, 95|18, 18|96 is one). Each update's pages,
   though, are ordered transitively **[checked: `adv5.py` on the input]**. That is why a
   comparator sort works here. Our test "real input, the rules order each update's pages" checks
   the same thing.
2. **Nobody else proves part 2 correct, and Thierry Martinez didn't do day 5 in Coq.** His
   repository has `.v` files only for days 1 and 2. Day 5 is `day05.py`, a depth-first
   topological sort **[checked: repository tree]**. The proof-language solutions:
   - **Hath995 (Dafny)** comes closest. `SortByRules` `ensures multiset(sorted) ==
     multiset(update)` and `InOrder(orderingRules, sorted)`, and `InOrder` is a direct
     transcription of the puzzle's rule. That is a real guarantee that holds with *no*
     assumption, but it is partial correctness only: the loop is `decreases *`, so Dafny never
     shows that it ends. It does not end when an update has a cycle. Nothing is proved about the
     sums or about uniqueness **[checked: file]**.
   - **shilangyu (Lean, Mathlib)** proves `updateOrderedSublist`: an update that is a sublist of
     the list of a `LinearOrder` is ordered. But the assumption is false for this input, which
     has no linear order on its pages. And `linearOrderList` is a stub that returns `[]`, so the
     theorem only says something about the empty update **[checked: file; `adv5.py` finds the
     3-cycle]**.
   - **main-- (Lean)** proves that parsing gives non-empty lists, plus two `validateRule`
     examples. Nothing about part 2 **[checked: file]**.
   - The other 18 Lean authors on GitHub (Matt's `mdr/aoc-2024` among them), 3 Idris, 1 Agda,
     1 Koka and 9 Roc authors prove nothing about the answer. aaronallen8455's Agda marks part 2
     `{-# NON_TERMINATING #-}` **[checked: grep for theorem, lemma, ensures, sorry, postulate;
     read the files named here]**.
3. **What we prove is more than anyone else, but under the strongest assumption.**
   - Part 1 needs no assumption: `inOrderCorrect` and `part1Correct`.
   - Part 2 has `reorderCorrect` (the output is a permutation and follows every rule), and
     `correctOrderingUnique` (so "the" right order is well defined). Nobody else proves
     uniqueness. From these, `part2Correct` gives the sum for *any* correct ordering function.
   - All of part 2 assumes `StrictTotalOrderOn` for every update. That assumption is checked by
     a run-time test on the real input, not proved.
   - The assumption is stronger than the puzzle needs. Where it fails but a unique answer still
     exists, our program gives a wrong answer, silently (point 4).
4. **Adversarial rule sets: the comparator sorts, ours included, fail on inputs that still have
   one right answer.** `adv5.py` tries every rule set on pages 1–4 against every update of 3 or
   4 pages, 196,608 cases in all (§3).
   - In class B there is exactly one valid order, but some pair of pages has no rule of its own.
     Our `sortWith` returns an order that breaks a rule in 3,264 of the 13,248 class B cases.
     Python's `cmp_to_key` does so in 8,928.
   - The smallest example: the rules `1|3` and `2|1`, with the update `3,2,1`. The only valid
     order is `2,1,3`, whose middle page is 1. Our program prints `Part 2: 3` **[checked: run
     on the file]**.
   - Topological sort (Kahn's algorithm, or depth-first search) and "swap the first broken pair
     until none is left" are right on every acyclic case. On a cycle, though, they raise an
     error, overflow the stack, or loop for ever, where the sorts quietly return something.
   - A widely argued megathread claim, that a sort "only needs the comparison … for items that
     are adjacent in the final list", is refuted by the same three-page case **[checked]**.
5. **Length is ordinary.** Our program is 37 code lines with its parser. The median of 440
   GitHub authors is 65. The shortest are John Tromp's Haskell (20) and Matt's own Lean (22 in
   `Solve.lean`, plus 42 for its types and parser) **[checked: `classify5.py`]**. Our spec (26)
   and proofs (184) are the longest by far, because nobody else wrote any.
6. **Speed: fine on the real input, the parser again at scale.** On the real input `run` takes
   0.36–0.40 s, `run --js` 0.37–0.39 s, and the native build 0.07 s, against CPython's 0.08 s.
   Parsing is most of every run. On 100 copies of the updates (0.9 MB), the best runs take
   12.5 s under `run`, 1.6 s in JS and 4.7 s natively, against CPython's 0.4 s. As on days 2 and
   3, native is slower than JS when `Std.Parse` dominates (§5; the timings are noisy).
7. **New: the kernel can prove the assumption for the real input.** `NOTES-2024.md` says this
   "evaluation in the kernel won't do in reasonable time". In fact the run-time test, stated as
   a theorem and proved by `rfl`, checks in 68 s wall clock (66 s CPU) with `--no-cache` on a
   loaded machine. Parsing the input by `rfl` alone takes 4.8 s of CPU, and a false version
   (`… = False` for the first update) is rejected **[checked: `scripts/sw/KernelCheck.sw`]**. Bridging that Boolean
   to `StrictTotalOrderOn` would make "6456 is the puzzle's answer for this input" a theorem
   with no assumption left (D1751).

**Verdict.** On proof, Stitchwort is clearly ahead. Nobody else proves part 2, nobody else
proves that the right order is unique, and the one other spec that matches the puzzle
(Hath995's Dafny) buys its guarantee by giving up termination. But our part 2 theorem rests on
the same assumption as the community's shortcut. What we add is that the assumption is
written down, its consequences are proved, and it is checked on the real input. The program
itself is the shortcut, and the proofs say exactly when it is right: on rule sets that only
order the pages transitively, it is as wrong as everyone else's sort. A topological sort would be
right on more inputs (§3). On length and speed, day 5 is unremarkable: as short as typical
Haskell or Lean, and as fast as CPython natively.

## 2. The solutions

### 2.1 GitHub

To spare the GitHub search limit, which is shared with the day 4 lane, I made no new
repository searches. `find5.py` took the 344 repositories of the day 3 note, the 598 of the
day 2 note and the 285 of the day 4 lane, dropped the Unison hits (bogus, as day 2 found), and
added `thierry-martinez/advent-of-code` by hand: 694 repositories. It reused the 340 trees
already saved and listed the rest with `gh api` (the core limit, not the search limit). It kept
the paths that look like day 5. `fetch5.py` fetched 584 files from raw.githubusercontent.com.
`classify5.py` kept the largest day 5 file per owner, among those that mention a `|` and
rules or updates: **440 authors**. Of those, 20 write Lean, 9 Roc, 3 Idris, and 1 each Agda,
Dafny and Koka. The rest write Clojure, Gleam, Haskell, Elixir, OCaml, F#, Scala, Racket, Elm,
PureScript and Common Lisp.

The regex tags (upper bounds, because a word can match in code that does something else)
**[checked: `classify.tsv`]**:

| Part 2 method | Authors (of 440) |
|---|---:|
| sort with a comparator (`sortBy`, `sortWith`, `mergeSort`, `qsort`, `Enum.sort/2`, …) | 232 |
| repeated swaps | 59 |
| topological sort | 30 |
| predecessor count as the sort key | 8 |
| mentions a cycle or transitivity, or checks for one | 17 |

The 17 that mention a cycle, read by hand:

- **Seven raise an error on a cycle inside an update.** Their topological sorts fail loudly
  (Asfaroth and akashkgarg in Clojure, jman2454 and dennismok2018pub in OCaml, pgeadas in F#,
  martinfalke in Elixir, WJWH in Haskell, whose message is `"cycle in graph (should never
  happen?)"`).
- **lukewilliamboswell's Roc returns a `CyclicRules` error** and tests for it:
  `expect order_update([1, 2], [{ before: 1, after: 2 }, { before: 2, after: 1 }]) ==
  Err(CyclicRules)`. Of everything I read, this is the most careful *program*.
- **rcklemm (OCaml) computes the transitive closure** (Floyd–Warshall) before sorting, and
  VeryCautious (F#) compares through chains of rules. Both are right on class B (§3), where
  plain comparators are not.
- **The rest only comment.** jhgarner (Lean): "I wrote this assuming the orderings were
  transitive but turns out they're not…". kevinwu1 (Scala): "the entirety of the rules contain
  cycles, but for a given list, there are no cycles".

The proof-language files, read by hand:

| Author | Language | Part 1 check | Part 2 method | What is proved |
|---|---|---|---|---|
| hath995 | Dafny | the spec, `InOrder` | swap broken pairs until `InOrder` (`decreases *`) | output is a permutation and in order, *if it ends* |
| shilangyu | Lean (Mathlib) | — | — | sublist of a `LinearOrder`'s list ⇒ ordered; the order assumption is false here, and the list is a `[]` stub |
| main-- | Lean | every rule against `dropWhile` | `mergeSort` with `r.contains (x, y) ∧ ¬r.contains (y, x)` | parsing gives non-empty lists; two `validateRule` examples |
| **mdr (Matt's)** | Lean | **neighbours only**: `slidingPairs ⊆ rules` | `mergeSort` with `p1 == p2 ∨ (p1, p2) ∈ rules` | `#guard` on the example |
| amesgen | Lean | all later pages | `RBSet.ofList xs cmp`, with `.eq` for "no rule" | nothing; an `RBSet` *drops* pages it thinks are equal |
| mfornet (marx38), dupuisf, adriandole, RussellEmerine | Lean | various | topological sort on the update | nothing |
| 12 other Lean | Lean | various | comparator sort (`qsort`, `mergeSort`), or swaps | `#eval` at most |
| BrianNormant | Idris 2 | | topological sort | nothing |
| AugustUnderground, PraneethJain | Idris 2 | | `sortBy` | nothing |
| aaronallen8455 | Agda | per-page lookups | `correct`, marked `{-# NON_TERMINATING #-}` | nothing |
| DeSevilla | Koka | | `sort` | nothing |
| 9 authors | Roc | | `sortWith`, swaps, or the Roc topological sort above | nothing |
| thierry-martinez | Python (not Coq for day 5) | rule positions | DFS topological sort on the update | — |

Three details matter:

- **Matt's Lean leans on the assumption twice.** Its part 1 accepts an update only if each
  *neighbouring* pair has a rule `a|b`. That is right when the order on the update is unique,
  but wrong when some pair has no rule (class C, §3). Its part 2 is the comparator sort. Our
  Stitchwort part 1 checks all pairs and is proved with no assumption **[checked: both
  files]**.
- **amesgen's `RBSet.ofList`** returns a *set*. Two pages with no rule between them compare
  `.eq`, and one of them disappears. On this input every pair has a rule, so nothing is lost
  **[checked: file; inferred: the input is a tournament]**.
- **John Tromp's Haskell** (20 lines, the shortest here) uses a two-valued comparator,
  `if (a,b) ∈ edges then LT else GT`, and checks neighbours only. That is the shortcut at its
  barest, and correct on this input **[checked: file; `adv5.py` "cmp_to_key, 2-way" gives
  6456]**.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

`arctic.py` made two requests: one for the posts around 5 December 2024 05:00 UTC, which found
post `1h71eyz`, and one for its comment tree. The post has 1,070 comments, 766 of them
top-level and 749 still live. 717 have a language tag: Python 183, Rust 70, C 50, Go 44,
JavaScript 43, Haskell 19. The proof languages are one Lean post (marx38) and one Dafny post
(Hath995), both covered above **[checked: `langs5.py`]**.

Method words in the 749 live comments (regex upper bounds): a comparator sort in 87, swap or
bubble in 78, topological sort in 51, a cycle in 27, transitivity in 10, total or partial order
in 9 **[checked: `words.txt`]**. Many posts only link to code, so these undercount.

What people said about the shortcut:

- **Relied on it knowingly.** IsatisCrucifer (C++): "Abusing the fact that the first portion of
  the input is giving us a total order", and so passed the rules to `std::is_sorted` and
  `std::sort` ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0hw3dd/)).
  ThunderChaser (Rust): "I just abuse the fact that the rules make a total ordering for a given
  update" ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0i4rr0/))
  **[cited]**.
- **Worried, but didn't check.** tcbrindle (C++): "did I just get lucky that this approach
  happened to work with my input?" ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0jpnoh/)).
  Othun (Julia): "Can someone convince me that my code is indeed correct ? Or did the authors
  make sur that the rules make a transitive `<` for each list ?" ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0k1xsz/)).
  Dullstar (D): "the input doesn't happen to contain anything that breaks the standard library
  sorts" ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0nxiba/))
  **[cited]**.
- **Checked it.** light_switchy (Dyalog APL) is the one poster who checks the assumption in
  code and says so. For each update the comments state that its graph "is its own transitive
  closure `(⊣≡∨.∧⍨∨⊢)¨gs` is all ones" and "is asymmetric and irreflexive", and conclude that
  "any sorting algorithm will work for individual subproblems"
  ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0nmxn1/))
  **[cited]**. That is our `StrictTotalOrderOn`, checked at run time, in about two lines of APL. Our
  test (`rulesOrderPages` in `Tests/Input.sw`) does the same in a few more.
- **Argued it from the wording, partly wrongly.** onrustigescheikundig (Clojure/Scheme) reads
  "very specific order" as "unique order". So each update's graph has a Hamiltonian path, and a
  neighbours-only part 1 check is enough. That part is right: in `adv5.py` the "neighbours have
  a rule a|b" check makes no mistake in class B. But the post goes on: "sorting algorithms
  generally only need the comparison operation to be well-specified for items that are
  adjacent in the final list". That is false. With `1|3` and `2|1`, the only order is `2,1,3`,
  whose neighbouring pairs both have rules, yet Python's `sorted` with that comparator returns
  `2,3,1` from the input `1,2,3`
  ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0o045w/))
  **[cited; checked: `adv5.py` first failures]**.
- **Tripped over the global cycle.** maitre_lld: "SPENT TWO HOURS trying to topologically sort
  ALL THE NUMBERS in my input BUT IT CAN'T BE DONE, there are cycles"
  ([comment](https://www.reddit.com/r/adventofcode/comments/1h71eyz/2024_day_5_solutions/m0lgeoc/)).
  marx38 (Lean): "you can't find a global topological sort, but … it needs to be found locally
  per update". Porges (Prolog): "I chose this because I thought you'd need to do inference on
  transitive relationships. But you don't!" **[cited]**.

## 3. The shortcuts on adversarial rule sets

`adv5.py` tries every relation on the pages {1, 2, 3, 4} (each of the 12 ordered pairs is a rule
or not: 4,096 rule sets) against every update that orders 3 or 4 of those pages (48 updates):
196,608 cases. Each case is classed by the rules restricted to the update's pages:

- **A**: a strict total order, our proofs' assumption (9,792 cases).
- **B**: acyclic with exactly one valid order, but some pair has no rule of its own (13,248).
  The puzzle still has one right answer.
- **C**: acyclic with several valid orders (28,392). In 27,240 of them the valid orders
  disagree on the middle page, so the puzzle's question has no single answer.
- **D**: a cycle, so no valid order exists (145,176).

`cross5.py` checks the script's copy of our `List.sortWith` (std's bottom-up merge sort, with
the program's test `!(precedes next page)`) against the real `stitchwort run` on 40 random
cases of classes B, C and D. There were no mismatches **[checked]**.

**Part 1: wrong verdicts** (judged against "no page comes after a page it must precede", all
pairs):

| Check | A | B | C | D |
|---|---:|---:|---:|---:|
| all pairs (ours, Thierry, most careful solutions) | 0 | 0 | 0 | 0 |
| neighbours only (`is_sorted` with the comparator; tromp) | 0 | 3,936 | 3,048 | 16,056 |
| each neighbour pair has a rule `a|b` (Matt's Lean) | 0 | 0 | 10,560 | 33,600 |
| sort, then compare with the original | 0 | 3,936 | 3,048 | 16,056 |

**Part 2: does it return a valid order?** (B: of 13,248; C: of 28,392)

| Method | A | B invalid | C invalid | D (no valid order exists) |
|---|---|---:|---:|---|
| **Stitchwort `sortWith` (ours)** | all valid | **3,264** | 1,800 | returns an order, silently |
| `cmp_to_key`, three-way comparator | all valid | 8,928 | 4,632 | returns, silently |
| `cmp_to_key`, two-way (`-1 if a|b else 1`) | all valid | 8,928 | 4,632 | returns, silently |
| sort by number of predecessors in the update | all valid | 7,104 | 1,632 | returns, silently |
| Kahn's topological sort on the update | all valid | 0 | 0 | raises an error |
| depth-first topological sort (Thierry's `day05.py`) | all valid | 0 | 0 | `RecursionError` |
| swap the first broken pair until none (Hath995's idea) | all valid | 0 | 0 | never ends (capped) |

On the real input, all eleven methods give 4569 and 6456, and all 197 updates are class A
**[checked: `adv5.out`]**.

What this says:

- **Our assumption is the strongest of the reasonable ones, and our program needs all of it.**
  The proofs are sound. Class B is simply outside `StrictTotalOrderOn`, so `part2Correct` says
  nothing there, and the program is in fact wrong on a quarter of those cases. The puzzle is
  well posed in class B, so a solver that handles it is strictly better.
  [`scripts/sw/Topo.sw`](aoc-2024-day05-community/scripts/sw/Topo.sw) is a 19-line
  topological version: repeatedly take a page that no remaining page must precede. It prints
  `Part 2: 1` on the three-page case and 6456 on the real input **[checked]**.
- **The swap loop is the cheapest correct program, and the hardest to make total.** It is right
  on A, B and C, and Dafny accepts it with `decreases *`. In Stitchwort it would need a proof
  that it terminates on acyclic input, which I did not attempt.
- **Under a cycle, every method is wrong one way or another.** The sorts give an answer that
  means nothing. The topological sorts fail. Our program sorts, so it would print a number.
  Only the test on the input would notice.
- **A proof of `Topo.sw` would need a weaker assumption and one new lemma.** The assumption:
  the rules are acyclic on each update (uniqueness, for the sum, needs class A or B). The
  lemma: a finite acyclic relation has a minimal element, so `firstPage` never fails on
  acyclic input. Std has `Nat.pigeonhole` (SW-729), which that lemma could build on. I estimate
  100–200 proof lines. This is **[inferred]**; I did not write it.

## 4. Length and readability

Code lines are non-blank and non-comment **[checked]**:

| Who | Language | Program | Spec | Proof |
|---|---|---:|---:|---:|
| tromp | Haskell | 20 | — | — |
| mniip | Lean | 24 | — | — |
| **mdr (Matt's)** | Lean | 24 solve + 42 types/parser | — | — |
| **Stitchwort** (`Day05.sw`) | | **37** (parser included) | **26** | **184** (`Proofs.sw` 66, `Part2.sw` 118) |
| median of 440 GitHub authors | mixed | 65 | — | — |
| hath995 | Dafny | 162 in all (spec is the program) | | partial correctness |
| shilangyu | Lean | no solver | | ~60, off target |

How the code reads:

- **Our program reads as well as any.** `inOrder` is three lines and says what it checks.
  `Update.reorder` is one line. The parser is four short functions, and it reports the line and
  column of bad input, which almost no community parser does **[inferred: most use `split` and
  `read`/`toNat!`/`int`]**.
- **Our test for "may come before" is subtle.** `page next => !(precedes next page)` is the
  right `le` for `sortWith`, but it took the comment above `mayPrecede` to explain it. A
  three-way comparator (`Less` if a rule says so, `Greater` if the reverse) via `List.sortBy` is
  what most people wrote, and it reads more directly. It is no more correct (§3: the same
  failures in B and C).
- **Our spec is the most literal in the community.** `printedBefore` and `followsRule` quote
  the puzzle's sentence, including the "if both pages are in the update" clause, which
  `followsRuleIsPrintedBefore` then proves adds nothing. Hath995's `RulesSatisfied` is as
  literal, but indexed. Nobody else has a spec.
- **The friction in our proofs was small and already logged.** The `||`-in-a-lambda
  elaboration mismatch has been fixed. The pair equality and `all`/`any` lemmas have moved to
  std. `updateExt` is still written by hand, because records have no eta (SW-55, SW-568,
  D1426/SW-789).

## 5. Speed

All times are wall-clock seconds from `bench5.py`: one warm-up, then the min–max of three runs.
They include process start-up. `x100` is the rules followed by the updates 100 times over
(19,700 updates, 0.9 MB) **[checked: `bench2.out`]**. Other lanes were running, so treat these
as rough. A first pass under a load average of 30 (`bench.out`) was up to twice as slow.

| Program | input | `run` | `run --js` | native |
|---|---|---:|---:|---:|
| `Hello` (read the input, print its length) | real | 0.14–0.15 | 0.23–0.24 | 0.00 |
| `ParseOnly` (the committed parser, no solving) | real | 0.27–0.28 | 0.36–0.38 | 0.05 |
| **`Day05.main`, the committed program** | real | **0.36–0.40** | **0.37–0.39** | **0.07** |
| `Topo.main` (part 2 only, topological) | real | 0.42–0.43 | 0.38–0.40 | 0.09 |
| `Hello` | x100 | 0.14–0.16 | 0.25 | 0.00–0.01 |
| `ParseOnly` | x100 | 5.0–11.4 | 3.1–4.0 | 2.3–3.7 |
| `Day05.main` | x100 | 12.5–29.5 | 1.6–6.0 | 4.7–9.8 |
| `Topo.main` | x100 | 17.9–18.2 | 1.9 | 6.5–7.6 |
| CPython, `ref5.py` (all-pairs check, `cmp_to_key`) | real | 0.08–0.09 | | |
| CPython, `ref5.py` | x100 | 0.41–0.51 | | |

What this says:

- **On the real input, solving costs a few hundredths of a second.** Parsing is 0.13 s of the
  0.38 s under `run` (over `Hello`), and 0.05 of the 0.07 s natively **[inferred: rows
  subtracted]**. Natively we are level with CPython.
- **At scale the parser dominates, as on days 2 and 3.** The x100 rows are the extremes of both passes. The load average reached 72 during the second pass, so they show orders of magnitude only. Two things hold in both passes. The native build is 2 to 4 times *slower* than JS here, as on days 2 and 3 (D1640, D1650). And `run` takes 12–14 s at best, which matches the 14.0 s that `NOTES-2024.md` measured on 28 October, so there is no sign of a regression since then **[checked: `bench.out`, `bench2.out`]**. CPython takes 0.4–0.5 s. I can't say why `ParseOnly` should be slower than the whole program under JS. It is probably noise, but that is **[unverified]**.
- **The topological version costs little more.** It does O(n²) lookups per placed page, against
  the merge sort's O(n log n), on updates of at most 23 pages.

## 6. Proofs: what we proved, what it cost

| | Stitchwort | hath995 (Dafny) | shilangyu (Lean) | main-- (Lean) | everyone else |
|---|---|---|---|---|---|
| Part 1 check is the puzzle's rule | **yes, no assumption** (`inOrderCorrect`) | spec is the program | — | no | no |
| Part 1 sum | **yes** (`part1Correct`) | no | no | no | no |
| Part 2 output is a permutation and follows every rule | **yes, under A** (`reorderCorrect`) | **yes, no assumption, if it ends** | vacuous | no | no |
| The right order is unique | **yes, under A** (`correctOrderingUnique`) | no | no | no | no |
| Part 2 sum | **yes, under A, for any correct ordering** (`part2Correct`) | no | no | no | no |
| The assumption holds on the real input | run-time test; **provable by `rfl` in ~68 s** (§1.7) | not needed | false | — | light_switchy's APL checks it at run time |
| Termination | yes (structural) | waived (`decreases *`) | — | — | Agda waived (`NON_TERMINATING`) |
| Cost | 26 spec + 184 proof lines; std's `sortWithSortedOn` and `pairwiseOfSortedOn` did the hard part | about 70 lines of lemmas and loop invariants (rough) | about 60 lines | about 40 live lines, on `splitOn` | — |

Two things kept our cost low:

- **Std's sort lemmas.** `List.sortWithSortedOn` and `List.pairwiseOfSortedOn` ask for totality
  and transitivity only *on the values being sorted*. That is exactly the per-update
  assumption, so `reorderCorrect` is mostly plumbing. Lean's `List.pairwise_mergeSort` asks for
  them on all values, and so would not apply directly to this input. `NOTES-2024.md` cites
  this, and I did not recheck it **[cited]**.
- **Uniqueness is short.** `orderUnique` is 25 lines, by induction on two permutations.

Where Dafny is better: its partial-correctness guarantee needs no assumption at all, and it
cost Hath995 no proof of the sort itself. The loop exits only once `InOrder` holds. Stitchwort,
being total, can't express "correct if it ends", so we pay for termination with a stronger
assumption, or (for `Topo.sw`) with a minimal-element lemma.

## 7. Candidate improvements, ranked by value over effort

| Rank | Candidate | Kind | Value | Effort | Evidence |
|---|---|---|---|---|---|
| 1 | **Correct the "won't do in reasonable time" line in `NOTES-2024.md`**, and add §3's two small cases as tests that `rulesOrderPages` *rejects* (`1|3, 2|1` / `3,2,1`, and `1|2, 2|1` / `1,2,3`), so the limit of the assumption is pinned with examples | aoc docs/tests | the record is accurate; the assumption's edge is concrete | trivial | §1.7, §3 |
| 2 | **Make the answer on the real input a theorem**: `everyUpdateOrdered` by `rfl`, plus a lemma that `rulesOrderPages … = True` implies `StrictTotalOrderOn`, giving `solvePart2 inputQueue = middlesOfReordered inputQueue ordering` for every correct `ordering`, with no assumption | proof | the first AoC day where the committed answer is proved to be the puzzle's, end to end (parser aside) | small to medium: the bridge lemma is 30–60 lines **[inferred]**; but 68 s of checking (D1751) | §1.7 |
| 3 | **Find where the kernel's 66 s goes**: `parsedSize` alone (parsing the 16 KB input by `rfl`) takes 4.8 s of CPU, the 197 updates the other ~60 s, on a heavily loaded machine | kernel / evaluator | every "decide it on the input" proof pays this; profile on a quiet machine first | small to measure | §1.7 |
| 4 | **Std: a minimal element of a finite acyclic relation, then `List.topoSortWith` with `Perm` and "follows every edge" lemmas** | library proof | `Topo.sw` provable under "acyclic on the update" (right on classes A–C); reusable for later AoC graph days | medium (100–200 lines) **[inferred]** | §3 |
| 5 | **Day 5's program switches to `Topo.sw`**, once 4 exists (D1750) | aoc | right on every well-posed input, not only on this one | small after 4 | §3 |
| 6 | Record eta, or generated `T.ext` (already SW-55, SW-568, SW-789) | kernel | removes `updateExt` | already tracked | §4 |
| — | A shorter part 2 via a three-way comparator and `List.sortBy` | program | reads slightly better; no more correct | trivial | §4 |

## 8. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D1750 | Day 5's program uses the comparator sort, which is proved under "a strict total order on each update", and is wrong on inputs where the order follows only by transitivity (§3). Should we aim for the topological version, proved under "acyclic on each update", which needs a minimal-element lemma in std (candidates 4 and 5)? | [yes, but not now: `backlog`, to do when a later AoC day (a graph or DAG puzzle) needs `topoSortWith` anyway; the real input is class A, so nothing is wrong today] |
| D1751 | The kernel proves the part 2 assumption for the real input by `rfl`, in ~68 s on a loaded machine (`--no-cache`). Commit the end-to-end theorem (candidate 2)? It would make day 5 the first day with its committed answer proved to be the puzzle's, at the cost of ~1 minute on every uncached check of the AoC project. | [yes, if candidate 3 or a quiet-machine timing brings it under ~20 s; otherwise keep it in this note's scratch file and leave the run-time test as it is] |

---

**Status** (29 October 2026): SW-893, this note, is done once reviewed. D1750 (topological
sort for day 5) and D1751 (proving the assumption on the input by `rfl`) are pending.
