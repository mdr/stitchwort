# AoC 2024 day 2: community solutions in other languages

**Date:** 29 October 2026. **Ticket:** SW-878. **Our version:** finished before this note:
`aoc/src/Aoc/Year2024/Day02/` (27 October), both parts proved for every list of reports. History
and friction are in `aoc/NOTES-2024.md` ("## Day 2"). The puzzle: each line is a report of
levels. A report is safe if the levels only rise or only fall, by one to three at each step.
Part 1 counts the safe reports. Part 2 also counts those that become safe when one level is
removed. The input `aoc/inputs/2024/day02.txt` has 1,000 reports of 5 to 8 levels. The answers
are 534 and 577.

The evidence labels are the same as in the day 9 note:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Where things are:

- **Scratch area:**
  `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/d2024-02/`.
  The fetched files are in `gh/files/`, the megathread JSON in `arctic/`, and the Stitchwort
  scratch project in `proj/`, which holds a copy of the day 2 sources.
- **Committed copies:** the scripts and Stitchwort scratch programs are in
  [aoc-2024-day02-community/scripts/](aoc-2024-day02-community/scripts/). The per-file tags are
  in [aoc-2024-day02-community/classify.tsv](aoc-2024-day02-community/classify.tsv).
- **Binary:** the main checkout's `target/release/stitchwort`, as it was on 29 October.
- **Timings:** wall-clock seconds from `scripts/bench2.py`: one warm-up, then the minimum and
  maximum of three runs. They include process start-up. Treat them as rough.

## 1. Summary

I took one day 2 solution from each of **427 GitHub authors** (`repos2.py`, `find2.py`,
`pick2.py`). 36 of them write in proof or dependently typed languages, or in the
smaller FP languages: 19 Lean 4, 10 Roc, 3 Idris 2, and one each in Agda, Coq/Rocq, Dafny and
Koka. The other 391 write in Haskell, OCaml, Clojure, Elixir, Scala, Gleam, F#, Racket,
PureScript and Elm. I read the proof-language files myself and tagged the rest by regex (§2.1).
I also read the r/adventofcode "2024 Day 2 Solutions" megathread through the Arctic Shift archive
(§2.2). It has 793 live top-level comments, 127 of them in functional or array languages, and one
each in Lean, Dafny and Coq. There was no F\*, Isabelle or Unison solution in either source.
GitHub's `--language Unison` filter returned unrelated repositories, so I dropped it.

Stitchwort compared with them:

1. **One other author proved as much as we did: Thierry Martinez, in Coq.** His
   [`day02.v`](https://github.com/thierry-martinez/advent-of-code/blob/main/2024/day02/day02.v)
   states the puzzle as Props (`safe`, and `quasisafe l := safe l ∨ ∃ l1 x l2, l1 ++ [x] ++ l2 =
   l ∧ safe (l1 ++ l2)`). He proves his Boolean brute force equivalent to them (`is_safe_iff_safe`,
   `is_quasisafe_iff_quasisafe`), with no `Admitted` or `Axiom`. The file is 336 lines, 233 of them code:
   about 63 of definitions and 170 of proof in 13 lemmas. Our proof of the same claims, plus
   the counts and `part2AtLeastPart1`, is 50 code lines, and `cases` does most of the work
   **[checked: both files]**. His spec is the clearer of the two (§4). Nobody else proves
   anything that says what the answer is:
   - Hath995's Dafny states `ensures exists ds: set<seq<int>> :: (forall d :: d in ds ==>
     SafeReport(d)) && |ds| == x`. That is true of `x = 0`, so it doesn't pin the count. His loop
     invariants are stronger, but the postcondition is what callers get.
   - shilangyu's Lean proves `is_safe_induct` and a `safe_bounds` theorem about how far the last
     level can be from the first. Neither concerns the answer.
   - The other Lean files have `#eval` or `#guard` on the example. None has a `theorem`
     **[checked: read every proof-language file; `grep` for theorem, lemma, ensures, Qed, sorry]**.
2. **Nearly everyone uses brute force for part 2, as we do.** They try the report with each level
   removed in turn. Lean has `List.eraseIdx` for this, Haskell `zipWith (++) (inits xs) (tail
   (tails xs))`, and Scala `patch`. In the megathread, 158 comments use brute-force words and 39
   use linear-time words **[checked: `langs2.py`; regex upper bounds]**. Reports have at most 8
   levels, so brute force costs nothing.
3. **The linear part 2 is where the bugs are, and nobody proves it, until §3.** Several people
   tried a one-pass check and gave up or got it wrong. mnkyman says "there are a lot of special
   cases with this approach", and Dullstar's faster version "proved to be a little unreliable when
   values near the front need to be removed" **[cited: megathread]**. I tested six linear methods
   against brute force on every report of 1 to 6 levels drawn from 1 to 8 (`methods2.py`).
   - Two common shortcuts are wrong. "Retry without either level of the first bad step" misses
     reports fixed by removing the first level, and gives 575 on our input instead of 577. "Skip
     the later level once" gives 568.
   - The careful ones pass: bcs-aoc's Haskell and crvdgc's Lean.
   - So far as I found, nobody proved a linear method. **I proved one in Stitchwort for this
     note:** `scripts/sw/LinearProved.sw`. The program is 16 lines and the proof is about 60, and
     it uses no axioms. It took three `check` runs (§3) **[checked]**.
4. **Length: about the same as Lean and Haskell, and longer than the shortest.** Our program is 20
   code lines, parser included. The shortest in our languages are Haskell one-liners. Vacuoso's
   two `part` lines are 208 and 266 characters long. James-Oswald's Lean and main--'s Lean are 14 code
   lines each, and amesgen's Lean is 31. The median of the 427 GitHub files is 42 code lines
   **[checked: `classify2.py` counts non-blank, non-comment lines]**. APL and Uiua do both parts
   in 3 or 4 lines **[cited]**.
5. **Speed: the parser is the problem, not the puzzle.** Under `run` the program takes 0.42 s.
   Start-up is 0.15 s and parsing with `Std.Parse` is about 0.25 s, which leaves a few
   hundredths for both parts. Splitting into lines and words instead takes the run to 0.30 s.
   With 100 copies of the input (100,000 lines), the `Std.Parse` parse takes 9.1 s under
   `run`, 4.6 s native and 1.9 s under `--js`. Splitting takes 1.3 s, 0.30 s and 0.85 s. CPython
   does both parts on that file in 0.38 s **[checked: §5]**. The native build is *slower* than
   JS on the `Std.Parse` parser, and `NOTES-2024.md` timed 100,000 lines at 2.0 s on 27 October.
   That suggests a regression since then **[inferred]** (D1640).

The verdict: on proof, Stitchwort comes out ahead for the effort. It matches the one complete
proof in the community (Coq) in under a third of the lines, and it proved the linear method,
which nobody else did, in about twenty minutes of scratch work. On length it is ordinary. On speed, day 2
shows a real defect: `Std.Parse` costs 10 to 20 times what splitting costs, and more natively
than in JS.

## 2. The solutions

### 2.1 GitHub

`repos2.py` ran `gh search repos` for four phrasings of "advent of code 2024" in 21 languages.
That found 672 repositories pushed since 1 December 2024. Dropping the bogus Unison hits leaves
598. `find2.py` listed each tree and kept day 2 paths, and `pick2.py` kept one file per owner
in the repository's language: 505 files. 427 of them look like day 2 (they mention safe, level,
report or dampen), and those are the sample. `classify2.py` tags each file. 321 of the 427 match
a removal idiom (`eraseIdx`, `removeAt`, `inits`/`tails`, `take … ++ drop`, `patch`, an
index filter, and so on). That is an upper bound, because some of the words are common
**[checked: classify.tsv]**.

The proof-language files, read by hand:

| Author | Language | Part 2 method | What is proved |
|---|---|---|---|
| thierry-martinez | Coq | brute (`find_sublist_rec`, with an accumulator) | both checks ⇔ the Prop spec, per report |
| hath995 | Dafny | the spec run directly (`exists i :: … ss[0..i] + ss[i+1..]`) | a count postcondition that `x = 0` satisfies |
| shilangyu | Lean | (no solver in the file) | `is_safe_induct`, `safe_bounds`; nothing about the answer |
| crvdgc | Lean | **linear**, a `while` loop over the differences | nothing; correct by `methods2.py` |
| jsr-p | Lean | removes the first bad difference's level | nothing |
| amesgen | Lean | `withoutOne` recursion (`as :: ((a :: ·) <$> withoutOne as)`); part 2 skips the `isSafe ∨` | `#guard` on the example |
| 15 other Lean | Lean | brute where I could tell: `eraseIdx` over `List.range`, `take ++ drop`, `dropSlice`, `enum.filter` | `#eval` at most |
| BrianNormant, AugustUnderground, BenBean18 | Idris 2 | brute (`take ++ drop`, `deleteAt'`) | nothing |
| aaronallen8455 | Agda | brute (`inits`/`tails`) | nothing |
| DeSevilla | Koka | skip-once recursion (`safe-dir-skipping`) | nothing; not tested here |
| 10 authors | Roc | brute | nothing |

Two details matter for the comparison:

- amesgen's part 2 is `count (withoutOne · |>.any isSafe)`, with no "or safe as it is". That
  is right only because removing the first level of a safe report leaves it safe. Our
  `dampenerAloneSuffices` proves that fact. amesgen relies on it silently **[checked: file]**.
- Hath995's Dafny is the cheapest "verified" style. The predicates are the spec, Dafny compiles
  the bounded `exists`, and so there is nothing to prove. But the one `ensures` is too weak to
  mean anything **[checked: file; inferred: `x = 0` satisfies it]**.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

`arctic.py` made two requests: a post search for the 2 December 2024 05:00 UTC window, then the
comment tree of post `1h4ncyr`. The post has 1,259 comments, 816 of them top-level, and 793 of
those still live. 738 have a language tag. Python leads with 170, then Rust 77, C 59, Go 40 and
Haskell 34 **[checked: `langs2.py`]**. The proof languages:

- **Lean:** marx38 ([mfornet/advent-of-code-2024](https://github.com/mfornet/advent-of-code-2024/blob/main/Aoc2024/Day02.lean)): "Today's solution was annoying (and unnecessary) to implement in O(n), but I guess it is possible if one precomputes the validity of each prefix and suffix. The solution presented here is O(n^2)" **[cited]**.
- **Dafny:** Hath995, the file above, posted inline **[cited]**.
- **Coq/Rocq:** ThierryMartinez, a link to the file above **[cited]**.

What the functional posters chose, in their own words:

- mstksg (Haskell): `possibilities = xs : zipWith (++) (inits xs) (tail (tails xs))`.
- NeilNjae (Haskell): "mainly writing down the problem as a few predicates".
- WhiteSparrow (Prolog): `append([Prefix, [_], Sufix], Ls)`, "Clear and concise, no debugging
  required!".
- bcs-aoc (Haskell): a linear `go` over differences marked `Safe` and `Unsafe`, "just so I could
  write this monstrosity of a function".

On linear time, people mostly said why they didn't bother. JWinslow23: "the version with
brute-forcing was much simpler to write and runs in milliseconds anyway". heyitsmattwade: "Seems
like there are too many edge cases" **[cited]**.

## 3. The linear method, tested and proved

For one direction (say rising), let the first bad step be between levels *i* and *i*+1.
Removing any level other than those two leaves that step in place, so only two removals need
trying. Doing that for both directions is linear. The usual mistake is to fix the direction from
the first step and then try the removals. If the first level is the bad one, the direction is
then wrong (`[1, 3, 2, 1]`).

`methods2.py` checks each method against brute force on all 299,592 reports of 1 to 6 levels
drawn from 1 to 8, and on our input **[checked]**:

| Method | Wrong on (of 299,592) | First failure | Our input (577) |
|---|---:|---|---:|
| per direction, drop either level of the first bad step (ours, `Linear.sw`) | 0 | — | 577 |
| direction from the first step, then drop either level of the first bad step | 670 | `[1, 3, 2, 1]` | 575 |
| the same, also dropping the level before | 0 | — | 577 |
| skip the later level of a bad step, once | 2,110 | `[1, 5, 6]` | 568 |
| at most one bad step | 10,172 | `[1, 6, 2]` | 580 |
| bcs-aoc's Haskell `go` over differences | 0 | — | 577 |
| crvdgc's Lean `isSafeRelaxed` | 0 | — | 577 |

Exhaustive testing to length 6 isn't a proof. `scripts/sw/LinearProved.sw` is one, written
for this note. It is index-free, as the Haskell and amesgen versions are:

```stitchwort
def tolerates (ok: Nat → Nat → Bool) (before: Nat) (level: Nat): List Nat → Bool
  | Nil => True
  | Cons next rest =>
    if ok level next then tolerates ok level next rest
    else (Cons level rest).chain ok || (ok before next && (Cons next rest).chain ok)
```

`toleratesOne` handles the first step the same way, with no `before`. The proof introduces the
brute force without indices, `anyRemoved holds (Cons x xs) = holds xs || anyRemoved (ys =>
holds (Cons x ys)) xs`. It shows `anyRemoved` equals the spec's `List.range … |> .any (… removeAt
…)` (`anyRemovedRange`), proves `toleratesCorrect` and `toleratesOneCorrect` by induction, and
ends with `isSafeLinearCorrect: report.isSafeLinear = safeWithDampener report` and
`part2LinearCorrect` against the committed spec. `stitchwort axioms` reports none for either.
`check --no-cache` takes 0.85 s **[checked]**.

It took three `check` runs, and two kinds of friction:

- **`rewrite` matches on the computed form.** My first congruence lemmas named
  `List.chain (Cons before (Cons level ys)) ok`, but the goal held its unfolded form, `ok before
  level && …`. The error printed the computed goal, and I copied that form into the lemma
  **[checked]**.
- **`match step: ok level next with | True` doesn't reach inside lambdas.** The goal still had
  `anyRemoved (ys => ok level next && …) rest` with `step: ok level next = True` in scope, and
  `cases` couldn't close it. An explicit `anyRemovedCong … (ys => rewrite step in rfl)` did. In
  the `False` branch, the lambda in the goal *was* refined (`ys => ok before level && False`).
  Why it is refined in one branch and not the other is **[unverified]**.

In Lean the same proof would be about as long. `simp` would do the congruences that I wrote by
hand, but nobody did it, so this is **[unverified]**.

Since SW-881 the linear check is the main program (`passesDampened` in `Day02.sw`), proved
against a `removals` spec in `Day02/Proofs/Dampener.sw`.

## 4. Length and readability, side by side

Code lines are non-blank and non-comment **[checked]**:

| Who | Language | Program | Proof |
|---|---|---:|---:|
| Vacuoso | Haskell | 2 (very long) lines plus types | — |
| James-Oswald, main-- | Lean | 14 | — |
| aaronallen8455 | Agda | 25 | — |
| amesgen | Lean | 31 | — |
| **Stitchwort** (`Day02.sw`) | | **20** | **50** (Spec 13) |
| **Stitchwort, linear** (`LinearProved.sw`) | | **16** | **~60** |
| hath995 | Dafny | 74 (spec is program) | weak `ensures` |
| thierry-martinez | Coq | ~63 (spec and program, no parser) | ~170 |

How the code reads:

- **The program reads well.** `report.levels.chain risesGently || report.levels.chain (level
  next => risesGently next level)` is as direct as the Haskell `zipWith`/`all` versions, and the
  parser is two lines (`Parse.eachLine`, `many1 (() => token nat)`). It reports the line and
  column of bad input, and only a few community parsers do that **[inferred: most use `read`,
  `toNat!` or `String.to_integer`]**.
- **Haskell's removal idiom is better than ours.** `zipWith (++) (inits xs) (tail (tails xs))`
  and amesgen's `withoutOne` need no indices. Our `List.range report.levels.length |> .map (index
  => { levels = report.levels.removeAt index })` is longer, and its proofs need
  `anyRemovedRange`-style lemmas.
- **Coq's spec is the most obviously right.** `∃ l1 x l2, l1 ++ [x] ++ l2 = l ∧ safe (l1 ++
  l2)` is the puzzle's sentence. Our spec's `removeAt index` asks the reader to trust
  `List.removeAt`. That is a small recursive definition with a test, but it is still one step
  further from the text.

## 5. Speed

All runs are from the scratch project, wall-clock seconds, min–max of three after a warm-up
**[checked: `bench2.py`, `brute2.py`]**. `x100` is the input 100 times over (100,000 reports).
`long400` is 75 reports of about 400 levels (`gen2.py`), where brute force is quadratic.

| Program | input | `run` | `run --js` | native |
|---|---|---:|---:|---:|
| `Hello` (read the input, print its length) | real | 0.15–0.17 | 0.26–0.27 | 0.01 |
| `Std.Parse` parse only | real | 0.39–0.40 | 0.43 | 0.05 |
| split into lines and words, parse only (`Split.sw`) | real | 0.30–0.32 | 0.42–0.45 | 0.01 |
| **`Day02.main`, the committed program** | real | **0.40–0.41** | **0.49–0.51** | **0.06** |
| `Split.main` (both parts, split parser) | real | 0.30–0.33 | 0.42–0.43 | 0.01 |
| `Std.Parse` parse only | x100 | 9.08–9.17 | 1.86–1.88 | 4.59–4.62 |
| split parse only | x100 | 1.27–1.28 | 0.84–0.87 | 0.30 |
| `Day02.main` | x100 | 9.63–10.01 | 1.85–1.91 | 4.76–4.99 |
| `Split.main` | x100 | 1.73–1.76 | 0.88–0.94 | 0.43 |
| part 2 brute force, `Std.Parse` | long400 | 1.27–1.31 | 0.56–0.57 | 0.38 |
| part 2 linear (`Linear.main`), `Std.Parse` | long400 | 0.69–0.71 | 0.47 | 0.20–0.21 |
| CPython brute force, both parts | real | 0.02 | | |
| CPython brute force, both parts | x100 | 0.38 | | |

What this says:

- **Part 2's method doesn't matter on real input.** Brute force and linear are within noise on
  the real input and on x100. Only reports of hundreds of levels separate them: on long400, brute
  force costs about 0.18 s natively over the parse and linear about 0.01 s **[inferred: totals
  minus the parse-only row]**.
- **`Std.Parse` dominates every run.** On x100 it is 7 times slower than splitting under `run`,
  and 15 times slower natively. Natively it is 2.5 times *slower than JS*. On every other
  workload in this note, and on day 9, native is the fastest. The parser runs as an effect
  handler (`{Parse}`), and SW-593 records that native effects spend 49% of their time
  allocating and freeing. So the effect runtime is the likely cause **[inferred]**.
- **Possibly a regression.** `NOTES-2024.md` (27 October, commit `eef373f3`) timed 100,000
  lines at 2.0 s under `run`. Today the same program takes 9.6–10.0 s. On 28 October, `2b541087`
  ("Std.Parse: constant memory per operation") changed `runFrom`'s clauses to resume in tail
  position, and SW-738 is the follow-up. I didn't build an older compiler to bisect, so the
  regression is **[unverified]**.
- **Against the community, we are slow only through start-up and the parser.** With the split
  parser, the native executable does x100 in 0.43 s, about CPython's 0.38 s. The committed
  program takes 4.8 s natively and 9.6 s under `run`. No community post reports a time worth
  comparing: everyone's brute force "runs in milliseconds" **[cited: JWinslow23]**.

## 6. Proofs: what we proved, what it cost

| | Stitchwort | thierry-martinez (Coq) | hath995 (Dafny) | shilangyu (Lean) | everyone else |
|---|---|---|---|---|---|
| Part 1 check is the puzzle's rule | **yes** (`isSafeCorrect`) | yes (`is_safe_iff_safe`) | spec is the program | no | no |
| Part 2 check is the puzzle's rule | **yes** (`isSafeWithDampenerCorrect`) | yes (`is_quasisafe_iff_quasisafe`) | spec is the program | no | no |
| The counts | **yes** (`part1Correct`, `part2Correct`) | no (per report) | weak `ensures` | no | no |
| Safe ⇒ dampener finds it | **yes** (`dampenerAloneSuffices`) | inside `is_quasisafe_iff_quasisafe` | — | — | amesgen relies on it |
| Linear part 2 | **yes**, scratch (`part2LinearCorrect`) | — | — | — | crvdgc, bcs-aoc: correct by test, not proof |
| Cost | 50 proof lines; `cases` closes the Boolean steps | ~170 lines of tactics | 0 | ~50 lines, off-target | — |

Our cost was low for two reasons: `cases` closes Boolean and arithmetic goals, `absDiff`
included, and std gained `List.chain` with its lemmas during day 2 (`NOTES-2024.md` item 7).
Day 2 is a fair test of "proves more with less effort", and Stitchwort passes it. The one
complete rival's proof is more than three times longer, and on this kind of goal Coq's `destruct`/`apply
andb_true_iff` style is plainly more work than `cases` **[inferred: from the two files]**.

## 7. Candidate improvements, ranked by value over effort

| Rank | Candidate | Kind | Value | Effort | Evidence |
|---|---|---|---|---|---|
| 1 | **Find why `Std.Parse` is slow, and slower natively than in JS.** First rerun the 27 October build on x100 to confirm or rule out a regression since `2b541087` (D1640). | runtime / std | 60–95% of day 2's run time; every AoC day parses with it | small to diagnose; the fix unknown (SW-593, SW-738) | §5 |
| 2 | **Commit the proved linear check** as a day 2 alternative (`Day02/Linear/`), with `methods2.py`'s counterexamples as tests (`[1, 3, 2, 1]`) (D1641) | aoc | the one thing here nobody else has; a worked example of proving an optimisation against a spec | small: the file exists and checks | §3 |
| 3 | **Std `List.removals` (or `withoutOne`)**, each list with one element removed, built recursively, with `anyRemovedRange`, `anyRemovedCong` and `anyRemovedOr` beside it | library | day 2's program and spec lose the index plumbing; the proofs get the index-free form for free | small | §3, §4 |
| 4 | **Let `match h: e with` refine `e` inside lambdas in the goal** (or say in the `cases` failure note that the atom sits under a binder) | elaborator | removes hand-written congruence instances like `anyRemovedCong … (ys => rewrite step in rfl)` | medium; needs the congruence machinery `rewrite` already has | §3 |
| 5 | **Optionally restate the part 2 spec as `∃ before level after`** (Coq's form), proved equal to the `removeAt` one | spec | the spec reads as the puzzle's sentence | small | §4 |
| — | Faster brute force, or the linear method in the committed program | program | none on real input (§5) | — | §5 |

## 8. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D1640 | `Std.Parse` takes 9.1 s under `run` and 4.6 s natively to parse 100,000 day 2 lines, where splitting takes 1.3 s and 0.30 s. `NOTES-2024.md` had 2.0 s for the whole run on 27 October, before `2b541087` changed `runFrom`. Open a ticket to bisect and fix, ahead of SW-813's general interpreter work? | [yes, `next`: confirm the regression with the 27 October build first; if confirmed, it is a fix, not tuning] |
| D1641 | Commit `LinearProved.sw` into `aoc/src/Aoc/Year2024/Day02/` as a proved alternative, keeping brute force as the program? | [yes, as an alternative; brute force stays the program, since it is shorter and no slower on the real input] |

---

**Status** (29 October 2026): SW-878, this note, is done once reviewed. D1640 and D1641 are
pending.
