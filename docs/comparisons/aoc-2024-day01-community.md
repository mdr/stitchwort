# AoC 2024 day 1: community solutions in other languages

**Date:** 29 October 2026. **Ticket:** SW-877. **Our version:** `aoc/src/Aoc/Year2024/Day01/`,
finished before this note (friction notes in `aoc/NOTES-2024.md`, "## Day 1"). Day 1 is the
easiest puzzle of the year. Each line of the input holds two location ids. Part 1 sorts both
columns, pairs them up and adds up the distances; part 2 adds up each left id times how often it
appears in the right list. The input is `aoc/inputs/2024/day01.txt`: 1,000 lines of five-digit
ids. The answers are 2,066,446 and 24,931,009.

This note follows the day 9 note (`aoc-day09-community.md`) and uses its labels:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page or file;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Where things are:

- **Scratch area:**
  `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/y24d1/`.
  The fetched files are in `gh/files/`, the megathread JSON in `arctic/`, the per-file table in
  `classify.tsv`, and the Stitchwort scratch project in `proj/`.
- **Committed copies:** the scripts and scratch programs are in
  [aoc-2024-day01-community/scripts/](aoc-2024-day01-community/scripts/).
- **Binary:** the main checkout's `target/release/stitchwort` (built 29 October, 08:40; `main` is
  at `1e5817d1`).
- **Timings:** wall-clock seconds from `scripts/rb.py`: one warm-up run, then three to five timed
  runs. They include process start-up, and other lanes were using the machine at the same time,
  so treat them as rough, to a factor of about 1.5.

## 1. Summary

I read day 1 solutions from **50 GitHub authors** in proof and dependently typed languages, plus
Roc and Koka: 27 in Lean 4, 13 in Roc, 4 in Idris 2, 2 in Agda, 2 in Coq/Rocq, and one each in
Dafny and Koka. I also read the r/adventofcode megathread through the Arctic Shift archive (§2):
802 top-level comments, 113 of them in functional, proof or array languages, 58 with code inline.
And I read 31 functional files linked from it. There was no F\*, Isabelle or Unison solution in
either source.

Stitchwort compared with them:

1. **Only one other author proved what we proved, and it took about five times the proof text.**
   Thierry Martinez's Coq file ([day01.v][tm]) has the same shape as ours. Part 1's spec is "the
   sum of distances between sorted permutations of the two lists". Part 2's spec counts
   occurrences. Both parts are proved for every input, with no `Admitted`. His proofs are 123
   lines, with four helper lemmas. Ours are 25 code lines, because std now has the lemmas
   (`sortEqOfPerm`, `sortOfSortedNat`, `countPerm`, `sumByPerm`, `getOrCounts`). Day 1's friction
   items 2, 3 and 6 added them. His part 1 theorem is weaker than ours, and his part 2 proves less:
   - Part 1: his theorem says the answer is the distance for *some* sorted permutations. Ours
     holds for *every* way of lining the lists up.
   - Part 2: he proves the quadratic `count_occ` version. We prove the count-map version, which
     is the one we run.
   - His file has no parser and no `main`. It came 12 days after the puzzle, and the answer was
     computed by a separate `day01.py` beside it **[checked: the repository tree]**.

   Among the other 49 authors:
   - natewhite345's Lean proves part 1's order-independence (`order_agnostic_arg_1`/`_2`, as our
     `part1AnyOrder`), commutativity, and that a list against itself gives 0. It had to prove
     `perm_unique_sort` along the way, as we did before std had `sortEqOfPerm`. It has no part 2.
   - shilangyu proves two side lemmas (two definitions of distance agree; `count` is the length
     of a filter).
   - Hath995's Dafny proves `|left| == |right|` after parsing, but only because of an
     `assume {:axiom}`.
   - Nobody else has a theorem. The rest test, if at all, with `#guard`, `example … := rfl` or
     Roc `expect` on the example **[checked: read the files; `scripts/classify.py`]**.
2. **Length: about average for the languages, not the shortest.** Our program is 22 code lines.
   That counts the record type, a parser that names the bad line and column, both parts and
   `main`. The Lean files have a median of 29 lines (12 to 56). The shortest Haskell and Scala
   solutions are 7 to 12 lines. BQN does it in 4. The difference is mostly parsing and error
   handling: most community code splits on white space and either crashes on bad input or
   silently drops it (§3) **[checked]**. The solving code is the same size everywhere. Ours is
   five lines, and Scala's `lefts.sorted.zip(rights.sorted).map(t => (t._1 - t._2).abs).sum` is
   no shorter.
3. **Readability: as good as the best of them.** `lists.left.sort |> .zipWith lists.right.sort
   Nat.absDiff |> .sum` and `Map.counts` with `getOr` read as plainly as the Haskell or Lean
   versions. They don't need Haskell's `M.fromListWith (+) (map (,1) ys)` idiom, or the
   hand-rolled `foldl` into a `HashMap` that the Lean and Roc files write. Two languages read
   closer to the puzzle text than we do: Dafny with `multiset(right)[val]` and Haskell with
   NeilNjae's `MS.occur` **[checked]**.
4. **Speed: fine on the real input, slow on large ones.**
   - Real input: the native executable takes **0.02 s**, against 0.015 s for a CPython script.
     `run` takes **0.65 s**, and 0.4 s of that is loading the imports before any work is done.
   - 100,000 lines: native takes **1.2 s**, against CPython's 0.04 s. About 1.0 s of it is
     `Std.Parse` (§4).
   - Nobody in the community reported a time that mattered for this day **[checked; cited:
     Roc's "<1ms"]**.
5. **Bad input: we are the only ones who name the line and column.** Of the 55 files in proof
   languages, Roc and Koka:
   - 18 crash with `!`, `unwrap` or `crash`;
   - 7 silently drop malformed lines (`filterMap`, `mapMaybe`, `getD`);
   - 16 return an `Except` or `Result`; two of those name the bad line's text, and none gives a
     position.

   **[checked: `classify.py`'s regexes, then `grep` for "line"; rough]**. This costs us about
   five lines.

Overall verdict: on day 1, Stitchwort does what the best of the community does, in about the
same space. It adds two things nobody else has together: proofs for every input of the program
we actually run, and parse errors that point at the input. The proofs are short only because std
grew the permutation lemmas for this day. Without them, ours would look like the Coq file. Where
we lose is speed on large inputs and the fixed start-up cost of `run`, and neither matters at
1,000 lines.

[tm]: https://github.com/thierry-martinez/advent-of-code/blob/main/2024/day01/day01.v

## 2. The sources

**GitHub.** `scripts/repos.py` ran `gh search repos` for four spellings of "advent of code 2024"
in each language. `scripts/links.py` took links from the megathread. `scripts/find.py` listed each
repository's tree and picked the day 1 file(s), and `scripts/fetch.py` saved them. The language
filter is ignored for Unison, which returned 136 unrelated repositories, so I dropped it. The
Coq, Koka and Isabelle searches hit GitHub's search rate limit and were re-run. Isabelle and
F\* returned nothing **[checked]**. A `KeenS/aoc2024` hit was a false match on `Day10_1.lean`. I
kept one entry per author (`curenosm` and `mdr` split day 1 across three files). `mdr/aoc-2024`
is Matt's own Lean 4 repository, from December 2024 **[checked: GitHub user `mdr` is Matt Russell, the owner of this repository's origin]**.

**The megathread.** `scripts/arctic.py` made two requests to Arctic Shift: the post search for
1 December 2024 05:00 UTC, then the comment tree of post `1h3vp6n` ("-❄️- 2024 Day 1
Solutions -❄️-"). The tree has 1,264 comments, 802 of them top level, and 775 still live.
`scripts/langs.py` counted language tags: 139 Python, 81 Rust, 21 Haskell, 17 Elixir, 8 Scala,
7 OCaml, 6 F#, 6 Clojure, 3 Dafny posts (all Hath995), 2 Lean, 2 Roc, 1 Coq/Rocq. Keyword
counts over live comments are upper bounds:
- "sort": 296;
- a Counter or frequency map: 128;
- counting per left id: 67;
- binary search: 3;
- radix or counting sort: 4.

Five comments mention proofs or verification, and none of them contains a proof (Hath995's
Dafny has `ensures` on the parser) **[checked]**.

Interesting points from the proof languages:

- **Pasting the input into the source.** bowtochris (Coq, 2,044 lines) and markrd-williams (Agda)
  paste the 1,000 pairs as length-indexed vectors and evaluate in the kernel (`Compute`). main--
  (Lean) pastes the input as a string literal. bowtochris's part 1 takes the minimum out of each
  vector repeatedly. That is the puzzle's wording taken literally, and the "remove-the-minimum
  spec" our notes chose not to write **[checked]**.
- **Totality costs where the library is thin.** markrd-williams's Agda defines its own `ℕ`,
  `List` and a bounded vector with a `raise` constructor so that quicksort passes the termination
  checker. DeSevilla's Koka writes its own quicksort with `pretend-decreasing` **[checked]**. We
  needed nothing like this, because `List.sort` and its lemmas are in std.
- **Equal lengths in the type.** natewhite345's `min_total_pairing_distance` takes
  `a.length = b.length` as an argument with default `by rfl`. Most others, like us, let `zip`
  drop the extra elements. We test that case ("lists of different lengths pair the shorter")
  **[checked]**.
- **Part 2's method.** Of the 55 files, about 27 count per left id (quadratic), about 18 build a
  map or multiset, and one (aaronallen8455's Agda) walks the two sorted lists together
  **[checked: regex, rough]**. At 1,000 lines the quadratic version is fast enough. Our spec is
  the quadratic one, and our program uses the map.

## 3. Side by side

Ours (`Day01.sw`, 22 code lines in all; the solving part):

```stitchwort
def solvePart1 (lists: LocationLists): Nat :=
  lists.left.sort
    |> .zipWith lists.right.sort Nat.absDiff
    |> .sum

def solvePart2 (lists: LocationLists): Nat :=
  let rightCounts := Map.counts lists.right
  lists.left.sumBy (id => id * rightCounts.getOr id 0)
```

amesgen's Lean, one of the tidiest of the 27 (23 lines with its test) **[cited]**:

```lean
let part1 := as.sort.zip bs.sort
  |>.map (fun (a, b) ↦ if a >= b then a - b else b - a)
  |> List.sum
let mults : RBMap ℕ ℕ := bs.map (·, 1) |> (RBMap.ofListWith · (·+·) _)
let part2 := as.map (fun a ↦ a * mults.findD a 0) |> List.sum
```

Hath995's Dafny part 2, the closest to the puzzle's words **[cited]**:

```dafny
var rightms := multiset(right);
return FoldLeft((sum, val) => sum + val, 0, Map((val:int) => val * rightms[val], left));
```

Thierry Martinez's Coq part 1 spec, which matches our `LinedUp` almost exactly **[cited]**:

```coq
Definition part1_spec (input: Input) (n: nat): Prop :=
  exists l1 l2 sorted1 sorted2,
  combine l1 l2 = input /\ Permutation l1 sorted1 /\ Permutation l2 sorted2 /\
  Sorted le sorted1 /\ Sorted le sorted2 /\
  n = list_sum (map (fun '(a, b) => distance a b) (combine sorted1 sorted2)).
```

Our spec and theorem (`Spec.sw`, `Proofs.sw`):

```stitchwort
type LinedUp (ids: List Nat) (inOrder: List Nat): Prop = {
  increasing: List.Sorted Nat.leq inOrder,
  sameIds: List.Perm inOrder ids
}

theorem part1Correct (lists: LocationLists) (leftInOrder: List Nat) (rightInOrder: List Nat)
    (leftLinedUp: LinedUp lists.left leftInOrder) (rightLinedUp: LinedUp lists.right rightInOrder):
    solvePart1 lists = totalDistance leftInOrder rightInOrder
```

Two differences matter:

- **Universal against existential.** Ours quantifies over every lining up. His theorem says one
  exists, and it doesn't show that the answer is unique.
- **What part 2 counts.** His part 2 spec defines "number of occurrences" by a minimal-length
  list of indices, which is far from the implementation. His `count_occ_spec` takes about 60 lines
  to connect the two. Our spec says `lists.right.count (== id)`, and std's `Map.getOrCounts`
  connects it to the map in one rewrite.

His spec is more independent of the library, and ours is closer to the code. Both readings are
defensible. His comment in the file argues the same choice we made in the notes: "the
specification should not mandate which sorting algorithm to use" **[cited]**.

What nobody proves, us included, is the parser. Our tests pin its behaviour: four parse tests,
three of them on error messages **[checked]**.

## 4. Speed

All on the real input from `aoc/` unless noted. The scratch programs (`scripts/sw/`) were run in
the scratch project `proj/`, whose `aocsrc` is linked to `aoc/src`.

| Program | `run` | `run --js` | native | Notes |
|---|---|---|---|---|
| `Aoc.Year2024.Day01.main` | 0.64–1.0 (mostly 0.65) | 0.79–1.1 | **0.021** | `build` without `--native`: 0.04 |
| `Hello.sw` (read the input, print its length) | 0.21 | 0.32 | 0.006 | start-up only |
| `Stages.parse` (our parser only) | 0.62 | | | so about 0.4 s is loading `Std.Parse`, `Map`, `List`… |
| `Stages.words` (`words` and `toNat` only) | 0.61 | | | the same: it's the imports, not the parse |
| `Spec.sw` (the spec run: quadratic `count`) | 0.76 | 0.75 | | at 1,000 lines quadratic costs only 0.1 s more |
| `Words.sw` (split on white space, `chunksOf 2`, `transpose`) | 0.55 | 0.67 | | |
| CPython `big.py ref` (`split`, `sorted`, `Counter`) | 0.015 | | | for scale |

On 100,000 synthetic lines (`scripts/big.py 100000`), native, with peak memory:

| Program | native (s) | peak memory |
|---|---|---|
| `Aoc.Year2024.Day01.main` | 1.22–1.28 | 171 MB |
| `Stages.parse` | 0.99–1.04 | 171 MB |
| `Stages.words` | 0.17–0.24 | 245 MB |
| `Stages.sort` (parse and sort) | 1.11–1.16 | |
| `Stages.counts` (parse and count map) | 1.07–1.09 | |
| `Words.sw` | 0.46–0.47 | 314 MB |
| `Spec.sw` | gave up after 56 s (`E-RESOURCE`, step limit) | |
| CPython | 0.04 | |

`run` takes 4.3 s and `run --js` 1.5 s on the same input **[checked: 29 October, three or five
runs each]**. What this shows:

- On the real input there is nothing to fix in the program. The native executable is as fast as
  Python. `run`'s 0.65 s is 0.2 s of start-up plus about 0.4 s of loading the modules it imports,
  which is the loading cost already raised as D1621 in the day 9 note **[inferred: `Stages.words`
  does almost no work and takes as long as the full program]**.
- On large inputs, natively, `Std.Parse` is the cost. `Parse.eachLine` with two `token nat`s
  takes about 10 µs a line, five times `Text.words` plus `Text.toNat`. Sorting and the count map
  add only about 0.1 s each. SW-861 (a state-handler resume inside a match arm isn't run as a
  loop, so `Std.Parse` uses a workaround) is the open ticket closest to this **[checked; inferred:
  the link to SW-861 is not measured]**.

## 5. Candidate improvements, ranked by value over effort

| Rank | Candidate | Kind | Value | Effort | Evidence |
|---|---|---|---|---|---|
| 1 | **Add day 1's numbers to D1621 / SW-813**: `run` spends about 0.4 s loading `Std.Parse`, `Map` and `List` for a program whose work is about 0.02 s | driver / runtime | sharpens the case for D1621; on day 1 the loading is 60% of `run`'s wall time | trivial | §4, `Stages.words` against `Hello` |
| 2 | **Measure `Std.Parse` throughput natively and add it to SW-861**: about 10 µs a line for `eachLine` with two `token nat`s, five times `words` and `toNat` | std / runtime | parsing is 80% of native time on large inputs; small on AoC's real inputs (about 10 ms for 1,000 lines) | trivial to record; the fix is SW-861's | §4 |
| 3 | **A one-line comment in `Proofs.sw`** saying that `part1Correct` holds for every lining up, so the answer doesn't depend on which sorted permutation is chosen (the Coq spec proves only that one exists) | docs | makes the strength of the claim visible to a reader comparing proofs | trivial | §3 |
| — | A `Multiset` type with `m[x]` lookup (Dafny's `multiset`, Haskell's `MS.occur`) | std | `Map.counts` with `getOr` already reads well, and `List.count` serves the spec | medium | §1 item 3 |
| — | Proving the parser (a round trip or a grammar) | proofs | nobody does it; four parse tests pin the behaviour | medium to large | §3 |
| — | Inline `#guard`-style tests beside definitions | language | tests are kept apart from `run` by design (`Tests/`) | — | §2 |

Two friction items from `NOTES-2024.md` are already resolved in the committed code:

- **Item 4** (holes in a congruence lemma filled too late): `part2AnyOrder` now writes
  `List.sumByCong left _ _ (id => …)`, and it checks.
- **Item 5** (`%section` in errors): a failing `rewrite` with `(== id)` now prints `(== id)`.

**[checked: `stitchwort check` in `aoc/` passes; a scratch theorem in `sect/`]**

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D1630 | `Std.Parse` is five times slower than `words` and `toNat` natively (about 10 µs a line), and is 80% of day 1's native time on 100,000 lines. Raise SW-861 (the runtime fix that would let `Std.Parse` drop its workaround) from backlog, or leave it? | [leave it in backlog and add the numbers: real AoC inputs are 1,000 to 20,000 lines, where parsing costs 10 to 200 ms natively; the per-run loading cost (D1621) is the bigger cost on small days] |

---

**Status** (29 October 2026): SW-877, this note, is done once reviewed. D1630 is pending. D1621
(per-run loading cost, from the day 9 note) is still pending, and this note adds data to it.
