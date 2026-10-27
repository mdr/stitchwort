# AoC 2025 day 7: community solutions in other languages

**Date:** 22 October 2026. **Ticket:** SW-247 (D413). **Our version:** `aoc/src/Aoc/Year2025/Day07/Day07.sw`
(program: a `Manifold` record with `start: Fin width` and rows `Vec Bool width`; part 1 carries a
flag per column down the rows, part 2 works up from the bottom row, one count per column), with
`Proofs/Spec.sw` (the timelines as explicit lists of splitters), `Proofs/Part1.sw`,
`Proofs/Part2.sw` and `Proofs/Distinct.sw` (all stated over the parsed manifold), and the tests in
`Tests/`. `docs/aoc-2025.md` "Day 7 (21 October 2026)" and "Over the manifold (22 October 2026,
SW-243)" describe the program and the proofs. This note looks at what other people wrote for 2025
day 7, in the wild, and asks what that suggests for Stitchwort. It follows the shape of
[aoc-day03-community.md](aoc-day03-community.md).

Labels, as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day7-community/sw/`,
run with the main checkout's `target/release/stitchwort` (built 22 Oct 2026, 09:03) against the
committed `aoc/inputs/2025/day07.txt` and `aoc/examples/2025/day07.txt`. Fetched solutions are in `gh/`
beside it, the megathread data in `arctic/`, the scripts in `scripts/`.

## 1. Summary

I read 55 solutions on GitHub (one per author; 59 files): 12 in Lean 4, 3 in Idris 2, one each in
Agda and Dafny, 8 in Haskell, 5 each in OCaml, Scala and Gleam, 4 in Clojure, 3 each in F#, Elixir
and Elm, and one each in Koka and Admiran (§2; narimiran also has a Common Lisp file). I then read the r/adventofcode Day 7 megathread through
the Arctic Shift archive (§2.2): 529 top-level comments, 523 not deleted, 92 language tags. 56
comments are in functional or proof-oriented languages (9 Haskell, 8 Common Lisp, 6 each in F#,
OCaml and Elixir, 5 each in Scala and Gleam, 3 Clojure, 2 each in Scheme and Racket, and one each
in Dafny, Admiran, Janet and Emacs Lisp), and 12 more in array languages (3 Uiua, 3 APL, 2 Goal, 2 Q,
one each BQN and K). I read all of them; 20 of the 56 have code inline. No Lean, Idris, Agda,
Coq/Rocq, Koka, Roc or Unison comment turned up, and I found no Unison, Roc, Coq/Rocq, F\* or
Effekt solution on GitHub either.

The main findings:

1. **Nobody proved day 7.** Across the 15 Lean, 3 Idris, Agda and Dafny files there is no
   theorem about what the solution computes. kim-em's `Day07/Basic.lean` has five: `dedup_nodup`,
   `mem_dedup_iff` and `mergeTimelines_sum` (about helpers; the last is marked "Proved by
   Aristotle", an automatic prover), and two that say nothing (`count + count = 2 * count` by
   `omega`, and `2 ^ splits = Nat.pow 2 splits` by `rfl`). sdiehl's only theorem is
   `fin_always_valid : i.val < n := i.isLt`, and its bounded coordinates are never used by the
   simulation. Hath995's Dafny has two lemmas (a set has a minimum) to help iterate a set, and the
   `problem7_*` methods have no `ensures`. So there is no proof to borrow; ours (`part1Correct`,
   `part2Correct`, `part2Distinct`, no precondition) is the only one I found **[checked: read
   every Lean, Idris, Agda and Dafny file; theorem lines counted with `grep`]**.
2. **The community's part 2 is a bag of counts, carried down the rows; ours is the same idea
   bottom-up.** Of the 55 GitHub authors, about 40 carry a map, bag, array or list of "ways to be in
   this column" forward, merging columns that meet; about 9 memoise a top-down recursion or tie the
   knot (glguy's lazy array, mstksg's `Map.fromSet`); one builds the count from the bottom row
   up, as ours does; 2 count from a grid-wide DP table; the rest simulate beams on the grid. In
   the 56 functional comments, about 30 carry counts forward, about 12 memoise, and the rest give a
   method in words or only a link **[checked: counted by hand; the boundaries are mine]**. Two
   Haskell authors chose our bottom-up shape: beefyhalo
   (`foldr go (repeat 1) restRows`) and thraya (Reddit, `foldr go (repeat 1) ll`). The three-line
   core of beefyhalo's, with the same edge value 1 as ours:
   `left = 1 : cur; right = drop 1 cur ++ [1]; go row cur = zipWith4 update row left cur right`.
3. **The neighbours are the whole day, and the array languages say it best.** A column's new
   value needs its left and right neighbours. The community reads them by carrying the previous
   cell along (Pengler38's `iter prevN prevC`, as our `fall`), by index arithmetic (`i-1`, `i+1`,
   about half the files), by a window (`tails`, thraya), or by shifting the whole row: Goal
   `(»x)*»y + («x)*«y + x*~y`, K `(1_m,0)+-1_0,m`, APL `1∘⌽+¯1∘⌽`, Uiua `↻1¯1`, in 9 of the 12
   array comments (the other three use a stencil or index a dictionary). Stitchwort has `Vec.zipWith3` and `Vec.headOr` (day 4 uses them) but no whole-row shift,
   and day 4's `peelCells` and day 7's `fall` and `splitRow` all carry the neighbour by hand.
   A scratch file with `shiftLeft`/`shiftRight` and `zipWith3` gets 21 and 40 on the example and
   1594 and 15650261281478 on the real input, first try **[checked: `shifts.sw`]**.
4. **Typed row lengths are the Lean community's equivalent of our `Vec`.** jorendorff's
   `Grid α = { nc, rows : Array (Vector α nc) }` is our `Manifold` shape; acarapetis keeps the beams as
   `Vector Bool n` and the counts as `Vector Nat n`; dupuisf's `Vector₂.getGrid` returns
   `⟨n, m, grid⟩`; BrianNormant (Idris) uses `(n ** m ** Vect n (Vect m Manifold))`. Our rows are
   `Vec Bool width` but our beams and counts are `List`s, so 57 lines of `Part1.sw` and `Part2.sw`
   mention `List.length` or `Nat.succInjective`, mostly to thread "this list is as long as the row"
   **[checked: `grep -c`]**. Keeping beams and counts as `Vec` in the program would remove most of
   them **[inferred; the column lemma for part 2 came out at break-even, §3.6]**.
5. **Our edge handling is more careful than the community's.** A splitter in column 0 or the last
   column sends one beam off the grid. The real input never does this, and Samstrikes (Elixir) says
   so: "ASSUMPTION: I won't have to do bounds checking". Our program treats an escaped beam as one
   timeline, and `part2Correct` is proved against a spec that does the same (Spec.sw), tested by
   the "splitter at the left edge" and "right edge" tests. kim-em and sdiehl check the edges;
   `c - 1` on a `Nat` (my own `sets.sw`, copying the Haskell and Idris shapes) quietly puts a beam
   back in column 0 **[checked: `sets.sw` header; the other comments from the files]**.
6. **Part 1 is the hard half of our proof, and the community treats it as the easy half.** Part 1
   is "count the splitters a beam reaches", a one-line set or flag fold in every language. Our
   `Part1.sw` is 387 lines and `Part2.sw` 69, because "some timeline reaches this splitter" is an
   existential over lists of hits (`reach`, `beamReach`, `fallKeeps`), while part 2's count has a
   per-column invariant. glguy and tenthmascot define part 1 as "splitters whose count is above
   zero", from the same table as part 2, and mstksg wrote "I really want to unite both of these
   into a single function and swap out `+` for `||` somehow". In our setting that sharing doesn't
   carry over, because the bottom-up counts say nothing about which splitters are reached from the
   top **[inferred]**; D456 asks whether to look for a cheaper part 1 proof anyway.
7. **Big numbers matter, and our `Nat` is right.** Part 2's answer is 1.57 × 10^13 on our input.
   54 megathread comments name 64-bit or big integers, and sim642 left a comment in the file:
   "part 2: 2012790981 (Int overflowed in countTimelines)" **[cited: file]**.
8. **One syntax gap shows again, in an old ticket.** `lines.head.flatMap (line => …
   line.length …)` is `E-CANNOT-INFER` ("can't work out the type of this function"), because the
   receiver of a dot call is the last argument and the lambda comes first (SW-228, parked).
   The error is **[checked: `mapbag.sw`, first version]**; the cause is my guess **[unverified]**.
   The workaround is an annotation, `((line: Text) => …)`.

The ranked candidates are in §5 and the decisions in §6 (D450–D456). The cheapest useful ones:

- whole-row `Vec.shiftLeft`/`shiftRight` with a fill value, `Vec.tabulate`, and their `getOr`
  lemmas (D450), then day 7 and day 4's row steps over `Vec` with them (D451);
- `List.findMap` beside SW-235's `findIndex`/`withIndex`, which replace the 16 lines that find S
  (D452), and `Abort` in `parseManifold` (D453);
- keep "S anywhere in the grid" (D454), and leave `Map.unionWith` for later (D455).

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker. "Proofs" means theorems in
the file, not tests. Every GitHub file was fetched, not run (the Haskell, Lean, Idris,
Agda, Dafny and OCaml programs were not built); I read the ones in the table, and only skimmed the
others (size, imports, the main function). The table lists the solutions that add something;
the others are listed after it.

| # | Language | Author / link | Lines | Method | Notable | Proofs? |
|---|---|---|---|---|---|---|
| 1 | Lean 4 | [jorendorff](https://github.com/jorendorff/advent-of-code/blob/HEAD/2025/day07/Day07/Basic.lean) | 74 | per-column step over `Vector` | `Grid α = { nc, rows : Array (Vector α nc) }`; a Parsec parser that builds `Vector α n` with `repeatN`; `Vector.finRange nc \|>.map (hasBeam row beams)`; `getD (i-1)` for the neighbours; "because the tachyon manifold is quantum, the step becomes a leap" | no |
| 2 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day7.lean) ([part 2](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day7_2.lean)) | 29, 21 | pure `step` over `Vector` | `State n` with `beams: Vector Bool n`; `zipIdx.map`; `splitters[i]?` for the neighbours; part 2 is `Vector Nat n` and `step` is 8 lines; `panic!` if a row has the wrong width | no |
| 3 | Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day07/Basic.lean) | 164 + 13 | list of (column, count), `dedup`, `mergeTimelines` | `fuel` for termination; the repo has a `claude-logs/` folder | 5 theorems, none about the answers: `dedup_nodup`, `mem_dedup_iff`, `mergeTimelines_sum` ("Proved by Aristotle", needs `maxHeartbeats 800000`), and two that are `omega` and `rfl` on identities |
| 4 | Lean 4 | [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day7.lean) | 135 | list of beams, `StateM`, `eraseDups`; part 2 association list | `BoundedCoord (maxRow maxCol) { row: Fin _, col: Fin _ }` and `safeGet` are defined and never used by the simulation; `fuel` | `fin_always_valid : i.val < n := i.isLt` |
| 5 | Lean 4 | [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day7.lean) | 69 | `StateM (Std.TreeMap (Fin m.cols) Nat)` | columns are `Fin m.cols`, so every lookup carries a `have … := by rw [← m.colsCorrect …]`; its own `Array.findAllIdx` returning `List (Fin arr.size)`; `neighbors (i: Fin n)` by `Fin.foldr` | no |
| 6 | Lean 4 | [dupuisf](https://github.com/dupuisf/aoc25/blob/HEAD/Aoc25/Day07.lean) | 47 | in-place `Vector` of flags (part 1) or counts (part 2) | `Vector₂.getGrid raw (many <\| oneOf …)` returns `⟨n, m, grid⟩`; `for hrow : row in 1...<n` and `setIfInBounds` | index bounds only |
| 7 | Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day07.lean) | 34 | one DP table over `HashMap (Int × Int) Char` | part 1 is "the splitters with a count above 0" (`countP … val > 0`), part 2 the last row's sum | no |
| 8 | Lean 4 | [josephmate](https://github.com/josephmate/AdventOfCode2025/blob/HEAD/AdventOfCode2025/Day07.lean), [adomani](https://github.com/adomani/advents/blob/HEAD/Advents/AoC2025/day07.lean), [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day7.lean), [vanshjangir](https://github.com/vanshjangir/AoC/blob/HEAD/2025/day07.lean), frutjus ([1](https://github.com/frutjus/aoc2025/blob/HEAD/day7/part1.lean), [2](https://github.com/frutjus/aoc2025/blob/HEAD/day7/part2.lean)) | 48–106 | sets of columns; in-place arrays; BFS | josephmate keeps every other line (`idx % 2 == 1`); adomani `#assert part1 atest == 21`; `partial def` in vanshjangir and frutjus | no |
| 9 | Idris 2 | [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day7/Solution.idr) | 158 | part 1 rewrites the grid until it stops changing; part 2 a `SortedMap (Fin n, Fin m) Integer` cache | `Grid = (n ** m ** Vect n (Vect m Manifold))`; `partial`; a commented-out attempt ending in holes `?cachemiss`, `?impl` | no |
| 10 | Idris 2 | [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day7.idr), [Pengler38](https://github.com/Pengler38/AoC-2025/blob/HEAD/src/Day7.idr) | 99, 35 | `SortedSet` intersection and difference; a left-to-right pass carrying the previous cell | Pengler38: `iter prevN prevC (n::ns) (c::cs)` returns the splits and the row in one recursion, `partial` | no |
| 11 | Agda | [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day07.agda) | 59 | `Data.Tree.AVL.Sets` and `Map`, `foldr` per row | `part1` and `part2` recurse on the row list, so total without a flag; `zipWithIndex` written locally | no |
| 12 | Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/7/Problem7.dfy) | 159 | sets and multisets of columns | `SetFold` over a set needs `ThereIsAMinimumNat` (two lemmas); `problem7_*` have no `ensures`; "If Dafny had multiset comprehension expression" **[cited]** | two lemmas about minima, nothing about the answers |
| 13 | Haskell | [glguy](https://github.com/glguy/advent/blob/HEAD/solutions/src/2025/07.hs) | 52 | lazy array defined in terms of itself (knot-tying) | `counts = listArray (bounds input) [ if 'S' == input ! i then 1 else u + l + r \| … ]`; part 1 is `length [() \| ('^', n) <- … , n > 0]` | no (doctest with 21 and 40) |
| 14 | Haskell | [mstksg](https://github.com/mstksg/advent-of-code/blob/HEAD/2025/AOC2025/Day07.hs) ([reflections](https://github.com/mstksg/advent-of-code/wiki/Reflections-2025#day-7)) | 74 | knot-tying over the splitter set: part 1 looks up from each splitter for light, part 2 looks down for paths | `M.fromSet splitters (…)` refers to its own result; "I really want to unite both of these into a single function and swap out `+` for `\|\|`" **[cited]** | no |
| 15 | Haskell | [beefyhalo](https://github.com/beefyhalo/aoc/blob/HEAD/src/2025/07.hs) | 31 | **bottom-up, ours**: `foldr go (repeat 1) restRows` | `go row cur = zipWith4 update row left cur right where left = 1 : cur; right = drop 1 cur ++ [1]`; part 1 a string rewrite with `go (_ : '\|' : _ : as) (_ : '^' : xs)` | no |
| 16 | Haskell | [RossPaterson](https://github.com/RossPaterson/advent-of-code/blob/HEAD/2025/Day07.hs), [nicuveo](https://github.com/nicuveo/advent-of-code/blob/HEAD/2025/haskell/src/Day07.hs), [PP6464](https://github.com/PP6464/AoC-2025-Haskell/blob/HEAD/src/Day07.hs), [stanosphere](https://github.com/stanosphere/advent-of-code/blob/HEAD/src/2025/Day7.hs), [GuillaumedeVolpiano](https://github.com/GuillaumedeVolpiano/adventOfCode/blob/HEAD/2025/days/Day7.hs) | 31–112 | row-by-row `Set`/`Bag`/`Map` fold; mutable unboxed vector | RossPaterson: "if the order does not matter, large groups of indistinguishable elements can be replaced with a count for each value, i.e. use a bag instead of a list"; nicuveo `M.unionWith (+)`; GuillaumedeVolpiano streams the bytes into an `IOVector` | no |
| 17 | OCaml | [mbacarella](https://github.com/mbacarella/ocaml-aoc2025/blob/HEAD/lib/day7.ml), [FizzyElt](https://github.com/FizzyElt/ocaml_aoc_2025/blob/HEAD/bin/day7/q2.ml), [KacperKopiec](https://github.com/KacperKopiec/advent-of-code/blob/HEAD/2025/day7/part2.ml), [lukaskollmer](https://github.com/lukaskollmer/advent-of-code/blob/HEAD/src/2025/day_07/solution.ml), [aguluman](https://github.com/aguluman/advent-of-code-ocaml/blob/HEAD/2025/day07/day07.ml) | 22–168 | in-place array of counts (FizzyElt, KacperKopiec, mbacarella); BFS queue and a memo matrix (aguluman); variant cells (lukaskollmer) | `assert false` for impossible cell pairs (mbacarella); KacperKopiec's part 2 is 22 lines | no |
| 18 | F# | [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day07.fs), [jrmcnair](https://github.com/jrmcnair/advent-of-code/blob/HEAD/2025/Day7.fs), [mattgallagher92](https://github.com/mattgallagher92/advent-of-code/blob/HEAD/2025/Day07.fs) | 17–86 | `Map` of counts folded over the rows | lboshuizen gets both parts from one fold in 17 lines: `Map.change col (fun v -> Some (defaultArg v 0L + n))`; `Seq.findIndex` for S | no |
| 19 | Scala 3 | [sim642](https://github.com/sim642/adventofcode/blob/HEAD/src/main/scala/eu/sim642/adventofcode2025/Day7.scala), [lupari](https://github.com/lupari/aoc2025/blob/HEAD/src/main/scala/assignments/Day07.scala), [bishabosha](https://github.com/bishabosha/advent-of-code-2025/blob/HEAD/scala/2025_day07.scala), [jelaby](https://github.com/jelaby/advent-of-code-2025-scala/blob/HEAD/src/main/scala/uk/co/mealor/aoc2025/Day7.scala), [Casper-Guo](https://github.com/Casper-Guo/AoC-Language-Exploration/blob/HEAD/2025.scala/day07.scala) | 31–188 | `groupMapReduce` over beams (sim642, lupari, bishabosha), BFS (sim642 part 1), `Memo.mutableHashMapMemo` (jelaby) | `.groupMapReduce(_._1)(_._2)(_ + _)`; sim642's trailing comment "part 2: 2012790981 (Int overflowed in countTimelines)" | no |
| 20 | Elixir, Clojure | [nikola-benes](https://github.com/nikola-benes/aoc2025elixir/blob/HEAD/07.exs), [lasseebert](https://github.com/lasseebert/advent_of_code_2025/blob/HEAD/lib/advent/day_07.ex), [ryoung786](https://github.com/ryoung786/AdventOfCode/blob/HEAD/lib/aoc/years/2025/day_07.ex), [narimiran](https://github.com/narimiran/aoc2025/blob/HEAD/clojure/src/day07.clj), [genmeblog](https://github.com/genmeblog/advent-of-code/blob/HEAD/src/advent_of_code_2025/day07.clj), [CodeFarmer](https://github.com/CodeFarmer/aoc-2025/blob/HEAD/src/aoc_2025/day_7.clj), [arnemart](https://github.com/arnemart/aoc/blob/HEAD/2025/07/7.clj) | 21–95 | `Map.merge` with `c1 + c2` (nikola-benes, 21 lines); `update … (fnil + 0)` (genmeblog); `memoize` (narimiran, CodeFarmer); arnemart rewrites grid cells in place | nikola-benes reads S off the first line with `Enum.find_index(& &1 == ?S)`; CodeFarmer's comment: "assume the first line always contains the start"; genmeblog takes S to be in the middle column (`(quot (count line) 2)`); narimiran: "I smell something Lanternfishy" **[cited: file]** | no |
| 21 | Koka, Gleam, Elm, Admiran | [junpls](https://github.com/junpls/aoc25/blob/HEAD/day07.kk), [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day07/day07.gleam), [bmatcuk](https://github.com/bmatcuk/adventofcode2025/blob/HEAD/day07/src/day07.gleam), [tilltheis](https://github.com/tilltheis/adventofcode-2025-gleam/blob/HEAD/src/day07.gleam), [houli](https://github.com/houli/advent-of-code-2025/blob/HEAD/src/day7.gleam), [bucsi](https://github.com/bucsi/aoc/blob/HEAD/solutions_gleam/src/aoc_2025/day_7.gleam), [albertdahlin](https://github.com/albertdahlin/advent-of-code/blob/HEAD/elm/src/Y25/D07.elm), [maxhille](https://github.com/maxhille/aoc-2025/blob/HEAD/days/Day07.elm), [taolson](https://github.com/taolson/advent-of-code/blob/HEAD/2025/day07.am) | 44–156 | sets and dicts; taolson merges sorted lists of (column, paths) | junpls: Koka `var num-splits` and `linear-set`; bmatcuk parses and folds in one `nibble` parser; taolson's `mergeBeams` is a sorted-list merge | no |
| 22 | Reddit, bottom-up | [thraya](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsylukn/) (Haskell) | inline | **bottom-up with a window**: `foldr go (repeat 1) ll` | `[ if b == '^' then x + z else y \| ((_,x):(b,y):(_,z):_) <- tails $ zip (wrap '?' qq) (wrap 1 nn) ]`; part 1 a `State` fold with `go (_:'\|':_:aa) (_:'^':_:xx)` | no |
| 23 | Reddit, bags | [lboshuizen](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsq6048/) (F#), [pianomanDylan](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsrjkao/) (Scala), [Stano95](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nstie8c/), [vanZuider](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsrekan/) (Haskell), [bmatcuk](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsrlovt/), [tymscar](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nssnc34/) (Gleam) | inline | a map or set of columns, one fold | pianomanDylan: "Used the `Semigroup` type-class from Cats to handle the Map merge operation. No DFS, no graph, no cache, just iteration and simple addition"; tymscar: "a fold inside a fold" **[cited]** | no |
| 24 | Reddit, array languages | [anaseto](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsq7jw7/) and [oantolin](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/ntf4zy8/) (Goal), [ap29600](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsqt518/) (K), [Daniikk1012](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsq80xu/) (BQN), [Andreasnl](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsq5a4o/), [aurele](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nssmrwe/) (Uiua), [light_switchy](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsvhh0x/), [voidhawk42](https://www.reddit.com/r/adventofcode/comments/1pg9w66/2025_day_7_solutions/nsq5u7k/) (APL) | 1–5 | the row step as a scan or reduce with whole-row shifts | oantolin's whole answer: `ans:{t:{(-i)+x+(»i)+«i:x*y}\s:~"."=""\=-read[x];(+//(1_s)&(-1_t);+/*\|t)}`; ap29600 "simple DP, reminds me of the idiom for pascal's triangle in k"; anaseto "Part 2 is actually shorter and simpler than part 1, as it is just a simple fold instead of a scan" **[cited]** | no |
| — | Stitchwort | `aoc/src/Aoc/Year2025/Day07/Day07.sw` + `Proofs/` + `Tests/` | 47 (program); 38 + 9 (tests) | part 1 flags down, part 2 counts up, S anywhere | `Manifold` with `start: Fin width` and `Vec Bool width` rows; edges proved; tests include both edges and merging beams | **yes**: `part1Correct`, `part2Correct`, `part2Distinct`, for every manifold; Spec 79 + Part1 387 + Part2 69 + Distinct 74 lines |
| — | Stitchwort, scratch | `shifts.sw`, `mapbag.sw`, `sets.sw`, `windows.sw`, `findstart.sw`, `shiftproof.sw` | 21–54 | the community's shapes | §4 | `shiftproof.sw` checks the part 2 column step |

Fetched and only skimmed, because they repeat these patterns: Casper-Guo (Scala), ryoung786 and
Zenor27 (grid graphs), caseyWebb's Elm file (1,368 lines).

### 2.1 What I couldn't find

- **Unison, Roc, Coq/Rocq, F\*, Effekt:** none in GitHub code searches or the megathread. Code
  searches for "splitter", "timelines", "tachyon" with `extension:lean`, `:idr`, `:agda`, `:v`,
  `:dfy`, `:kk`, `:roc` and `:u` found the files above plus jorendorff's, which my author list
  had missed, and unrelated hits (FemtoRV `femtorv32_tachyon.v`) **[checked: `gh/search.txt`]**.
- **Day 7 from some earlier authors:** Dessertion, benjaminfjones, ianclement, stonarini,
  a2435191 (Lean), devcordde (Idris; only C and Elixir under `Day-07`), frectonz (Idris), lambdam
  (OCaml) and tschady (Clojure) had no day 7 file my path search matched. The search matched `day07`, `Day7`, `07.` and `day_07` names, so a file
  with another name would be missed **[checked: `gh/paths.txt`]**.
- **Reddit itself:** not contacted; the megathread came from the Arctic Shift archive. Links to
  pastes (topaz) weren't decoded: F# r_so9, Scala FCBStar-of-the-South, Common Lisp raevnos, Haskell
  vanZuider, F# LtHummus and Janet veydar_ have no code I could read.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** Requests to [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift): a post
search by time window (7 Dec 2025, 04:50–05:20 UTC; the wider window timed out with "Maybe slow
down a bit"), `/api/posts/ids?ids=1pg9w66`, and
`/api/comments/tree?link_id=t3_1pg9w66&limit=25000` (1.8 MB). No requests to reddit.com
**[checked: saved in `arctic/`]**. Terms as in the day 1 note.

**What it holds.** "2025 Day 7 Solutions" (7 Dec 2025, 05:00 UTC, recorded score 1 and
`num_comments` 0, which the archive took when the thread was new). The tree has 796 comments in
all: **529 top-level**, 6 of them `[deleted]`/`[removed]`, 504 of the 523 live ones with a language
tag and 19 without. 183 of the 523 have code inline **[checked: `scripts/langs.py`]**.

**The landscape.** Tags counted once per comment and language; spelling variants merged by script:

| Language | Comments | | Language | Comments |
|---|---|---|---|---|
| Python | 119 | | Ruby, R | 7 each |
| Rust | 60 | | Perl, F#, OCaml, Elixir | 6 each |
| C++ | 30 | | Scala, Bash, Gleam | 5 each |
| JavaScript, Go | 22 each | | Awk, Raku, Swift | 4 each |
| C#, TypeScript, Java | 15 each | | Clojure, Dart, Uiua, SQL, Julia, Google Sheets | 3 each |
| C | 14 | | Scheme, Racket, Dyalog APL, Goal, Q, Nim, Odin, Pascal, Intcode, Tailspin, … | 2 each |
| Kotlin | 13 | | Dafny, Admiran, Janet, BQN, K, Lily, Elle, Ajla, Smalltalk, … | 1 each |
| Haskell, Zig | 9 each | | | |
| Common Lisp | 8 | | | |

The 56 functional and proof-oriented comments are 11% of the live ones (day 3 had 76, day 2
66, day 1 82). Across all 523, about 95 mention memoising or a cache, 51 dynamic programming, 54
64-bit or big integers, 18 Pascal's triangle, Galton boards or lanternfish (2021 day 6;
narimiran's "I smell something Lanternfishy", Bumblee420 "reminded me of 2021 Day 6"), and 6
that every other row of the input is empty (sheshanaag filters `even . fst`, argentcorvid steps by
2) **[checked: regexes in `scripts/words.py`, upper bounds; a word can match in a comment about
something else]**.

## 3. Themes

### 3.1 Finding S

| Approach | Who | Example |
|---|---|---|
| Read S off the first line | about 16 of 55 | `elemIndex 'S' firstRow` (beefyhalo), `grid.[0].IndexOf('S')` (lboshuizen), `Seq.findIndex` (jrmcnair), `dat[0]!.dropWhile (· != 'S')` (adomani), `indices 'S' (hd rows)` (taolson) |
| Seed the whole first line: S is 1, the rest 0 | 6 | `Array.map (fun c -> if c = 'S' then 1 else 0)` (KacperKopiec), `parseRow n 'S'` (acarapetis), `grid[0].map fun x => if x == '.' then false else true` (dupuisf), Pengler38's `'S' => 1` on every row |
| Search the whole grid | about 20 | `grid.find(_._2 == 'S').get._1` (lupari), a `for r … for c …` loop (kim-em, sdiehl, aguluman), `head [p \| (p, c) <- pcs, c == 'S']` (RossPaterson) |
| Assume where it is | 3 | genmeblog takes the middle column (`(quot (count (first lines)) 2)`); narimiran's Lisp takes the column of the first splitter; CodeFarmer's comment: "assume the first line always contains the start" |
| A lexer or parser tags it | 8 | `lexer.token("S", Start)` (bmatcuk), `Vector₂.getGrid … (oneOf #['.', '^', 'S'])` (dupuisf), `Cell.start` (jorendorff, mbacarella) |

**[checked: from the `'S'` search in `gh/`; the counts are rough, a file may do two things.]** On
our input S is in the first line, in column 71 (the middle of 141), and every other line has no
splitter **[checked: `awk` on `aoc/inputs/2025/day07.txt`]**, so all of these assumptions hold on it.

**Stitchwort today.** `parseManifold` finds the first S anywhere (`findStart`, `startFrom`,
`firstFound`, `columnOf`: 16 code lines), takes the rows below it, and turns S's column into a
`Fin width` with `Fin.ofNatCheck`. That is more general than the community's "S is on the first
line" and costs the 16 lines; the proofs don't touch them (SW-243 moved the theorems over the
parsed manifold). With the search helpers the community uses, `findStart` is five lines
(`findstart.sw`, three tests pass **[checked]**):

```
def findStart (lines: List Text): Option (Nat, Nat) :=
  findMap (((r, line)) => (findIndex (ch => ch == 'S') line.toList).map (c => (r, c))) (withIndex lines)
```

`findMap` (Lean `findSome?`, Scala `collectFirst`, F# `tryPick`) is not in the SW-235 batch;
`findIndex` and `withIndex` are. D452 and D454 ask about this.

### 3.2 The methods

| Method | How it works | GitHub (of 55) | FP megathread (of 56) |
|---|---|---:|---:|
| Counts forward, row by row | a map, bag, array or list of "ways to be in this column"; a splitter moves its count to both neighbours; merge columns that meet | ~40 | ~30 |
| Memoised or knot-tied recursion, top-down | `timelines(row, col)` with a cache, a lazy array, or `Map.fromSet` | ~9 | ~12 |
| Counts from the bottom, up | start with 1 per column below the last row; a splitter's count is the sum of its neighbours' | 1 (beefyhalo; ours is a second) | 1 (thraya) |
| One DP table over the grid | `dp(r, c) = from above + from the splitters beside` | 2 (glguy, tenthmascot) | 0 |
| Part 1 only: sets | beams as a `Set`; hits are the intersection; passes the difference | ~20 | ~14 |

**[checked: counted by hand from the files and comments; approximate, and the boundaries between
families are mine]**

"Forward counts" is the community's answer to the puzzle's trap: part 2 has about 1.6 × 10^13
timelines, so listing them is out. Several say so: "Surprised to hear people were using DFS or BFS
solutions since I'd assume they would not finish in reasonable time" (mbacarella), "Brute force would be basically impossible I think" (Stano95), both on Reddit **[cited]**.

**Stitchwort today.** All the shapes ran first time, apart from one annotation and one import:

```
-- mapbag.sw, after lboshuizen, nicuveo, stanosphere: one fold, a Map of counts
def land (row: Set Nat) (acc: (Map Nat Nat, Nat)) (column: Nat) (count: Nat): (Map Nat Nat, Nat) :=
  if Set.contains column row then
    (Map.insertWith (a b => a + b) (column + 1) count (if column == 0 then acc.fst else Map.insertWith (a b => a + b) (column - 1) count acc.fst), acc.snd + 1)
  else (Map.insertWith (a b => a + b) column count acc.fst, acc.snd)
```

`mapbag.sw` (21 lines) prints 21 and 40 on the example and 1594 and 15650261281478 on the real
input, in 0.16 s under `run` and 0.29 s under `run --js`; `sets.sw` (part 1 with
`Set.intersect`, `Set.difference`, `Set.union`) prints 21 and 1594; `windows.sw` (thraya's
`tails` shape, with `tails` written locally) prints 40 and 15650261281478 **[checked]**. For
comparison the committed program takes 0.18 s and 0.32 s (three runs each). Speed is not an issue
on this day: most of that is loading the prelude.

### 3.3 Neighbours: how the row step reads left and right

| Technique | Who | Cost in Stitchwort |
|---|---|---|
| Carry the previous cell down the recursion | Pengler38 (`iter prevN prevC`), beefyhalo's part 1, **ours** (`fall`, `splitRow`) | written today; the carry (`fromLeft`, `left`) is a parameter the proofs have to state |
| Index arithmetic with a safe read | `splitters[i-1]?` (acarapetis), `getD (i-1)` (jorendorff), `Map.findWithDefault` | `List.getOr d i xs`, O(i) per read |
| Shift the whole row | `left = 1 : cur; right = drop 1 cur ++ [1]` (beefyhalo); Goal `»x` and `«x`; K `0,m`; Uiua `↻1¯1` | **missing for `Vec`**; `shifts.sw` writes the two shifts in 6 lines |
| A window of three | `tails` and `(_,x):(b,y):(_,z):_` (thraya); jelaby's `windows` | needs `tails` (SW-235); `windows.sw` works with a local one |
| In-place array updates | dupuisf, mbacarella, lichtbogen: `beams[i-1] += n; beams[i+1] += n; beams[i] = 0` | no mutable arrays (D299, not now) |

**Stitchwort today.** The shift form, with `Vec` for the beams and counts so lengths are in the
types **[checked: `shifts.sw`, 21 and 40, 1594 and 15650261281478]**:

```
def shiftRight (fill: a): Vec a n -> Vec a n          -- every element one place right
  | VNil       => VNil
  | VCons x xs => VCons fill (shiftRight x xs)

def shiftLeft (fill: a): Vec a n -> Vec a n           -- every element one place left
  | VNil       => VNil
  | VCons x xs => VCons (Vec.headOr fill xs) (shiftLeft fill xs)

def step (state: (Nat, Vec Bool w)) (row: Vec Bool w): (Nat, Vec Bool w) :=
  let hit := Vec.zipWith (s b => s && b) row state.snd
  (state.fst + (Vec.toList hit).count (x => x),
   Vec.zipWith3 (p l r => p || l || r)
     (Vec.zipWith (s b => b && not s) row state.snd) (shiftRight False hit) (shiftLeft False hit))

def splitRow (row: Vec Bool w) (below: Vec Nat w): Vec Nat w :=
  Vec.zipWith3 (s here sides => if s then sides else here) row below
    (Vec.zipWith (l r => l + r) (shiftRight 1 below) (shiftLeft 1 below))
```

The row-step part of the committed program (`solvePart1` to `splitRow`) is 15 code lines; the
shift version's program part is 13 lines, plus 9 for `tabulate` and the two shifts, which a
library would hold. So this is not about shorter: it is that `fall`'s carried `fromLeft` flag,
`splitRow`'s carried `left`, and their length facts are gone, and the same two shifts do day 4's
`peelCells` (`left + here + columns.headOr 0`, the same carry).

### 3.4 Lengths in types

| Representation | Who | Cost |
|---|---|---|
| `Array (Vector α nc)` in a record with `nc` | jorendorff | the parser builds each row with `repeatN`, so a wrong width is a parse failure |
| `Vector Bool n` state, `Vector Bool n` splitters | acarapetis | `parseRow` calls `panic!` if a row has the wrong width |
| `(n ** m ** Vect n (Vect m Manifold))` | BrianNormant | `traverse (toVect l)` in `Maybe` |
| `Fin m.cols` as a map key | bjornestol | a `have … := by rw [← m.colsCorrect …]` per lookup |
| `List` with the lengths as hypotheses | kim-em, sdiehl, **ours** for beams and counts | 57 lines of `Part1.sw`/`Part2.sw` mention `List.length` or `Nat.succInjective` |

**Stitchwort today.** The rows are `Vec Bool width` and the start is a `Fin width`, like
jorendorff's, and the proofs convert rows with `Vec.toList` and pass `List.length beams = w` by
hand (`hb`, `hf`, `fallLength`, `splitRowLength`, `countsLength`). The library already has
`Vec.zipWith3` (day 4 uses it) and `Vec.getOrZipWith3` (a `getOr` over a `zipWith3`, for exactly
this); the only missing pieces are the shifts and a two-vector `getOrZipWith`. Section 3.6
measures what that buys.

### 3.5 Edges

| Handling | Who |
|---|---|
| "ASSUMPTION: I won't have to do bounds checking" | Samstrikes (Elixir) |
| `if col > 0` and `col + 1 < numCols` | kim-em, sdiehl (a beam going off the grid is dropped, so it is not counted in part 2) |
| `setIfInBounds`, `getD (i-1)`, `[i]?` | dupuisf, jorendorff, acarapetis (dropped as well) |
| `fromMaybe 1` at the bottom, "leaving the map" is one timeline | mstksg, beefyhalo (`1 : cur`, `cur ++ [1]`), **ours** |

The puzzle says nothing about a splitter beside the edge, and the real input never has one (the
first and last columns of every line of `aoc/inputs/2025/day07.txt` are `.`, **[checked: `awk`]**), so every
solution above is right on the real input. For a splitter in the last column, the beam that leaves
is one more timeline in part 2 on our reading of the puzzle (D219); solutions that drop it
under-count. Ours counts it and the proof says so: `Spec.sw`'s `timelinesFrom` makes the left
side of a column-0 splitter one timeline ending there, and `part2Correct` holds for every manifold
**[checked: `Tests/Examples.sw`, "splitter at the left edge" and "right edge", both `(1, 2)`]**.
Writing the spec forced a decision the puzzle text leaves open (D219 recorded part 1's; the edge
beam is part 2's); the community solutions made it silently, if at all.

### 3.6 Proofs and automation

Nobody on day 7 proves the answer (§1, finding 1). What the community does have:

- **Types as the invariant:** `Fin n` columns (bjornestol, sdiehl) and `Vector α n` rows
  (jorendorff, acarapetis, dupuisf), the same move as our `Manifold`. bjornestol's version shows
  the price of putting the proof in the key type (`Fin m.cols`): every use needs a `have`.
- **Automatic provers on helper lemmas:** `mergeTimelines_sum` in kim-em's file is 35 lines of
  `aesop`, `grind` and `linarith` output, labelled "Proved by Aristotle (v4.24.0), requires
  increased heartbeats for v4.24.1". It proves that merging duplicate columns keeps the total, a
  fact our proofs never need because `splitRow` writes each column once. This is a data point for
  SW-101 (arithmetic automation), not a technique to copy.
- **Executable checks beside the code:** `#assert part1 atest == 21` (adomani), doctests (glguy),
  `%expect_test` elsewhere. Our `test`s do this.

**Where our proof time goes.** `Part1.sw` is 387 lines and `Part2.sw` 69. Part 2's invariant is per
column ("this column's count is the timelines from it"), proved by one induction on the rows
(`countsAre`). Part 1's is a statement about which splitters some timeline reaches, so it needs
the reachability relation, the beam flags tied to it (`fallKeeps`), and a sum over columns
(`splitsBelowSum`). mstksg's reflection is the nearest thing to an argument: part 1 ties the knot
upward ("did this splitter receive light") and part 2 downward, and he had not managed to unify them.
**[inferred]** the same split is why one function can't serve both in our proofs.

**An experiment: the part 2 column step over `Vec` with shifts.** `shiftproof.sw` proves, checked by
the release binary **[checked]**:

```
theorem splitRowAt (row: Vec Bool w) (below: Vec Nat w) (c: Nat):
    List.getOr 1 c (Vec.toList (splitRow row below))
      = (if List.getOr False c (Vec.toList row) then List.getOr 1 c (Cons 1 (Vec.toList below)) + List.getOr 1 (Succ c) (Vec.toList below) else List.getOr 1 c (Vec.toList below))
```

which is the statement of `Proofs/Part2.sw`'s `splitRowAt`. It takes 14 lines, and the
three length lemmas the list version needs (`splitRowLength` 6 lines, `countsLength` 7) are not
needed, so 14 against 21 lines. It also needs four library lemmas of 22 lines in all
(`shiftRightGet`, `shiftLeftGet`, `shiftRightCons`, and `getOrZipWith`, the two-vector twin of
`Vec.getOrZipWith3`) that a library would hold once and day 4 would reuse. So for part 2 the saving is small, and
the lemmas that pay for it are reusable. For part 1 (`fallAt`, `fromLeft`, `fallLength`: 21 lines, and
the `hb`/`hf` hypotheses through `fallKeeps`, `splitsBelowSum` and `beamStart`) I expect a similar
saving but did not try it **[speculative]**.

### 3.7 Library breadth

| Helper | Seen in | Stitchwort |
|---|---|---|
| Set intersect, difference, union | Haskell (nicuveo, stanosphere, vanZuider), Idris (spikedoanz), Koka (junpls), Admiran, F# | `Set.intersect`, `difference`, `union` **[checked: `sets.sw`]** |
| Merge a count into a map: `unionWith (+)`, `insertWith`, `Map.change`, `groupMapReduce`, `fnil`, `Map.merge` | about 20 files | `Map.insertWith` **[checked: `mapbag.sw`]**; no `Map.unionWith` or `Map.fromListWith` |
| Index of the first match, first `Just` | `elemIndex`, `findIndex`, `IndexOf` (about 15 files); `findSome?`, `collectFirst`, `tryPick` | `List.find` only; `findIndex`, `withIndex` in SW-235; **`findMap` missing** |
| `zipWith4`, `zipIdx`, `finRange` | beefyhalo (`zipWith4`), acarapetis (`zipIdx`), jorendorff (`finRange`) | `List.zipWith3`, `Vec.zipWith3` (day 4); no `zipWith4` |
| `foldr` with a lazy infinite `repeat 1` | beefyhalo, thraya | `List.replicate w 1`, `Vec.replicate`; both fine |
| Vector from a function of the index: `Vector.finRange nc \|>.map`, `Array.init`, `Vector.ofFn` | jorendorff; `List.init` or `Array.init` in a few more | **no `Vec.tabulate`**; `shifts.sw` writes it in 3 lines |
| Lazy arrays and knot-tying | glguy, mstksg, Haskell memo | not applicable: strict and total |

**[checked: by pattern and by hand; the file counts are rough]**

The day 3 note's `maxBy`, `dropWhile`, `tails` and the others were not needed on day 7 except
`tails` (thraya's shape), `findIndex` and `withIndex` (the S search).

### 3.8 Big numbers and speed

Answers: 1594 and 15650261281478 on our input. The community's ones are of the same sizes; sim642
lost a day to `Int` (above). Stitchwort's `Nat` is unbounded, and `run --js` uses `bigint`.

Timings reported in the megathread: 1.2 ms (Chez: "Part 1 and Part 2 run the same code"), 884 µs and 832 µs for parts 1 and 2 (G_de_Volpiano, Haskell), 2.6 ms (dijotal, Common Lisp),
about 100 µs (giacomo_cavalieri, Gleam), 50 µs (Bumblee420, OCaml), 0.0005 s and 0.001 s (p4bl0,
OCaml) **[cited]**. Ours: 0.18 s under `run`, 0.32 s under `run --js`, most of it start-up
**[checked]**.

## 4. Side by side

The bottom-up row step in Haskell, in our committed program, and in the shift form:

```haskell
-- beefyhalo (Haskell): the whole of part 2
final = foldr go (repeat 1) restRows
go row cur = zipWith4 update row left cur right
  where
    left = 1 : cur
    right = drop 1 cur ++ [1]
    update '^' x _ z = x + z
    update _ _ y _ = y
```

```
-- Stitchwort (Day07.sw): the committed splitRow; `left` is the carried neighbour
def splitRow (left: Nat): List Bool -> List Nat -> List Nat
  | Cons s ss, Cons here rest => Cons (if s then left + rest.headOr 1 else here) (splitRow here ss rest)
  | _,         _              => Nil
```

```
-- Stitchwort, scratch shifts.sw: beefyhalo's shape, over Vec
def splitRow (row: Vec Bool w) (below: Vec Nat w): Vec Nat w :=
  Vec.zipWith3 (s here sides => if s then sides else here) row below
    (Vec.zipWith (l r => l + r) (shiftRight 1 below) (shiftLeft 1 below))
```

beefyhalo's `zipWith4` has four inputs; Stitchwort's has `zipWith3`, so `shifts.sw` adds the two
neighbours first (`zipWith (l r => l + r)`), as Goal's `(»x)*»y + («x)*«y` does.

The same step in the array languages, and a typed per-column version:

```
oantolin (Goal):   t:{(-i)+x+(»i)+«i:x*y}\s            -- the step (excerpt), scanned over the rows
ap29600 (K):       beams{m:x*y; (x*~y)+(1_m,0)+-1_0,m}/ splitters
light_switchy (APL): +⌿⊃(×∘~⍨+(1∘⌽+¯1∘⌽)⍤×)⌿⌽'.'≠⊃⎕NGET'7.txt'1
```

```
-- jorendorff (Lean), per column over Vector, neighbours by getD
def countTimelines {nc: Nat} (row : Vector Cell nc) (timelines : Vector Nat nc) (i : Fin nc) : Nat :=
  (if row[i] == Cell.start then 1 else if row[i] == Cell.empty then timelines[i] else 0)
  + (if i.val > 0 && row.getD (i - 1) Cell.empty == Cell.splitter then timelines.getD (i - 1) 0 else 0)
  + (if row.getD (↑i + 1) Cell.empty == Cell.splitter then timelines.getD (↑i + 1) 0 else 0)
-- solve2 = Array.foldl (fun timelines row => Vector.finRange nc |>.map (countTimelines row timelines)) (Vector.replicate nc 0) rows |>.sum
```

Our spec against the others' non-spec:

```
-- kim-em: the nearest to a specification, about a helper
theorem mergeTimelines_sum (xs : List (Nat × Nat)) :
    (mergeTimelines xs).foldl (fun acc (_, c) => acc + c) 0 = xs.foldl (fun acc (_, c) => acc + c) 0 := by
  -- Proved by Aristotle (v4.24.0), requires increased heartbeats for v4.24.1
  induction' xs using List.reverseRecOn with xs ih <;> aesop; …

-- Stitchwort, Proofs/Part2.sw and Part1.sw: about the answers, over the parsed manifold
theorem part2Correct (manifold: Manifold): solvePart2 manifold = part2Spec manifold
theorem part1Correct (manifold: Manifold): solvePart1 manifold = part1Spec manifold
```

## 5. Candidate features, ranked by value over effort

Kinds: **sugar** (syntax only), **library**, **tooling**, **refactor**, **language** (elaboration
or kernel).

| Rank | Candidate | Kind | Value | Effort | Evidence | Ticket |
|---|---|---|---|---|---|---|
| 1 | **`Vec.shiftLeft`/`shiftRight` (with a fill value), `Vec.tabulate`, and their `getOr` lemmas, with `Vec.getOrZipWith`** | library | medium: day 4's `peelCells` and day 7's `fall` and `splitRow` all carry a neighbour by hand; 9 of 12 array comments and beefyhalo shift | small (9 lines of definitions, 22 of lemmas, the lemmas proved in `shiftproof.sw`) | §3.3, §3.6, `shifts.sw`, `shiftproof.sw` | none; D450 |
| 2 | **Day 7 (and day 4) row steps over `Vec` with the shifts, ports of the proofs** | refactor | medium: lengths in types (57 lines of proofs mention `List.length`), the same two shifts for both days; part 2's column lemma is 14 against 21 lines | small to medium (port `Part1.sw`'s `fallAt`, `fromLeft`, `fallLength`; time-box and keep it only if smaller) | §3.4, §3.6 | none; D451, after D450 |
| 3 | **`List.findMap`** (with SW-235's `findIndex` and `withIndex`) | library | low to medium: `findStart` goes from 16 lines to 5 | trivial | §3.1; `elemIndex`, `findIndex`, `IndexOf` in about 15 files, `findSome?`/`collectFirst` in the idiom | none; D452, beside SW-235 |
| 4 | **`Abort` in `parseManifold`** | refactor | low: a flat `let`s instead of a `flatMap`/`map` pair | trivial | `findstart.sw` (`Option.orAbort`, three tests pass); no AoC program uses `Abort` yet | none; D453, with SW-224's idea |
| 5 | **Keep "S anywhere" and `start: Fin width`** | decision, no change | — | — | §3.1: about 22 of 55 take S from the first line (6 by seeding it) and 2 more assume its column; ours costs 16 lines and no proof | D454 |
| 6 | **`Map.fromListWith`, `Map.unionWith`** | library | low: `Map.insertWith` in a fold already does it | trivial | about 20 files merge counts; `mapbag.sw` works with `insertWith` | none; D455, not now |
| 7 | **A cheaper part 1 proof** | design note | unknown: 387 against 69 lines | medium to large | §3.6 | none; D456, not now |
| — | Already parked, now with day 7 evidence | | | | | |
| — | SW-228 (dot receiver position) | language | the `lines.head.flatMap (line => …)` `E-CANNOT-INFER` in `mapbag.sw` is its case | — | §1, finding 8 | already parked |
| — | SW-235 (list batch 2: `tails`, `findIndex`, `withIndex`, …) | library | thraya's window shape needs `tails`; `findStart` needs the other two | — | §3.1, §3.3 | already parked; D452 adds `findMap` |
| — | SW-101 (arithmetic automation) | language | kim-em's `aesop`/`grind`/`Aristotle` lemma on `mergeTimelines` is the only day 7 use of automation | — | §3.6 | backlog; no change |
| — | Local mutable variables, mutable arrays (dupuisf, mbacarella, lichtbogen) | language | low | large | about 10 files and 6 Reddit comments with code update an array or variable in place **[checked: by hand, rough]** | **not now** (D299); no change |
| — | Lazy arrays and knot-tying (glguy, mstksg) | language | none: Stitchwort is strict and total | — | §3.2 | no change |

Why this order:

- **Rank 1 is the day's only real gap, and it is already half there.** The library has `Vec.zipWith3`,
  `Vec.headOr` and `Vec.getOrZipWith3` (day 4 uses the first two). The shifts are the missing half, and the experiment
  shows the lemmas are short and go through on the first or second try.
- **Rank 2 is worth doing only if the part 1 port is no longer than the saving.** The
  evidence for the proof saving is the 14 against 21 lines for part 2, plus the length hypotheses I
  counted but did not remove; I have not tried part 1 **[speculative]**.
- **Ranks 3 and 4 are small and independent.** `findMap` costs one definition and one lemma-free
  test; `Abort` costs nothing to the library.
- **Rank 5 is a trade-off the code already made.** Taking S from the first line would delete
  `findStart` and its tests and turn `start` into a seed vector, but the proofs say "the particle
  from S" and S is a single cell; I would keep it unless the parse cost mattered more.
- **Ranks 6 and 7 stay out for now.**

## 6. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D450 | Add `Vec.shiftLeft` and `Vec.shiftRight` (with a fill value), `Vec.tabulate`, their `getOr` lemmas and `Vec.getOrZipWith` to the standard library, each with an example? | [yes; one small ticket, definitions and lemmas from `shifts.sw` and `shiftproof.sw`] |
| D451 | Rewrite Day 7's row steps with `Vec` beams and counts and these shifts (and Day 4's `peelCells`), porting the proofs? | [yes, time-boxed, after D450; keep it only if the proofs end up no longer than today's] |
| D452 | Add `List.findMap` to SW-235's batch, and use `findIndex`, `findMap` and `withIndex` in `findStart`? | [yes; SW-235 plus one definition] |
| D453 | Use `Abort` in `parseManifold`? | [yes, with the D451 rewrite] |
| D454 | Keep Day 7's model as it is: S anywhere in the grid, `start: Fin width`, rather than the community's "S is on the first line" seed row? | [keep] |
| D455 | Add `Map.fromListWith` and `Map.unionWith`? | [not now; `Map.insertWith` in a fold covers day 7, wait for a second day that wants them] |
| D456 | Write a design note on a cheaper part 1 proof (a reach relation as an inductive predicate, or part 1 from forward counts)? | [no, not now; revisit if a later day needs the same reachability argument] |

---

**Status** (short form, 22 October 2026): D450 shifts and `tabulate`, pending; D451 Day 7 and Day 4
over `Vec` with shifts, pending (after D450); D452 `findMap` with SW-235, pending; D453 `Abort` in
`parseManifold`, pending; D454 keep S anywhere, pending; D455 `Map.fromListWith`/`unionWith`, pending;
D456 part 1 proof note, pending. Unchanged by day 7: SW-228 dot receiver position and SW-235 list
batch 2 (parked), SW-101 backlog, D299 local mutable variables not now, D296 operator sections and
D297 text patterns not now.
