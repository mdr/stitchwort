# AoC 2025 day 8: community solutions in other languages

**Date:** 22 October 2026. **Ticket:** SW-308 (D535). **Our version:** none yet; this note comes
first, as the audit that feeds the program and the proof (the order the user asked for: audit
others, then solve and prove, then a gap analysis). The puzzle background is in
`docs/aoc-2025.md` "Day 8: junction boxes": 1,000 points in 3D, join the 1,000 closest pairs
(by squared distance) into circuits, multiply the three biggest circuit sizes (part 1); keep
joining until one circuit is left and multiply the x coordinates of the last pair (part 2).
The input is `aoc/inputs/day08.txt`. This note follows the shape and method of
[aoc-day07-community.md](aoc-day07-community.md) and
[aoc-day03-community.md](aoc-day03-community.md).

Labels, as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Scratch files for every Stitchwort claim are in
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/day8-community/proj/src/`
(`Common.sw`, `B1.sw` to `B6.sw`), run with `target/release/stitchwort` built from this
worktree at `9f7a9fe5` (`nix develop -c cargo build --release -p stitchwort-cli`, 24 s), on the
committed `aoc/inputs/day08.txt`. Timings are wall-clock seconds from `/usr/bin/time`, one run
each, on the machine that built it, so read them to a factor of about 1.5. Fetched solutions are in
`gh/`, the megathread data in `arctic/`, the scripts in `scripts/`, all beside `proj/`.

## 1. Summary

I fetched day 8 solutions from 83 GitHub authors (one per author; 96 files): 11 in Lean 4, 3 in
Idris 2 (one is a stub), one each in Agda and Dafny, 13 in Haskell, 11 in OCaml, 9 each in Scala
and Gleam, 8 in Clojure, 7 in Elixir, 6 in F#, 2 in Elm, one each in Koka and Admiran (§2).
I read the proof-language, Haskell and persistent-structure files in full and read the rest through
targeted greps for the method. I then read the r/adventofcode Day 8 megathread through the
**Arctic Shift archive** (§2.2): 386 top-level comments, 380 not deleted, 370 with a language tag. 52 are
in functional, proof-oriented or niche languages (10 Haskell, 5 each in F# and OCaml, 4 each in
Scala, Common Lisp and Elixir, 3 each in Clojure, Scheme and Racket, 2 Gleam, one each Dafny,
Admiran, Prolog, Janet, Lily, Smalltalk, Kenpali, Jactl and Tailspin). I read all 52; 14 have code
inline. No Lean, Idris, Agda, Koka, Roc or Unison comment turned up, and I found no Coq/Rocq, F\*,
Isabelle or Unison solution on GitHub either.

The main findings:

1. **Nobody proved day 8.** Of the 11 Lean files only kim-em's and sdiehl's have theorems (12 in
   all), and none of them says what the answer is. kim-em's `Day08.lean` has three statements
   about the solution, each ending in `sorry`, one of which (`connectKShortest_processes_k`)
   only concludes `length ≤ 3`; its `Basic.lean` has four, all about `distSq` or the parser
   (two are labelled "Proof by Aristotle", an automatic prover). sdiehl's `connected_refl`,
   `symm`, `trans` and `connected_equivalence` are true by `rfl`, because `Connected` is defined as
   "same `findRoot`". Hath995's Dafny proves that `AllPairs` has `n(n-1)/2` elements and keeps a
   `Valid()` invariant on its union-find (indices in bounds, sizes positive); `Valid()` doesn't
   rule out cycles, and every method is marked `decreases *` **[inferred: the connection is mine]**; and the `problem8_*` methods have no
   `ensures` **[checked: read every Lean, Idris, Agda and Dafny file; `grep` for theorem lines]**.
   No Mathlib `SimpleGraph` or connected-component theory is imported anywhere
   **[checked: `grep -l SimpleGraph`, no hits]**. So there is no proof to borrow, and the library
   support to lean on is our own `Map` lemmas (§5).
2. **Everyone sorts all 499,500 pairs, and almost everyone is right to.** About 76 of the 83
   authors sort the full list of pairs (by `sort`, `sortBy`, `sortOn`, `qsort`, `mergeSort`,
   `sorted`) **[checked: by hand and by regex, approximate]**. The few that don't: sim642, aguluman
   and GuillaumedeVolpiano put the pairs in a priority queue and take from it as needed; taolson
   sorts lazily with a quicksort whose comment says it is "so that not all pairs have to be sorted
   first"; b-valdez buckets the points into a spatial hash and keeps a bounded max-queue of the
   1,000 best; narimiran and nicuveo throw away pairs beyond a distance cut-off before sorting
   (narimiran's 20,000 comes from "some tweaking and experimenting" **[cited]** and is safe only because of how the inputs look **[inferred]**). On
   our input the sort is cheap: in Stitchwort `List.sortBy` on all 499,500 pairs takes **1.8 s**
   under `run` (§5.2), against an estimate of 12 to 15 s in `docs/aoc-2025.md` **[checked: `B2.sw`]**.
3. **Part 2 needs only 6,204 of the 499,500 sorted pairs.** On our input the last merging pair is
   at sorted index 6,203 **[checked: `sw/stats.py`]**. That is why the sorted-prefix loops
   everywhere are fast and why laziness (Haskell `scanl'`, Scala `Iterator.scanLeft`, Janet
   `generate`) is idiomatic: build the whole sorted list, consume the front.
4. **Circuits are tracked three ways, and the immutable ones are not slower.** Of the 83 authors,
   about 25 use a union-find (mutable arrays or `IOVector`/`Hashtbl`: glguy, GuillaumedeVolpiano,
   KacperKopiec, heathhenley, bjoli, aguluman, lboshuizen, rolandtritsch and others; a library
   `DisjointSet`/`UnionFind`: matajoh, lupari, sim642, devries, tenthmascot, nikola-benes; **a
   persistent one over a `Map`**: beefyhalo, MrCrLr, jpyamamoto, trajafri, and kneegma on Reddit;
   stanosphere has his own `UnionFind` module whose internals I did not read). About 40 keep a list, set or `Seq` of circuits as sets and merge by scan
   (`partition`, `intersection`): RossPaterson, mstksg, nicuveo, merlinorg, sondresl,
   JavadocMD and others. About 13 keep a map from point to circuit label plus a map from label to
   members, and relabel the smaller side on a merge (thraya, bmatcuk, killertux, bucsi, taolson,
   lasseebert, mtravers, bjornestol, frutjus). Three more go through a graph and a DFS
   (phibr0, nikola-benes's first version, jpyamamoto's part 1) **[checked: counted by hand; the
   boundaries are mine]**. Reported run times for the pure ones: Haskell with a `Set` of sets
   241 ms and 397 ms for the two parts (MyEternalSadness), Racket sets about 500 ms
   (RudeGuy2000), Chez 95 ms and 107 ms (onrustigescheikundig, with a disjoint set) **[cited]**.
5. **The purely functional recipe is two lines and a fold.** The three most common immutable
   shapes are: `IntMap`/`Map` parent pointers with no path compression, `find` by recursion and
   `union` as `insert root1 root2` (beefyhalo, about 15 lines for `find`, `union` and the sizes); a `Set (Set a)` where
   each join `partition`s the circuits that touch the pair and unions them (merlinorg: three lines
   inside a `scanLeft`); and a `Map` of labels relabelled on merge. In Stitchwort the first
   (`B4.sw`) runs both parts in **2.7 s**, the third (`B6.sw`, `Map.map` relabel) in **3.7 s**, and
   the list-of-labels version the repository's plan names (`B3.sw`, `List.map` relabel) in
   **21.7 s**, nearly all of it in the 1,000 joins, not the sort (§5.2). The cause of that
   gap is **[unverified]** (my guess: a chain of unforced `List.map`s).
6. **Two traps catch people, and the answer to both is in the spec.** (a) Part 1 counts the 1,000
   closest *pairs*, including ones already in the same circuit (a "connection" that does
   nothing), not 1,000 merges. Hath995: "doing nothing counts!" is the "biggest obstacle";
   onrustigescheikundig tried both ways; at least six authors (adomani, bjornestol, merlinorg, nikola-benes, b-valdez, bucsi)
   special-case the example's 10 by looking at the input size. (b) Ties in distance are never mentioned in the code, and only one comment
   (audioAXS, Python) even says they might matter. There are none in our input: all 499,500
   squared distances are different **[checked: `sw/stats.py`: 0 repeated values; the 1,000th is
   65,741,882 and the 1,001st 65,747,201]**. rolandtritsch's comment says ties "are broken by the
   stable index order of the pair list", the only place it is said.
7. **Integers: the squared distance needs 35 bits, and a quarter of the authors use a float
   sqrt.** The largest squared distance on our input is 26,178,032,634 (35 bits), more than a 32-bit
   `Int`, and part 2's answer, 8,079,278,220, is 33 bits **[checked]**. About 25 of the 83
   authors compute `sqrt` of a `Double`/`Float` to sort by (Pengler38, BrianNormant and mbacarella
   in the proof languages; Zenor27, bucsi, killertux, guillheu in Gleam; Scala, F#, Elixir,
   Clojure authors) **[checked: regex for sqrt/float/pow plus reading; approximate]**; the rest sort by the
   squared integer, which is what narimiran notes: "we don't really need to take a square root".
   One Reddit comment reports a silent C++ int overflow. Stitchwort's `Nat` can't overflow.
8. **What Stitchwort has is enough for a correct program today, with one gap in speed that a
   `Map` fixes.** `List.sortBy` (with `Sorted`, `Perm` and length theorems), `Map` and `Set`
   (a balanced tree with a proved order invariant and `getInsert`/`getInsertOther` lemmas),
   `List.tails`, `findMap`, `withIndex`, `Nat.absDiff`, `Vec.tabulate` all exist **[checked: read
   `crates/elab/src/std/`]**. Missing: `Array` (SW-112, backlog; not needed, see §5), any lemma
   about `Map.map`, a graph library, and a ready connectivity specification (§5.3).
9. **One parse gap showed up while writing the benchmarks.** The tuple pattern
   `(Some x, Some y, Some z)` is `E-PARSE` ("expected `)`, but found `y`") **[checked: first
   version of `Common.sw`]**; nested `flatMap`s replaced it. The cause is **[unverified]** (my
   guess: an application pattern after a comma in a tuple pattern needs its own parentheses).

The recommended approach and decisions D537 to D539 are in §6. The cheapest useful ones:

- sort all pairs once with `List.sortBy` on a `(distance, i, j)` key, fold the sorted list into a
  `Map` of circuit labels or a `Map` of parent pointers, stop part 2 at the first pair after which one
  circuit is left (D537);
- prove the labels equal the connectivity of the pairs joined so far, with the 1,000 as "pairs, not
  merges", and say how ties are broken (D538);
- add `Map.map`'s `get` lemma and a `List.pairs`-style helper only (D539); no `Array`, no partial sort.

## 2. The solutions

"Lines" counts non-blank lines that don't start with a comment marker. "Proofs" means theorems in
the file, not tests. Every file was fetched, not run (the Haskell, Lean, Idris, Agda, Dafny and
OCaml programs were not built). The table lists the solutions that add something; the others are
listed after it.

| # | Language | Author / link | Lines | Method | Notable | Proofs? |
|---|---|---|---|---|---|---|
| 1 | Lean 4 | [jorendorff](https://github.com/jorendorff/advent-of-code/blob/HEAD/2025/day08/Day08/Basic.lean) | 100 | all pairs `qsort`ed, then a typed union-find | `UnionFind n` holds `map : Vector (Fin n) n` and `count : Fin (n + 1)`; `find` threads the vector through path compression; `partial def` for `find`; part 2 counts steps with `counting_foldl_until` | no |
| 2 | Lean 4 | [kim-em](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day08.lean) ([Basic](https://github.com/kim-em/AoC2025/blob/HEAD/AoC2025/Day08/Basic.lean)) | 86 + 60 | `Array.qsort` of edges, library `UnionFind` | a `claude-logs/` folder in the repo | 8 theorems: `distSq_comm`, `distSq_nonneg`, `distSq_self`, `parseLine_eq` (two "Proof by Aristotle"), `Edge.lt_trans` (`omega`), and three `sorry`: `generateEdges_spec`, `connectKShortest_processes_k` (concludes only `length ≤ 3`), `connectUntilOne_last_edge` |
| 3 | Lean 4 | [acarapetis](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day8.lean) ([part 2](https://github.com/acarapetis/advent-of-code-2025/blob/HEAD/Day8_2.lean)) | 49, 43 | `mergeSort` of all pairs; a `HashMap` from vertex to clique; relabel all values on each merge | part 1 re-counts cliques with `values.eraseDups.length` after every merge; Lean `dbg_trace` left in; "VertId" and "CliqueId" are `UInt16` newtypes | no |
| 4 | Lean 4 | [tenthmascot](https://github.com/tenthmascot/advent-of-code-2025/blob/HEAD/AoC2025/Day08.lean) | 42 | `mergeSort` on `all_pairs`; a `DSU` imported from `Utils.Bad.DSU` | part 2 is a structural recursion on the list of edges with a `merges_needed` counter ("intentional Nat subtraction") | no |
| 5 | Lean 4 | [sdiehl](https://github.com/sdiehl/aoc-2025-lean/blob/HEAD/AoC2025/Day8.lean) | 104 | `mergeSort` of all pairs; `UnionFind` of `Array Nat` with `fuel` for `findRoot` | `Connected uf i j := (uf.findRoot i).1 = (uf.findRoot j).1` and its four equivalence theorems, all one-liners | 4 trivial: `connected_refl`, `symm`, `trans`, `equivalence` |
| 6 | Lean 4 | [bjornestol](https://github.com/bjornestol/Advent-of-Code-2025-Lean/blob/HEAD/Aoc2025/Day8.lean), [ngrislain](https://github.com/ngrislain/lean-adventofcode-2025/blob/HEAD/LeanAdventofcode2025/Day8.lean), [josephmate](https://github.com/josephmate/AdventOfCode2025/blob/HEAD/AdventOfCode2025/Day08.lean), [adomani](https://github.com/adomani/advents/blob/HEAD/Advents/AoC2025/day08.lean), [vanshjangir](https://github.com/vanshjangir/AoC/blob/HEAD/2025/day08.lean), [frutjus](https://github.com/frutjus/aoc2025/blob/HEAD/day8/part2.lean) | 66–220 | bjornestol: two `TreeMap`s (point to circuit, circuit to points), merge by appending; ngrislain: rank union-find that calls `numCircuits` (O(n) per edge) in part 2; josephmate: two `HashMap`s; adomani: hard-codes the 1,000th distance (`63390489`) and merges `HashSet`s of arrays | adomani's header: "~5s" for part 1 and part 2 "takes approximately 40" (hard-coded answer); frutjus defines `List.tails` and a `Monad List` instance to write the pairs; `#assert part1 atest == 40` (adomani) | no |
| 7 | Idris 2 | [Pengler38](https://github.com/Pengler38/AoC-2025/blob/HEAD/src/Day8.idr), [BrianNormant](https://github.com/BrianNormant/Advent-of-Code-2025/blob/HEAD/src/day8/Solution.idr), [spikedoanz](https://github.com/spikedoanz/advent-of-code-2025/blob/HEAD/src/Day8.idr) | 89, 133, 8 | Pengler38: `sortBy` on `Double` distances, `SortedSet` circuits found by repeated scanning; BrianNormant: for each point the list of others sorted by closeness, repeat "find the global closest" 1,000 times, part 2 runs until two circuits remain and then looks for the closest crossing pair | Pengler38's own `TODO this will stop early because isAllConnected doesn't quite take a list of all points`; `partial` throughout; spikedoanz: a stub printing "part 1 works" | no |
| 8 | Agda | [jpyamamoto](https://github.com/jpyamamoto/advent_of_code_2025/blob/HEAD/src/Day08.agda) | 148 | stdlib `sort` on all pairs; part 1: build adjacency and DFS (`reachable`) per vertex; part 2: persistent union-find over `Data.Tree.AVL.Map` | `{-# TERMINATING #-}` on `find` and `reachable`; `∣ p , q ∣²` as the distance name; `addEdge` inserts `rootX ↦ rootY` | no |
| 9 | Dafny | [Hath995](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/8/Problem8.dfy) ([QuickUnion](https://github.com/hath995/dafny-aoc-2025/blob/HEAD/problems/8/QuickUnion.dfy)) | 429 + 216 | `MergeSortBy` on `AllPairs`, or a hand-written `PriorityQueue` class; `QuickUnion` class with size-weighted union | proves `|AllPairs xs| = n(n-1)/2` via `RowCount`/`LemmaTotalSize` and loop invariants; `Valid()` is bounds and positive sizes only; all methods `decreases *` | `LemmaTotalSize`, `LemmaRowStep`, `IsTotalOrder`, `ThereIsAMinimumTuple`, and 11 `ensures` in `Problem8.dfy` (about `AllPairs` and the parser); none about the answer |
| 10 | Haskell | [glguy](https://github.com/glguy/advent/blob/HEAD/solutions/src/2025/08.hs) | 91 | `sortBy` on all pairs (stable), mutable `DisjointSet` in `IO`, `unifySets` returns `Bool` | one loop gives both parts: after 1,000 pairs it prints the sizes, then keeps going to the last | no (doctest) |
| 11 | Haskell | [beefyhalo](https://github.com/beefyhalo/aoc/blob/HEAD/src/2025/08.hs) | 59 | **persistent union-find**: `type UnionFind = MonoidalIntMap Int` parent pointers, no compression, no rank; `unfoldr` for part 2 | `find parent x = case M.lookup x parent of Just p \| p /= x -> find parent p; _ -> x`; `union` is `M.insert ra rb parent`; sizes via `foldMapWithKey` into `IntSet`s | no |
| 12 | Haskell | [RossPaterson](https://github.com/RossPaterson/advent-of-code/blob/HEAD/2025/Day08.hs), [mstksg](https://github.com/mstksg/advent-of-code/blob/HEAD/2025/AOC2025/Day08.hs), [sondresl](https://github.com/sondresl/AdventOfCode/blob/HEAD/2025/Haskell/src/Day08.hs), [Andrew-42](https://github.com/Andrew-42/advent-of-code/blob/HEAD/src/Year2025/Day08.hs), [massung](https://github.com/massung/advent2025/blob/HEAD/src/Days/Day8.hs), [miguel-negrao](https://github.com/miguel-negrao/Aoc_2025/blob/HEAD/8/src/AoC.hs), [tonniewhood](https://github.com/tonniewhood/AdventOfCode/blob/HEAD/2025/Day8/day8.hs) | 32–174 | a list or `Set` of `Set` circuits; one fold or `scanl`/`State` step finds the circuits that touch the pair and unions them | RossPaterson: `connectPair` with `pickBy`, `solve2` is `length $ takeWhile (> 1) $ map length $ scanl connectPair …`; sondresl: `addToSets sets x = Set.insert (Set.union x (Set.unions xIn)) rest where (xIn, rest) = Set.partition (not . Set.disjoint x) sets`, part 1 is `states !! 999`; mstksg: `replicateM 1000 chomp` in `StateT … Maybe`, originally with `fgl` (2 s, down to 100 ms by hand) | no |
| 13 | Haskell | [stanosphere](https://github.com/stanosphere/advent-of-code/blob/HEAD/src/2025/Day8.hs), [nicuveo](https://github.com/nicuveo/advent-of-code/blob/HEAD/2025/haskell/src/Day08.hs), [GuillaumedeVolpiano](https://github.com/GuillaumedeVolpiano/adventOfCode/blob/HEAD/2025/days/Day8.hs), [trajafri](https://github.com/trajafri/Advent-of-Code-2025/blob/HEAD/app/Day8.hs) | 52–149 | stanosphere: own `UnionFind` module (clusters as a `Map` of `Set`s), `scanl'` of states; nicuveo: `Seq (HashSet P3)` with a distance threshold from the bounding box; GuillaumedeVolpiano: mutable unboxed heap and `IOVector` union-find, streaming parser; trajafri: `Map` of parents with `Float` distances | stanosphere recomputes `clusterMap` on each of up to 6,204 states; nicuveo's `computeThresholdWith 2` keeps only pairs closer than half the smallest span, a heuristic | no |
| 14 | OCaml | [KacperKopiec](https://github.com/KacperKopiec/advent-of-code/blob/HEAD/2025/day8/part2.ml), [bjoli](https://github.com/bjoli/Bjolang/blob/HEAD/Examples/aoc/2025/day08.ml), [heathhenley](https://github.com/heathhenley/AOC/blob/HEAD/2025/lib/day08.ml), [aguluman](https://github.com/aguluman/advent-of-code-ocaml/blob/HEAD/2025/day08/day08.ml) | 47–169 | array or `Hashtbl` union-find with size or rank; aguluman: own binary min-heap (`EdgeHeap`) of edges | bjoli: pairs as `List.init … \|> List.concat \|> List.sort compare`, union-find in 12 lines with arrays | no |
| 15 | OCaml | [b-valdez](https://github.com/b-valdez/aoc/blob/HEAD/solutions/2025/8/solution.ml) | 114 | **no full sort**: a spatial hash (cell size from sampling 20 random pairs), a bounded `Pqueue` of the 1,000 best edges for part 1, **Prim's algorithm** for part 2 | the only file that selects the 1,000 smallest instead of sorting; `Nondeterministic Error` if fewer than 1,000 found | no |
| 16 | OCaml | [mbacarella](https://github.com/mbacarella/ocaml-aoc2025/blob/HEAD/lib/day8.ml), [FizzyElt](https://github.com/FizzyElt/ocaml_aoc_2025/blob/HEAD/bin/day8/q2.ml), [lukaskollmer](https://github.com/lukaskollmer/advent-of-code/blob/HEAD/src/2025/day_08/solution.ml), [cod1r](https://github.com/cod1r/aoc/blob/HEAD/2025/day8.ml), [jackadrianglass](https://github.com/jackadrianglass/side_projects/blob/HEAD/challenges/aoc_2025/day8-ocaml/lib/day8.ml), [phibr0](https://github.com/phibr0/aoc25/blob/HEAD/day08/solution.ml) | 84–213 | `Set` of `Set`s or list of groups merged by scan; `Float` distances in 4 of them; phibr0 builds adjacency and DFS | lukaskollmer: `CoordSetSet = Set.Make(CoordSet)`, `Float.pow` in `distance` | no |
| 17 | Scala | [merlinorg](https://github.com/merlinorg/advent-of-code/blob/HEAD/src/main/scala/year2025/day08.scala) | 30 | **lazy stream of states**: `sorted.iterator.scanLeft(Set.empty[Set[Vec3]])((circuits, pair) => circuits.partition(pair.exists).swap.fold(_ + _.foldLeft(pair)(_ ++ _)))` | part 1 is `.nth(1000, …)`, part 2 is `findMap` on the first state with one circuit | no |
| 18 | Scala | [sim642](https://github.com/sim642/adventofcode/blob/HEAD/src/main/scala/eu/sim642/adventofcode2025/Day8.scala), [lupari](https://github.com/lupari/aoc2025/blob/HEAD/src/main/scala/assignments/Day08.scala), [rolandtritsch](https://github.com/rolandtritsch/scala3-aoc-2025/blob/HEAD/src/main/scala/aoc2025/Day08.scala), [bishabosha](https://github.com/bishabosha/advent-of-code-2025/blob/HEAD/scala/2025_day08.scala), [JavadocMD](https://github.com/JavadocMD/advent-of-code/blob/HEAD/aoc2025/src/aoc2025/Day08.scala), [Philippus](https://github.com/Philippus/adventofcode/blob/HEAD/src/main/scala/adventofcode2025/Day08.scala), [jelaby](https://github.com/jelaby/advent-of-code-2025-scala/blob/HEAD/src/main/scala/uk/co/mealor/aoc2025/Day8.scala), [Casper-Guo](https://github.com/Casper-Guo/AoC-Language-Exploration/blob/HEAD/2025.scala/day08.scala) | 27–178 | sim642: Kruskal from his library, a mutable `PriorityQueue` of all pairs ("it is faster to use a PriorityQueue than sort the Seq of all pairs because Kruskal will only need some closest pairs" **[cited: file]**); lupari: `scanLeft` over states with a library `UnionFind`; others scan sets | rolandtritsch's header gives the cost as "O(n^2 log n) time and O(n^2) space" and says ties follow the stable pair order | no |
| 19 | F# | [lboshuizen](https://github.com/lboshuizen/aoc25/blob/HEAD/Day08.fs), [matajoh](https://github.com/matajoh/aoc_2025/blob/HEAD/day08.fs), [jstnlef](https://github.com/jstnlef/adventOfCode2025/blob/HEAD/Day8.fs), [markpattison](https://github.com/markpattison/advent-of-code/blob/HEAD/2025/Day8.fs), [damirarh](https://github.com/damirarh/AoC2025/blob/HEAD/AoC2025.Lib/Day08.fs), [pillsgood](https://github.com/pillsgood/AOC.FSharp/blob/HEAD/AOC.FSharp/Y2025/Day08.fs) | 25–87 | lboshuizen: `mkUnionFind` over an array in 6 lines, both parts in 25; the rest scan a list of circuits or a `Map` of sets | `iterate (Array.get parent) x \|> Seq.find (fun i -> parent[i] = i)` is lboshuizen's `find`; damirarh moves a `Set` between `Map` keys | no |
| 20 | Elixir | [nikola-benes](https://github.com/nikola-benes/aoc2025elixir/blob/HEAD/08.exs), [lasseebert](https://github.com/lasseebert/advent_of_code_2025/blob/HEAD/lib/advent/day_08.ex), [ryoung786](https://github.com/ryoung786/AdventOfCode/blob/HEAD/lib/aoc/years/2025/day_08.ex), [claytonflesher](https://github.com/claytonflesher/advent_of_code_2025/blob/HEAD/lib/day08.ex), [sreetamdas](https://github.com/sreetamdas/advent-of-code/blob/HEAD/2025/day_08.exs), [wisq](https://github.com/wisq/aoc2025/blob/HEAD/08/b.exs), [MrCrLr](https://github.com/MrCrLr/aoc2025/blob/HEAD/day8/day8.exs) | 35–201 | nikola-benes: 35 lines with a `DisjointSets` module and `Enum.reduce_while`; lasseebert: `Map` point to `MapSet`; ryoung786 and sreetamdas: list of `MapSet`s; MrCrLr: `Map` parent and size | nikola-benes keeps a second, graph version (`08_1.exs`) for part 1 | no |
| 21 | Clojure | [narimiran](https://github.com/narimiran/aoc2025/blob/HEAD/clojure/src/day08.clj), [genmeblog](https://github.com/genmeblog/advent-of-code/blob/HEAD/src/advent_of_code_2025/day08.clj), [CodeFarmer](https://github.com/CodeFarmer/aoc-2025/blob/HEAD/src/aoc_2025/day_8.clj), [arnemart](https://github.com/arnemart/aoc/blob/HEAD/2025/08/8.clj), [crinklywrappr](https://github.com/crinklywrappr/aoc/blob/HEAD/src/crinklywrappr/aoc/2025/day08.clj), [gulllberg](https://github.com/gulllberg/advent-of-code-clojure/blob/HEAD/src/advent_of_code/year_2025/day_08.clj), [tomas81508](https://github.com/tomas81508/advent-of-code/blob/HEAD/src/advent_of_code/dec_2025/day_08_1.clj), [mtravers](https://github.com/mtravers/aoc2025/blob/HEAD/src/aoc2025/day8.clj) | 39–141 | sets of sets with `clojure.set/union`; mtravers: point to circuit `Map` re-pointed on each merge | narimiran's write-up explains the 20,000-wide cube grid and a Manhattan pre-check; CodeFarmer: "this can be made faster by keeping only the closest n pairs and insertion-sorting" **[cited: file]** | no |
| 22 | Gleam, Elm, Koka, Admiran, Roc | [Zenor27](https://github.com/Zenor27/AOC2025/blob/HEAD/src/days/day08/day08.gleam), [bmatcuk](https://github.com/bmatcuk/adventofcode2025/blob/HEAD/day08/src/day08.gleam), [tilltheis](https://github.com/tilltheis/adventofcode-2025-gleam/blob/HEAD/src/day08.gleam), [houli](https://github.com/houli/advent-of-code-2025/blob/HEAD/src/day8.gleam), [bucsi](https://github.com/bucsi/aoc/blob/HEAD/solutions_gleam/src/aoc_2025/day_8.gleam), [killertux](https://github.com/killertux/AOC2025/blob/HEAD/src/day8.gleam), [devries](https://github.com/devries/advent_of_code_2025/blob/HEAD/src/day08/solution.gleam), [kfc35](https://github.com/kfc35/advent_of_code_gleam/blob/HEAD/src/aoc_2025/day_8.gleam), [guillheu](https://github.com/guillheu/AoC25/blob/HEAD/src/day8.gleam), [albertdahlin](https://github.com/albertdahlin/advent-of-code/blob/HEAD/elm/src/Y25/D08.elm), [maxhille](https://github.com/maxhille/aoc-2025/blob/HEAD/days/Day08.elm), [junpls](https://github.com/junpls/aoc25/blob/HEAD/day08.kk), [taolson](https://github.com/taolson/advent-of-code/blob/HEAD/2025/day08.am), [arnemart](https://github.com/arnemart/aoc/blob/HEAD/2025/08/8.roc) | 44–280 | bmatcuk, killertux, bucsi: two `Dict`s (box to id, id to boxes); tilltheis, Zenor27, kfc35: `Set` of circuits; houli: persistent vector `iv` of sets; devries: a `disjoint_set` library; taolson: **lazy `qsort`** and a map from circuit number to boxes plus a reverse map | taolson: "use a lazy qsort to sort the boxPairs so that not all pairs have to be sorted first"; junpls (Koka) uses `ref` cells for parents and `float64` coordinates | no |
| 23 | Reddit | [thraya](https://www.reddit.com/r/adventofcode/comments/1ph3tfc/2025_day_8_solutions/nsz7zrk/) (Haskell), [kneegma](https://www.reddit.com/r/adventofcode/comments/1ph3tfc/2025_day_8_solutions/nt10zuk/) (Clojure), [mstksg](https://www.reddit.com/r/adventofcode/comments/1ph3tfc/2025_day_8_solutions/nswlp0x/), [vanZuider](https://www.reddit.com/r/adventofcode/comments/1ph3tfc/2025_day_8_solutions/nt0dehd/) (Haskell), [NeilNjae](https://www.reddit.com/r/adventofcode/comments/1ph3tfc/2025_day_8_solutions/nszohml/) (Haskell), [sheshanaag](https://www.reddit.com/r/adventofcode/comments/1ph3tfc/2025_day_8_solutions/nsyrh4w/) (Haskell) | inline | thraya: `State` with three `Map`s (next circuit number, sizes, box to circuit) and `lens`; kneegma: a persistent forest as a `Map` of `[parent size]` with path compression threaded through every `find`; vanZuider: two maps, "assign color A to all nodes of color B"; NeilNjae: union-find kept from last year; sheshanaag: `Data.DisjointSet` | kneegma: "I wish I had a built-in min-heap but nothing. The immutable priority-queue didn't help either as it's rather slow." and "I'm sure there must be a more idiomatic/ergonomic way to implement disjoint set on top of immutable data" **[cited]** | no |
| — | Stitchwort, scratch | `Common.sw`, `B1.sw` to `B6.sw` | 8–50 | the shapes above | §5.2 | — |

Fetched and not read in depth, because they repeat these patterns: caseyWebb's Elm, devcordde's C and Elixir
under `Day-08`, the other Python/Rust/Go authors on Reddit. 83 authors in all: Laguana's
`day8.fs` (a Forth file) is not counted.

### 2.1 What I couldn't find

- **Day 8 from some earlier authors:** natewhite345, andorp, Dessertion, benjaminfjones, ianclement,
  stonarini, a2435191 (Lean), frectonz (Idris), lambdam (OCaml), tschady (Clojure), HeikoRibberink,
  PP6464 (Haskell), 0xErwin1, jrmcnair and mattgallagher92 (F#), dupuisf (Lean) had no day 8
  file my path search matched (names `day08`, `Day8`, `08.`, `day_08`, a folder `8`)
  **[checked: `gh/paths.txt`, `scripts/find8b.sh`]**.
- **Proof languages:** code searches for "junction", "playground" and "circuits" with
  `extension:lean`, `:idr`, `:agda`, `:v`, `:dfy`, `:kk`, `:roc`, `:fst`, `:thy`, `:purs` found the
  files above and only unrelated hits (`openai/math` Lean files, Software Foundations)
  **[checked: `gh/search.txt`, `gh/search2.txt`]**. No Coq/Rocq, F\*, Isabelle, Unison, Roc or
  Effekt day 8.
- **Reddit itself:** not contacted; the megathread came from the Arctic Shift archive. Links to
  pastes (topaz) weren't decoded: Guile runnerx4, Scheme CowImaginary3155, F# r_so9, Racket raevnos,
  Haskell vanZuider's code, Gleam Dense-Virus-1692 and Kenpali Meamoria have no code I could read
  (vanZuider and r_so9 explain the method in prose).

### 2.2 The Reddit megathread (via the Arctic Shift archive)

**Source.** Requests to [Arctic Shift](https://github.com/ArthurHeitmann/arctic_shift): a post
search by time window (8 Dec 2025, 04:50 to 05:20 UTC), `/api/posts/ids?ids=1ph3tfc`, and
`/api/comments/tree?link_id=t3_1ph3tfc&limit=25000` (1.4 MB). No requests to reddit.com
**[checked: saved in `arctic/`]**. Terms as in the day 1 note.

**What it holds.** "-❄️- 2025 Day 8 Solutions -❄️-" (8 Dec 2025, 05:00 UTC; the archive records
`num_comments` 517). The tree has 597 comments in all: **386 top-level**, 6 `[deleted]` or
`[removed]`, 370 of the 380 live ones with a language tag and 10 without. 90 of the 380 have code
inline **[checked: `scripts/langs.py`]**.

**The landscape.** Tags counted once per comment and language:

| Language | Comments | | Language | Comments |
|---|---|---|---|---|
| Python | 95 | | Swift | 8 |
| Rust | 44 | | Kotlin | 6 |
| C++ | 20 | | R, Zig | 6 each |
| Go | 17 | | F#, OCaml, Ruby | 5 each |
| C# | 14 | | Scala, Common Lisp, Elixir | 4 each |
| JavaScript | 12 | | Clojure, Scheme, Racket, Julia, Raku | 3 each |
| Java | 11 | | Gleam, Goal, Uiua, Dyalog APL, Awk, Odin, Tcl, Perl, SQL, Dart, D | 2 each |
| Haskell | 10 | | Dafny, Admiran, BQN, K, Q, Lily, Smalltalk, Prolog, Mojo, Crystal, … | 1 each |
| C, TypeScript | 9 each | | | |

The 52 functional, proof-oriented and niche comments are 14% of the live ones (day 7 had 56 of
523). Across all 380, about 96 mention union-find or disjoint sets, 26 Kruskal, 19 a minimum
spanning tree, 37 a heap or priority queue, 8 a k-d tree or spatial structure (several of them to
say they weren't needed: Boojum "I didn't really need that", jwezorek "it doesn't really help you
find the n globally closest pairs"), 4 a partial sort or top-k, 3 Prim, 15 that a connection
inside one circuit "does nothing", 21 a graph library (networkx, scipy, fgl) **[checked: regexes
in `scripts/words8.py`, upper bounds; a word can match in a comment about something else]**.

**Method in the 52.** About 14 use union-find (shrekcoffeepig, Stano95, NeilNjae, sheshanaag,
mstksg's blog, lluque8, FCBStar-of-the-South, lboshuizen, giacomo_hb, TheScown, daic0r with ETS,
onrustigescheikundig with vectors, POGtastic with the OCaml `unionFind` package, dodo-obob); about 14
keep circuits as sets or lists (MyEternalSadness, RudeGuy2000, argentcorvid, tymscar, mestar12345,
munchler, Foldzilla, minikomi, …); about 8 keep a point-to-circuit map (thraya, vanZuider, AustinVelonaut,
minikomi, CodeFarmer); about 5 build a graph (G_de_Volpiano, eipi-10, munchler, nikola-benes's first
version, r_so9, who binary-searches the number of connections and re-runs part 1 for part 2)
**[checked: counted by hand; the boundaries are mine]**.

**Timings reported:** MyEternalSadness (Haskell) 241 ms and 397 ms; dodo-obob (OCaml) 0.56 s with
an integer map as the queue, 0.26 s with a sorted list; onrustigescheikundig (Chez) 95 ms and
107 ms, then 68 ms and 85 ms; RudeGuy2000 (Racket) "~500 milliseconds"; dijotal (Elixir) 464 ms
and 419 ms after a first run of "1-1.5 minutes"; eipi-10 (Elixir) 2 to 3 s; argentcorvid (Common
Lisp) 1.5 s and 16 s; mvorber (F#) 7 to 8 s; POGtastic (OCaml) 45 s; Cute-Document3286 (Zig) 584
µs and 2.4 ms with a bounded heap; robertotomas (Rust) 616 µs with Prim for part 2
**[cited]**. mestar12345 (F#) did not finish in 3 hours because of a lazy sequence that
was not realised **[cited]**.

## 3. Themes

### 3.1 Closest pairs: how to get the sorted prefix

| Approach | Who | Cost in their words or in numbers |
|---|---|---|
| Build all 499,500 pairs, sort them all | about 76 of 83 | 1.8 s in Stitchwort (§5.2); 0.26 s to 0.56 s in OCaml (dodo-obob); "dominated by sorting" (onrustigescheikundig, rolandtritsch) |
| Priority queue of all pairs, take from the front | sim642 (Scala `PriorityQueue`), aguluman (own heap), GuillaumedeVolpiano (unboxed mutable heap), python-b5 (Lily) | sim642: faster than sorting because Kruskal stops early; kneegma (Clojure): the immutable queue was "rather slow" **[cited]** |
| Lazy sort, force only the front | taolson (Admiran `qsort`), the Haskell `sortOn`/`take` shapes | with laziness `take 1000 (sort xs)` is O(n + k log n) in a lazy language **[inferred]**; Stitchwort is strict (§5.1) |
| Bounded structure of the k best, one pass | b-valdez (bounded `Pqueue`), Cute-Document3286 (Zig bounded heap), tobega ("K-Select heap"), CodeFarmer (a comment: "insertion-sorting into a thousand-edge list") | O(n log k); part 2 then needs something else (Prim, or sort more) |
| Spatial cut-off: a grid of cubes or a distance threshold, then sort what's left | narimiran (cubes of 20,000, pre-check with Manhattan distance), nicuveo (half the smallest span), b-valdez (spatial hash, cell size from sampled distances) | narimiran: "lots of boxes are very far apart and they will not be directly connected" **[cited]**; the cut-off is a property of the input, not proved |
| Prim's algorithm, no sort at all | b-valdez and robertotomas (part 2); part 2's pair is the heaviest edge of the minimum spanning tree | robertotomas: Union Find "allocates ~12MB … so I switched to prim's algorithm" **[cited]** |
| k-d tree | Boojum, edgeman312 (scipy), concettina-wakamoto, jwezorek (tried, rejected) | the tree finds nearest neighbours, not the globally closest pairs (jwezorek) |

**[checked: from the files and comments; counts approximate]**

For our input the sorted prefix needed is 1,000 pairs for part 1 and 6,204 for part 2, out of
499,500 **[checked: `sw/stats.py`]**. The community's own lesson is that sorting everything is
fine; the exceptions are speed experiments (sim642 wanted the time down; b-valdez and narimiran
wrote a spatial structure for fun, narimiran says so in the file).

### 3.2 Tracking circuits

| Approach | How a join works | Who | Sketch of cost |
|---|---|---|---|
| Union-find on mutable arrays | `find` with path compression, `union` by size or rank | about 25 (glguy, GuillaumedeVolpiano, KacperKopiec, heathhenley, bjoli, aguluman, lboshuizen, rolandtritsch, Casper-Guo, lupari, sim642, matajoh, devries, claytonflesher, ngrislain, kim-em, tenthmascot, hath995) | near-constant per join |
| **Persistent union-find on a `Map`** | `find` by chasing parents, `union` = one `insert`; no mutation | beefyhalo, MrCrLr, jpyamamoto, trajafri, kneegma (with compression, threading the forest); sdiehl and jorendorff (threaded arrays/vectors) | log n per step, depth grows without compression or rank; jorendorff's `partial def find` |
| Set of sets (or list of sets) | `partition` out the circuits touching the pair, union them with the pair | about 40 (RossPaterson, mstksg, sondresl, merlinorg, massung, Andrew-42, miguel-negrao, tonniewhood, genmeblog, CodeFarmer, JavadocMD, Philippus, pillsgood, markpattison, tilltheis, kfc35, …) | O(circuits) per join: 1,000 at the start, so about 10^6 element touches per part, a few hundred ms in compiled FP (MyEternalSadness 241 ms, RudeGuy2000 500 ms) |
| Two maps: point to label, label to members | relabel the members of one side; keep the bigger side's label | thraya, vanZuider, AustinVelonaut (taolson), bmatcuk, killertux, bucsi, lasseebert, mtravers, bjornestol, frutjus, josephmate, minikomi | O(size of the moved side) per join |
| A label for every point, relabel all | scan the whole label vector or map on each real merge | acarapetis (`HashMap.map`), Stitchwort scratch `B3`/`B6` | O(n) per merge: 999 merges for part 2, so about 10^6 |
| Graph, then components by DFS/BFS | add each edge, run a traversal for the circuits | phibr0, jpyamamoto (part 1), nikola-benes's first version, eipi-10, G_de_Volpiano (Reddit) | a traversal per query; part 2 repeats it per edge (munchler: "Part 2 takes a few seconds to run because I recompute all the circuits on each iteration") |
| Prim's algorithm | the heaviest edge of the tree | b-valdez, robertotomas | O(n²) with no sort and no union-find |
| Binary search on the number of connections, re-run part 1 | | r_so9 | log₂(6204) runs of part 1 |

**[checked: counted by hand; one author may appear under two approaches]**

Note what a "join" has to do to answer part 2: **know when one circuit is left**. The three
ways are a counter of circuits decremented on each real merge (glguy, Lean `numComponents`,
Stitchwort `B3`/`B4`/`B6`'s `comps`), `size == n` of the merged circuit (mstksg, tymscar), and
`Set.size circuits == 1` (the set-of-sets files, O(1) with a `Set`). The counter needs no extra
structure and has the simplest invariant: it falls by exactly one on each join that changes
anything **[inferred]**; it is also `docs/aoc-2025.md`'s "each useful join lowers the circuit count by one".

### 3.3 Purely functional and immutable approaches

The question: what did people use when they refused mutable arrays, and how fast was it?

| Structure | Author | Language | What they said | Speed |
|---|---|---|---|---|
| `MonoidalIntMap Int` of parents, no compression | beefyhalo | Haskell | 22 lines for `find`, `union`, `componentSizes` | not reported **[unverified]** |
| `Map` of `[parent size]` with path compression threaded through every call | kneegma | Clojure | "I'm sure there must be a more idiomatic/ergonomic way to implement disjoint set on top of immutable data" **[cited]** | not reported |
| `Set (Set a)` + `partition` per join | merlinorg, sondresl, RossPaterson, mstksg | Scala, Haskell | 3 lines for the step; the stream of states answers both parts | 241 ms / 397 ms (MyEternalSadness's `Set` version) **[cited]** |
| `State` with `Map` point→circuit and `Map` circuit→size | thraya | Haskell | `lens` makes it read like an imperative program | not reported |
| `Seq (HashSet P3)` | nicuveo | Haskell | `Seq.adjust'`, `Seq.deleteAt` | not reported |
| `Vector` threaded through `set`, linear use | jorendorff, sdiehl, ngrislain | Lean | in Lean a threaded `Array`/`Vector` is updated in place when nothing else holds it, so it is a mutable array in disguise **[inferred; Lean's runtime behaviour, not checked]** | not reported |
| ST monad or `IO` with mutable vectors | glguy, GuillaumedeVolpiano | Haskell | the fast ones | GuillaumedeVolpiano: Reddit "a lot of room for improvement" |
| `scanl'` over a persistent structure | stanosphere, NeilNjae, MyEternalSadness, sondresl | Haskell | keeps the intermediate states, `!! 999` for part 1 and `takeWhile` for part 2 | MyEternalSadness 241 and 397 ms **[cited]** |

**[checked: from the files and comments]** None of the purely functional versions I found
reports its time except MyEternalSadness's; the others' speed is **[unverified]** for compiled
code. In Stitchwort I measured four of the shapes (§5.2): parent `Map` 2.7 s, label `Map` 3.7 s, label
`List` 21.7 s, and Prim over `List`s (part 2 only) 1.0 s. Two practical lessons from the community:
- **Don't recompute the circuit list per step.** stanosphere's `scanl'` with `clusterMap` per state
  and munchler's "recompute all the circuits on each iteration" both pay O(n) per edge for part 2's
  6,204 edges; the counter (§3.2) avoids it.
- **Merge the smaller side.** The two-map versions (thraya, vanZuider, bmatcuk) keep a list of
  members per label, so a join touches only one side, as union by size would.

### 3.4 Ties, integers, and the "1,000 connections" trap

| Question | Community | Our input |
|---|---|---|
| Sort by `sqrt` or by the squared integer | about 25 of 83 sort by a `Double`/`Float` (Pengler38, BrianNormant, mbacarella, lukaskollmer, jackadrianglass, Zenor27, bucsi, killertux, guillheu, ryoung786, claytonflesher, wisq, Philippus, bishabosha, arnemart, crinklywrappr, CodeFarmer, MrCrLr, junpls, damirarh, pillsgood, trajafri, …); the rest by `Int`, `Long` or `Nat` | squared distances reach 26,178,032,634 (35 bits); a float `sqrt` of a 35-bit integer is exact enough here, but it is a risk the Stitchwort `Nat` doesn't have **[checked]** |
| Ties between pairs | never handled; Haskell/Scala/OCaml `sort` is stable, so ties follow generation order (rolandtritsch says so); audioAXS (Python) says ties might matter | 0 repeated squared distances among 499,500 pairs **[checked: `sw/stats.py`]** |
| "1,000 connections" means pairs, not merges | at least 6 authors switch on input size (10 for the example, 1,000 otherwise): adomani (hard-coded `mdis`), bjornestol (`startsWith "162"`), merlinorg (`length == 20`), nikola-benes (`size <= 20`), b-valdez (`Sample`), bucsi (`take 10`) | after 1,000 pairs there are 287 circuits, so 713 merges and 287 "does nothing" pairs **[checked: `sw/stats.py`: 713 merges]** |
| Part 2: the answer is the pair that makes the last merge | all of them; BrianNormant stops at two circuits then looks for the closest crossing pair; the Prim ones use the heaviest tree edge | sorted index 6,203; 999 merges; answer 8,079,278,220 **[checked]** |

The example has 20 points and uses 10 pairs; `aoc/examples/` has no `day08.txt` yet (days 1 to
7 only) **[checked: `ls`]**, so the example text has to be added from the puzzle
statement. The expected answers on the example are 40 and 25,272 (adomani's `#assert`s,
glguy's doctest, sondresl, Pengler38) **[cited]**.

### 3.5 Proofs

Nobody proves the answer (§1, finding 1). What the community does have:

- **Types as the invariant:** jorendorff's `UnionFind n` with `Vector (Fin n) n` and `count : Fin (n + 1)`
  makes "indices in range" and "count within 0..n" free, the same move as day 7's `Vec`/`Fin`
  (its `find` is `partial def`, so termination, which is the hard part, is not proved). BrianNormant's
  `Fin n` and `natToFin` give the same bounds with a lot of `Maybe`.
- **Automatic provers on helper lemmas:** kim-em's `distSq_nonneg` is `nlinarith [sq_nonneg …]`
  (labelled "Proof by Aristotle"). The statements that matter (`generateEdges_spec`,
  `connectKShortest_processes_k`, `connectUntilOne_last_edge`) are `sorry`.
- **A Dafny union-find with a `Valid()` predicate:** `QuickUnion.Valid()` says the arrays
  have the right length and every parent is in bounds and every size is positive. It doesn't say
  the parent pointers have no cycle, so `findRoot` needs `decreases *`, Dafny's "may not terminate"
  marker. That is the same thing our termination checker would ask for, as fuel or a measure.
- **Executable checks beside the code:** `#assert part1 atest == 40`, doctests; our `test`s do this.

What a proof about day 8 would need to say, at its smallest: after joining the pairs `es`, two
points are in the same circuit exactly when the equivalence closure of `es` relates them; part 1
is the product of the three largest classes after the first 1,000 pairs; part 2 is the x
product of the first pair after which one class is left. Nobody states this. Tools it would need:
a closure relation (an inductive family: `Joined es i j` with `refl`, `edge`, `symm`, `trans`;
docs/proposals/indexed-families.md), a label or parent store whose `get` and `insert` are
characterised (our `Map` has `getInsert`, `getInsertOther`, `getInsertWith`), a proof that the
store is acyclic if it is a parent store (fuel for `find` or a `decreasing` measure), and
counting facts for the class sizes.

### 3.6 Library breadth

| Helper | Seen in | Stitchwort |
|---|---|---|
| All pairs `i < j` | `tails`, `combinations 2`, `choose 2`, `List.init … concat`, `Seq.combinations`, nested `for` loops, `Each` in a list monad (frutjus's `Monad List`) | `List.tails`, `List.flatMap`, `List.cross`, `Each.collect` with `each`/`require` **[checked: `B1.sw` builds 499,500 triples in 0.32 s with a recursion over `withIndex`]**; no `List.pairs` or `combinations` |
| Sort by key | `sortOn`, `sortBy (comparing …)`, `sort_by` | `List.sortBy cmp`, `Ord.compare`, `Nat.compare`; stable (comment at `Sort.sw:513`) with `sortBySorted`, `sortByPerm`, `sortLength` |
| Top 3 of a list of sizes | `sortOn Down`, `take 3`, `product` | `List.sortBy (a b => Nat.compare b a)`, `take`, `product`; `List.maximum` only gives one |
| Parent or label store | `IntMap`, `Map`, `HashMap`, `Hashtbl`, `Dict` | `Map k v` and `Set k` (balanced tree, `Ord`-keyed) |
| `partition`, `unions`, `disjoint` on sets | Haskell `Set`, Scala `Set` | `List.partition`; `Set.union`, `intersect`, `difference`; no `Set.unions`, `Set.disjoint`, `Set.partition` |
| `scanl`, `unfoldr`, lazy states | Haskell, Scala `Iterator.scanLeft` | `List.scanLeft` (strict: builds all states); `List.unfold` with a `decreasing` measure (`std/List/Unfold.sw`) |
| Union-find library | `Data.DisjointSet`, `Kruskal`, `unionFind` package, `disjoint_set` | none; the structure is 10 to 25 lines over a `Map` |
| Priority queue / heap | `Data.Heap`, `PriorityQueue`, `Pqueue`, `heap` | none |
| `Array` with O(1) get/set | OCaml `Array`, Lean `Array`/`Vector`, Haskell `IOVector` | none (SW-112, backlog) |

**[checked: by pattern and by reading `crates/elab/src/std/`]**

## 4. Side by side

The same kernel in four languages: join a pair into circuits.

```haskell
-- beefyhalo (Haskell): persistent union-find on an IntMap
find parent x = case M.lookup x parent of
  Just p | p /= x -> find parent p
  _ -> x
union parent a b
  | ra == rb = parent
  | otherwise = M.insert ra rb parent
  where ra = find parent a; rb = find parent b
```

```scala
// merlinorg (Scala 3): the whole circuit step, over a lazy stream of states
sorted.iterator.scanLeft(Set.empty[Set[Vec3]]): (circuits, pair) =>
  circuits.partition(pair.exists).swap.fold(_ + _.foldLeft(pair)(_ ++ _))
```

```lean
-- jorendorff (Lean 4): typed union-find over Vector (Fin n) n, threaded
structure UnionFind (n : Nat) where
  map : Vector (Fin n) n
  count : Fin (n + 1)
partial def UnionFind.find {n : Nat} (u : UnionFind n) (i : Fin n) : (UnionFind n × Fin n) :=
  if u.map[i] == i then (u, i)
  else let ⟨u, x⟩ := find u u.map[i]; (UnionFind.mk (u.map.set i x) u.count, x)
```

```
-- Stitchwort, scratch B4.sw: the same shape as beefyhalo's, over our Map (2.7 s for both parts)
def find (m: Map Nat Nat): Nat -> Nat -> Nat
  | Zero,   x => x
  | Succ f, x =>
    let p := Map.getOr x x m
    if p == x then x else find m f p

def union (n: Nat) (m: Map Nat Nat) (i: Nat) (j: Nat): Map Nat Nat :=
  let a := find m n i
  let b := find m n j
  if a == b then m else Map.insert a b m
```

The fuel `n` for `find` is the part the proof has to justify (a chain of parents is shorter than
n); beefyhalo and merlinorg need nothing of the kind because Haskell and Scala allow general
recursion. Stitchwort's `decreasing` (SW-199, stage 1) could take the place of the fuel, with the
same obligation **[inferred; not tried]**.

And the proof side, the nearest anyone got:

```lean
-- kim-em: statements about the answer, all sorry
theorem connectUntilOne_last_edge (points : Array Point) :
    points.size > 1 → ∃ edge, connectUntilOne points = some edge := by sorry

-- sdiehl: true by rfl, because Connected is defined as "same root"
def Connected (uf : UnionFind) (i j : Nat) : Prop := (uf.findRoot i).1 = (uf.findRoot j).1
theorem connected_refl (uf : UnionFind) (i : Nat) : Connected uf i i := rfl
```

## 5. Stitchwort today, per approach

### 5.1 What exists and what's missing

| Need | Exists today | Missing | Rough cost |
|---|---|---|---|
| Parse a point | `Text.split ','`, `Text.toNat`, `List.filterMap`, `Option.flatMap` | tuple patterns with `Some` after a comma (E-PARSE, §1 finding 9) | none: use `flatMap` |
| Squared distance | `Nat.absDiff`, `*`; `Nat` is unbounded (no 35-bit worry) | nothing | none |
| All pairs | `List.tails`, `List.flatMap`, `List.cross`, `Each`; `B1.sw`'s recursion | `List.pairs` (or `combinations 2`) with a length lemma `n(n-1)/2` if the proof wants it | small: 3 lines and one lemma (Hath995's Dafny spends about 100 lines on this: `RowCount`, `LemmaTotalSize`) |
| Sort 499,500 pairs | `List.sortBy` (stable), `sortBySorted`, `sortByPerm`, `sortLength`; 1.8 s | nothing for correctness | none |
| Partial sort / top-k | nothing | `List.takeSmallest k`, or a bounded insertion fold; a heap | medium; measured *slower* than sorting (§5.2); only worth it if a bigger input shows up |
| Circuit store | `Map`, `Set` with `get`/`insert` lemmas, `Map.map`, `Map.foldLeft`, `Map.values` | a `get` lemma for `Map.map`; a `get` lemma for `Map.fromList` | small each: the tree lemma `Map.Tree.mapWithin` is there for the order, not for `get` **[checked: `Map.sw`]** |
| Union-find | a 12-line `find`/`union` over `Map` (`B4.sw`) | the acyclic invariant for `find`'s fuel, or a measure | medium: an invariant that every chain ends within `n` steps, preserved by `insert root root'`; **[inferred]** 150 to 300 lines |
| Labels with relabel | `Map.map` relabel (`B6.sw`), 3.7 s | the `get`-after-`map` lemma; a members map for small-side relabel is optional | small to medium |
| Connectivity spec | inductive families exist (docs/proposals/indexed-families.md); `List.Perm`, `List.Sorted` as models | `Joined es i j` (closure), class sizes, "three largest" | medium; §6 |
| Graph, BFS | nothing | a graph library | large and not needed |
| `Array` (SW-112) | `Vec` is a linked list (O(n) access) | O(1) get/set | large; **not needed**: the `Map` versions run in under 4 s |
| Prim | `List.minBy`, `List.filter`, `List.map` | nothing | none: `B5b.sw` is 20 lines; 1.0 s |

### 5.2 Micro-benchmarks

All on `aoc/inputs/day08.txt` (1,000 points), `target/release/stitchwort run` unless marked, one run
each, wall-clock seconds, including about 0.15 s of start-up **[checked: scratch files in
`proj/src/`, `scripts/rb.sh`]**.

| File | What it runs | `run` | `run --js` | Result |
|---|---|---:|---:|---|
| `B1.sw` | build the 499,500 `(d², i, j)` triples and count them | 0.32 | 0.40 | 499,500 |
| `B2.sw` | build and `List.sortBy` all of them, print the 1,000th | **1.80** | 4.84 | `Some (65741882, (82, 130))`, same as Python |
| `B3.sw` | sort, then labels as a `List Nat` relabelled by `List.map` on each merge; parts 1 and 2 | **21.66** | not run | 42315 and 8079278220 |
| `B3a.sw` | the same, part 1 only | 9.75 | not run | 42315 |
| `B3i.sw` | the same, part 1's 1,000 joins only, no sizes | 9.60 | not run | |
| `B4.sw` | sort, then a parent `Map` (no compression), `find` with fuel `n`; both parts | **2.73** | 5.16 | 42315 and 8079278220 |
| `B6.sw` | sort, then labels in a `Map` relabelled with `Map.map`; both parts | **3.69** | not run | 42315 and 8079278220 |
| `B5a.sw` | part 1 without the full sort: a bounded sorted list of the 1,000 best, inserted into when a pair is below the current largest | 9.32 | not run | 42315 |
| `B5b.sw` | part 2 with Prim's algorithm over lists, no sort, no union-find | **0.99** | 0.59 | 8079278220 (heaviest tree edge 236,567,544) |

What this says:

- **Sorting all the pairs is cheap** (1.8 s of the 2.7 s in `B4`); the 12 to 15 s estimate in
  `docs/aoc-2025.md` was too pessimistic by about 7×, because that note predated the fast runtime
  **[checked: `docs/evaluator-speed.md` header: `run` now uses a separate machine]**. `run --js` is
  *slower* than `run` for sort-heavy code (4.84 s against 1.80 s), the opposite of the day 4
  finding.
- **A `Map` store is the right size of tool.** `B4` and `B6` do 1,000 and 6,204 pairs through a
  balanced tree in 0.9 to 1.9 s on top of the sort.
- **The label `List` is the trap.** `B3` takes 21.7 s, about 8× `B6`, though both do the same
  999 relabelling joins; `B3i` shows it's the 1,000 joins (9.6 s with the sort), not the sizes or
  the sort. The reason is **[unverified]**; my hypothesis is that `List.map` results are lazy thunks
  and each `getOr` walks the pending chain, so the cost per join grows with the number of joins before
  it. The practical consequence stands whatever the cause: don't write day 8 the way
  `docs/aoc-2025.md` "Plain approach" says (a label `List`).
- **A bounded insertion fold doesn't beat the sort** here (9.3 s against 1.8 s for the full sort),
  though it does O(n log k) comparisons; I did not find out where the time goes **[unverified]**.
  So "partial sort" is not a gap to fill for this input.
- **Prim for part 2 is the fastest correct program**: 1.0 s, no sort, no union-find, 1M distance
  evaluations on lists. But it proves a different statement (the heaviest edge of a spanning tree), so
  it is not what the puzzle says and doesn't help part 1.
- JS: sorting 499,500 pairs is 2.7× slower than `run`; `B5b` (no sort) is faster in JS (0.59 s). **[checked]**

### 5.3 Candidate list, ranked by value over effort

| Rank | Candidate | Kind | Value | Effort | Evidence |
|---|---|---|---|---|---|
| 1 | **Day 8 over `Map`: sort all pairs, fold into a label or parent `Map`, stop at one circuit** | program | the whole day; 2.7 to 3.7 s | small | §5.2 `B4`, `B6` |
| 2 | **`Map.map` `get` lemma** (and `Map.fromList`'s) for a label-map proof | library | enables the label proof | small | §5.1 |
| 3 | **`List.pairs` with `length = n(n-1)/2`** | library | day 9 also wants all pairs (`docs/aoc-2025.md` day 9 part 1, 122,000 pairs); Dafny's 100 lines are the cost avoided | small | §5.1 |
| 4 | **A connectivity specification `Joined`** (closure) and its label theorem | proof | the content of the proof | medium | §3.5, §6 |
| 5 | **Parent-store acyclicity** (for `B4`'s fuel) | proof | only if the parent `Map` is chosen | medium | §5.1 |
| 6 | `Set.partition`/`Set.unions`/`Set.disjoint` | library | the set-of-sets version, which is the community's most common shape, becomes a three-liner; no proof benefit | small | §3.6 |
| 7 | Tuple pattern with applications after a comma | parser | the E-PARSE in finding 9 | small, **[unverified]** cause | `Common.sw` |
| — | `Array` (SW-112), heap, partial sort, graph library, k-d tree | library | none needed for this day | large | §5.2 |
| — | Local mutable variables | language | none (D299 not now) | large | no change |

## 6. Recommendations for our day 8

**Approach.** Parse to a `List (Nat, Nat, Nat)` (or a record of three `Nat`s; the AoC shape is
`parse` / `solvePart1` / `solvePart2` on the parsed input). Take the number of pairs as a parameter
(`solvePart1 (k: Nat) points`, 1,000 in `main`, 10 in the example test). Build every pair `(d², i, j)`
with `i < j`, sort with `List.sortBy` on the key `(d², i, j)` (a total order, so ties are decided
and the proof need not appeal to the sort's stability). Fold the sorted list into a store of
circuits; part 1 stops after `k` pairs and takes the top three sizes; part 2 continues from the
same state until a counter of circuits reaches 1, and multiplies the x coordinates of that pair.
Do not use a `List` of labels (§5.2).

**Data structure.** Two candidates, both measured:

- **Labels in a `Map`** (`B6.sw`, 3.7 s): invariant is `label i == label j` iff joined; one lemma
  needed beyond what exists (`get` after `Map.map`). Simplest proof.
- **Parent `Map`** (`B4.sw`, 2.7 s, the persistent shape of beefyhalo): fastest, no new `Map`
  lemma (it uses only `get` and `insert`), but the proof needs the acyclic invariant for the fuel.

I would take the labels `Map` for the first version and keep the parent `Map` in reserve **[my
choice, not measured on proofs]**. An `Array` would be nicer but nothing here needs it.

**Proof spec.** Over the parsed points (no text), for every list of points, every `k`, every
tie-free or tie-broken order given by the key:

1. `Joined es i j` (equivalence closure of the pairs `es`, an inductive family).
2. Lemma: after folding `es`, `label i = label j ↔ Joined es i j` (and the counter equals the
   number of classes).
3. `part1Correct`: the answer is the product of the three largest class sizes of `Joined
   (take k sorted)`; `part2Correct`: the pair returned is the first in `sorted` after which one
   class is left, and its x product.

Smaller alternatives: (A) refine to the naive label-vector model (the program equals a simple
`List`-label function; shorter, but then "the naive one is right" is itself unproved), (C) prove only
counting facts (each real join lowers the count by one; part 2 stops when it reaches 1; about 50
to 100 lines, `docs/aoc-2025.md`'s "worth proving" list). Rough sizes **[inferred, not tried]**: C
50–100 lines, A 100–200, the full spec above 250–450; day 7's part 1 took 387 and part 2 69.

**Decisions for Matt**

| ID | Decision | Recommendation |
|---|---|---|
| D537 | Day 8 program shape: sort all 499,500 pairs by `(d², i, j)` and fold into a `Map` (labels, or parent pointers), part 2 by continuing the same fold; no `Array`, no heap, no partial sort, no Prim. | [yes; labels `Map` first, parent `Map` in reserve] |
| D538 | Proof spec level: the full connectivity spec (`Joined` closure, label theorem, `part1Correct`, `part2Correct`), against the cheaper counting-only version (C) or the refinement to a naive model (A). And ties: break them by `(d², i, j)` in the spec, and count a "connection" inside one circuit as one of the `k`. | [full spec, ties by `(d², i, j)`; start with C as a stage if the full one slips] |
| D539 | Library additions with the day: `List.pairs` (with `length = n(n-1)/2`) and the `Map.map`/`Map.fromList` `get` lemmas; leave `Set.partition`/`unions`/`disjoint`, `Array` (SW-112), heaps and graph code for later. Also add `aoc/examples/day08.txt` (the 20-point example, expected 40 and 25,272). | [yes] |

---

**Status** (short form, 22 October 2026): D537 program shape, pending; D538 proof spec level and
ties, pending; D539 `List.pairs` and `Map.map` lemma, pending. SW-308 (this note) done once
reviewed; the day 8 program, proof and gap analysis come after. Unchanged by day 8: SW-112 `Array`
backlog, SW-199 `decreasing` (stage 1 built), SW-235 list batch 2 (parked), D299 local mutable
variables not now.
