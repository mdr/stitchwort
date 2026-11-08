# Why dijkstra and disk are 14x and 7.8x CPython

SW-2369, Sonnet, 8 November 2026. Measurement study: no product code changed,
nothing from the experiments committed. Tools: `task profile:native --
dijkstra disk` (samply, `--group`, call counts, per-definition entry counts,
SW-2331), stage-by-stage variants of the AoC programs built with `stitchwort
build --native`, and instrumented copies of the Python ports. Numbers marked
**[measured]** come from a run or a count; **[estimated]** ones say how.

**Machine and noise.** These runs were on the agent user's Mac while other
lanes built, so absolute times are about half the Overmind headline's
(dijkstra native 5.5 s here against 11.8 s; CPython 0.50 s against 0.84 s;
disk 8.5 s against 17.5 s, CPython 1.19 s against 2.24 s). The ratios agree
(11x here, 14x there; 7.1x and 7.8x), so the shares below carry over.
Stage times are `user` seconds, good to about 10% on this loaded machine.

## Summary

- **dijkstra** is a different, heavier algorithm run on a slower structure.
  Stitchwort calls std's verified `Graph.distances`, which pushes every
  edge into a tree-`Set` queue without asking whether it improves the cost,
  and keeps the finished costs in a tree `Map` it consults once per pop.
  Python pushes only improvements, into a C heap, and a dict. Counted on
  the real input: the queue sees **1.04 M pushes and 956 k pops** in
  Stitchwort, **260 k and 260 k** in Python (4x the queue traffic; 696 k
  of the pops are stale). Each queue or table operation is then 12-19
  comparisons and a path copy of an immutable balanced tree.
  A Lean-shaped formulation in Stitchwort (improvement-only pushes, an
  `Array` of costs, one packed `Nat` key) runs the same input in **0.86 s
  instead of 5.5 s [measured]**, within 1.7x of CPython.
- **disk** is 47% parsing, which Python and Lean do not do the same way.
  Parsing 900,000 digits through `Std.Parse` takes 3.9 s (28 effect steps
  per digit); `text.toList.map` takes about 0.1 s, and the program is then
  **4.4 s instead of 8.3 s [measured]**. The other half is the file-moving
  loop and list passes, where Stitchwort does the same work as Lean but
  with immutable-tree updates and about 5 allocations per element.
- Cross-cutting in both: allocating and freeing. Memory management is
  **33% of dijkstra's self time and 53% of disk's [measured]**.

## 1. dijkstra (2021 day 15)

Input: the real 100x100 map (part 1) and its 500x500 tiling (part 2), so
260,000 positions in all.

### 1.1 Top 5 costs

Self-time shares from the samply profile (5,770 samples); they do not
overlap. Counts are from `--count-bodies` and `call-counts` runs.

| # | Cost | Self time | Counts | What it is |
|---|---|---:|---|---|
| 1 | `Std.Map.Tree` work: `insertWith` 7.6, `shape` 5.7, `rebuild` 5.0, `get` 3.4, `minView` 2.9 | 24.6% (the `Std.Map.*` group: 65% inclusive) | 17.5 M insert steps, 8.6 M `minView` steps, 18.1 M `get` steps; 25.0 M `shape` + `rebuild` | Walking and re-balancing the tree: a path copy per insert or pop. |
| 2 | Freeing: `value::free` 8.4, `drop_glue` 5.8, `Fields::drop` 4.1, `Rc::drop_slow` 1.7, `take_children` 1.6 | 21.6% (`sw_drop_words` 27.6% inclusive) | 40.4 M cells allocated, 12.1 M `sw_drop_words`, 6.7 M `sw_cell_free`; only 1.9 M `sw_ctor_reuse` | The old path of each tree is freed node by node after every update. |
| 3 | Comparing keys: `Position.%compare` 9.5, `Pair.compareWith` 3.0 + `/value` 2.1, `Nat.compare` 1.8, `Position.%compare/value` 1.7 | 18.1% | 35.6 M `Position.%compare`; 12.35 M `Pair.compareWith` (each calls `Nat.compare`, and on a tie `Position.%compare`) | Position keys in the settled `Map`; `(cost, position)` pairs in the queue, compared through a closure for the second component. |
| 4 | Allocator: `mi_free` 4.5, `mi_malloc_aligned` 4.4, `_mi_malloc_generic` 1.2, `mi_theap_malloc…` 0.9, `mi_page_queue_find_free_ex` 0.7 | 11.7% | the 40.4 M cells above | mimalloc behind each `sw_cell_new`. |
| 5 | Closure plumbing: `sw_apply_prepare` 2.7, `apply2` 2.6 (shared with the edge lambdas) | 5.3% | 14.5 M `sw_apply_cached`, 14.5 M `sw_apply_prepare` (14.3 M the partial-application fast path), 9.4 M `sw_closure`, 4.3 M `sw_pap` | Calling `compareWith`'s argument comparers as function values. |

Together 81%. `sw_prim` is gone (410 calls) since SW-2328/SW-2329, so the
earlier "26% in `sw_drop_words`" is still true (27.6% now) and the
"Position/Pair compare about 18%" is unchanged (18.1% now): tonight's fixes
did not touch this program's costs much (13.0 s to 11.8 s).

### 1.2 The algorithm, against Python and Lean

| | Stitchwort (`Graph.distances`) | Python | Lean |
|---|---|---|---|
| Queue | `Set (Nat, Position)`, a balanced tree, path-copied | `heapq` of `(risk, row, column)` tuples, C code | `TreeSet Nat`, key `distance * size + position`, in-place when unique |
| Costs so far | `Map Position Nat` (tree, keyed by a two-field record) | `dict` keyed by `(row, column)` | `Array Nat` indexed by position |
| Push rule | every edge of a settled state, always | only if the new cost is lower than the dict's | only if lower than the array's |
| Pop rule | `settled.contains state` on each pop (19 comparisons) | `risk > cost[...]` dict lookup | `cost > distance[here]` array read |
| Pushes / pops | **1,037,600 / 956,211** (696 k stale) | **259,998 / 259,997** (0 stale) | same as Python |
| Edge enumeration | `Position.neighbours.filterMap` plus `boxEnter` and a graph-edge list per state | four tuples | four `Option`s |

Counts for Stitchwort are from `insertWith`/`searchFrom` entries (1,297,604
`pushEdges` entries include 260 k terminal calls); Python's from an
instrumented copy of `bench/compare/dijkstra/main.py` run on the real input.

Per pop the native program does: 1.1 queue inserts at about 12 levels each
(12.35 M compares through `Pair.compareWith`), one `minView` of about 9
levels (8.55 M), one `settled.contains` of about 19 levels (18.1 M), and a
settled insert of about 17 levels on the 260 k fresh pops. That is 44 M
tree steps, each allocating a node through `shape` + `rebuild` on the
write paths (25.0 M rebuilds). Python does 260 k heap pushes and pops in C
(about 18 comparisons each) and 520 k dict operations.

So it is both: **more work** (4x the queue operations, an extra table lookup
per pop) **and the same kind of work done more slowly** (a path copy and
free per tree step, comparisons through closures).

### 1.3 What each part is worth (experiments)

Scratch copies of Day 15 with the search written by hand (the answers
match: 656 and 2979); wall times on the same loaded machine, one run each,
the baseline the stock program's 5.49 s:

| Variant | Queue | Costs | Pushes | Time | vs baseline |
|---|---|---|---|---|---:|
| baseline: `Graph.distances` | `Set (Nat, Position)` | `Map` (settled) | every edge | 5.49 s | 1.0x |
| E5 | `Set (Nat, Position)` | `Map Position Nat` | improvements | 2.47 s | 2.2x |
| E4 | `Set Nat`, packed key | `Map Position Nat` | improvements | 2.10 s | 2.6x |
| E3 | `Set (Nat, Position)` | `Array Nat` | improvements | 1.19 s | 4.6x |
| E1 | `Set Nat`, packed key | `Array Nat` | improvements | 0.86 s | **6.4x** |
| CPython | heap | dict | improvements | 0.50 s | |
| Lean (Overmind) | `TreeSet Nat` | `Array` | improvements | 0.20 s (Overmind) | |

Reading it:
- **Improvement-only pushes plus a cost table consulted once per edge**
  (baseline to E5): 5.5 s to 2.5 s. This is the largest single step and it
  is algorithmic.
- **Dense `Array` costs instead of a tree `Map`** (E5 to E3): 2.5 s to
  1.2 s.
- **A packed `Nat` key instead of a `(Nat, Position)` pair** (E3 to E1):
  1.2 s to 0.86 s, 28%: the cost of comparing through `Pair.compareWith`
  and `Position.%compare`.
- The remaining distance from E1 to Lean (4x, 0.86 s against 0.2 s) is the
  runtime: Lean's tree updates in place, with unboxed scalars. That is the
  memory-management cost (rows 2 and 4 above) and the per-node work.

### 1.4 Fixes

Estimated gains are on the 5.5 s baseline. "Estimated" gains say how.

| # | Fix | Gain | How estimated | Who |
|---|---|---:|---|---|
| 1 | **A cheaper `Graph.distances`**: push an edge only if it beats the best cost known for its target, which means keeping a best-so-far table beside the settled one (or testing the target against `settled` and the queue's best); and a variant `Graph.distancesIndexed` for states with a dense index (grid positions) that keeps costs in an `Array`. Both stay inside the verified spec (`Graph.SearchResult`); the proofs of `searchFrom` change. | 5.5 s to about 1.2-2.5 s (2.2x for the push rule alone, 4.6x with an `Array`) | **[measured]** E5 and E3: same algorithm written by hand in the scratch copies | Opus (changes the proof of the search: soundness, termination measure `unsettledIn`) |
| 2 | **Or: an AoC-local formulation** like E1 for Day 15, with its own proof | 5.5 s to 0.86 s (6.4x) | **[measured]** E1 | Sonnet, but it drops the reuse of std's proven search; the proofs in `Aoc.Year2021.Day15.Proofs` would need rewriting (see §3 fairness) |
| 3 | **Reuse the dead node in `Map.Tree` rebuilds.** `sw_ctor_reuse` fires 1.9 M times against 25 M `rebuild`/`shape` node rebuilds and 40.4 M cell allocations; a unique `Bin` being rebuilt on the way back up the recursion should reuse its cell, which removes the free (row 2) and the malloc (row 4) for those. Check why reuse does not fire in `balance`/`rebuild` (the old node is matched, then the recursive call intervenes: a drop-reuse token has to survive the call). | about 15-20% | **[estimated]** rows 2 and 4 are 33% of self time; if 60-70% of the 25 M node rebuilds reuse their cell, about half of that goes, discounted for the work reuse itself adds | Opus (compiler reuse analysis, near the native ABI) |
| 4 | **Compare `Position` and pairs without closures**: specialise `Pair.compareWith` for known component orders (SW-2135 widened to dictionaries), so the queue key compare is one inlined `Nat` compare then one inlined `Position` compare. | about 10% | **[estimated]** row 3 plus part of row 5 is 23% of self time; E3 to E1 (removing the pair compare entirely) is 28%; inlining removes the closure calls (row 5 and `compareWith`'s 5.1%) but keeps the compares themselves, so about a third to a half of that | Sonnet (SW-2135 already on the board; Opus if it touches core/unifier) |
| 5 | **A heap in std** (`Std.Heap`, pairing or leftist: O(1) insert, no re-balancing) as the queue of `Graph.distances` and for priority queues in AoC generally. | about 15-20% on top of fix 1's gain | **[estimated]** queue-related tree steps are 20.9 M of the 44.2 M (47%) at 65% inclusive for `Std.Map.*`, so about 1.7 s; a pairing heap does a constant-work insert and a pop of about log n cheap merges, assume 60% of that saved | Opus for the proofs (heap spec, `popMin` termination), Sonnet for the implementation after a design note |
| 6 | Early exit at the target (Python returns on reaching it): nothing to gain here, since the target is the last position popped (260 k of 260 k pops). | none | **[measured]** Python's pops equal the position count | |

Gains do not add: fix 1 removes the stale traffic that fixes 3-5 would
otherwise speed up. Ranked by gain: 2 (6.4x, but weakens the verified
story) or 1 (2.2-4.6x, keeps it), then 3, 5, 4.

## 2. disk (2024 day 9)

Input: the real disk map repeated 45 times, **899,999 digits, 450,000
files**.

### 2.1 Top 5 costs

Stages timed by building the program with `main` cut down after each stage
(`user` seconds on the loaded machine; the stages sum to 8.3 s, the full
program's 8.3 s). Python's stage times for the same input are alongside.

| # | Cost | Time | Share | Python | Counts |
|---|---|---:|---:|---:|---|
| 1 | **Parsing the digits** with `Std.Parse` (`many1 (digit().toNat)`) | 3.9 s | 47% | 0.06 s (`[int(d) for d in text]`) | 25.2 M `sw_eff_step` (28 per digit), 26.1 M `sw_apply_prepare`, 31.5 M `sw_apply_cached`, 20.3 M closures, 9.9 M continuations pushed, 4.5 M `Std.Parse.%elim` and 4.5 M `handlePlus` |
| 2 | **The file-moving loop** of part 2 (`mapAccumLeft … FreeSpace.moveFile`: `leftmostFit`, `remove`, `add`) | 2.2 s | 27% | 0.54 s with layout and `FreeSpace` build | 4.05 M `leftmostFit` lambda calls (450 k files x 9 lengths); 30.4 M `Map.Tree.minOr` steps; 11.7 M `rebuild`/`shape`; 9.8 M `insertWith` steps; 14.3 M `Nat.compare` |
| 3 | **Layout and building `FreeSpace`** (`layoutFrom`, `joinTouching`, `FreeSpace.of`) | 1.05 s (0.57 + 0.48) | 13% | included in the 0.54 s | 450 k spans folded one at a time into a `Map Nat (Set Nat)`; `layoutFrom` allocates a pair and two cells per file |
| 4 | **Part 1's list passes** (`blocksFrom`, `fileBlocks`, `fillFront`, `withIndex.sumBy`) | 0.8 s | 10% | 0.45 s | 7.2 M `replicate` cells, 6.5 M and 4.25 M checksum lambda calls, 5.2 M `Fin.ofNatLt`/`toNat` pairs (over 5 passes of a 4.5 M-element list) |
| 5 | **Part 2's checksum** (`File.checksum`: `rangeFrom … sumBy`) | 0.15 s | 2% | 0.09 s | 2.2 M `File.checksum` lambdas |

Cross-cutting, from the profile (13,993 samples): the allocator is 31.4% of
self time (`mi_malloc_aligned` 10.0, `mi_free` 9.6), dropping another 21.5%
(`value::free` 6.2, `drop_glue` 6.1, `Fields::drop` 4.9, `Rc::drop_slow`
2.3, `take_children` 2.0), with 127 M `sw_cell_new`, 66 M `sw_drop_words` and
32 M `sw_cell_free` over the run. `sw_apply_prepare` alone is 7.5%: that is
the parser.

Against SW-2296: it called `parseDiskMap` 39% inclusive and `compactFiles`
35%. The inclusive profile cannot split them: the parse handler's
continuation runs the rest of `main` from `rt_loop`, so `parseDiskMap` now
shows 63% inclusive and `compactFiles` 24.7%. The stage builds above are the
reliable split.

### 2.2 The algorithm, against Python and Lean

| | Stitchwort | Python | Lean |
|---|---|---|---|
| Parse | `Std.Parse`: parser combinators on effects | `[int(d) for d in text]` | `toList.toArray.map` |
| Part 1 | lists of `Block`; replicate, filterMap, fillFront, withIndex | list of ids; comprehension, slice | `Array (Option Nat)`, one loop with a counter |
| Free spans | `Map Nat (Set Nat)`: length to set of starts, persistent | `dict` of `heapq` heaps, O(1) peek of the smallest start | `TreeMap Nat (TreeSet Nat)` |
| `leftmostFit` | `toList`, `filterMap`, `minBy`, `filter` (4 lists per file) | loop over the dict's 9 items, `starts[0]` | `foldl` over the map, `min?` |
| Part 2 checksum | `rangeFrom … sumBy`, one list per file | `sum(range(...))`, in C | inner loop |

The algorithm is the same as Lean's. The differences: (a) the parser, a
different technique; (b) Python's O(1) heap peek against the set's `min`
(a walk down the left spine, 7.5 steps per call on average); (c)
allocation: lists where the ports use loops and arrays.

Part 2 beyond parsing is about 3.4 s against Python's 0.63 s (5.4x); part 1
is 1.8x; parsing is 65x.

### 2.3 What each part is worth (experiments)

| Variant | User time | Notes |
|---|---:|---|
| baseline | 8.3 s | |
| parse by `input.trim.toList.map (c => c.digitValue.getOrElse 0)` | 4.4 s | **[measured]**, same answers; parse cost falls from 3.9 s to about 0.1 s |
| `leftmostFit` by `Map.foldLeft` and `Set.min`, no intermediate lists | 4.25 s (from 4.4) | **[measured]**, about 4% of the total: the list building is not the cost |

### 2.4 Fixes

| # | Fix | Gain | How estimated | Who |
|---|---|---:|---|---|
| 1 | **Make `Std.Parse` cheap** (docs/proposals/parse-runtime.md; operations in place, docs/proposals/operations-in-place.md stages B-D): 28 effect steps and 29 `apply_prepare` calls per character. This is the cost behind expressions, scan and bridge too. | disk 8.3 s to about 4.4 s if parsing cost reached `text.toList.map`'s; realistically half of the 3.9 s | **[measured]** for the bound (variant above); the share a runtime fix recovers is **[estimated]** | Opus (already the design the board holds) |
| 2 | **Parse by characters in Day 9** (the formulation above). It is a one-line change; the cost is that the day then no longer demonstrates `Std.Parse`, and whatever the Day 9 proofs say about `diskMapLine` (read in `Aoc.Year2024.Day09.Proofs`) needs a restatement. | 8.3 s to 4.4 s (1.9x) | **[measured]** | Sonnet; needs Matt's view on the fairness note in §3 |
| 3 | **A faster `FreeSpace`**: build from the sorted spans in one pass (a `Set.fromSortedList` or grouping by length) instead of 450 k single inserts, and keep the minimum start per length cached (or a heap per length as the Python port does). | 0.5-0.8 s (6-10%) | **[estimated]** from the stage times: `FreeSpace.of` is 0.48 s, of which about 70% is the repeated insert path; the move loop's tree steps (11.7 M rebuilds, 9.8 M inserts) are about half of its 2.2 s and a heap or cached minimum removes about half of those | Sonnet |
| 4 | **Reuse in tree rebuilds and fewer short-lived lists** (same as dijkstra fix 3, plus the cell allocator of docs/proposals/cell-allocator.md): allocation and dropping are 53% of self time. | 10-15% | **[estimated]** from the 25.5% `mi_` and 21.5% drop share, discounting a third for work that has to stay | Opus |
| 5 | Part 1 as a counter loop over an `Array` (as the Lean port), part 2's checksum as an arithmetic series (`Nat.sumRange`-style lemma in std). | 0.3-0.5 s (4-6%) | **[estimated]** stage times 0.8 s + 0.15 s, assume half saved | Sonnet; an arithmetic-series lemma belongs in std |

Ranked by gain: 1/2 (up to 1.9x), 4 (10-15%), 3 (6-10%), 5 (4-6%).

## 3. The fairness rule (D3342, natural data structures)

Things Matt may want to rule on, since the speed comparison is affected:

1. **dijkstra compares a verified generic search with hand-written specialised
   loops.** The Stitchwort day calls std's `Graph.distances`, whose
   algorithm is chosen for provability: generic over the state type, pushes
   every edge, tree `Set` and `Map`. Python's and Lean's ports are written
   for speed: an improvement test, a dense array (Lean) or a hash dict
   (Python), a packed key (Lean). In E1 the Stitchwort program written the
   Lean way is 6.4x faster and within 1.7x of CPython. Stitchwort has no hash
   map in std and no heap, so "the natural structure" for its Python-style
   code does not exist yet; `Array` is the natural structure Lean uses.
   Options: keep the day as is and label it "the verified std search";
   write the day Lean's way; or give std the indexed search of fix 1 and
   keep the verified story.
2. **disk's ports do not parse.** Python and Lean convert characters
   directly; Stitchwort's day uses the parser combinators it showcases, and
   the 900,000-digit scaled input (a 45x repeat) makes the parse 47% of the
   run. If the comparison is meant to isolate the algorithm, the parse
   belongs in neither or in all three; if it is meant to measure the
   languages' idiomatic programs, it stays and the parse runtime is the
   thing to fix (disk fix 1).
3. **The Python port's `FreeSpace` uses `heapq` per length**, an O(1) peek
   that Lean's and Stitchwort's ordered sets do not have; Lean's ordered
   set plays the same part as Stitchwort's (`TreeSet`), so Stitchwort and
   Lean are comparable there, Python slightly favoured.
4. Smaller: Python returns at the target in dijkstra (no effect here, the
   target is the last pop); Lean's loop drains the whole queue; the disk
   Python checksum is `sum(range(...))` in C.

## 4. Commands run

- `nix develop -c task profile:native -- dijkstra disk --top 25` (71 s
  including the builds), then `python3 dev/profile_top.py
  target/profile/{dijkstra,disk}.json.gz --group … --focus …` on the saved
  profiles.
- `stitchwort build --native` of scratch copies (in the lane's scratchpad
  and, for the Day 15 variants, a temporary `aoc/src/Aoc/Scratch/`
  directory, deleted): disk with `main` cut after parse, part 1, part 2,
  layout, `FreeSpace.of` and `compactFiles`; disk with a text-list parse;
  disk with a fold-based `leftmostFit`; Day 15 with the four search
  variants E1, E3, E4, E5.
- `python3 bench/compare/{disk,dijkstra}/main.py` on the committed inputs
  (plus stage timing and push/pop counts from copies).
- The Lean ports were read, not run (no `lake` on this user's PATH); their
  times are Overmind's from docs/reviews/SW-2295-comparative-speed.md.

## 5. Findings worth filing

- A std search with an improvement test and an indexed variant (dijkstra
  fix 1).
- `sw_ctor_reuse` is 1.9 M against 25 M tree-node rebuilds in `Map.Tree`:
  find out why reuse does not fire in `balance`/`rebuild`.
- `Std.Heap`.
- `Std.Parse` in disk: the profile shows a 28-step effect chain per digit
  (parser fix, already known).
- `profile_top.py`: inclusive time under an effect handler is
  uninterpretable (`parseDiskMap` is 63% inclusive because the handler
  runs the rest of `main`); a note in the tool's output, or the
  handler-installing-definition idea from SW-2296 §3.
