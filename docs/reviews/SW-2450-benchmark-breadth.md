# Benchmark breadth: are we fitting the ten, and what to add (SW-2450)

Paper lane, Opus, 8 Nov 2026, against `main` at `c6ee547a3`. Nothing was built, run or
timed. Claims are marked **[read]** (this repository, or another project's source read
for this note), **[measured earlier]** (a number another report recorded, with where),
**[web]** (read on the web, with the link) and **[inferred]** or **[estimated]** (my
reasoning, not tested).

Matt, 8 Nov 2026: "I don't want us to over optimize on a fixed set of particular
benchmarks. Maybe there are other benchmarks we should be considering as well ... it
would be good to get a bit closer to Lean's performance on the runtime."

## Summary for Matt

**The problem.** Since last night, about 25 speed changes have taken native code from 23×
to 11.7× Lean's time on the ten comparison programs **[measured earlier,
SW-2295]**. Most of those changes are general: they help any program with that shape.
But the ten decide *which* shapes get work. Three of them (the parsers expressions and
scan, binary-trees, dijkstra) drove about two thirds of tonight's merges. Three changes
rewrote the benchmarked AoC days themselves. Some kinds of program that users will write
aren't in the set at all: floating point, bit operations, in-place arrays beyond one
big table, effects other than the parser's, and multishot choice (`Each`). One design
gate is exposed by this. Compact values' option A passes its "boxed floats are rare"
test only because no decision program uses floats.

**The change.** Add eight programs as a second, "wide" set beside the ten: five from
Lean's and the Benchmarks Game's suites, plus one each for effects, text with hash maps,
and floats. They are spectral-norm, const_fold, fannkuch-redux, rbmap (with its
checkpoint variant), deriv, unionfind, k-nucleotide and an `Each` n-queens. Report three
geometric means: the original ten (unchanged, so the history line goes on), the eight
new ones, and all eighteen. Separately, time every AoC day natively, by instruction
count, so a change's effect outside the benchmark programs shows. Widen compact values'
decision set before its gate is rerun. Rerun the wide set every five speed merges and
before every design gate.

**What it should do.** It would catch over-fitting directly: a change that moves only
the program it was tuned on shows as a core-only gain. It would put Lean's own home
ground in the table. const_fold, deriv, rbmap and binarytrees are the programs Lean's
reference-counting paper was tuned on, so "closer to Lean" would be judged where Lean
is strongest. It would also give the float and array work a measurement before anyone
designs it. Porting cost **[estimated]**: about 8–10 Sonnet lane-hours for all eight
in three languages, done as four lanes of two programs each. Adding them to an
Overmind run should cost about 10–15 more minutes on top of today's 28.

## 1. Over-fitting check

### 1.1 Today's speed changes, one by one

Each change is from `git log --merges` since 7 Nov 23:00 (81 merges, about 30 of them
about speed). I sort them by whether the mechanism is general or fitted to one of the
ten. There is a second question: was it *chosen* because one of the ten showed it? That
is where fitting really happens.

**General mechanism (helps every program with the pattern)** **[read: merge titles and
diffs]**:

| Change | Mechanism | Chosen because of | Who else benefits |
|---|---|---|---|
| SW-2302 | big-number arithmetic borrows operands | pidigits | any program with numbers past 64 bits. No AoC day has them, so in practice only pidigits |
| SW-2323 | `List.flatMap` in one pass (std) | matcher | 27 AoC days call `flatMap` **[read: grep]** |
| SW-2328 | native list-building holes inline | matcher | every native program that builds lists front to back |
| SW-2329 | native comparisons as values; `Array.getOr`/`set` inline | memory-game | comparisons: all. Arrays: only 2020 day 15 uses `Array` in `aoc/` **[read: grep]**, so the array half is measured on one program |
| SW-2321, SW-2362, SW-2363, SW-2440, SW-2443 | fixed-size cell helpers, mimalloc entry points, per-run cell cache, strong-count-only uniqueness, freeing shallow cells | binary-trees | every allocating program: −2% on the others for the cell cache (SW-2363), −1 to −2% for the rest **[measured earlier, merge titles]** |
| SW-2349, SW-2433 | operations in place stage B (forwarding clauses skipped), one shared `JumpK` | expressions, scan | every program that runs handlers. bridge moved 1.13× too. But no program in the ten runs a handler other than `Parse`, `Fail` and `IO` |
| SW-2337 | `Std.Parse` keeps expected problems unformatted | scan, expressions | 65 of the 71 AoC days parse with `Std.Parse` **[read: grep]**, though on the real inputs parsing is rarely their main cost **[inferred]** |
| SW-2336 | apply fast paths | expressions, scan | every program calling unknown functions |
| SW-2388, SW-2391 | last read is a move; reuse across calls | dijkstra | every program that rebuilds `Map`s or trees |
| SW-2405 | `f x + n` recursion as loops carrying the sum | octopus | 12 std and 10 aoc functions, per the merge |
| SW-2415, SW-2398, SW-2399 | determined fields not stored; `Fin` as machine numbers | (measured on 2025 day 3, 2021 day 9) | indexed types. **The only speed work tonight measured outside the ten.** |
| SW-2370, SW-2376, SW-2382 | `Graph.distances` queues only improvements; `reachable` by BFS; search takes the popped pair (std) | dijkstra | real complexity fixes in std, used by 2021 day 15, 2024 days 1 and 16, and `Graph` users 2020 day 7, 2021 day 9, 2024 day 18 **[read: grep]** |

**Fitted to one of the ten (the benchmark program or an API only it uses)** **[read:
diffs]**:

| Change | What changed | Assessment |
|---|---|---|
| SW-2320 (octopus −68% time) | 2021 day 11 itself: a lookup table per round, neighbours counted without lists. New `Grid.lookupOr` / `countAround` in `Aoc.Common`, with lemmas | Fair as a program: Python's port already indexes a 2-D list in O(1), so the day now does what the ports do. But the 3× gain is the program, not the compiler. A user's grid day written the old way (`at.around.count flashed.has`) is as slow as before. |
| SW-2374 (disk −3%) | 2024 day 9: checksum as a counter fold (part 1) and by Gauss's rule (part 2) | Part 2 now uses a different algorithm from the Python port, which still sums the range (`bench/compare/disk/main.py:109`). The effect is small, since file lengths are at most 9. Part 1's rewrite works around `withIndex` plus `sumBy`, which allocate a pair per cell, instead of making that pattern cheap. |
| SW-2394, SW-2396 (dijkstra −57% instructions) | a cost-table API in std (`Graph.Costs`, `distancesWith`, `Graph.Index`), and day 15 passes a grid index | The API is general, but only the benchmarked day uses it. 2024 day 16 (Reindeer Maze) and 2024 day 18 are also grid searches and still take the `Map` path **[read: grep for `index :=`]**. |

**What it adds up to.** No change was a trick that only works on its benchmark. Every
compiler and runtime change is a general mechanism with tests of its own. But:

- Three of the twelve AoC-side gains came from rewriting the measured program, and the
  table can't tell those apart from compiler gains. octopus's 15.9 → 5.1 s was the
  program, not the compiler. The history line mixes the two.
- The *priority order* was set entirely by the ten. Counting today's merge titles by
  the program they name or measure **[read: rough, the topics overlap]**: parsers and
  effects 15, binary-trees and allocation 13, dijkstra, `Graph` and reuse 12, disk 6,
  octopus 4, matcher 4, memory-game 3, bridge 2, pidigits 1.
- **Only one piece of tonight's speed work was measured on a program outside the ten** (the
  `Fin` pair, SW-2398 and SW-2399). Nothing checks whether the other changes moved
  other AoC days, slowed them, or did nothing. The ticket asked for that check. It
  needs runs, so §3.4 proposes the sweep that would make it routine.

### 1.2 Which of the ten dominate decisions

- **expressions and scan** together carry about a third of the log-sum of the native /
  Lean ratio (75× and 77× of a geomean of 11.7× on the latest run; ln 75 + ln 77 = 8.7
  of the ten's total 24.6, about 35% from two of ten programs) **[derived from
  SW-2295's latest table]**. The headline geomean moves most when they move. That is
  why the effect runtime got the most work. Both measure the same thing (`Std.Parse`'s
  effect machinery on text), so in effect it counts twice.
- **binary-trees** is the only program where memory and allocation show cleanly. So it
  was given its own threshold in compact values' gate (1.25×, `compact-values.md` §5),
  which makes one 30-line microbenchmark a veto on a 10–16 hour design.
- **dijkstra** set the morning's agenda (twelve merges). It is now 13× Lean, near the
  median, so it will matter less from here.
- bridge, matcher, disk, octopus and memory-game have had little attention of their
  own. pidigits is already ahead of Lean.

### 1.3 Patterns the ten miss

Checked against what the ten actually do **[read: `programs.toml`, the ports, std]**:

| Pattern | In the ten? | Why it matters | What the language has today |
|---|---|---|---|
| **Floating point** | none | physics, geometry and statistics; compact values' option A boxes floats; the ten can't see a float slowdown | `Float` with `+ - * / floor` as natives. **No `sqrt`** (nor `sin`, `exp`, `pow`). A `Float` is a tagged three-word value in native code (`TAG_FLOAT`, `n1.rs:3534`), and arithmetic seems to go through the runtime's natives, not inline instructions **[read; not traced]** |
| **Bit operations** | none | hashing, PRNGs, bitsets, puzzles (2020 day 14, 2024 days 17, 22 and 24, 2025 day 7 use them) | `Nat.xor/and/or/shiftLeft/shiftRight` are recursive definitions, one step per bit. About 4.3 µs per XOR **[measured earlier, `aoc/NOTES-2024.md` day 22]**; SW-2010 backlog. Likely the single largest gap per operation in the language **[inferred]** |
| **Arrays updated in place, many small ones** | memory-game only (one 30M-entry table) | sorting, permutations, dynamic programming | `Array` with O(1) `get/set/swap` when unshared (`std/Array/Array.sw`). Inline in native only for `getOr`/`set` (SW-2329) |
| **Strings and text processing** | scan (per-character scanning through `Parse`) | splitting, building and comparing strings, hashing substrings | `Text` natives for length, take, drop, split, join, compare (`natives.rs` `TextNative`). Never measured outside `Parse` |
| **Maps and sets at scale, non-`Nat` keys** | memory-game (`Nat` keys, really an array now), dijkstra (now an array), octopus (`Map` of positions) | Python's `dict` of tuples or strings is the everyday case. A persistent tree with `Ord`-dictionary comparisons is where the 35–50× days came from (`comparative-speed.md` §7) | weight-balanced `Map`/`Set`; no hash map |
| **Deep (non-tail) recursion** | binary-trees (depth 19), expressions (shallow) | tree algorithms, naive recursions (tak, fib) | not measured |
| **Mutual recursion** | none | interpreters, parsers by hand, even/odd state machines | supported (`docs/syntax.md:226`); not measured |
| **Higher-order and polymorphic code** | matcher (closures from a rule `Map`) | `map/fold` pipelines with lambdas, which is how Stitchwort is meant to be written | apply fast paths (SW-2336); unspecialised closures still a known cost (SW-2135) |
| **Effects other than parsing** | none: only `Parse`, `Fail`, `IO` | user abilities (state, generators, `Each`); the language's distinctive feature | abilities with handlers; `Each` with multishot `fork`. No benchmark of state, generators or multishot choice |
| **Big numbers beyond pidigits** | pidigits | factorials, exact rationals, 2020 day 13-style CRT | `num-bigint` |
| **I/O and parsing of large input** | none at scale: inputs are a few hundred KB | log processing; reverse-complement and k-nucleotide read 100+ MB | `IO.readAll` into `Text`; `readLine`. Output only as `Text`, so binary output (mandelbrot's PBM) is UTF-8-encoded and can't be written faithfully |

## 2. Candidates

### 2.1 Lean 4's own benchmarks

**Where they are** **[read: GitHub API tree of `leanprover/lean4` `master`, 8 Nov
2026]**. The Lean sources are no longer in `tests/bench/`, which now holds the other
languages' versions (OCaml, SML/MLton, Haskell, Swift, C++) of the cross-language suite,
`rbmap2/3/500k.lean`, `unionfind_clean.lean`, a `qsort/` Lake package and the temci
configs. The run-time Lean programs are in **`tests/compile_bench/`**, each with an
`.init.sh` giving its test size and its benchmark size (`TEST_BENCH`). The
cross-language set (binarytrees, const_fold, deriv, qsort, rbmap, rbmap_checkpoint) is
the one from Ullrich and de Moura's reference-counting paper ("Counting Immutable
Beans", IFL 2019; `tests/bench/README.md`: "created for the IFL19 paper") **[web,
read]**. Lean's CI tracks it on its speed center.

The run-time programs, at their benchmark sizes:

| Program | Bench size | What it stresses | Stitchwort port today | Value |
|---|---|---|---|---|
| **binarytrees** | 21 | allocation and freeing. Lean's version runs depths in parallel with `Task.spawn`; `binarytrees.st` is single-threaded | **have it** (our port is single-threaded, `Nat` checks, depth 18) | already in |
| **const_fold** | 23 | builds an `Expr` tree of 2^23 leaves, reassociates `Add`/`Mul` chains, folds constants, evaluates. Allocation, nested pattern matching, in-place reuse of matched cells (the Perceus/FBIP case) | **easy**: 80 lines, plain inductive types and structural recursion. Needs a 4 GB stack in Lean (`LEAN_STACK_SIZE_KB`); ours must handle depth-23 non-tail recursion too | **high**: like binary-trees, but rewriting instead of building fresh, so reuse shows. The program Lean's runtime was designed around |
| **deriv** | 10 | symbolic differentiation of x^x, ten times. Many overlapping patterns, `Int`, `String` equality, large expression trees, counting | **medium**: `add` and `mul` are `partial` in Lean (they re-call themselves with swapped arguments). Ours needs a measure or a fuel argument (`decreasing`, `docs/syntax.md:1000`), which changes the code a little but not the work. `count` is `UInt32` (no overflow at 10) | **high**: tree rewriting with real shape, text compare, `Int` |
| **qsort** | 400 | for i < 400, sort a fresh random array of size i, 400 times. `UInt32` arithmetic for the LCG and indices, `Array.swap` in place | **medium**: `UInt32` wrap-around is `% 2^32` on `Nat` (Python does `& 0xFFFFFFFF`), `swap` exists. `partitionAux` needs a `decreasing hi - j` measure. Lean's version uses `@[specialize]` (a tuned trick, against our fairness rule); our Lean port would drop it | medium: in-place arrays. fannkuch-redux covers the same ground and is better known |
| **rbmap** | 2,000,000 | inserts into a hand-written red-black tree with `Nat` keys, then folds. Path copying, and its in-place reuse when the tree is unique | **easy**: the code transcribes directly, nested patterns included | **high**: the reference persistent-tree benchmark (Koka's rbtree is the same program). Its insert path is the one our `Map` takes |
| **rbmap_checkpoint** | 2,000,000, keep every version (freq 1) | the same, but keeps old versions alive, so reuse must fail and copying must be correct and cheap | **easy**, same code | **high**, as a variant: our reuse-across-calls work (SW-2391) is exactly the case this checks |
| rbmap_fbip | 2,000,000 | insertion through a zipper, frame-limited reuse (Lorenzen and Leijen) | easy | low: a technique comparison, not a user program |
| rbmap_library | 2,000,000 | Lean's library `RBMap` | port as "our std `Map` against Lean's `Std.TreeMap` against Python `dict`" | medium: the library-against-library row, though memory-game and dijkstra used to do this |
| **unionfind** | 3,000,000 | union-find over an `Array` of records inside a hand-rolled `StateT`/`ExceptT` monad stack. Array updates through an effect layer | **medium**: State and failure as abilities (a user `State` ability with a handler, or `Fail`), the array in the handler's state. Whether `set` stays in place through the handler is the interesting part | **high**: the only one that tests effects plus in-place update together, and Lean's natural version is monads, so it compares the two designs directly |
| liasolver | one input file | linear Diophantine solver: `HashMap Nat Int`, `AssocList`, `Int` division with rounding; 370 lines | **expensive**: 2–3 h. `HashMap` becomes `Map`; `Id.run do` loops become folds | medium: the only "real program", but costly to port and to keep faithful |
| nat_repr | 15,000 | `Nat.repr` of about 112M small numbers, summing lengths | **trivial** | low–medium: `Nat.toText` and short-lived text cells; a cheap fill-in |
| hashmap, treemap, phashmap | 10,000 reps of 2^11 ops | micro-benchmarks of `Std.HashMap`/`TreeMap` ops on random `UInt64` keys, reported in ns per op | would need rewriting as fixed-count programs (we have no clock), and `UInt64` multiply-wrap | low: k-nucleotide and rbmap cover maps more naturally |
| iterators, sigmaIterator, io_compute, parser, server_startup, bitvec_zero_counts, trailingZeros | — | Lean's own iterator library, `ByteArray` with `UInt64` xorshift (io_compute), Lean's parser, the language server | not portable, or Lean-specific | none for us. io_compute is a bit-ops benchmark, which day 22 does in AoC form |

**Comparing on Lean's home ground.** These programs are what Lean's compiler and runtime
were designed and tuned against: unboxed scalars, reuse of matched cells, borrowed
parameters, `@[specialize]`. So the native / Lean ratio there is the hardest one we can
show. That is the point if the goal is "closer to Lean". If a change narrows the gap on
the AoC days but not on const_fold or rbmap, it is likely fitting our programs rather
than closing a runtime gap. Our existing ten mostly favour Lean through its `Array` and
`HashMap`. These favour it through its reference-counting design, which is the part we
have copied (reuse, borrowing). So they test our version of Lean's own idea
**[inferred]**.

### 2.2 Benchmarks Game programs not in the set

| Program | What it stresses | Port today | Verdict |
|---|---|---|---|
| **fannkuch-redux** (n = 10–11) | small `Int` arrays, flipping prefixes in place, permutation counting; pure integer loops | **easy–medium**: `Array.swap`/`getOr`/`set`; flips as a loop of swaps. Lean: `Array`. Python: list | **add**: the in-place-array program we lack, well known, no I/O |
| **spectral-norm** (n = 2000–5500) | `Float` arithmetic in nested loops over arrays of floats; one `sqrt` at the end | **easy**: one `sqrt` can be Newton's method in the program (exact to the printed 9 digits), or wait for a `Float.sqrt` native. Printing `%.9f` needs a small formatter from `floor` and `Int` | **add**: the cheapest float benchmark that is faithful today |
| **n-body** (50M steps) | `Float` arithmetic on five bodies' records, `sqrt` in the inner loop | **blocked** on `Float.sqrt` as a native: Newton per pair would be a different program | **reserve**: add once `sqrt` exists (a small std/core change; it would also need the guide). It is the float benchmark people quote |
| **mandelbrot** | floats plus bit packing into bytes, binary PBM output | **not faithful**: output is `Text`, so bytes above 127 come out UTF-8-encoded. A checksum variant is possible, but that is no longer the game's program | skip until there's byte output |
| **k-nucleotide** | reads a FASTA file (fasta's output), counts every k-mer for k = 1, 2, 3, 4, 6, 12, 18 in a hash table keyed by strings, sorts frequencies | **medium**: `Map Text Nat` against `dict` and Lean's `HashMap String Nat`; the input is made by a fasta `gen.py` at run time (no 250 MB committed) | **add**: text slicing plus maps keyed by strings at scale, the most "Python-shaped" program available |
| **fasta** | LCG random numbers, cumulative-probability lookups on floats, line-by-line output | easy–medium | reserve: mostly output throughput. Use it as k-nucleotide's generator instead |
| **reverse-complement** | read 250 MB, reverse-complement, write it back: pure I/O throughput | medium: `readAll` into one `Text` and out again | reserve: tells us about `IO` and `Text` at a size no AoC input reaches. Worth adding if I/O becomes a topic |
| **regex-redux** | regular expressions | **not portable**: no regex library | skip |

### 2.3 Koka, Roc and the effect-handlers suite

- **Koka's `test/bench/koka`** **[read: GitHub API]**: binarytrees, cfold, deriv,
  nqueens, rbtree, rbtree-ck, rbtree-del, tak, sfib, hamming, pyth, counter, mstate and
  `-int`/`-fbip` variants. Most are Lean's suite again (the Perceus paper used the same
  programs). The new ones are **nqueens** (lists and recursion), **rbtree-del**
  (deletion, which none of Lean's has), and **mstate/counter** (a state *effect* in a
  loop).
- **Roc**: its old `crates/cli/tests/benchmarks` (cFold, deriv, nQueens, rBTreeCk,
  quicksort, closure) is gone from `main` after the compiler rewrite. Only two `.roc`
  benchmark files remain **[read: GitHub API tree]**. It adds nothing that Lean's and
  Koka's don't.
- **effect-handlers-bench** (`effect-handlers/effect-handlers-bench`) **[read: GitHub
  API, README]**: countdown (state, tail-resumptive), fibonacci_recursive (a no-effect
  baseline), product_early (abort), iterator, generator, nqueens (multishot), tree_explore
  (multishot plus state), triples (multishot), parsing_dollars (a parser written with
  effects), resume_nontail and handler_sieve (deeply nested handlers). It is implemented
  for Koka, OCaml 5, Effekt, Eff and others. **This is the suite for our most
  distinctive feature**, and it reaches cases `Parse` never does: non-tail resumption,
  multishot, and a deep stack of handlers.
  - The comparison languages are a question: Lean has no handlers, so Lean's port is a
    monad (fair, since monads are what a Lean user writes), and Python's is a loop or
    a generator.
  - A Koka or OCaml 5 runner would be the true peer. nixpkgs has `koka` **[not
    checked: an inference from memory, to verify before adding a runner]**.
  - I'd start with **nqueens through `Each`** (multishot, the only one with an
    obvious Python and Lean twin: backtracking with lists). The rest can follow as an
    "effects" sub-set if the first one teaches us something.

### 2.4 A broad AoC suite

There are 71 solved days in `aoc/src` (2020: 20, 2021: 18, 2024: 24, 2025: 9), all with
committed inputs and answers in `crates/cli/tests/running/aoc_answers.rs` **[read]**.

- **Natively over time (cheap, recommended now).** A task `bench:aoc` builds each day
  with `build --native`, runs it once on its real input, checks the answers it prints
  against `ANSWERS`, and records instructions retired (macOS `time -l`, Linux `perf
  stat`, as `compare.py` already does). It writes one JSON per run plus a diff against
  the previous one: days that moved more than 2%, up or down.
  - Instructions, not time, because most days run under 0.3 s natively, where wall time
    is noise. That is also why they can't simply join the comparison table.
  - It answers the ticket's question ("did tonight's fixes move anything outside the
    ten?") for every future merge batch. Today it can't be answered without runs.
  - My guess at what it would show for tonight **[inferred, not measured]**: broad small
    gains from the cell cache, apply fast paths and `Parse` stage 2 on every day. Larger
    gains on the `Graph.distances` days (2024 days 1 and 16) from the queue fix. Nothing
    on the grid days that kept the old neighbour code.
  - Cost: one Sonnet lane, about 1.5 h, reusing `compare.py`'s instruction counting.
    Run time unknown: the native builds dominate **[estimated: 5–15 min on Overmind]**.
- **Against CPython.** Only three days have a Python solution today, and those were
  independent cross-checks, not ports (`comparative-speed.md`, Summary). A port per day
  is well-bounded mechanical work (the Stitchwort program is the spec), so it suits
  DeepSeek: about 15–20 min a day, about 20 h for all 71, which is too much at once
  **[estimated]**. Better: port the days whose native run is over 0.3 s, plus the
  days with patterns the ten lack.
  - **2024 day 22** (bit operations and a `Map` of 4-tuples; 6M XORs).
  - **2020 day 17** (a `Set` of `List Int` keys; the reserve in the original plan).
  - **2020 day 11** (grid with views).
  - **2024 day 16** (Dijkstra without the index).
  - **2021 day 16** (bit parsing).
  - **2020 day 14** (bitmasks).

  Each of those can graduate into the wide set if it says something the eight don't.

## 3. Recommendation

### 3.1 The programs to add first, ranked

Ranked by what each would tell us that the ten can't, then by porting cost (three
languages each: Stitchwort, Python, Lean; Sonnet) **[costs estimated]**:

| # | Program | Source | Tells us | Port cost | Size to aim for (Lean about 0.5 s) |
|---|---|---|---|---|---|
| 1 | **spectral-norm** | Benchmarks Game | floats in native code: a whole axis with no measurement, and the input compact values' option A needs | 1 h (a `%.9f` formatter and an in-program Newton `sqrt`) | n about 1000–2000 |
| 2 | **const_fold** | Lean (IFL19) | tree rewriting with reuse, on Lean's design point | 45 min | Lean's 23 is probably too big for our memory today; start at 20–21 |
| 3 | **fannkuch-redux** | Benchmarks Game | many small arrays updated in place, integer loops | 1–1.5 h | n = 10 |
| 4 | **rbmap** with **rbmap-ck** | Lean (IFL19) | persistent-tree insert when unique (reuse) and when shared (copying); the path our `Map` takes | 1 h for both (one `.sw` with a mode argument, two `programs.toml` entries) | 1–2M inserts; checkpoint every 10th |
| 5 | **deriv** | Lean (IFL19) | rewriting with many overlapping patterns, `Int`, `Text` equality | 1 h (a fuel or measure for `add`/`mul`) | 9–10 |
| 6 | **unionfind** | Lean | state and failure as abilities around an array: in-place update through a handler, against Lean's monads | 1.5 h | 1–3M |
| 7 | **k-nucleotide** | Benchmarks Game | text slicing, `Map Text Nat` at scale against `dict` and `HashMap` | 1.5 h, plus a fasta `gen.py` (fixed seed, run time) | fasta 1–5M |
| 8 | **nqueens-each** | Koka, effect-handlers-bench | multishot `Each` against Lean's list backtracking and Python's recursion | 1 h | n = 10–12 |

In reserve: n-body (after a `Float.sqrt` native), 2024 day 22 (bit ops; after or
alongside SW-2010), nat_repr (cheap filler), reverse-complement (I/O), qsort (overlaps
fannkuch), liasolver (expensive).

**Lanes.** Four Sonnet lanes of two programs each, along the existing pattern:
- 1 + 3 (floats and arrays);
- 2 + 4 (trees);
- 5 + 6 (deriv, unionfind);
- 7 + 8 (text and effects).

They touch different folders and can run side by side. Each brief carries the
fairness rules (`comparative-speed.md` §4): no `@[specialize]` or `unsafe` in Lean (Lean's
own qsort and binarytrees use `@[specialize]` and `partial`; our ports keep `partial`
where Lean needs it, as a Lean user would, but add no tuning). Python with natural
structures (D3342). A salt where Lean's CSE could merge two identical pure calls, as
binary-trees has. `expected.txt` from all three agreeing. Where a port must differ (fuel
in deriv, Newton `sqrt` in spectral-norm, `% 2^32` emulation), the program's README says
so.

**Friction the ports will hit**, worth knowing before the briefs **[inferred]**:
- no `Float.sqrt`;
- no fixed-width integers;
- no byte output;
- `decreasing` proofs for index loops (qsort, fannkuch) or a fuel argument;
- possibly the native stack depth on const_fold's depth-23 recursion.

Each is a finding about the language as much as about speed, and should be filed as the
ports find it.

### 3.2 Keeping the history comparable

- **`programs.toml` gets a `set` field**: `"core"` for the ten (the default, so today's
  entries don't change) and `"wide"` for the additions. `null` stays outside both.
- **`compare.py` prints three geometric means** per pair (native / CPython, native /
  Lean): **core** (the ten, exactly as now), **wide** (the additions alone) and **all**.
  Today the geomeans are computed by hand for `history.toml`. Printing them removes a
  step and a chance of error **[read: `compare.py` has no geomean]**.
- **`history.toml` keeps one line per run**, with new keys beside the old ones:
  `native_over_lean` and `native_over_cpython` keep meaning the core ten, forever.
  `wide_native_over_lean`, `wide_native_over_cpython` and `wide_programs` (how many
  were in the wide set that run) are added. The core geomean is never redefined. If a
  core program must be replaced, that is a new key and a note, not a silent change.
  - The wide set will grow. A change in `wide_programs` breaks that series, and the
    report says so. The first wide run gets its own baseline line.
- **Program changes are marked.** When a benchmarked program's source changes (octopus,
  disk and dijkstra tonight), the report's "change" column says "program", not the
  compiler, and the ports are rechecked to do the same algorithm.
  - disk's Gauss's rule should either go into the Python and Lean ports too, or be
    noted as a known difference.
  - A one-line rule for the README: *a benchmarked AoC day may be improved like any
    other day, but the report counts it separately and the ports follow.*
- **A held-out check for each speed lane.** A lane that tunes a change on one of the
  ten also reports its instruction count on two wide programs of the same pattern, or
  on the AoC sweep. A change that only moves its own target is still welcome, but it is
  then known as such.

### 3.3 Widening the decision set for design gates

Compact values' decision set (binary-trees, matcher, dijkstra, octopus, memory-game,
expressions) has two blind spots:

1. **Floats.** Option A (one-word values) boxes `Float` unless D (unboxed fields) comes
   with it. Its gate's second condition, "boxed floats and mid-sized numbers in under 1%
   of field stores", passed because V0's census found none (`compact-values.md` §7.3).
   Nothing in the set uses floats, so the test could not fail. **Before the gate is
   rerun, spectral-norm (and n-body when it exists) should be in the census and the
   prediction**, with A's float cost stated.
2. **One allocation benchmark with a veto.** binary-trees has its own 1.25× threshold.
   const_fold and rbmap are allocation-heavy too, but rewrite rather than build fresh,
   so they would test whether E's gain on binary-trees carries over to reuse-heavy
   code. **Proposal**: the gate's "allocation" condition becomes the geomean of
   binary-trees, const_fold and rbmap, not binary-trees alone.

General rule, for Matt to confirm: **a design gate's decision set has at least one
program for each pattern the design changes**, chosen before the prediction is made.
The full wide set is always reported beside it. For compact values that means
adding spectral-norm, const_fold and rbmap to the six (nine programs). The thresholds
can stay where they are.

### 3.4 Cadence

- **Every speed merge** (as now): the lane's own instruction counts on what it targets.
  Plus, once it exists, `bench:aoc` on the Mac in instructions (minutes, no quiet
  machine needed), with any AoC day that moves over 2% named in the report.
- **Every five speed merges, or daily if fewer**: the full Overmind run with the wide
  set (`--instructions`, all runners). About 40 minutes with the eight added
  **[estimated: 28 min today plus 10–15]**. One line in `history.toml`.
- **Before every design gate** (compact values' V4 rerun, operations in place stage D's
  decision): the wide set and `bench:aoc`, whatever the count.
- **Reflection**: every third wide run (about every 15 speed merges), a short paper lane
  asks:
  - Which programs drove the merges since the last review?
  - Did any change move only its target?
  - Has any program gone quiet (within 2× of Lean, nothing left to learn)?
  - Should a reserve program come in?

  That is this lane, made routine, at about 45 minutes a time.

## 4. Not done, and findings

**Not done.** Nothing was built or run, so the ticket's request to check whether
tonight's fixes moved AoC days outside the ten is answered with the sweep proposal in
§2.4, not with numbers. I read the Lean sources of `tests/compile_bench/` (const_fold,
deriv, qsort, rbmap and variants, unionfind, hashmap, liasolver's outline, nat_repr,
binarytrees) for this note. I didn't read the other languages' versions in
`tests/bench/`. Koka's programs were listed, not read. The nixpkgs `koka` package and
the native float path (inline or a call) were not checked.

**Findings worth filing:**

1. **`bench:aoc`: every AoC day natively, by instruction count, with a diff against the
   last run** (Sonnet, 1.5 h). This is the generality check every speed lane is missing.
2. **Wide set, four port lanes** as in §3.1 (Sonnet, about 2–2.5 h each), and the
   `set` field, three geomeans and `history.toml` keys of §3.2 (Sonnet, 45 min, which
   could ride with the first port lane). This supersedes SW-2346's open list, which can
   close into it.
3. **`Float.sqrt` (and perhaps `exp`, `log`, `sin`, `cos`) as primitives**, like `mul`
   and `div`. The kernel computes them with Rust's `f64` under `float.md` §3.3's
   contract. It unblocks n-body and every geometry program. It is user-visible std, so
   it needs guide and syntax docs; it touches std core, so Opus or a careful Sonnet.
   Check `float.md` first: sqrt is correctly rounded in IEEE 754, so it fits the
   contract better than `sin` does.
4. **SW-2010 (native bit operations)** should be raised. A 4.3 µs XOR is likely the
   worst per-operation gap in the language, and 2024 day 22 or io_compute-style code
   would show it as a ratio in the hundreds **[inferred]**.
5. **The disk port's part 2 differs from the Stitchwort day** (Gauss's rule since
   SW-2374). Make the Python and Lean ports do the same, or note it in the README
   (Sonnet, 10 min).
6. **2024 days 16 and 18 could take `Graph.distances`' grid index** (SW-2396) as day 15
   does: the API exists, only the benchmark uses it. That is a small follow-up that
   also shows whether the API is general in practice.
7. **2024 day 9 part 1's workaround** (`foldLeft` with a counter instead of `withIndex
   |> sumBy`) points at `withIndex` plus `sumBy` allocating a pair per element. A
   fusion or a std `sumByWithIndex` would help every day written the natural way. Worth
   a profile ticket.
8. **The geomean is dominated by the two parsers measuring the same thing**: about 35%
   of the core geomean's log comes from expressions and scan. That's no reason to change
   the core set (the history matters more), but the report could also show the core
   geomean with scan and expressions counted as one "parsing" entry, so a parser gain
   isn't read as twice as general as it is.
