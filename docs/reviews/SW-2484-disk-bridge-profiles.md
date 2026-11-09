# Disk and bridge, profiled natively (SW-2484)

SW-2484, 9 Nov 2026, Sonnet, `lane/SW-2484` from `main` at `287261d94` (after effect-runtime R1-R3).
Measurement and write-up only: no compiler or runtime code changed. The two programs are the
`disk` (AoC 2024 day 9) and `bridge` (AoC 2024 day 7) entries of `bench/compare/programs.toml`,
at the comparison's input sizes (disk: the real map repeated 45 times, 900,000 digits; bridge: the
real input repeated 150 times, 127,500 lines, 3.76 MB).

The latest comparison (SW-2295-comparative-speed.md, job 32) has native at 17.6x Lean on disk and
18.9x on bridge. This note says where the time goes, what each cost is in the problem's terms, and
what to change, ranked.

**How to read the numbers.** The machine was loaded (load average 2-4, other lanes running), so
absolute times are rough: native disk took 6.2-6.4 s here against Overmind's 13.3 s, CPython 1.15 s
against 2.24 s; the native/CPython ratio matches (5.4x here, 5.95x there). Shares inside one profile
are what this note uses. Everything is **measured** unless it says *estimated*, and an estimate says
how it was made. Stage times are wall-clock `/usr/bin/time -p` of natively built variants (below).

## 0. Summary

1. **Disk's biggest cost was a hidden allocation in `Map.Tree.minOr`, and fixing it is measured at
   -16% of the whole program.** `minOr` walks down a tree's left spine passing `Some (key, value)`
   as the accumulator, so every level builds a pair and a `Some`. Part 2 calls `Set.min` on a
   `Set` of free-span starts nine times per file, 30.4 M `minOr` steps in all, about 52 M of the
   run's 105 M cells (the cells the fix removed). Carrying the key and value as two arguments and building the pair once at
   the end took disk from 6.23 s to 5.24 s (three runs each), cells 105.5 M to 53.9 M, frees 60.6 M
   to 34.8 M. The change is eleven lines (section 3.1), and the one proof that mentions `minOr` took
   a three-line lemma.
2. **Bridge is a parsing benchmark: 80% of its time is `Std.Parse` on effects.** Parsing alone is
   5.65 s of 6.9 s; the search is 1.2 s. Lean's bridge reads the file with `splitOn` and
   `String.toNat!`. Parse time follows the number of effect steps closely, about 0.15 us each
   (bridge 5.65 s over 38.1 M steps; the same program with fewer operations ran 24% fewer steps in 18%
   less time). Each number on a line costs six operations (three `mark`s and three `span`s), each
   routed through a handler: six effect steps, six slow applies, four closures.
3. **Disk is split almost evenly between parsing (44%) and part 2 (44%); part 1 is 9%.** Parsing
   900,000 digits costs 3.1 us a digit: 24 effect steps and 20 closures per digit, from four
   operations per digit in `many`.
4. **Both programs spend 55-60% of their self time in allocation and freeing** (allocator 25-30%,
   Rust drop glue and `value::free` 23-24%, `sw_*` entry points 11-20%); generated code is only
   29-34%. The hot generated bodies are mostly call overhead and refcounts, not work (section 2).
5. **Bridge allocates 12 GB, 58% of it closures and effect-runtime function objects** (census:
   7.0 GB of `Fun`s against 5.2 GB of cells). A closure per `canMake` level
   (`operators.any (match ...)`) is a third of its closures.

Ranked targets (details in section 4):

| # | Target | Disk | Bridge | Basis |
|---|---|---:|---:|---|
| 1 | `minOr`/`maxOr` build the result once, not per level | **-16%** | 0 | measured |
| 2 | One fused whitespace-and-number operation (`token nat`: 3 operations to 1) | 0 | -14 to -23% | estimated from measured per-operation cost |
| 3 | Cheaper operations: R4 (SW-2464), R5 (SW-2465), then operations in place | -2 to -3% | -3 to -4% (R4+R5); structural change -20 to -35% | R4/R5 scaled from the proposal; the rest estimated |
| 4 | `canMake` without a closure per level (`List.any` with a known lambda) | 0 | -5 to -8% | measured on a hand-written variant |
| 5 | `many` takes `optional`'s mark and has no `manyStep` thunks | -5% | -3% | measured |
| 6 | Ord dictionary for `Nat` keys inlined (`Std.Nat.compare` through a function value) | -3 to -4% | 0 | estimated from profile shares |
| 7 | `replicate k x ++ rest` without the copy (`blocksFrom`, part 1) | -2 to -3% | 0 | estimated: copy cells x cost |
| 8 | Compact values (SW-2324): fewer bytes per cell and `Fun` | not estimable | not estimable | census bytes below |
| 9 | `digitCount` and `10 ^ n` for `placeValue` (concatenation) | 0 | up to -3% | upper bound from self-time shares |

Targets 1, 2, 4 and 5 are small library or std changes (hours); 3 and 8 are the existing design
work. SW-2460 (`withIndex |> sumBy`) is not material here any more: disk's checksum is a
`foldLeft` over a pair, and bridge's `eachLine` makes one `withIndex` pair per line (127,500, well
under 1%).

## 1. Disk (2024 day 9)

### 1.1 Where the time goes, by stage

Natively built variants of the same program (scratch entry points in the AoC project, not
committed), each reading the same 900 kB input:

| Variant | Wall (s) | What it adds |
|---|---:|---|
| parse only (`parseDiskMap`, count the digits) | 2.84 | 44% of the 6.43 s run |
| parse + part 1 | 3.40 | part 1: **0.56 s (9%)** |
| parse + part 2 | 5.69 | part 2: **2.85 s (44%)** |
| both (`main`) | 6.43 | |

### 1.2 Top functions (whole run, 7,073 samples)

| Function | self | note |
|---|---:|---|
| `mi_free` / `mi_malloc` | 9.5% / 8.6% | allocator 30.1% in all |
| `drop_glue::<Value>`, `Fields::drop`, `value::free`, `Rc<[Value]>::drop_slow` | 7.2 / 6.5 / 4.5 / 3.5% | freeing, 21.7% together |
| `sw_apply_prepare` | 3.8% | the parser's slow applies |
| `Std.Map.Tree.insertWith.%match1[0][reuse]` | 3.0% | free-span map and set updates |
| `sw_cell_new`, `sw_eff_step` | 3.2%, 2.4% | |
| `Std.List.replicate[cells]`, `Std.List.append[cells]` | 2.2%, 2.1% | part 1's block list |
| `Std.Map.Tree.minOr`, `shape`, `rebuild[reuse]` | 1.9%, 1.9%, 1.8% | |
| `Std.Nat.compare` (through a function value) | 1.3% (+ `apply2`) | map keys |

By kind: generated code 34.0%, allocator 30.1%, Rust runtime 22.9%, `sw_*` entry points 11.4%.
Inclusive times mix in the continuation of handlers (the profiler marks those), so the stage cuts
above are the reliable split: `parseDiskMap` and `compactFiles` look like 39% and 42% inclusive,
and the stages say 44% and 44%.

Runtime calls (`call-counts` build): 105.5 M `sw_cell_new`, 60.6 M `sw_drop_words`, 22.5 M
`sw_apply_prepare`, 21.6 M `sw_eff_step`, 18.5 M `sw_closure`, 8.1 M `sw_bind`. Split by stage
(difference of the stage builds):

| | cells | frees | apply_prepare | eff_step | closures |
|---|---:|---:|---:|---:|---:|
| parse (900,000 digits) | 13.5 M (15 per digit) | 16.2 M | 22.5 M | 21.6 M (24 per digit) | 18.0 M (20 per digit) |
| part 1 | 15.5 M | 7.4 M | 0 | 0 | 0 |
| part 2 | **75.6 M** (168 per file) | 36.1 M | 0 | 0 | 0.45 M |

### 1.3 Parsing: four operations per digit

`diskMapLine` is `many1 (() => digit().toNat) |> .toList`. One round of `Parse.manyFuel`
performs `mark()`, then `optional` performs its own `mark()` and wraps the parser in a handler,
then `digit` performs `next`, then `manyStep` performs `mark()` again to check that something was
read. That is the four routed operations per digit the counts show (3.6 M for 900,000 digits).
Each routed operation costs about 6 effect steps, 6 slow applies and 5 closures: a `Bind` node,
a `Done` cell, a `StateK` resumption, a `Jumped` object and the continuation closures. The effect
runtime's objects (20.7 M of the run's cells and funs) are all parse.

Cost model: parse time 2.84 s over 3.6 M operations is 0.79 us an operation, 0.13 us a step.
The CPython port is `[int(d) for d in text]`; Lean's is `toList.toArray.map`.

### 1.4 Part 2: the free-span search

```
def FreeSpace.leftmostFit (free: FreeSpace) (length: Nat) (before: Nat): Option Span :=
  free.toList
    |> .filterMap (entry => if length <= entry.fst then entry.snd.min |> .map (...) else None)
    |> .minBy .start |> .filter (.start < before)
```

For each of 450,000 files, the free spans are a `Map Nat (Set Nat)` of at most nine lengths. The
search takes the nine entries, asks each `Set` for its smallest start, and keeps the leftmost.
Then one `Set` and one `Map` are updated twice (`remove`, `add`). Per file:

| | per file | total | what |
|---|---:|---:|---|
| `Map.Tree.minOr` entries | 67 | 30.4 M | the spine walk of `Set.min`, about 7 levels x up to 9 lengths |
| `Std.Map.Tree.shape` | 26 | 11.7 M | balance checks on the updates |
| `rebuild[reuse]`, `insertWith[reuse]` | 25, 21 | 11.3 M, 9.4 M | |
| `Std.Nat.compare` (function value) | 32 | 14.3 M | the keys' `Ord` |
| `Map.Tree.toListOnto` | 19 | 8.6 M | `free.toList` |

`minOr`'s inclusive time is 20% of the part-2 profile and it is the largest allocator: its
bytecode builds the pair (`Ctor tag 0, 2 args`) and the `Some` on every step, then tail-calls
itself with them as `found`. The 30.4 M steps are about 52 M of the 75.6 M cells part 2 builds (the fix
below removed 51.6 M), and their frees. That is the cost the minOr fix (section 3.1) removes.

What it is **not**: building `free.toList` and the `filterMap`/`minBy` over it. A variant that
folds with `Map.foldLeft` (no list, no options) ran part 2 in 5.37-5.56 s against 5.47 s, and
built 4 M fewer cells: noise. The list, the options and the lambdas are about 2% of cells.

Lean and CPython do the same scan (Lean: `TreeMap.foldl` with `starts.min?`, CPython: a loop
over a dict of heaps); neither allocates per level. Lean's `TreeSet.min?` returns the key
without a tuple, and its Nat keys are unboxed scalars, so the comparisons are inline `<`.

### 1.5 Part 1

Part 1 is 0.56 s: `blocksFrom` builds the disk as `replicate fileLength (FileBlock id) ++
replicate freeLength Free ++ blocksFrom ...` (5.15 M `append[cells]` entries, 7.2 M `replicate`
entries: every block is built, then copied by `++`), then `fillFront` and `foldLeft`. 15.5 M cells
for 4.1 M blocks. Lean builds a 4 M-element array in place and indexes it. Peak memory is 709 MB
(census): 12 M live cells at the top, mostly the block lists.

### 1.6 Instruction split of the hot bodies (`--by-instruction`)

Generated code is 34% of the run, spread over many bodies; the top body (`insertWith.%match1`)
is 3.0%.

| Body | self | split of its self time |
|---|---:|---|
| `Map.Tree.insertWith.%match1[0][reuse]` | 3.0% | call 37%, prologue 23%, untagged 13%, work 10%, checks 8%, refcounts 8%; the two `Call`s and the `TailCall` are 38% |
| `Std.Map.Tree.minOr` | 1.9% | work 36% (the `Unpack` of a shared node is a third: its refcount increments on six fields), untagged 29%, refcounts 21%, checks 10% |
| `Std.List.replicate[cells]` | 2.2% | untagged 38%, work 35% (the two `Hole(Fill)` prims 15%), dec 12% |
| `Std.List.append[cells]` | 2.1% | work 59% (`Hole(Fill)` 24%), untagged 28% |
| `Std.Nat.compare` | 1.3% | `Return` 43%, `Test` 25% |

("untagged" is the profiler's bucket for instructions the map can't place: block glue and
spills.) After the minOr fix `minFrom` is 1.9% self and the profile shape is the same: the rest
of the generated code is call, return, and refcount traffic.

## 2. Bridge (2024 day 7)

### 2.1 Where the time goes, by stage

| Variant | Wall (s) | |
|---|---:|---|
| parse only (`parseEquations`, count the lines) | 5.84 (5.64-5.65 on repeats) | **83%** of 7.07 s |
| parse + part 1 | 6.17 | part 1: 0.33 s |
| parse + part 2 | 6.72 | part 2: 0.9 s |
| both (`main`) | 7.07 | |

Cuts inside the parse (same input, variants of the parser):

| What runs | Wall (s) |
|---|---:|
| `IO.readAll().lines` | 0.39 |
| + `.map (.toList)` | 0.50 |
| `eachLine` with one `Parse.span` per line (the whole line) | 0.98 |
| + `nat()` and `char ':'` | 1.22 |
| the whole `equationLine` | 5.64 |

So reading lines is 0.4 s, `eachLine`'s per-line setup (handler start, `Parse.whole`, the
`withIndex` pair) about 0.5 s, and the numbers after the colon, `many1 (() => token nat)`,
**4.4 s**: about 830,000 numbers (6.5 a line, estimated from 51 operations a line at 6 each) at 5.3 us each.

### 2.2 Top functions (whole run, 13,436 samples)

| Function | self | note |
|---|---:|---|
| `sw_apply_prepare` | 9.0% | slow applies: 42.8 M (20.1 M partial applications, 6.7 M closures, 6.6 M `DoneK`, 6.6 M `JumpK`, 2.8 M resumptions) |
| `mi_free` / `mi_malloc` | 8.6% / 6.4% | allocator 25.0% |
| `drop_glue::<Value>` | 6.9% | |
| `sw_eff_step` | 6.0% | 38.1 M steps |
| `value::free`, `Fields::drop` | 4.2%, 3.0% | |
| `apply2`, `apply4`, `apply1` | 3.1%, 1.8%, 1.1% | the shared apply stubs |
| `rt_loop`, `state_step` | 2.9%, 1.3% | the effect runtime's loop |
| `Fun::take_children`, `Rc<Fun>::drop_slow` | 2.7%, 2.7% | freeing closures |
| `Std.Parse.%elim` | 2.4% | the parse handler's clause match |
| `Value::clone` | 2.3% | |
| `Day07.canMake.%match1` | 2.1% | the search |
| `Std.List.spanOnto[empty]` | 1.4% | `span` collecting a run of characters |
| `sw_closure` | 1.4% | |

By kind: generated code 29.0%, allocator 25.0%, Rust runtime 24.4%, `sw_*` entry points 20.0%.
The `Std.Parse` group is 9.2% self and 32.8% inclusive; `Day07` 3.3% self. Everything else is the
effect runtime, which attributes its time to no definition. The saved profile is
`target/profile/bridge.json.gz`.

Runtime calls: 48.5 M `sw_drop_words`, 42.8 M `sw_apply_prepare`, 39.2 M `sw_cell_new`, 39.0 M
`sw_closure`, 38.1 M `sw_eff_step`, 22.2 M `sw_apply_cached`, 14.1 M `sw_bind`. Split by stage:

| | cells | frees | apply_prepare | eff_step | closures |
|---|---:|---:|---:|---:|---:|
| parse | 32.1 M (250 per line) | 32.0 M | 42.8 M | 38.1 M (300 per line) | 26.2 M |
| part 1 | 0.7 M | 3.0 M | 0 | 0 | 2.9 M |
| part 2 | 6.3 M | 13.7 M | 0 | 0 | 10.0 M |

### 2.3 Parsing: six operations per number

`equationLine` is `nat()`, `char ':'`, then `many1 (() => token nat)`. Per number in the
`many1`: `mark()` (`optional`'s), `spaces()` (a `span`), `nat()` (a `span`), `spaces()` (a `span`),
`mark()` (`manyFuel`'s `before`) and `mark()` (`manyStep`'s check). That is 6 operations; a line
has about 51 operations (6.56 M in all, the routed-operation count). Each costs about 0.9 us. Of
the cost, the handler's own work (`spanOnto` building a list of characters per run, 6.7 M entries;
`isDigit`/`isSpace` through a closure, 3.5 M and 2.7 M; `digitValue` and `Nat.fromDigits`,
`digitsAcc` 5.6 M entries) is small: those bodies are each under 1.5% self. The rest is the six
effect steps, six slow applies and four closures each operation costs.

Per-operation cost, measured (variants in section 4): taking the operation count from 6.69 M to
5.05 M (-24%) took the parse from 5.65 s to 4.65 s (-18%), about 0.6 us per operation removed.

### 2.4 Search: a closure per level

`canMake` is `operators.any (match | Add => ... | Multiply => ... | Concatenate => ...)`: every
level allocates a closure capturing the operators, the target and `first` (17.7 M `canMake`
bodies and 17.7 M lambda88 entries; `List.any` 23.8 M entries) and applies it per operator.
`placeValue` calls `Nat.pow 10 number.digitCount` (9.3 M `pow`, 5.6 M `digitsAcc`, each x2 for the
step). Lean's version is a direct three-way `||` with array indexing.
A hand-written variant with direct recursion over a `Bool` flag (no closure, no `any`) took part 1
plus part 2 from 1.24 s to 0.7-0.9 s.

### 2.5 Instruction split of the hot bodies

| Body | self | split |
|---|---:|---|
| `Std.Parse.%elim` | 2.4% | work 44% (the `Unpack`s of the handler's state pair: 28%), prologue 19%, untagged 22%, dec 10%; the four `TailApply`s are 15% |
| `Day07.canMake.%match1` | 2.1% | work 26%, untagged 24%, **prologue 22%**, dec 9%, call 8%; `DivFuel` prims 10% |
| `Std.List.spanOnto[empty]` | 1.4% | work 41%, untagged 30%; the `Apply` of the predicate is 25% of it (refcounts 25% of that) |
| `Std.List.any[empty]` | 1.0% | the `Apply` of the lambda is 38% (work 33, inc 31, check 27) |
| `canMake/lambda88` | 0.9% | `TailCall` 57% (call 97%): it only unpacks five captures and calls `canMake` |

## 3. The one change measured end to end

### 3.1 `minOr`: carry the key and value, build the pair once

Experiment, in the worktree and then reverted (the patch is in the lane's scratchpad only):

```
-def Map.Tree.minOr (found: Option (k, v)): (tree: Map.Tree k v) → Option (k, v)
-  | Tip => found
-  | Bin _ l kk vv r => Map.Tree.minOr (Some (kk, vv)) l
+def Map.Tree.minFrom (foundKey: k) (foundValue: v): (tree: Map.Tree k v) → (k, v)
+  | Tip => (foundKey, foundValue)
+  | Bin _ l kk vv r => Map.Tree.minFrom kk vv l
+
+def Map.Tree.minOr (found: Option (k, v)): (tree: Map.Tree k v) → Option (k, v)
+  | Tip => found
+  | Bin _ l kk vv r => Some (Map.Tree.minFrom kk vv l)
```

(`@[tailrec]` and `@[noReceiver]` kept on both.) `Map.Tree.minOnto` in `Map/Spec.sw` needs
`theorem Map.Tree.minFromOr (kk: k) (vv: v): (l: Map.Tree k v) → Some (Map.Tree.minFrom kk vv l) =
Map.Tree.minOr (Some (kk, vv)) l` (`| Tip => rfl`, `| Bin ... => rfl`) and a `rewrite
Map.Tree.minFromOr kk vv l in` before the recursive call. Both files check; I ran no other
std test. `Map.Tree.maxOr` has the same shape and wasn't changed.

| | before | after |
|---|---:|---:|
| disk `main`, wall (3 runs) | 6.23, 6.22, 6.24 s | 5.43, 5.24, 5.21 s |
| `sw_cell_new` | 105.5 M | 53.9 M |
| `sw_drop_words` | 60.6 M | 34.8 M |
| part 2 only (fold variant), wall | 5.38 s | 4.34 s |

After the change the profile's shape: allocator 25.9%, generated code 38.1%, `Std.Map` 22.7%
inclusive, `Std.List` 45.4% (mostly part 1 and the parse's lists), `Std.Parse` 14.4%.

## 4. Ranked targets

Estimated savings are shares of the program's own wall time. "Overlap" names the existing work.

| # | Target | Program | Saving | How measured or estimated | Overlap |
|---|---|---|---:|---|---|
| 1 | `Map.Tree.minOr`/`maxOr` (and any `Option (k, v)` accumulator loop in std) build the result once | disk | **-16%** | measured, section 3.1 | new; SW-2404 (map draining) is a different allocation but the same family |
| 2 | A fused operation for whitespace-number-whitespace (`token nat` is 3 operations: two `span`s and a `nat` span), or a `Parse.nat` that reads digits without a character list | bridge | -14 to -23% | measured: dropping one of the three spans per number plus one mark saved 1.0 s (14%); two of three at 0.6-0.97 us a removed operation x 1.66 M is 1.0-1.6 s. Semantics need care: a variant that skipped trailing spaces is cheaper but accepts different text | new; SW-2327 option E (library changes inside `Std.Parse`) |
| 3a | R4, perform folded into its `Call` (SW-2464) | disk, bridge | -1.2 to -1.8% (3.6 M performs), -2 to -3% (6.56 M) | estimated: the proposal's bridge figure scaled by performs; instructions 370-560 per perform | SW-2464 |
| 3b | R5, no resumption for a fused state handler without `k` (SW-2465) | disk, bridge | about -1% each | the proposal's figure; 3.6 M and 6.56 M `StateK`+`Jumped` pairs here | SW-2465 |
| 3c | Operations in place for tail-resumptive operations (the structural fix: each parse operation costs 6 steps now) | both | -20 to -35% of the parse, so disk -9 to -15%, bridge -17 to -29% | estimated: halving the 0.13-0.15 us a step cost (parse time follows steps within 15%, section 2.3) | operations-in-place.md stages C/D, SW-2402 |
| 4 | `canMake` without a closure per level: specialise `List.any` for a lambda, or write the operators as a `Bool` flag | bridge | -5 to -8% | measured on a hand-written variant: search 1.24 s to 0.7-0.9 s | SW-2135 (specialising closures that capture locals) |
| 5 | `Parse.many`: reuse `optional`'s mark and skip the `manyStep` thunks (measured as `optionalFrom before parser` and an inline `if`) | disk, bridge | -5% (disk parse 2.65 to 2.25-2.4 s), -3% | measured; 0.9 M operations removed: 3.6 M to 2.7 M, eff steps -12%, closures -10% | SW-2327 stage 2 touched `Parse.expected` only; `Parse.manyFuel` has proofs (Reads.sw) to update |
| 6 | Specialise `Map` operations at `Nat` keys (the `Ord` dictionary through `Std.Nat.compare/value`: 14.3 M applies) | disk | -3 to -4% | estimated: `Nat.compare` 1.3% + `/value` 0.5% + `apply2` 2.3% (part of it) of self time | SW-2135, SW-814 (fused balance; its estimate -30% instructions per level) |
| 7 | `blocksFrom` without `replicate ++`: pass the rest to a `replicateOnto` | disk | -2 to -3% | estimated: 5.15 M `append` entries and the cells they copy, at 30 ns an object | new; `List.append` self 2.1% |
| 8 | Compact values (SW-2324) | both | not estimated | census bytes: disk cells 8.18 GB today, 5.09 GB under E, 3.08 GB under A; bridge funs 6.97 GB today, 5.33 GB E, 1.76 GB A; peaks 709 MB and 240 MB today, 441 MB and 150 MB (E), 269 MB and 90 MB (A). Allocator calls don't change, only bytes touched | SW-2324, SW-2441 (E) |
| 9 | `digitCount` and `10 ^ n` as primitives or a small table for `placeValue` | bridge | up to -3% | upper bound: `Nat.pow` and `digitsAcc` are each under 1% self | SW-2398-style unboxing doesn't apply; a `Nat` primitive would |

Combined, the cheap library items (1, 2, 4, 5, 6, 7, 9) are -28 to -30% on disk (6.23 to about
4.4-4.5 s) and about -25 to -40% on bridge (6.9 to about 4.2-5.2 s), against CPython's 1.15 s
and 2.02 s locally. That leaves both at roughly 4x CPython and, for bridge, about 12x Lean; target
3c (or parsing as a compiled state machine, parse-runtime.md option C) is what closes the rest of
bridge's gap, since parsing would still be 3.5 s of a 4.5 s run.

### Why Lean and CPython are faster, in these two programs

- **Parsing is the whole difference on bridge.** Lean and CPython split the text and convert
  numbers: no effects, no closures, no operations. We run a parser combinator library as an effect,
  at about 0.9 us an operation.
- **Part 2 of disk:** the same algorithm, but they walk the tree without allocating (Lean's
  `TreeMap`/`TreeSet` are persistent but their `min?` and `foldl` don't build tuples), keep
  `Nat`s unboxed and compare them inline; ours built 168 cells per file and called `Nat.compare`
  through a dictionary 32 times per file.
- **Part 1 of disk:** they use arrays updated in place (Lean `Array.push`, CPython `list.extend`).
  We build and copy lists of 4 M cells (peak 709 MB; a 4 M-element array of boxed `Option Nat` is a fraction of that).
- **Closures:** Lean's `canMake` is a direct `||` chain with no operator list; ours allocates a closure per
  level (17.7 M) and applies it through `apply1`.

## 5. Commands and results

```
nix develop -c task profile:native -- disk bridge --top 25          # 78 s; profiles, call counts, per-body entry counts
nix develop -c task profile:native -- disk bridge --no-counts --top 5 --by-instruction --bodies 6
nix develop -c task profile:native -- bridge --no-counts --top 3 --group Std.Parse --group Aoc.Year2024.Day07 --group Std.List
CARGO_TARGET_DIR=target/census nix develop -c cargo build --release -p stitchwort-standalone --features value-census
STITCHWORT_RUNTIME=$PWD/target/census/release/libstitchwort_standalone.a stitchwort build --native Aoc.Year2024.Day09.main -o prog   # in aoc/
STITCHWORT_VALUE_CENSUS=out.txt ./prog < input
```

- Inputs were built as `bench/compare/compare.py` builds them (`join0` x 45, `lines` x 150).
- Stage cuts: scratch namespaces `Aoc.Year2024.Day09.Scratch*` and `Day07.Scratch*` in `aoc/`
  (uncommitted; deleted before the commit) with `parseOnly`, `part1`, `part2` entry points, built
  with `stitchwort build --native` and timed with `/usr/bin/time -p`.
- Local timings: native disk 6.2-6.4 s, bridge 6.9-7.1 s; CPython disk 1.15 s, bridge 2.02 s.
  Reference timings for Lean are Overmind's job 32 (disk 754 ms, bridge 820 ms); Lean isn't
  installed on this machine, so the Lean comparisons are of the source (`bench/compare/lean/Compare/Disk.lean`,
  `Bridge.lean`), not timed here. PyPy isn't installed either.

## 6. What I'm unsure of

- **Absolute times are from a loaded machine** (load 2-4). The experiment comparisons ran back to
  back in the same shell session, three times for the minOr fix and twice for the others, with
  differences well above the repeat spread (about 0.05-0.2 s), but they are not Overmind runs.
- **Estimates for 3b, 3c, 6, 7 and 9** are modelled from shares or per-object costs, not
  measured. Ask for a measurement before ranking them against 1, 2, 4 and 5.
- **Target 2's range** comes from two measured points (one operation kind removed, one mark
  removed) that I extrapolated to two operations per number; its real saving depends on how the
  fused operation is written and whether the empty-span case is cheaper than the non-empty one.
- **The minOr patch passed the checking of the files it touches** and ran disk to the same
  answers (569206969452930596 for part 2, checked against the unpatched run), but I ran no std
  test suites; `maxOr` and proofs about `min` elsewhere weren't looked at.
- **Instruction-level splits** attribute samples by address; skid blurs single instructions, and
  `untagged` is large (20-40%) because block glue isn't mapped. I used them for the hot bodies' shape
  (call overhead, refcounts), not for single-instruction claims.
- The effect runtime's own time is attributed to no definition (handler continuations run from
  `rt_loop`), so "parse" shares come from stage cuts, not from the inclusive column.
