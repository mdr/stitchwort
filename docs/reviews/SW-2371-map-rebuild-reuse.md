# SW-2371: why `Std.Map.Tree` rebuilds don't reuse the cell they take apart

SW-2371, Sonnet, 8 November 2026. Investigation: no product code changed.
Question from SW-2369 (dijkstra, 2021 day 15): about 25 M `Map.Tree` node
rebuilds, but `sw_ctor_reuse` fires only 1.9 M times. Numbers marked
**[measured]** come from a run, **[estimated]** ones say how.

## Answer

Two separate causes, and the second hides the first.

1. **Wrong counter.** The 1.9 M is **misses**, not hits (SW-2361: native code
   does the unique-cell reuse inline and calls `sw_ctor_reuse` only when it
   fails). Counting hits and misses per site shows that `Map.Tree`'s `Bin`
   cells are essentially never reused: the reuse that does happen is for
   other shapes (the `(smallest, rest)` pair in `minView`, `Option`/list
   cells in `popMinRaw`, `pushEdges`, `filterMap`). The `Bin` constructor
   executes **fresh 25.7 M times and reuses 0.35 M times** [measured].
2. **Most of those cells could not be reused anyway, because they are
   shared** (the search keeps the old queue alive; below). Once the sharing
   is gone, the cells *are* unique, but the reuse analysis still can't pair
   them: the `Unpack` of the old node is in `insertWith`/`minView`, and the
   new `Bin` is built in another function (`balance` then `rebuild`). Reuse
   is only within one compiled body.

So all three candidates in the brief were partly right, in this order: the
cell is shared (inherent to how `Graph.searchFrom` is written, not to
persistent maps), the unpack and rebuild are in different functions, and
field counts are not a factor (every `Bin` is 5 fields, `Tip` has none).

## Method

Temporary instrumentation in the bytecode interpreter
(`crates/rt/src/machine.rs`, reverted, patch not committed): per
`(body, instruction)` counts of `Ctor` (fresh), `CtorReuse` hit and miss,
and `Unpack` unique / shared, with the dumped bytecode of the top bodies.
The run is `stitchwort run Aoc.Year2021.Day15.main < inputs/2021/day15.txt`
(the real input, both parts, answers 656 and 2979); the interpreter's
reference counts match native code's because both follow the same bytecode
(the native counts in SW-2369 agree: 25.0 M `shape`/`rebuild` entries, 22.3 M
here at the `Bin` constructor in `rebuild`). Body names come from
`STITCHWORT_NATIVE_DUMP` (the `bodyN` numbers are the bytecode body numbers).
Wall times are native `user` seconds, three runs each, on a quiet-ish
machine, good to about 2%.

## The table (stock `Graph.distances`)

`Bin` cells built or taken apart in `Std.Map.Tree` [measured]:

| # | Body, instruction | What | Count | Case |
|---|---|---|---:|---|
| 1 | `Map.Tree.rebuild` `Ctor Bin` (pc 17) | `Keep` arm: `bin l key value r` | **22.29 M fresh** | Callee of `balance`; no `Unpack` in this body, so no token to claim. |
| 2 | `Map.Tree.insertWith.%match1[0]` `Unpack` (pc 36, pc 11) | the `Bin` being descended through, `Less`/`Greater` arms | 12.91 M **shared**, 3.26 M unique, **0 with a token** | Token is not requested (`NO_REG`): the arm calls `balance`, it builds no `Bin` here. 80% of the unpacks find the cell shared. |
| 3 | `Map.Tree.minView` `Unpack` (pc 5) | the `Bin` of the left spine | 7.60 M **shared**, 0 unique, no token | Same: rebuilt via `balance`. The 7.60 M `CtorReuse` hits here are the `(smallest, rest)` pair, not a `Bin`. |
| 4 | `Map.Tree.singleL` / `doubleL` / `doubleR` `Ctor Bin` | rotations | 0.79 M + 0.97 M + 0.45 M fresh; 0.35 M hit, 0.44 M miss at `singleL` pc 31 | The only `Bin` reuse in the library: 0.35 M hits against 0.44 M misses (shared). |
| 5 | `insertWith.%match1[0]` `Ctor Bin` (pc 9, 34) | `Tip` arm and `Equal` arm (`Bin s l kk (f value vv) r`) | 0.49 M + 0.73 M fresh | `Tip` has nothing to reuse; `Equal` unpacks with no token because the `Unpack` is a separate lifted match body. |
| 6 | `Map.Tree.get.%match1`, `shape` `Unpack` | read-only walks (`contains`, size reads) | 17.2 M / 4.3 M "shared" | Reads of a map that stays alive; nothing to reuse and not a defect. |

Totals for `Bin`: **fresh about 25.7 M, hits 0.35 M, misses 0.44 M**.
Cells allocated in all, 40.4 M (SW-2369). The 1.9 M `sw_ctor_reuse` calls
are the misses over every constructor in the program (this table has 0.44 M
of them).

## Cause 1: the old queue is kept alive (`Graph.searchFrom`)

`Graph.searchFrom` has `queue`, `queued`, `found` and a `decreasing` clause
alongside the runtime values; `queue` is used by proof terms and the
termination measure only, yet it is an ordinary `Set` parameter: the caller
evaluates and passes it. The recursive call is
`searchFrom graph sources pushed … pushed.popMin rfl`: `pushed` is the new
`queue` argument *and* the argument of `popMin`. So:

- `popMin` (`minView`) runs with the queue's root at reference count 2
  (the parameter slot of the next iteration holds the other), so its unpack
  copies fields instead of moving them: row 3, 7.6 M shared unpacks.
- `rest` shares every node off the popped spine with the old `queue`, which
  is alive until the next iteration finishes, so `pushEdges`' `insertWith`
  walks (row 2) meet shared cells on 80% of steps.

**Check [measured]:** the same search written by hand without the proof
parameters (`fastFrom graph fuel queue settled`, popping with `popMin` and
`pushEdges` as before; scratch, not committed; answers 656 and 2979) has
**no shared unpack in `insertWith` or `minView` at all** (the 16 M insert
steps and 7.6 M pop steps all unique) and runs **5.44 s to 4.49 s, -17%**
(native, three runs each: 5.46/5.42/5.50 against 4.49/4.48/4.50). Interpreter
user time 42 s to 32 s. That gain is from skipping reference-count traffic and
field copying on shared cells, with nothing yet reusing a cell.

This is the "proof-only parameter that still costs" problem of
`docs/proposals/erase-proof-data.md` (SW-2028): marking `queue` `ghost`
would remove the argument at run time, and with it both holds. Nothing in
the reuse analysis is wrong here.

## Cause 2: `Unpack` and `Ctor` are in different bodies

With cause 1 removed, the Bin cells being rebuilt are unique, but:

- `insertWith`/`minView` unpack a node (no token requested) and then call
  `Map.Tree.balance`, which calls `shape` and `rebuild`; `bin` inside
  `rebuild` builds the new `Bin`. `Instr::Unpack`'s token and `CtorReuse`
  pair only inside one body (`code.rs`, `Expr::Ctor` claims from
  `self.tokens` of the body being lowered).
- Even inside one function, a `match` written inside an arm is lifted to a
  separate body (`insertWith.%match1[0]`, `qins.%match2`); the `Unpack`
  stays in the outer body and the arms' `Ctor` is in the lifted one, so the
  token is never in scope. An `if`/`else if` chain keeps both in one body.

**Check [measured]:** a scratch copy of the search over a raw
`Std.Map.Tree` queue (own `qins`/`qmin`/`qpop`, nothing else changed), the
`Keep` case built inline in the same body as the `Unpack`:

| Variant | `Bin` fresh | `Bin` hit | Native user seconds |
|---|---:|---:|---:|
| `qins`/`qmin` calling `Map.Tree.balance` (std's shape) | 25 M | 0.4 M | 7.15 |
| `Keep` built inline, nested `match` (lifted) | `qins` 10.9 M, rotations 6.8 M | 6.8 M (`qmin` only) | 6.90 |
| `Keep` built inline, `if` chain (no lifting) | 6.8 M (rotations) | **17.7 M** | **6.70** |

Both rows beat std's shape and the `if` chain reuses 17.7 M of about 25 M
`Bin` cells. The three variants are about 2.5 s slower than std's
`insertWith` over `Set` in absolute terms (the scratch's compare and wrapper
path differs; not investigated), so only the differences are meaningful:
inline reuse is worth **-0.45 s (6%)** in that scratch, i.e. about 25 ns per
reused node (free plus allocation), well below the estimate in SW-2369's fix 3.

## What would make them reuse

| # | Change | Gain | How estimated | Size/Who |
|---|---|---:|---|---|
| A | **Make `queue` of `searchFrom` a ghost parameter** (SW-2028), or restate `searchFrom` without the duplicate (proofs of `searchFrom`/`restQueued` change). | **-17% on dijkstra** (5.4 s to 4.5 s), and every other graph search | **[measured]**, the hand-written `fastFrom` | Ghost parameters need Matt's decisions D2900-D2905; the restatement is an Opus proof job. Biggest, and independent of B. |
| B | **Build the `Keep` node in the arm that unpacked the old one**: in `insertWith` (Less/Greater arms) and `minView`, `if` on the two size tests and `Bin (Succ (sl + sr)) l2 kk vv r`, falling back to `rebuild (shape …)` only for rotations; `if` rather than `match` so nothing is lifted. | **-6% on top** (0.45 s of 7.1 s in the scratch) once nodes are unique; nothing while they are shared | **[measured]** `qins`/`qmin` vs the `balance` form; the 17.7 M reuse hits are the mechanism | Std Map code, but every theorem about `insertWith`/`minView`/`balance` unfolds `balance`: proving `balance l kk vv r = Bin …` under the two size tests is one lemma, then each existing proof can rewrite with it. Not a small change, so not made here (my experiment with `match`-free arms in std itself fails to check at `Map.Tree.insertWithWithin`, as expected). Sonnet after A. |
| C | **Reuse across a call** in the compiler: let `Unpack`'s token travel to the callee (or inline `balance`/`rebuild`/`bin` into the caller). | The same 6% without touching std's proofs, plus every other persistent-structure update (`Set`, `Map.remove`, `deleteMin`, other libraries) | **[estimated]** B's measured per-node saving times all rebuilds | Opus, native ABI and bytecode (new calling convention for tokens); larger than B. |

Order: A (17%, needs a decision), then B or C (6%), and C only if more
structures than `Map.Tree` benefit.

**Per-node saving [estimated]:** `value::free`, `drop_glue`, `Fields::drop`
and `Rc::drop_slow` plus `mi_free` and `mi_malloc_aligned` are 33% of
dijkstra's self time over 40.4 M cells (SW-2369), about 45 ns per cell;
reuse still writes five fields and checks the count, and the measured
saving is about 25 ns per reused `Bin`.

## Not done

- No change made to std: B touches every theorem about `insertWith`,
  `minView` and `balance`, which is not a small, clearly safe change; A needs
  a decision.
- The absolute 2.5 s gap between std's `Set` and the scratch's raw-tree
  queue is not explained; only differences between scratch variants are
  used.
- `Set`/`Map.remove`/`deleteMin` and other callers of `balance` were not
  counted separately; dijkstra uses only `insertWith` and `minView`.
- No native per-site hit counters: counts are from the interpreter, whose
  reuse rules (`Instr::CtorReuse`, `Instr::Unpack`) are the ones native code
  inlines.
