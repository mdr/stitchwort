# Where native executables spend their time (SW-2296)

SW-2296, 7–8 Nov 2026, Opus, on `lane/SW-2296` from `main` at `99ce66d61`. Ten of the
comparison programs (bench/compare) were built with `stitchwort build --native`, sampled
with samply 0.13.1 (1 kHz), and run again against a runtime library that counts native
code's calls into it. Other lanes were running, so absolute times are rough; the shares
within a profile are what this note uses. Every share is **measured** unless it says
*estimated*.

This checks the hypotheses of [docs/research/lean-runtime-speed.md](../research/lean-runtime-speed.md)
(SW-2318, from reading code) and [SW-2298-native-bignum.md](SW-2298-native-bignum.md).

To redo any of it: `task profile:native -- octopus matcher` (section 4).

## 0. Summary

**The top findings, by share of the program's time:**

1. **Octopus is the grid.** Looking up a cell walks the rows and then the row
   (`Flashed.has` → `Std.List.get`: 24%), and `Position.around` builds three lists per
   octopus per round to find its 8 neighbours (44%). Together about **68%** of octopus.
   SW-2320 confirmed.
2. **The two slowest programs, expressions and scan (about 37 s each), are parsing.**
   Nearly all their time is in `Std.Parse` running on effects and closures. The generic
   apply path, for partial applications and mismatched arity, takes 22%. The effect
   runtime's steps take 15–19%. Freeing closures takes 14%. Expressions makes 262 million
   slow-path applies, 258 million effect steps and 137 million closures. None of the
   hypotheses covers this. It needs a design note (new ticket, below).
3. **Allocation through the runtime costs binary-trees about 30%.** `sw_ctor` is 37% of
   the time, but mimalloc itself is only 8% of that. The rest is Rust's `Rc<[Value]>`
   layout code, the copy of the fields, and the call itself. Freeing through
   `sw_free_emptied` adds 15%. SW-2321 confirmed.
4. **A cell-by-cell loop's hole operations go through the generic `sw_prim`.** These
   are `Hole(New|Fill|Take)`, which `List.map`, `filter`, `append` and `concat` run once
   per cell. Each call also allocates a `Vec` for its arguments. That is 88% of octopus's
   141 million `sw_prim` calls and 99% of matcher's 99 million. `sw_prim` is 19% of
   octopus and 15% of matcher. New ticket.
5. **Big-number copying is 20% of pidigits**, measured. `Value::to_bigint` copies every
   operand (`memmove`, 19%). SW-2302 confirmed. The word-sized `Int` path of SW-2304
   doesn't matter there: native code calls into the runtime only 543,000 times in the
   whole run, under 1% of the time.
6. **Freeing structures recursively costs 15–26% of every AoC program**
   (`sw_drop_words` → Rust drop glue → `mi_free`). Inline freeing (SW-2321) saves only
   the call; the walk over the structure stays. Fewer and smaller cells help here
   (SW-2324), and so does reuse.

**Tooling.** The profiles were unreadable at first, because generated functions were
named `body123`. Three things were added (section 4):
- each compiled body's symbol is now its Stitchwort definition;
- a `call-counts` runtime counts native code's calls into the runtime, split by
  operation;
- `task profile:native` does the whole loop in one command.

What the tools still can't show is in section 3.

## 1. Per-program hotspots

The native time is the check run from `task bench:compare:check` on a loaded machine,
startup (about 0.2 s) included. "Inclusive" includes callees. Tail calls replace the
caller's frame, so inclusive time follows the machine stack, not the source's calls.
Code run by the effect runtime appears under `rt_loop`, not under its caller.

**Self time by kind** (share of samples):

| Program | native s | generated code | allocation¹ | rest of runtime (Rust) | `sw_*` entry points | system² |
|---|---:|---:|---:|---:|---:|---:|
| octopus | 7.2 | 43.0% | 27.0% | 19.8% | 8.6% | 1.6% |
| matcher | 7.7 | 40.6% | 25.1% | 21.2% | 12.0% | 1.0% |
| binary-trees | 2.1 | 47.4% | 36.0% | 0.6% | 7.9% | 8.2% |
| pidigits | 1.4 | 0.6% | 1.5% | 75.5% (num-bigint) | 0.0% | 22.5% |
| memory-game | 4.5 | 32.8% | 37.8% | 21.7% | 6.8% | 0.8% |
| dijkstra | 6.0 | 49.8% | 20.4% | 21.7% | 4.6% | 3.1% |
| disk | 9.8 | 24.9% | 34.6% | 24.4% | 12.3% | 3.4% |
| bridge | 10.5 | 23.4% | 31.3% | 24.3% | 18.6% | 1.9% |
| expressions | 39.0 | 21.6% | 31.7% | 23.9% | 20.1% | 2.1% |
| scan | 37.0 | 21.3% | 30.8% | 25.5% | 20.1% | 2.1% |

¹ mimalloc, plus Rust's `Rc`/`Vec` allocation code (`allocate_for_slice`,
`rc_inner_layout_for_value_layout`, `RawVec` growth).
² Mostly `_platform_memmove`, which in binary-trees is `sw_ctor` copying fields and in
pidigits `to_bigint` copying digits.

**Calls into the runtime** (from the `call-counts` build; the main ones):

| Program | `sw_ctor` | frees³ | `sw_prim` (hole ops) | `sw_apply_prepare` | apply-cache misses | `sw_closure` | `sw_eff_step` |
|---|---:|---:|---:|---:|---:|---:|---:|
| octopus | 65 M | 68 M | 141 M (124 M) | 13 M | 25 M | 10 M | 0 |
| matcher | 22 M | 75 M | 99 M (99 M) | 24 M | 32 M | 20 M | 12 M |
| binary-trees | 68 M | 68 M | 0 | 0 | 0 | 0 | 0 |
| pidigits | 0.05 M | 0.3 M | 0.5 M (0.1 M) | 0 | 0 | 0 | 0 |
| memory-game | 30 M | 30 M | 60 M + 30 M owned (0) | 0 | 0 | 0 | 0 |
| dijkstra | 40 M | 19 M | 7 M (4 M) | 14 M | 15 M | 9 M | 0.3 M |
| disk | 124 M | 98 M | 41 M (39 M) | 26 M | 32 M | 20 M | 25 M |
| bridge | 60 M | 89 M | 23 M (6 M) | 54 M | 66 M | 42 M | 49 M |
| expressions | 208 M | 292 M | 35 M (23 M) | 262 M | 305 M | 137 M | 258 M |
| scan | 194 M | 286 M | 52 M (24 M) | 248 M | 293 M | 119 M | 205 M |

³ `sw_drop_words` (a drop whose count reached zero, the whole structure freed) plus
`sw_free_emptied` (an emptied unique cell).

### octopus (2021 day 11; Lean about 48× faster)

| Function | self | inclusive |
|---|---:|---:|
| `Std.List.get` (from `Flashed.has` → `Grid.at` → `cellAt`) | 18.3% | 21.1% |
| `Aoc.Year2021.Day11.Flashed.has` | 1.4% | 23.8% |
| `Aoc.Common.Position.around` (3 lists per call: two `range`s, `flatMap`, `filter`) | 0.6% | 43.7% |
| `Std.List.count` closure (`at.around.count flashed.has`) | 1.2% | 29.4% |
| `sw_prim` (88% of calls are hole ops, 11% `Nat` `==`) | 4.7% | 19.2% |
| `sw_drop_words` (freeing the neighbour lists) | 0.1% | 16.8% |
| `mi_malloc_aligned` / `mi_free` | 8.8% / 9.3% | |

The machine's per-definition profile agrees: `run --profile` puts 48% of the
interpreter's time in `Std.List.get`, over 282 million steps of the walk for
13.1 million lookups, about 21 cells walked per lookup.

### matcher (2020 day 19; Lean about 16× faster)

| Function | self | inclusive |
|---|---:|---:|
| `Std.Map.Tree.get.%match1` (the rule table, a tree `Map`) | 8.3% | 17.0% |
| `Std.Nat.compare` (called through a function value, `Std.Nat.compare/value`) | 6.6% | 6.8% |
| `Std.List.concat` (`flatMap`'s second pass) | 1.3% | 16.0% |
| `sw_prim` (99% hole ops) | 3.3% | 15.1% |
| `Aoc.Year2020.Day19.parseReceived` (parsing the input) | | 24.1% |
| `sw_apply_prepare` | 4.3% | 8.9% |
| `sw_drop_words` | | 16.5% |

### binary-trees (Lean about 9.5×, but the Lean port is being fixed, SW-2319)

| Function | self | inclusive |
|---|---:|---:|
| `Main.Tree.check` | 32.2% | 47.2% |
| `Main.Tree.make` | 15.0% | 52.1% |
| `sw_ctor` | 5.5% | 37.1% |
| inside `sw_ctor`: `memmove` 7.2%, `rc_inner_layout_for_value_layout` 6.7%, `allocate_for_slice` 6.7%, mimalloc 7.8% | | |
| `mi_free` (through `sw_free_emptied`, as `Tree.check` takes the tree apart) | 10.9% | 15.1% |

Per instruction in `Tree.check` (by hand, from objdump: section 3):
- The per-call bookkeeping is about 15% of the function's self time, about **5% of the
  program**. That is the step count, the frame-limit and stack checks before each of
  its two calls, and the error-flag load after each.
- The prologue and epilogue are another 29% of its self time (9% of the program). They
  save six pairs of callee-saved registers and keep a 272-byte frame, because every
  value is three words.

### pidigits (Lean about 5× faster)

| Function | self | inclusive |
|---|---:|---:|
| `sw_prim` → `prims::int` | | 96–98% |
| `num_bigint` `scalar_mul` | 34.9% | 39.8% |
| `BigUint` `add` | 21.3% | 21.3% |
| `Value::to_bigint` (copying each operand) | 0.2% | 20.3% (19.2% of it `memmove`) |
| `prims::euclid`, `prims::trunc` (division) | | 15.0%, 14.7% |

### memory-game (2020 day 15)

| Function | self | inclusive |
|---|---:|---:|
| `Starting.nextAfter` | 23.1% | 41.5% |
| `sw_prim`: 30 M `Nat.Leq`, 30 M `Array.GetOr` | 3.8% | 17.5% |
| `sw_prim_owned`: 30 M `Array.Set`, its arguments collected into a `Vec` | 1.4% | 12.0% |
| `sw_drop_words` (one cell freed per turn) | | 25.0% |

### dijkstra (2021 day 15)

| Function | self | inclusive |
|---|---:|---:|
| `Std.Map.Tree.insertWith`, `rebuild`, `shape`, `minView`, `get` (the tree `Map` as a priority queue and distance table) | 24.4% | 42% + 14% |
| comparing `Position`s: `Position.%compare`, `Pair.compareWith` (and `/value`), `Nat.compare`, `apply2` | 16.8% | about 18% |
| `sw_drop_words` | | 26.3% |

### disk, bridge, expressions, scan

Parsing with `Std.Parse` dominates.
- **expressions and scan:** `Std.Parse.eachLine` and `parseInstructions` are 99% inclusive.
- **bridge:** `Std.Parse` and the effect runtime are 17% by self time alone.
- **disk:** `parseDiskMap` is 39% inclusive, `compactFiles` 35%.

What the parsing costs, in expressions:
- `sw_apply_prepare` 22.4% inclusive (10.4% self);
- `sw_eff_step` 19.4%;
- dropping closures (`Rc<Fun>::drop_slow`) 15.6%;
- the shared apply stubs `apply1`/`apply2`/`apply4` 12–17% each (overlapping).

Scan is the same within a point or two. Only about 22% of self time is generated code.

## 2. The hypotheses

| Hypothesis (ticket) | Verdict | Measured share |
|---|---|---|
| O(row+column) grid lookup in `Aoc.Common` (SW-2320) | **Confirmed**, the largest single cost measured | octopus: lookup 24%. With `around`'s lists (44%) the grid code is about 68%. |
| Closures not specialised when they capture locals (SW-2135) | **Confirmed where code is higher-order; refuted for octopus** | octopus: apply paths and `sw_closure` together under 5%. matcher: 12–15% (apply 9%, closures 3%, `Nat.compare` through a function value 3%). dijkstra: about 18% comparing keys through `Pair.compareWith` closures. Parsers: much of the 22% apply slow path. |
| A runtime call for every allocation and free (SW-2321) | **Confirmed** | binary-trees: `sw_ctor` 37%, of which about 29% is not mimalloc, plus frees 15%. Elsewhere `sw_ctor` is 3–14%. Recursive freeing (15–26%) stays after it. |
| Per-call bookkeeping: steps, frame limit, stack, error flag (SW-2322) | **Confirmed, at the low end** | binary-trees: about 5% (instruction-level, see section 3 on skid). Another 9% in prologue and epilogue is about register pressure from three-word values, not the checks. |
| Two-pass `List.flatMap` (SW-2323) | **Confirmed, moderate** | matcher: `List.concat` 16% inclusive (an upper bound). octopus: 7.5% inside `around`. |
| Object size (SW-2324) | **Can't tell directly** | Allocation is 20–38% of self time and recursive freeing 15–26%; field copying (`memmove`) is 7% of binary-trees. What would tell: cache-miss counts (not available from samply on macOS), or a direct experiment (section 3). |
| `Int` arithmetic through runtime calls (SW-2304, first half) | **Refuted for pidigits** | 543,000 runtime calls in the whole run, under 1%. The time is the big-number work itself. |
| An argument list allocated per runtime call (SW-2304, second half) | **Confirmed, small** | `Vec` allocation in `sw_prim`/`sw_prim_owned`: octopus 4.1%, matcher 2.5%, memory-game 4.9%, disk 1.4%, each plus the matching free. |
| Big-number copying (SW-2302) | **Confirmed** | pidigits: `to_bigint` 20.3%, almost all `memmove`. |

Not in the hypotheses, and measured:
- **Hole operations through the generic `sw_prim`**, with an argument `Vec` and a clone
  per `Fill`: octopus 17% (88% of `sw_prim`'s 19%), matcher 15%, disk 7%.
- **`Nat` comparisons, `Array.GetOr` and `Array.Set` through `sw_prim`.** In native code
  only `Nat` `Add`, `Sub`, `Mul` and `DivFuel` have an inline fast path
  (`n1.rs`, `Gen::prim`). Memory-game makes 30 million calls each of `Nat.Leq`,
  `Array.GetOr` and `Array.Set` (29.5% together). Octopus makes 15 million `Nat` `==`.
- **`Std.Parse` on effects and combinators** (expressions, scan, bridge; 24% of matcher;
  part of disk): the slow apply path, effect steps and closure churn (section 1).

## 3. What the tools can and can't show

**Fixed in this lane:**
- **Symbol names.** Generated bodies were `body{N}`, so samples in generated code could
  not be tied to definitions. Now each body is named after its definition:
  - `Std.List.get#67`: a global's body, with the body's number from
    `STITCHWORT_NATIVE_DUMP`;
  - `Aoc.Common.Position.around/lambda86/lambda85#321`: a lambda, named after the body
    that makes it;
  - `Std.List.map/value`: a global's adapter as a function value.

  Specialised copies keep the optimiser's names (`Std.List.map[empty][cells]#219`).
- **Call counts.** A sampling profile shows time, but not how many calls it is spread
  over, nor which operation a generic helper ran. With `stitchwort-rt`'s new
  `call-counts` feature, a runtime library counts each helper and each `sw_prim`
  operation, and prints the counts when `STITCHWORT_CALL_COUNTS` is set. It is built
  apart, in `target/profiling/`, and linked through `STITCHWORT_RUNTIME`, so shipped and
  test builds don't have it.
- **One command.** `task profile:native -- NAME... [--top N] [--focus FUNCTION]`. For
  each program it builds the executable and input as the comparison does, then:
  - records with samply to `target/profile/NAME.json.gz`;
  - prints self time by kind, the top functions by self and inclusive time, and the
    callers and callees of each `--focus` function (`dev/profile_top.py`);
  - prints the call counts.

**Still missing, and what each would show** (proposed tickets in section 5):

1. **Instruction-level attribution in generated code.** To split `Tree.check` into its
   real work, reference counting and call bookkeeping, I disassembled it with
   `objdump` and joined it with samples by address, by hand. The fix:
   - set Cranelift's source location on each instruction to the bytecode `pc`
     (`set_srcloc`);
   - emit the `pc` ranges per body;
   - fold samples into bytecode instructions, and those into kinds (step/frame/error
     checks, inc/dec, calls).

   That would turn the SW-2322 and refcount questions into a table. Skid (a sample
   landing on the instruction after a slow one) makes single-instruction counts fuzzy;
   kinds summed over blocks are reliable enough. About 1–2 h.
2. **Call counts per definition in native code.** The machine's `run --profile` has
   them; native code has none. Tail calls and TRMC loops hide callers on the machine
   stack, so inclusive times are approximate. Fix: an `Options` flag that makes each
   body increment its own counter on entry, printed by the counting runtime. About 1 h.
   Done (SW-2331): `build --native --count-bodies` (`Options::count_bodies`); `task profile:native` prints the top 40 bodies by entries, by symbol name.
3. **Effectful code loses its caller.** A handler's continuation runs from `rt_loop`, so
   inclusive time of, say, parsing can't be summed under the function that parses. Only
   self time grouped by name prefix works (how the parse shares above were made). A
   `--group PREFIX` option in `profile_top.py` would make that one command (15 min). A
   real fix would record the definition that installed each handler, so a sample could
   be charged to it.
4. **Memory behaviour.** samply on macOS doesn't read hardware counters, so cache misses
   and memory bandwidth (the SW-2324 question) are invisible. Options:
   - Instruments' CPU Counters template (`xctrace`, Matt's machine only);
   - or settle SW-2324 by experiment: shrink one hot cell kind (a `Nat` field inline)
     and time binary-trees.
5. **The runtime's lines.** `--unstable-presymbolicate` saves symbols only, not lines.
   For which arm of `prims::eval` is hot, the call counts answer it now; for anything
   else, `samply load` on the saved profile. A runtime built with
   `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only` in `target/profiling/` works with it.

## 4. Tooling added

- `crates/native/src/n1.rs` (`body_symbols`): each body's symbol is its definition's
  name and number. Test: `object::each_body_is_named_after_its_definition`.
- `crates/rt/src/call_counts.rs`, `call-counts` feature (also on
  `stitchwort-standalone`): hooks in 16 helpers of `native_abi.rs`, plus `sw_prim` and
  `sw_prim_owned` by operation number. The report prints at the end of a native run
  (`run::run_native_on`). Without the feature, every hook is an empty inline function.
  Test: `call_counts::tests::the_report_counts_helpers_and_operations` (checks the
  counts with the feature, and an empty report without).
- `dev/profile-native`, `dev/profile_top.py`, `task profile:native`.
  `bench/compare/compare.py` now runs `main()` only as a script, so the profiler can
  reuse its `Program` (inputs, arguments, targets).

## 5. Fixes ranked by measured share

The shares overlap: the hole operations in octopus are partly inside `around`, for
example. Each line names the programs where its share is largest.

| # | Fix | Ticket | Measured share | Effort (*estimated*) |
|---|---|---|---|---|
| 1 | O(1) grid cells, and `around` without building lists | SW-2320 | octopus about 68% (lookup 24%, `around` 44%) | 60–90 min |
| 2 | Make `Std.Parse` cheap: a design note on the parser's run-time shape. Options: a polymorphic or PAP fast path in native `Apply`; specialising combinators (SW-2135 widened); `Parse` compiled as a state-passing loop | **new** (Opus, design first) | expressions and scan (the slowest, about 37 s): apply slow path 22%, effect steps 15–19%, closure frees 14%; matcher's parse 24%; bridge 17%+ | design 90 min |
| 3 | Inline allocation and freeing | SW-2321 | binary-trees about 29% (non-mimalloc part of `sw_ctor`) plus part of 15% frees; others 3–14% | 60–90 min |
| 4 | Inline the hole operations (`New`/`Fill`/`Take`) in native code: a store and a load, not `sw_prim` with an argument `Vec` and a clone | **new** (Sonnet or Opus: near the native ABI) | octopus about 17%, matcher about 15%, disk about 7% | 45–60 min |
| 5 | Big numbers by reference | SW-2302 | pidigits 20% | 30 min |
| 6 | Specialise capturing closures and partial applications, including comparison dictionaries (`Ord`) | SW-2135 | dijkstra about 18%, matcher 12–15%, parsers (with #2) | 90 min |
| 7 | Inline fast paths for `Nat` comparisons (`Leq`, `EqNat`, `DecEqNat`) beside `Add`/`Sub`, and `Array.GetOr`/`Set` without the generic path | **new** (Sonnet) | memory-game about 25–29%, octopus about 2%, bridge about 1.5% | 45 min |
| 8 | One-pass `List.flatMap` | SW-2323 | matcher up to 16%, octopus up to 7.5% | 30 min |
| 9 | No argument `Vec` per runtime call | SW-2304 (second half only; drop the `Int` half: under 1% of pidigits) | 1.4–4.9% plus frees | 15–30 min |
| 10 | Cheaper call protocol | SW-2322 | binary-trees about 5% (another 9% in prologue/epilogue is from three-word values, SW-2324) | 60 min |
| 11 | Compact values | SW-2324 (design note) | can't measure directly; allocation 20–38% and recursive freeing 15–26% everywhere are what it would shrink | 90 min note |

Profiling tickets proposed (section 3):
- instruction-to-bytecode attribution for generated code (1–2 h);
- per-definition call counts in native code (1 h);
- `profile_top.py --group PREFIX` (15 min).

Small application-level notes, not ranked:
- octopus computes `cavern.cells.length`, the whole cell list, once per step, only for
  its length;
- it compares whole grids with `next == flashed` each round (`List.decEq` 0.7%).
