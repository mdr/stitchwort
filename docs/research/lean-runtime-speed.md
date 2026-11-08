# Why compiled Lean runs faster than our native executables, and what to take

SW-2318, a paper lane (D3343), 7 Nov 2026, on `main` at `7e29d9834`. Nothing was built or
run. I read:
- the C that `lake build` wrote for every Lean port;
- our native compiler (`crates/native/src/n1.rs`), its runtime (`crates/rt`) and the
  Stitchwort sources of the four programs;
- Lean 4's compiler and runtime at `leanprover/lean4` master `da4295ad` (a sparse clone).

The harness pins Lean v4.34.1 (`bench/compare/lean/lean-toolchain`), so the source I read
may differ from the compiler that wrote the C. Where the two could disagree, I trust the
generated C.

This builds on `docs/research/in-place-reuse.md` (Perceus, reuse tokens),
`docs/research/compilation.md` (cards C1, C13),
`docs/proposals/comparative-speed.md` §7, `docs/proposals/interpreter-speed.md` (stage 4b)
and `docs/reviews/SW-2298-native-bignum.md` (pidigits). It doesn't repeat them.

Labels: **[read]** I read it at the place given; **[inferred]** my reasoning, which a
profile or a count should confirm; **[cited]** from a source outside the repository, named.

The rough smoke ratios this note explains (Lean = 1, bigger is slower): binary-trees,
native 9.5 (CPython 32); pidigits, native 5 (CPython 1.9); octopus, native 48;
matcher, native 16.

## 0. Summary

**The answer in one paragraph.** Lean isn't fast through one trick. Five things add up,
and they matter differently on each program:
1. Lean specialises higher-order code to the exact closure it is given, and closures that
   capture local variables count too: their captures become extra parameters. The loops
   come out with direct calls and no closure allocation. Our optimiser specialises only
   for closures that capture nothing.
2. Lean's objects are small: an 8-byte header, and 8 bytes per field, with small numbers
   stored inside the pointer. Ours have a 16-byte header and 24 bytes per field. A tree
   node is 24 bytes in Lean and 64 bytes here.
3. Lean allocates and frees inline, through a small-object allocator. Our native code
   makes a runtime call for every constructor and every free.
4. Lean borrows read-only parameters (no reference-count traffic) and has no per-call
   bookkeeping. Every call in our native code counts a step, checks the frame limit and
   the stack pointer, and then checks an error flag in memory.
5. The ports use different data structures. Lean's octopus uses a flat `Array`, and its
   matcher a `HashMap`. Our AoC days use a list-of-lists grid with O(row + column) lookup,
   and a tree `Map`.

One finding changes a headline number. **The binary-trees comparison isn't valid as it
stands.** Lean's compiler merged the two identical calls `Tree.make depth` into one
(common subexpression elimination), so Lean builds a shared tree of `depth + 1` nodes
where we and CPython build `2^(depth+1)` nodes. Lean's own copy of this benchmark adds a
dummy argument "to suppress the common sub-expression elimination optimization" (§2.1).
Fixed, the real native/Lean gap on binary-trees is perhaps 2–3×, not 9.5× **[inferred]**.

**Top takeaways, by expected payoff on these programs (all estimates [inferred]):**

| # | Take | Programs it helps | Estimated effect | Fits |
|---|---|---|---|---|
| 1 | Fix the binary-trees Lean port; audit the other ports' C for removed work | binary-trees (the measurement) | 9.5× becomes about 2–3× on paper | new, small |
| 2 | O(1) grid cells in `Aoc.Common` (array-backed `Grid.at`/`map`), and `around` without building lists | octopus, every grid day | octopus 48× → about 5–10× | new; next to SW-1369, SW-1475 |
| 3 | Specialise on closures and partial applications that capture locals, with captures as extra parameters (Lean's `specialize`) | matcher, octopus, any `map`/`flatMap`/`count` with a lambda | matcher 1.5–3×; octopus 1.3–2× on what's left after 2 | SW-2135, widened |
| 4 | Inline allocation and freeing in native code | binary-trees, everything that allocates | 10–25% | new; in-place-reuse.md §3.1 "drop specialisation" |
| 5 | Compact values: 8-byte fields, a small header (design note first) | binary-trees, matcher, every list and tree | 1.3–2× on allocation-heavy code | new (D3358); compilation.md C13 |
| 6 | A cheaper call protocol in native code (frame limit and error flag in registers) | binary-trees, matcher (call-heavy) | 5–20% | new |
| 7 | `List.flatMap` in one pass | matcher | 5–15% | new, small |
| 8 | pidigits: SW-2302 to SW-2305 as already planned | pidigits | as SW-2298 says | existing |

## 1. Where Lean's speed comes from

Each mechanism is tied to the generated C (in the scratchpad's `lean-ir/Compare/*.c`,
cited as `Octopus.c:342`) or to Lean's source (`lean4/…`).

### 1.1 Specialisation, including closures that capture locals

**Plain version.** When a loop is written with `for`, `flatMap` or `Array.ofFn` and a
lambda, Lean compiles a private copy of the loop with the lambda's body pasted in. The
lambda's captured variables become ordinary parameters of the copy. So there is no
closure to allocate and no indirect call per element.

**Evidence.**
- In octopus, `flashersAround`'s two nested `for` loops become two C functions named
  `forIn'_loop___at___00Cavern_flashersAround_spec__0` and `__1`. Their parameters are
  `row, column, flashed, cavern` and the loop state, and their bodies are straight-line
  arithmetic and `lean_array_get` with no allocation (`Octopus.c:342-480`) **[read]**.
- In matcher, `sequences.flatMap fun sequence => endsWithAll table message fuel sequence
  position` becomes `List_flatMapTR_go___at___00endsWith_spec__1(table, message, n,
  position, …)`, which calls `endsWithAll` directly (`Matcher.c:1735`, `:1798`)
  **[read]**.
- `HashMap.get?` at `Nat` is specialised too: the hash is three inline shifts and xors,
  then a bucket index (`Matcher.c:1577-1599`) **[read]**.
- The mechanism is `lean4/src/Lean/Compiler/LCNF/Specialize.lean`. `mkSpecDecl` takes
  "`params`: new parameters that arguments in `argMask` depend on", and specialises
  `fixedHO` (fixed higher-order) and `fixedInst` (instance) parameters
  (`SpecInfo.lean:16-50`) **[read]**. Specialisations are cached across modules
  (`specCacheExt`), and nothing caps how many there are **[read]**.

**Ours.**
- `opt.rs` copies a recursive function for a known argument only when that argument is a
  global, a partial application of constants, or a closure that captures nothing
  (`known_function`, `crates/rt/src/opt.rs:1198-1209`) **[read]**.
- A program may have at most 64 copies (`COPIES`, `opt.rs:61`) **[read]**.
- So `at.around.count flashed.has` (octopus) and `leftAfterWith table.get …` (matcher)
  aren't specialised: `flashed` and `table` are local variables **[read]**.
- Each call of such a function value goes through native code's apply path. Its fast
  path is only for "a function value to exactly its arity with nothing yet applied". A
  partial application such as `table.get` goes through the shared stub and
  `sw_apply_prepare` (`n1.rs` header, "Closures") **[read; that these sites take it is
  inferred]**.
- Each closure costs two allocations, the `Rc<Fun>` and the `Box` of captures
  (`value.rs:89`) **[read]**.
- interpreter-speed.md's stage 4b (SW-2135) already plans copies for capturing lambdas.
  What Lean adds is the scope: partial applications of locals, the loop helpers in std,
  and no small global cap.

### 1.2 Small objects with small numbers inside the pointer

**Plain version.** A Lean value is one machine word. If its low bit is 1, it *is* a small
number (or a constructor without fields); otherwise it points to an object with an
8-byte header. Our value is three words, and a constructor's fields are three words
each. So every cons cell, tree node and record is about 2.7 times bigger here, which
means more memory traffic and more cache misses.

**Evidence.**
- Lean's header is `int m_rc; unsigned m_cs_sz:16; unsigned m_other:8; unsigned m_tag:8`,
  8 bytes (`lean4/src/include/lean/lean.h:179-183`) **[read]**.
- `lean_box(n)` is `n << 1 | 1` (`lean.h:367`) **[read]**.
- A `Tree.node` is `lean_alloc_ctor(1, 2, 0)`, 8 + 2 × 8 = 24 bytes
  (`BinaryTrees.c:176`) **[read]**.
- Scalar fields are stored unboxed after the pointers: matcher's `Rule.letter` keeps its
  `Char` as a raw `uint32` (`lean_ctor_get_uint32`, `Matcher.c:1658`) **[read]**.
- Ours: `Value` is a 3-word `repr(u8)` enum (`crates/rt/src/value.rs:27-54`). A
  constructor is `Data(u32, Fields(Rc<[Value]>))`. `Rc` puts a strong and a weak count
  (16 bytes) before the fields, and each field is a 24-byte `Value` **[read]**.
  - A `Node l r` is 16 + 48 = 64 bytes against Lean's 24.
  - A `[n, ..rest]` cell is also 64 against 24.
  - A `Position { row, column }` is 64 against 24 **[inferred from the layouts]**.
- compilation.md C13 already records a 5× gap, measured on a hand translation of the
  `Set` insert to Rust, between numbers boxed as our values and numbers unboxed in the
  nodes (native-compilation.md §0). That is an upper indication, not a measurement of
  the runtime.

### 1.3 Allocation and freeing inline

**Plain version.** Building a Lean constructor is a few inline instructions plus a call to
a small-object allocator. Our native code stages the fields on the stack and calls into
Rust, which then allocates through `Rc`.

**Correction (SW-2360).** Lean 4.13 had its own small-object allocator; 4.34 (the version
compared here) calls mimalloc's small-object entry inline instead, with mimalloc compiled
into the same C file (`lean.h:510-600`, `runtime/mimalloc.cpp`). See
docs/proposals/cell-allocator.md.

**Evidence.**
- Lean: `lean_alloc_ctor` → `lean_alloc_ctor_memory` → `lean_alloc_small_object`
  (`lean.h:527-560`, `:864`, all `static inline`) **[read]**. The fields are then
  written directly (`lean_ctor_set`, `BinaryTrees.c:177-178`) **[read]**.
- `lean_dec_ref` is inline: decrement if the count is above 1, otherwise call
  `lean_dec_ref_cold` (`lean.h:741-748`) **[read]**.
- Closed constant objects have `m_rc = 0` and are never counted (`BinaryTrees.c:38`,
  `.m_rc = 0`) **[read]**.
- Ours: `Ctor` stores each field to a temporary stack slot, then calls `sw_ctor`
  (`n1.rs:3439-3450`). That calls `Rc::<[Value]>::new_uninit_slice` and copies the
  fields in (`crates/rt/src/native_abi.rs:1376-1390`) **[read]**.
- A unique cell taken apart by `Unpack` is freed by a call to `sw_free_emptied`
  (`n1.rs:4091`) **[read]**.
- Both runtimes use mimalloc: ours by `#[global_allocator]` in
  `crates/standalone/src/lib.rs`; Lean's when built `USE_MIMALLOC`
  (`lean4/src/CMakeLists.txt:135`). I didn't check whether nixpkgs' Lean is built
  with it **[read; unchecked for the nix build]**. So the difference is the call
  path and staging, not the allocator.

### 1.4 Borrowed parameters, and no per-call bookkeeping

**Plain version.** When a Lean function only reads an argument, it takes it "borrowed":
the caller doesn't increment its count and the callee doesn't decrement it. And a Lean
call is a plain C call. Ours does four checks around every call.

**Evidence.**
- Lean: `Tree.check` never touches its argument's count. Only its `_boxed` wrapper, used
  when it is called as a closure, decrements (`BinaryTrees.c:193-224`) **[read]**.
- `endsWith` passes `table` and `message` down the recursion with no `lean_inc` or
  `lean_dec` on either (`Matcher.c:1610-1740`) **[read]**.
- The passes are `inferBorrow`, `explicitRc`, `insertResetReuse`, `expandResetReuse` and
  `coalesceRC` (`lean4/src/Lean/Compiler/LCNF/Passes.lean:146-153`) **[read]**.
- Ours: arguments are always owned (in-place-reuse.md §1.2). A value read again later is
  cloned (an increment) when it's passed **[read there]**.
- Each native `Call` also does three things (`n1.rs:3178-3191`) **[read]**:
  - it counts a step: the pinned register, decremented and compared (`n1.rs:2891-2899`);
  - it checks the frame limit, which loads the limit from the context, then compares the
    stack pointer with a floor also loaded from the context (`n1.rs:2909-2924`);
  - after the return, it loads the context's error word and branches
    (`n1.rs:2928-2944`).
- That is roughly 10–12 instructions and three loads per call **[inferred from the
  code]**. A `Tree.check` node visit in Lean is about as long (`BinaryTrees.c:193-217`).
- The step counter and the frame limit are semantics (D1253: a run runs out at the same
  point on every runner), so they stay. The stack-pointer test is a backstop "the
  build's stack sizing keeps from firing" (`n1.rs:2916-2917`) **[read]**.

### 1.5 Common subexpression elimination

**Plain version.** If a function computes the same pure expression twice, Lean computes
it once and uses the result twice. Our optimiser doesn't.

**Evidence.**
- `cse` runs three times in Lean's pipeline (`Passes.lean:96`, `:115`, `:138`)
  **[read]**.
- `Tree.make` calls itself once and stores the same result in both fields: `lean_inc` of
  the result, then `lean_ctor_set(…, 0, x); lean_ctor_set(…, 1, x)`
  (`BinaryTrees.c:174-179`) **[read]**.
- `opt.rs` has no such pass (its rules are listed at `opt.rs:1-33`) **[read]**.

### 1.6 The rest: smaller, or already planned

- **Big numbers.** `lean_int_mul`, `lean_int_ediv` and friends are inline for small
  values, and call GMP-backed `mpz` for big ones (`Pidigits.c` uses `lean_int_mul` 11
  times; `lean4/src/runtime/mpz.cpp:175`, `:207`) **[read]**. SW-2298 covers our side.
- **Unboxed results.** Lean functions returning `Bool` return `uint8_t`
  (`Cavern_flashRound___lam__0`, `Octopus.c:608`), with a `_boxed` wrapper for closure
  calls **[read]**. Ours always return three words. That is cheap in registers, so it
  is small **[inferred]**.
- **The C compiler.** clang `-O3` inlines lean.h's helpers and allocates registers
  globally. Cranelift (`opt_level = "speed"`, `n1.rs:509`) does less. I'd put it at
  1.1–1.5× at most here, small next to the items above **[inferred; not measured]**.
- **Arithmetic and comparisons on small numbers.** These are inline on both sides:
  - Lean: `lean_nat_add`'s scalar fast path (`lean.h:1731-1736`);
  - ours: tag checks plus `uadd_overflow` (`n1.rs:3896-3950`) and inline comparisons
    (`n1.rs:3968-3995`).
  Not a gap, except `Int` in native code, which always calls the runtime (SW-2304)
  **[read]**.
- **Dictionary passing for `Ord`/`Eq`.** `opt.rs` already copies functions at known
  instance constants (`known_argument`, `opt.rs:1215-1220`), so it isn't a major cost in these four
  programs **[inferred]**.

## 2. The four programs

### 2.1 binary-trees (native 9.5×)

The programs: `bench/compare/binary-trees/main.sw` and
`bench/compare/lean/Compare/BinaryTrees.lean`, both written `Node (make d) (make d)`.

| Rank | Cause | Confidence |
|---|---|---|
| 1 | **Lean's CSE turns the benchmark into a walk.** Lean's `Tree.make` builds `depth + 1` shared nodes; we build `2^(depth+1) − 1`. At depth 18 the iterations allocate about 2^23 nodes each, eight times: about 68 M allocations and frees for us and CPython, about 1.5 M for Lean. Both still visit all 68 M nodes in `check`, since Lean's `check` doesn't know the tree is shared | the CSE is **[read]** (`BinaryTrees.c:174-179`); the counts **[inferred]** from the loop bounds |
| 2 | Our cells are 64 bytes against 24, allocated and freed by runtime calls (§1.2, §1.3) | **[read]**; the share is **[inferred]** |
| 3 | Per-call checks (§1.4): two calls per node in `make` and two in `check` | **[read]**; the share is **[inferred]** |
| 4 | `check` is borrowed in Lean, but ours consumes the tree as it walks, which frees it on the way. That is work Lean does too, after the walk, so it's not a gap | **[read]** |

Lean's own benchmark, `tests/compile_bench/binarytrees.lean`, writes `make' (n d :
UInt32)` and calls `.node (make' n (d - 1)) (make' (n + 1) (d - 1))` under the comment
"This function has an extra argument to suppress the common sub-expression elimination
optimization" **[cited: fetched from GitHub for this note]**.

With the port fixed, I'd expect Lean's time to rise 3–5×, because it starts allocating.
That puts native at about 2–3× Lean, and CPython at about 6–10× Lean instead of 32×
**[inferred]**.

### 2.2 octopus, 2021 day 11 (native 48×)

The programs: `aoc/src/Aoc/Year2021/Day11/Day11.sw`, on `Aoc.Common.Grid`, and
`bench/compare/lean/Compare/Octopus.lean`, on a flat `Array Nat`. The Python port pads a
list of lists, so it also reads a cell in O(1).

| Rank | Cause | Confidence |
|---|---|---|
| 1 | **Each cell lookup walks lists.** `Flashed.has` calls `Grid.at`, which calls `cellAt`: `rows.get row`, then `row.get column`, O(row + column) list steps, plus a `Some` (`Grid.sw:111-114`, `Day11.sw:57`). Lean reads `flashed[r * width + c]!` (`Octopus.c:389`). Eight lookups per cell per round | **[read]** |
| 2 | **`Position.around` builds about 9 records and about 25 list cells per call.** That is a `List.range` of rows, a `flatMap` over 3 ranges and maps of columns, then a `filter`, with a closure per stage (`Grid.sw:72-75`). Lean's loops allocate nothing (`Octopus.c:342-480`) | the code is **[read]**; the counts **[inferred]** |
| 3 | `count flashed.has`, `cavern.flash (at level => …)` and `mapWithIndex`'s lambdas aren't specialised, because they capture locals (§1.1). Each element is a call through the apply path, and each round allocates closures | **[read]** opt.rs; **[inferred]** for these sites |
| 4 | Each round rebuilds the grid as lists (`Grid.map` → `mapCells`, `Grid.sw:130`, `:198`), compares it with the last by structural equality (`Day11.sw:79`), and rebuilds `cells` just to take its length for the fuel (`Day11.sw:84`). Lean uses `Array.ofFn` and `isEqv` on arrays | **[read]** |
| 5 | Cell size, allocation path, call checks (§1.2–1.4) on everything above | **[inferred]** |

Ranks 1 and 2 are about the data structure and the algorithm, not the compiler. The other
two languages read a cell in O(1); we don't. So most of the 48× would go if the grid were
array-backed, even with no compiler change **[inferred]**. `Grid.lookup` already gives
O(1) reads through arrays (`Grid.sw:204`), but `Grid.at` and `Grid.map` don't use it.

### 2.3 matcher, 2020 day 19 (native 16×)

The programs: `aoc/src/Aoc/Year2020/Day19/Day19.sw` and
`bench/compare/lean/Compare/Matcher.lean`. The algorithms match: both return the list of
ways to continue, ours as suffixes of the message and Lean's as positions in an array.

| Rank | Cause | Confidence |
|---|---|---|
| 1 | **Higher-order calls that aren't specialised.** `leftAfterWith` is handed `table.get`, a partial application of a local (`Day19.sw:168`). So every rule lookup is an apply of a partial application through the runtime stub. Each `flatMap` builds a closure capturing `rule`, `more` and `message` (two allocations, three increments) and calls it per element. Lean's copy of the loop takes `table` and `message` as parameters and calls `endsWithAll` directly (`Matcher.c:1735`, `:1798`) | **[read]** both sides; the stub path is **[inferred]** from `n1.rs`'s rules |
| 2 | **A tree `Map` with `Ord` against a `HashMap`.** Each lookup descends about 7 levels for about 130 rules, against one hash and a bucket (`Matcher.c:1577-1599`) | **[read]**; the depth **[inferred]** |
| 3 | `List.flatMap xs f` is `List.concat (List.map xs f)` (`crates/elab/src/std/List/Toolkit.sw:787`): two passes and an intermediate list of lists. Lean's `flatMapTR` appends into one `Array` (`Matcher.c:1764`) | **[read]** |
| 4 | Reference counting: `rule` and `message` are owned, so they are cloned on each recursive call and dropped at its end. Lean borrows both (§1.4) | **[read]**; the share is **[inferred]** |
| 5 | Cell size, allocation path, call checks | **[inferred]** |

### 2.4 pidigits (native 5×)

`docs/reviews/SW-2298-native-bignum.md` already ranks this. The causes are full divisions
for a one-digit quotient, copies of both operands before every operation
(`prims.rs:274`, `value.rs:217`), and native code calling the runtime for every `Int`
operation. Its tickets are SW-2301 to SW-2305. I found two things to add:
- `div_rem_magnitude`'s small-quotient path (`crates/rt/src/prims.rs:305-329`) still
  computes `d >> shift` and `a >> shift` as whole new numbers just to read their top 64
  bits. That is two O(n) allocations and copies per division where reading the top limbs
  would do **[read]**. It belongs with SW-2302.
- Lean, like us, allocates a fresh number for every result (`lean_int_mul` returns a new
  `mpz` object). So once SW-2302 and SW-2303 land, what remains is GMP's kernels against
  `num-bigint`'s, which is SW-2305's question **[inferred]**.

## 3. What to take

Each entry follows the brief rules: the problem, the change, and what it should do. Every
effect below is an estimate **[inferred]**, to be confirmed by SW-2295's measurement.

### 3.1 Make the comparison honest first

- **Problem.** The binary-trees row says we are 9.5× slower than Lean. Most of that is
  Lean skipping the allocation the benchmark exists to measure.
- **Change.** Write the Lean port as Lean's own benchmark does (an extra argument, `make'
  n d`, so the two calls differ), and check the answer is unchanged. Then read each port's
  generated C for any other work the compiler removed: CSE'd calls, closed terms hoisted
  to start-up. A quick scan found only small closed constants in matcher, pidigits and
  dijkstra (`grep _closed__` over the C files) **[read]**.
- **Should do.** Binary-trees' Lean time rises, perhaps 3–5×, so the ratios fall to
  about 2–3× (native) and 6–10× (CPython). Do this before SW-2295 measures. It costs
  20 minutes.

### 3.2 O(1) grid cells (octopus and every grid day)

- **Problem.** A day that reads a neighbour's cell walks the rows and then the columns.
  On a 100 × 100 grid that is about 100 list steps per read.
- **Change.** In `Aoc.Common`, have `Grid` keep an array copy of its rows, built once,
  and have `Grid.at` read it in O(1). Keep `rows: List (List a)` as the specification the
  proofs use. Then add an `around` that doesn't build lists: a fold over the eight
  offsets, next to SW-1475's compass offsets. The alternative, a `Grid` whose only field
  is an array, would mean re-proving the Grid lemmas. A cached view keeps the proofs as
  they are (`Grid.lookup`, `Grid.sw:204`, already builds the table).
- **Should do.** Octopus from 48× to about 5–10× Lean. Grid days gain on `run` as well
  as native.
- **Costs and limits.** An array copy per grid, and a lemma that `at` agrees with
  `cellAt` (std's `Array` is specified as a list, SW-112). It rules out nothing.
- **Fits.** New. It sits beside SW-1369 (rows as `NonEmptyList`) and SW-1475.

### 3.3 Specialise on capturing closures and partial applications (Lean's `specialize`)

- **Problem.** `xs.count flashed.has`, `xs.flatMap (s => go rule more s message)` and
  `leftAfterWith table.get` each make closures and call through function values once per
  element, because the function captures a local.
- **Change.** SW-2135 (interpreter-speed stage 4b) already plans copies of recursive
  functions for capturing lambdas. Widen it the way Lean does:
  - take partial applications of locals too (`table.get`), not only lambdas;
  - add the captures as new parameters of the copy (Lean's `mkSpecDecl` `params`);
  - specialise only fixed parameters (passed on unchanged in the recursion: Lean's
    `fixedHO`), so copies don't recurse without end;
  - replace the global cap of 64 copies (`opt.rs:61`) with a per-call-site or size
    budget, which runs out with a note, never silently.
- **Should do.** Matcher about 1.5–3×, octopus about 1.3–2× on what's left after §3.2.
  It helps on `run` as well as native, as interpreter-speed.md estimates (up to about 2×
  on SW-1672-shaped loops).
- **Costs and limits.** Code size, and optimiser risk: Opus, with the differential tests.
  The allocation traces change, so the snapshots are regenerated. Step counts fall, as
  with today's inlining.

### 3.4 Inline allocation and freeing in native code

- **Problem.** Every constructor in native code stages its fields on the stack and calls
  `sw_ctor`, and every free calls `sw_free_emptied` or `sw_drop_words`.
- **Change.**
  - Emit the allocation in Cranelift: call mimalloc's small-object entry for the size
    (known at compile time from the arity), write the counts and fields straight from
    registers, and keep `sw_ctor` for the trace builds. `probe_layout` already pins `Rc`'s
    layout for the strong and weak offsets.
  - Free a unique emptied cell of known arity the same way.
  - in-place-reuse.md §3.1 lists the freeing half as "native could inline the unique-cell
    free of known arity".
- **Should do.** 10–25% on allocation-heavy programs (binary-trees, list days).
- **Costs and limits.** More `unsafe` layout knowledge in `n1.rs` (already there for the
  counts). Traces must still agree, so the trace build keeps the helper path.

### 3.5 Compact values (the biggest structural lever)

- **Problem.** Every list cell, tree node and record is about 2.7× Lean's size (§1.2), so
  memory traffic and cache misses grow with it.
- **Two designs to compare in a note.**
  - **A. One-word values everywhere** (Lean, OCaml). Small `Nat`/`Int` are tagged
    (63-bit), and everything else points to an object with an 8-byte header holding the
    kind, tag, arity and a 32-bit count.
    - Costs: a `Float` must be boxed wherever its type isn't known, and our IR keeps no
      types after erasure, so Float-heavy code would allocate. The one-form rule moves to
      63 bits. The machine, native code, the codec, the allocation trace and
      `probe_layout` all change.
  - **B. Compact cells, three-word registers.** Fields are stored as one tagged word;
    heap values (big numbers, `Text`, closures) get a uniform header, so one word can
    point to any of them. Registers and the calling convention keep three words, and
    native code converts at `Field` and `Ctor`.
    - Gets most of the memory saving and leaves the calling convention alone. It is
      probably a step towards A.
- **Should do.** 1.3–2× on allocation-heavy native code. C13's 5× from the hand-written
  Rust `Set` is the optimistic end.
- **Costs and limits.** The largest change here, mostly `unsafe` runtime code. It goes
  with SW-593 (effect representation), which also rewrites `Fun` and the effect nodes.
  Migration cost doesn't count (D2303), so the question for Matt is the end state:
  D3358.

### 3.6 A cheaper call protocol in native code

- **Problem.** Every call does about 10–12 instructions and three loads of bookkeeping
  (§1.4). In `Tree.check` that is about as long as the work.
- **Change.**
  - Pass the frames still allowed in a register, counting down as the steps already do,
    instead of loading the limit from the context per call.
  - Drop the per-call stack-pointer comparison where the build's stack sizing already
    rules it out. Keep a guard page, or a check in bodies with unbounded frames.
  - Return the error in the result's first word (a reserved tag) instead of loading the
    context's error word after every call.
- **Should do.** 5–20% on call-heavy native code. Steps and frame limits stay exact
  (D1253), so `E-RESOURCE` points don't move.
- **Costs and limits.** It touches the exits and `stack_for`'s reasoning, so it's Opus
  work. It rules out nothing.

### 3.7 One-pass `List.flatMap`

- **Problem.** `flatMap` builds the whole list of lists and then concatenates it.
- **Change.** Define it by direct recursion (`f x` appended to the rest), with the
  current definition kept as a theorem (`flatMap xs f = concat (map xs f)`), so the
  proofs that use it still go through.
- **Should do.** Matcher 5–15%, and any search written with `flatMap`.
- **Fits.** New, small; std work.

### 3.8 Already planned, and confirmed by this reading

- **Borrowed parameters.** D2276 gates them on SW-1811's measurement. Lean borrows
  exactly the parameters these programs pass down unchanged (`table`, `message`, `cavern`,
  `flashed`). Add matcher and octopus to SW-1811's program list. No new ticket.
- **Reuse across helpers** (SW-1812) helps `Map` inserts, not these four programs much.
- **pidigits:** SW-2302 (plus the shift copies in §2.4), SW-2303, SW-2304, and SW-2305
  for GMP's question.

## 4. What not to take

- **CSE of calls that allocate.** It is what made Lean's binary-trees fast, but it creates
  sharing. Sharing defeats our in-place reuse: a uniquely held cell or `Array` that two
  uses now share gets copied instead of updated. Real programs rarely compute the same
  expensive pure call twice on purpose. CSE of non-allocating expressions (arithmetic,
  field reads) is harmless but buys little after `opt.rs`'s inlining. D3359 asks.
- **Lean's multi-threaded reference counts.** Its objects can be marked shared between
  threads, with atomic counts (`lean_is_st`, `lean.h:642`, `:783-789`). A Stitchwort run is one
  thread (in-place-reuse.md §1.3), so we already have the cheap case.
- **Dropping steps or frame limits.** They are what makes `E-RESOURCE` agree across
  runners (D1253). Take the cheaper encoding (§3.6), not the removal.
- **A C backend through clang.** It would get clang's inlining and register allocation,
  at the cost of a C toolchain at build time, slower builds and a second code generator
  to keep in step with the machine. The gaps above are much larger than Cranelift's.
- **Type-directed unboxing** (Lean's `explicitBoxing`, `UInt8`/`UInt32`/`Float`
  parameters and `_boxed` wrappers). It needs the types in the IR, and ours are erased
  before the rt IR. Our small numbers aren't heap-allocated anyway; our cost is their
  size (§3.5), not boxing.
- **`@[implemented_by]` and `unsafe` escape hatches** as a speed tool. Lean's std uses
  them for `Array` and `HashMap` internals. Our equivalent is a trusted native, bound by
  hash with differential tests (SW-112, SW-1825), and that discipline should stay.
- **A std `HashMap` now.** It would help matcher's lookups (rank 2). But it needs a
  `Hash` interface and a specification as a map for the proofs, nat-map.md (SW-1603)
  found tree `Map`'s cost mostly elsewhere, and SW-1825's native `Map.Tree.get` attacks
  the same lookups without a new type. Revisit after SW-1825 is measured.

## 5. Decisions for Matt

- **D3358.** Is compact values the end state for the runtime, so a design note can choose
  between one-word values everywhere (A) and compact cells with three-word registers (B),
  in step with SW-593's effect representation? **[rec: yes, a note first.** It is the one
  structural gap that touches every allocating program (64 bytes against 24 per cell). It
  is too big to start without a chosen end state, and it changes how `Float` is held.**]**
- **D3359.** Should the optimiser merge repeated pure calls (common subexpression
  elimination), as Lean does? **[rec: no, for calls that may allocate.** It mostly helps
  benchmarks, and the sharing it creates blocks in-place reuse and array updates. Fixing
  the Lean port (§3.1) is the orchestrator's call and needs no decision.**]**

Calls I made:
- the order of the tickets below;
- putting the grid fix in `Aoc.Common` (a cached array view) rather than changing the
  day, so the proofs stay as they are;
- adding the shift copies to SW-2302 rather than filing a ticket;
- treating borrowing as SW-1811's evidence, not a new ticket.

## 6. What I didn't cover

- **Nothing was timed or counted.** Every share and effect in §2 and §3 is inferred from
  the code. SW-2295's measurement, with an allocation count per program, should confirm
  or refute the rankings.
- **Dijkstra, memory-game, disk, expressions, scan and bridge.** These weren't in the
  brief's measured four, so I didn't read their Lean C.
- **The Lean version.** I read the Lean source at master. The harness's v4.34.1 wrote
  the C, which I read as it is.
- **Whether nixpkgs' Lean uses mimalloc and GMP.** Inferred from the defaults, not checked.
- **Cranelift against clang on the same code.** Not compared.
- **The papers.** Counting Immutable Beans and Perceus are used through compilation.md C1
  and in-place-reuse.md, not reread.

## 7. Tickets to file

In order of expected payoff for the native/Lean gap. Each runs only the targeted tests
named.

1. **[Sonnet or DeepSeek, 20 min] binary-trees' Lean port defeats CSE**, as Lean's
   `tests/compile_bench/binarytrees.lean` does (`make' n d`). Read every port's generated
   C for other removed work (CSE'd calls, closed terms hoisted to start-up), and note the
   result in `bench/compare/README.md`. *Tests:* `task bench:compare:check --
   binary-trees` (answers only). Do it before SW-2295.
2. **[Sonnet, 60–90 min] `Aoc.Common.Grid`: O(1) `at` and `map` through a cached array
   view, and `Position.around` as a fold over offsets**, with a lemma that `at` agrees
   with `cellAt`. Switch 2021 day 11 to it. *Tests:* `task test:one` on the Grid tests
   and day 11's; `task audit:touched -- Aoc.Common`. Expected: octopus 48× → about
   5–10×. It touches SW-1475's offsets, so it runs after SW-1475 or absorbs its offsets
   half.
3. **[Opus, 90 min] Widen SW-2135**, not a new ticket: specialise on partial applications
   of locals as well as capturing lambdas, captures as extra parameters, fixed
   parameters only, and a per-site budget in place of `COPIES = 64` that runs out with a
   note. *Tests:* the optimiser tests, the differential closure programs, `run --native`
   on `closures.sw`, then matcher's answer check. Expected: matcher 1.5–3×. It runs one
   after the other with SW-1812, as planned.
4. **[Opus, 60–90 min] Native code allocates and frees cells inline** (a direct
   small-object call of known size, fields stored from registers, the inline free of a
   known-arity emptied cell), with the helper path kept for trace builds. *Tests:* the
   native agreement and trace tests (`task test:lane AREA=native`). Expected: 10–25% on
   binary-trees.
5. **[Opus, 90 min, paper] Design note: compact values**, after D3358. It compares A
   and B (§3.5) with SW-593's effect representation, measures C13's `Set` case on
   today's native code, and plans the stages.
6. **[Opus, 60 min] A cheaper native call protocol**: the frame limit as a counted
   register, the stack-pointer check only where the stack sizing doesn't rule it out,
   and the error returned in the result's words. *Tests:* the native `E-RESOURCE` and
   step-count agreement tests, `task test:lane AREA=native`. Expected: 5–20% on
   call-heavy code.
7. **[Sonnet, 30 min] One-pass `List.flatMap`**, keeping `flatMap = concat ∘ map` as a
   theorem. *Tests:* std's List tests, the std audit for the module, and day 19's tests.
   Expected: matcher 5–15%.
8. **Notes on existing tickets, not new ones:**
   - SW-2302: also drop the two whole-number shifts in `div_rem_magnitude`'s
     small-quotient path (`prims.rs:315-316`); read the top limbs instead.
     *Correction (SW-2302, 8 Nov 2026): in num-bigint 0.5.1 `&BigUint >> n` copies only
     the digits above the shift, one or two words here, so these aren't whole-number
     copies; left as they are.*
   - SW-1811: add matcher and octopus to the programs whose read-only increment share it
     measures.
   - SW-2295: run after ticket 1, and record allocations per program beside the times.
