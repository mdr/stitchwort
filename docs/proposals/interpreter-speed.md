# Interpreter speed: where the machine's time goes, and what to change first

**Status:** design note, 7 November 2026 (SW-813). Read only: nothing was
built, run or profiled for it. Every measured number below comes from an
earlier note and says which one. The questions for Matt are D3060 and D3061,
[at the end](#7-questions-for-matt).

Claims are marked:
- **[source]**: read in the code at `4af1dbf25`, with `file:line`;
- **[measured earlier]**: a number another note or the AoC notes recorded,
  with where;
- **[inferred]**: my reasoning from the code and those numbers, not tested.

## Summary

**The problem, plainly.** `stitchwort run` is slow on every AoC day that
does real work. 2021 day 15 takes about 20 s on the machine, 4.5 s with
`--native` and 3 s with `--js` (`crates/cli/tests/running/aoc_answers.rs:323-325`).
2021 day 11 takes 4.1 s, against 1.3 s natively (`aoc/NOTES-2021.md:2739-2740`).
A million `Set` inserts take 8.7 s (`native-compilation.md` §1.2). The same
machine runs `test`s, the counterexample search and the playground, so the
slowness reaches proofs and the browser too, not only `run`.

**What the numbers already say.** The machine executes about 116 host CPU
instructions for each bytecode instruction on the `Set` benchmark, and about
180 on the bare-call benchmark. It does so at 4.5 to 6.5 instructions per
cycle (§0). So the CPU isn't waiting on mispredicted jumps. It is doing too
much work around each instruction. Most of that work is in calls and
returns: about 900 host instructions per call on the bare-call benchmark.
After that comes reading and writing registers with checks, a second
dispatch for each primitive, and freeing. Changing how the machine
dispatches (threaded code) attacks the smallest part, and it would slow the
playground.

**The change.** Keep the `match` loop and the bytecode. Make the work around
each instruction smaller, in this order:

0. Measure first: runtime benchmarks with deterministic counts, and an
   opcode-level profile.
1. Calls and returns that stay inside the instruction loop, on a register
   stack that isn't resized at every call.
2. Word-sized fast paths for the hot number primitives.
3. Freeing that doesn't build a work list for children it can't free.
4. Cheaper closure calls: in the machine, and by specialising recursive
   functions on the lambdas they're given (SW-1672).

**What it should do.** About 1.5–2× on `Map`- and `Set`-heavy days and
2–3× on call-dominated code, with identical output, step counts and
`E-RESOURCE` points **[inferred; stage 0 replaces these guesses with
numbers]**. Native code (`run --native`, `build --native`) gets stages 3
and 4b too, because they change the shared values and the IR. It doesn't
get stages 1 and 2, which only touch the interpreter loop.

## 0. What earlier measurements already show

These numbers come from `native-compilation.md`, taken on an Apple M4 Pro in
October. The machine is now an M1 Pro (SW-1090), so stage 0 measures again.

| Program | Wall | Cycles | Host instructions | Bytecode instructions | Host per bytecode | Per cycle |
|---|---:|---:|---:|---:|---:|---:|
| `Set` inserts, 1M (`native-compilation.md:1375-1377`, §1.2) | 9.64 s | 38.1 G | 171.6 G | 1.478 G | **116** | 4.5 |
| `micro_call`, 20M calls (`:1380`) | 0.92 s | 3.58 G | 18.9 G | about 0.105 G **[inferred]** | **about 180** | 5.3 |
| `micro_tail`, 20M turns (`:1383`) | 0.59 s | 2.29 G | 14.8 G | about 0.08 G **[inferred]** | **about 185** | 6.5 |

The bytecode counts for the two micro programs are estimates. `down` runs
`NatCase`, `NatPred`, `Call`, `Prim`, `Return` per call; `spin` runs
`NatCase`, `NatPred`, `Prim`, `TailCall` per turn (`bench/native/micro_call.sw`,
`micro_tail.sw`). The host counts include checking, which is about 0.09 s of
each run (§1.3).

What follows from the table:
- **A call and return cost about 37 ns and roughly 900 host
  instructions** (§1.3). Native code does the same call in 2.2 ns with the
  frame and step counting kept. The `Set` benchmark enters a frame every 18
  bytecode instructions (81 frames per insert, §1.2). Calls are the biggest
  single cost.
- **Mispredicted dispatch isn't the bottleneck.** At 4.5–6.5 instructions
  per cycle, the core is retiring work, not stalling. The October profile
  put about 19% of the time in the jump table (§1.2). Threaded dispatch
  mainly removes mispredictions and a few instructions per dispatch, so its
  ceiling here is that 19% **[inferred]**.
- **A good bytecode interpreter spends roughly 10–30 host instructions on a
  simple instruction** **[inferred, from general experience with Lua- and
  wasm3-style interpreters; not measured here]**. Ours spends 116–185 on
  average. That gap is the room this note is about.
- The October profile of the `Set` run (§1.2, `nat-map.md:119-125`): 63% in
  the `run` loop, 11% dropping values, 7% allocating, 4% growing the
  register vector, the rest mostly `nat_add` and `nat_mul`.

The ticket's day 19 figure (11M closure calls dominating 8.1 s) came before
SW-1636. That change built the rules into a `Map` once and took the day from
7.6 s to 2.3 s. The closure-call pattern is still SW-1672's: 2020 day 15
spends 83% of its self time in `Nat.iterate`, which makes one closure call
per turn.

**What the native note already proposed.** `native-compilation.md` §5 route
(a), "A faster interpreter", listed:
- no register clearing on entry;
- superinstructions;
- a 16-byte `Value`;
- threaded dispatch.

It estimated 1.3–2× over 2–3 lanes. This note builds on that with the
per-instruction reading below. It differs in three places:
- It puts calls and returns first.
- It drops threaded dispatch (§2.3).
- It leaves the 16-byte `Value` to the representation work. A smaller
  `Value` changes the layout native code reads (`value.rs:24-28`), so it
  belongs with SW-593.

## 1. Where the time goes, from the code

The loop is `run` (`crates/rt/src/machine.rs:969-1471`). It has two levels.
The outer loop delivers a pending result to where it goes
(`:972-1019`), then loads the top frame (`:1022-1024`). The inner loop
fetches an instruction, counts it and matches on it (`:1058-1062`). Below is
what each part does per instruction, read from the code. The cost figures
are **[inferred]** host-instruction estimates, for stage 0 to check.

### 1.1 Dispatch

- `let instr = code.instrs[pc]` copies a 24-byte `Instr` (`code.rs:54-223`;
  the size is my reading of the largest variant, `CtorReuse`) with a bounds
  check. Then `st.executed += 1` writes to the machine's state
  (`machine.rs:1059-1061`), then the `match` jumps through a table.
- This is a few host instructions plus one indirect jump. It's cheap. Its
  cost rises only when the jump mispredicts, which the instructions-per-cycle
  figures say is not the main problem.

### 1.2 Operand decoding and register access

- Each register access is `st.regs[base + r]` (`reg!`, `:1026-1030`), with
  a bounds check against the vector's current length. `st.regs` is reloaded
  whenever something might have changed it (a push, a call out of line).
- An operand list is a slice of `code.ops` (`ops!`, `:1031-1035`): one more
  load and bounds check before the registers themselves.
- `get!` (`:1043-1052`) tests the `MOVE` bit on every operand, then either
  takes the value (a 24-byte write of `Erased`) or clones it. A clone of a
  `Value` is a `match` over its 12 variants (`value.rs:28-53`), with a
  reference-count increment for the 7 that own something.
- Every write `reg!(dst) = v` first drops what the register held: one more
  `match` on the old value, usually `Erased`.

So a three-operand instruction does about six bounds checks, three tag tests
for moves, a clone or take per operand and a drop of the old destination.
That is perhaps 30–50 host instructions before any real work
**[inferred]**.

### 1.3 Calls and returns: the biggest cost

A saturated call of a known global (`Instr::Call`, `:1091-1113`):
1. `save!()` writes the pc into `st.frames.last_mut()`;
2. `enter_frame()` adds a step, compares it with the limit, and compares
   the frame count with its limit (`:396-408`);
3. it looks up `image.global_code[g]`, then pushes each argument onto
   `st.regs` (a capacity check per push);
4. `st.regs.resize(new_base + regs, Value::Erased)` writes `Erased` into
   every register of the new frame (`:1100-1103`), slots and temporaries
   alike;
5. it pushes a `Frame` of about 40 bytes (`:93-100`): code, pc, base, an
   optional closure and a `Ret`;
6. `profile_entered` tests whether a profiler is on;
7. `continue 'outer` goes back to the outer loop, which tests `pending`,
   loads `frames.last()` again, indexes `image.codes` again and rebuilds
   `code`, `base` and `pc` (`:1020-1024`).

A return (`Instr::Return`, `:1457-1463`):
1. it takes the result and pops the frame;
2. `release` pops every register of the frame one by one, testing each for
   whether it owns anything (`:1474-1485`);
3. it builds `pending = Some((v, frame.ret))`, about 48 bytes, and
   `continue 'outer`s;
4. the outer loop matches on `Ret` and, for `Ret::Reg(r)`, writes the
   caller's register, dropping its old value (`:974`). Then it does step 7
   above for the caller.

A frame has as many registers as its body's slots and temporaries
(`Code::regs`, `code.rs:237`). The optimiser inlines aggressively
(`opt.rs:49-61`), so bodies are wide: the roguelike's widest is 2,760 bytes,
about 115 registers (`native-only.md:384`). So each call costs about 2 × R
writes of registers, plus the outer loop's frame reload twice. That is
likely most of the ~900 host instructions per call **[inferred]**.

A tail call (`TailCall`, `:1114-1121`, and `replace`, `:480-501`) moves the
arguments into `scratch`, releases every register, appends the scratch,
resizes and goes round the outer loop. A self tail call, which is every
loop, pays all of that to stay in the same body.

### 1.4 Reference counting

- Increments come from clones of operands that aren't moved (§1.2), and
  from `Captured` (`:1068-1074`), which clones each captured value as it's
  read.
- Decrements come from drops of overwritten registers, from `release`, and
  from `Drop` and `Unpack`.
- How many there are is the in-place reuse work's subject: 0.9–1.6
  increments per cell on AoC programs (`docs/research/in-place-reuse.md`
  §2.2), with borrowed parameters as the fix it is weighing (D2276, waiting
  on SW-1811's data). This note doesn't touch the number of counts, only
  the mechanism around them (§3).

### 1.5 Closure calls

`Instr::Apply` (`:1218-1251`):
- `get!(f)` clones the function value (an increment) unless it was moved;
- `exact` (`:1496-1511`) dereferences the `Rc<Fun>`, reads
  `program.lambdas[l].params` from the `Program`, which is a different
  structure in different memory from the image, reads
  `image.lambda_code[l]`, and clones the `Rc` again for the frame's `env`
  (a second increment);
- `fv` is dropped when the arm ends (a decrement), and `env` when the frame
  returns (another).

So a closure call makes two increments and two decrements of the closure,
then the whole call cost of §1.3. Each `Captured` read then goes through
`st.frames.last()` and a `match` on the `Fun` (`:1068-1074`).

Making a closure (`Instr::Closure`, `:1272-1277`) allocates twice: the
`Rc<Fun>` and its `Box<[Value]>` of captures (`value.rs:89`). Both are
freed when it dies.

### 1.6 Primitives

The general `Prim` arm (`:1163-1209`) runs a chain of tests before the
work:
- is it `Text.fold`;
- does the operation consume its arguments (`op.consumes()`);
- is it `Array.replicate`;
- is `number_words` on (only in the counterexample search,
  `crates/driver/src/counterexample.rs:270`);
- then a `match` on the operand count, building a slice of references.

Then `prims::eval` (`prims.rs:417`) matches on the operation again. Only
then does `nat_add` check that both operands fit in a word (`prims.rs:168-175`).
The `Test` instruction already shows the better pattern: compare word-sized
numbers inline, fall back to `eval` for everything else (`machine.rs:1405-1455`,
stage 4's measured gain in `fast-runtime.md`). `Map.Tree.shape`, half of a
`Map` insert's instructions (`nat-map.md:121`), is mostly `Nat`
multiplications and comparisons.

### 1.7 Freeing

`Drop for Fields` (`value.rs:345-355`) makes a `Vec` work list and moves
every *deep* child into it (`take_from`, `:274-280`), whether or not this
cell is the child's only owner. `free` then pops each child and tries to take
its children (`:284-288`). A shared child is only decremented when popped.
So freeing a unique `Map` node whose subtrees are shared (the normal case
after a persistent insert) allocates and frees a work list just to decrement
two counts. A long unique list is fine: one work list for the whole list
**[source for the mechanism; how often it happens, inferred]**. `Fun` and
`Delay` drops do the same (`:357-371`).

## 2. Designs, and the one I recommend for each cost

### 2.1 Calls and returns

**Problem.** Every call and return leaves the instruction loop, writes and
releases the whole register window, and reloads the frame twice (§1.3).

- **A. Calls and returns inside the inner loop (recommended).** Keep the
  current frame's `code`, `base` and `pc` in local variables. `Call`,
  `Apply` of an exact-arity function, `TailCall` and `Return` to a register
  update those locals and carry on in the same loop. Only the uncommon
  results (`Ret::Host`, `Const`, `Apply`, `Fold`, the effect runtime's
  `Eff`, `Then`, `Inject`, `Step`) go through `pending` and the outer loop.
  The `Frame` gets smaller: the common return target is a `u32`
  destination register, and the other `Ret` variants are a rare,
  separately stored case. The executed-instruction counter lives in a
  local and is added to the state when the loop leaves. A self tail call
  (`TailCall` to the same body) moves its arguments into the parameter
  registers and drops only the registers that own something, without
  `scratch`, `truncate` or `resize`.
  - *Cost:* a careful rewrite of the loop's call paths, about 300 lines of
    `machine.rs`. The effect runtime enters through `push`, `apply` and
    `Ret`, so those keep working and need testing.
  - *Rules out:* nothing.
  - *Precedent:* Lua 5 does it this way: `OP_CALL` of a Lua function
    re-enters the same `luaV_execute` loop with a new frame instead of
    returning to a caller (*The Implementation of Lua 5.0*, 2005, §7)
    **[from memory, not re-checked]**. CPython 3.11 did the same for
    Python-to-Python calls ("inlined" calls in the eval loop) **[from
    memory]**.
- **B. Leave the call path alone and add superinstructions for the common
  pairs** (`Call` then `Return`, `CtorReuse` then `Return`). This saves one
  dispatch per pair. Stage 4 already judged it "not worth it at these sizes"
  (`fast-runtime.md`, "As built (stage 4)" item 7), and it doesn't touch the
  ~900 instructions of the call itself.
- **C. Closure compilation** (each body a tree of Rust closures). Rejected
  for the same reason as in `fast-runtime.md` §2.2: it recurses on the Rust
  stack, which the playground doesn't have.

**What A should do:** `micro_call` and `micro_tail` drop by 30–50% of their
host instructions; `Set` inserts by 10–20% **[inferred]**. Frames entered,
steps and `E-RESOURCE` points stay exactly the same, because `enter_frame`
is still called once per frame.

### 2.2 The register window: a fixed size, but where?

**Problem.** The window's size is already fixed when the bytecode is made
(`Code::regs`, `code.rs:237`). What grows and shrinks is the one shared
vector: `resize` on every call writes `Erased` into every register, and
`release` pops every register on every return (§1.3).

- **A. A register stack that keeps its length (recommended).** Keep one
  `Vec<Value>` and grow it only when a frame would pass its end. Track the
  top of the stack separately from the vector's length. Invariant: *every
  register above the top frame's window is `Erased`.* A push then writes
  nothing: the new window is already `Erased`. A return walks the window and
  takes out only the registers that own something (`Value::owns`,
  `value.rs:227`), leaving the rest. A Nat or a tag is overwritten with
  `Erased`, which is a plain store. A debug assertion at push checks the
  invariant.
  - *Why `Erased` and not leftovers:* leaving stale numbers above the top
    would save the stores. But a compiler bug that reads a register before
    writing it would then compute with an old `Nat` and print a wrong
    answer, where today it panics on `Erased`. Failing loudly is worth a
    store.
  - `Ret::Reg` keeps its absolute register index, which needs one
    contiguous vector. Growth by doubling stays amortised, and the frame
    limit bounds it as today.
- **B. A separate allocation per frame** (`Box<[Value]>` of `regs`). This
  adds an allocation per call, which is worse than today. Rejected.
- **C. Segmented stacks**, a chunk per N frames, so that growing never
  copies. That only matters for recursion millions deep, which the frame
  limit already bounds. It would make `Ret::Reg` a pair of chunk and index.
  Not worth it now.

**What A should do:** take most of the 4% "growing the register vector" and
part of the 11% dropping (§0) **[inferred]**. It's part of the same lane as
§2.1, since both change `push`, `replace`, `release` and the call arms.

### 2.3 Dispatch and operand decoding

**Problem.** Dispatch is a `match` with a table jump, and operands go through
`code.ops` with bounds checks (§1.1, §1.2).

- **A. Keep the `match` and make each arm lighter (recommended now).**
  §2.1, §2.4 and §2.5 do that.
- **B. Direct threading by guaranteed tail calls** (each instruction a
  function that tail-calls the next one's handler). Rust's `become` is
  unstable, with stabilisation hoped for in 2027. Matt Keeter measured it at
  1.5–2× faster than a `match` natively but **1.2–4.6× slower in wasm**
  (both cited in `native-compilation.md` §2.10). The playground runs this
  machine in wasm (`crates/web`). And §0 says mispredicted dispatch isn't
  where the time is. Rejected for now. It is worth revisiting only if, after
  stages 1–4, the jump table is over a quarter of the profile, and `become`
  is stable.
- **C. A prepared form private to the machine** (conditional, stage 5). At
  `Machine::new`, translate each `Code` into the machine's own instruction
  list. Operands would sit inline instead of in `code.ops`, and the hot pairs
  would be fused (`Switch` then `Unpack`, the most frequent pair in stage
  4's count, `fast-runtime.md` stage 4). CPython 3.11's specialising
  interpreter (PEP 659) rewrites instructions into specialised forms in the
  same way **[from memory]**. The key point is *private*. The shared `Instr`
  set, which native code translates one for one (`crates/native/src/n1.rs`,
  87 `Instr::` arms), doesn't change, so native code has nothing to
  mirror. Worth doing only if stage 0b shows decoding (operand loads and
  checks) over about 20% after stages 1–3.

### 2.4 The hot number primitives

**Problem.** `a + b` on two small `Nat`s goes through five tests, a slice and
two nested `match`es before it adds (§1.6).

- **A. Match arms for the hot operations, before the general `Prim` arm
  (recommended).** `Instr::Prim { op: PrimOp::Nat(Native::Add), .. }` and so
  on, for `Nat` `+ - * / %` and `==`/`<=`, `Int` `+ - <`, and the `Nat` bit
  operations once SW-2010 lands. Each tests that both operands are words,
  computes inline, and otherwise falls through to `prims::eval` as today.
  - *Counts:* `number_cost` is 0 unless an operand is big
    (`prims.rs:373-386`). So a fast path taken only for word-sized operands
    charges exactly what the general path charges, in every mode.
  - *Format:* no new instruction, so no native change.
- **B. Typed instructions chosen at compile time** (`NatAdd { dst, a, b }`
  in `Instr`). This is faster to decode, but it changes the shared
  instruction set, so `n1.rs` must learn each new instruction. Native code
  already has its own `Nat` fast paths (the N1 row of
  `native-compilation.md` §6), so it gains nothing. Rejected in favour of A,
  or of C in §2.3 if decoding turns out to matter.

**What A should do:** 5–15% on arithmetic-heavy code, `Map.Tree.shape`
included **[inferred]**.

### 2.5 Closure calls

**Problem.** A call of a small lambda pays the full call (§1.3), plus two
increments and two decrements of the closure, plus lookups in the
`Program`. Making the lambda costs two allocations (§1.5). SW-1672's
`Nat.iterate` loop makes a closure call per turn, 30M times.

- **A. A cheaper `Apply` in the machine (recommended, small).**
  - When the function operand is moved (`MOVE`), move its `Rc` straight
    into the frame's `env`, with no clone and no drop.
  - Keep each lambda's parameter count and code index side by side in the
    `Image`, so `exact` reads one small table and not the `Program`.
  - Cache the current closure's captures in a local, so `Captured` doesn't
    go through `frames.last()` and a `match`.
  - This is a machine-only change, done after §2.1, since it touches the
    same arms.
- **B. Specialise recursive functions on the lambdas they're given
  (recommended, the bigger win).** `opt.rs` already copies a recursive
  function called with a *known* function (`specialise`, `opt.rs:1228`). But
  a closure literal counts as known only if it captures nothing
  (`known_function`, `:1198-1208`). Extend it: for a call like
  `Nat.iterate n (x => step grid x) start`, where the recursion passes the
  function on unchanged, make a copy of `iterate` that takes the captures
  (`grid`) as extra parameters, threads them through its recursive calls,
  and calls the lambda's body directly. That direct call can then be
  inlined, as the copies are today.
  - *Effect:* the closure, its two allocations, the `Apply` and the
    `Captured` reads all go. Native code gets the same gain, because it runs
    the same IR.
  - *Bounds:* the existing ones (`COPY_SIZE`, `COPIES = 64` per program,
    `opt.rs:60-61`). Stage 0b should count how often the 64 limit is hit on
    AoC programs.
  - *Precedent:* MLton defunctionalises the whole program; GHC's
    specialisation of functions on known arguments is the same idea
    **[from memory]**.
  - *Risk:* the optimiser is where a wrong answer can come from
    (`fast-runtime.md` stage 4, "What's left"). This is Opus work, with
    differential tests.
- **C. One allocation per closure** (captures inline in the `Rc`). This
  changes `Fun`'s layout, which native code reads (`value.rs:78-84`,
  `native_abi::probe_layout`). It belongs with SW-593's representation work,
  not here. B removes the hot closures altogether, which makes C matter
  less.

**What it should do:** A, 3–8% on closure-heavy runs. B, up to about 2× on
SW-1672-shaped loops (2020 day 15's `iterate`, `foldLeft` with a capturing
lambda), on both runners **[inferred]**.

### 2.6 Freeing

**Problem.** Freeing a unique cell with shared children allocates a work
list just to decrement them (§1.7).

- **A. Only unique children go on the work list (recommended).** In
  `take_from`, a deep child that isn't uniquely owned is dropped on the
  spot: that only decrements, and can't recurse. A child that is uniquely
  owned goes on the list as today. The work list is still allocated lazily,
  so freeing a cell whose children are all shared, or are numbers, allocates
  nothing.
  - *Still never recurses:* only shared drops happen inline, and a shared
    drop frees nothing.
  - *Both runners:* native code uses the same drop glue (`Value`'s drop,
    `sw_free_emptied`; "about 10% in freeing" in `native-compilation.md`
    N2a), so native code gains too.
  - *Trace order:* the allocation trace records a `dec` for each child
    (`alloc_trace.rs`). A shared child's `dec` now comes before its
    siblings' frees rather than after. Both runners share the code, so the
    agreement tests still agree. Any committed trace snapshot regenerates.
- **B. A reusable work list per thread.** This saves the allocation but
  still pushes and pops every child. A is simpler and does less work.

**What it should do:** 3–10% on `Map`- and `Set`-heavy runs **[inferred]**.

### 2.7 Bounds checks, and `unsafe`

The machine has no `unsafe` at all (`docs/reviews/code-review-rt.md`,
summary). Every register access, operand list and jump target is checked
(§1.2).

- **A. Keep the checks (recommended now).** At about 116 host
  instructions per bytecode instruction, perfectly predicted checks are not
  the first problem.
- **B. Unchecked access, justified by a bytecode validator.** At image
  construction, check that every register is below `regs`, every operand
  list is inside `ops`, and every jump and table entry is inside the body.
  Then the loop uses unchecked indexing. The same validator would also close
  the review's F3 ("native compilation trusts any `Image`") for native code.
  This is a trust decision (D3060), and worth taking only if stage 0b shows
  the checks above about 10% after stages 1–3.

## 3. How this fits the in-place reuse work and the native backend

**In-place reuse** (`docs/research/in-place-reuse.md`, SW-1809 to SW-1816)
decides *how many* allocations and reference-count changes a program makes:
- inlining for reuse, SW-1812;
- dropping unused parameters at entry, SW-1813;
- borrowed parameters, D2276.

This note makes each allocation, count change, call and instruction
*cheaper*. Neither does the other's job:
- §2.5 B adds copies through `opt.rs`, as SW-1812 does. Both should share
  one size and fuel budget. The two lanes run one after the other, not side
  by side.
- §2.6 changes the drop glue. SW-1810's report counts increments and frees
  by site, and its totals must still equal the allocation trace's. Running
  §2.6 after SW-1810 lets that report show the gain.
- Stage 0b's opcode counts and SW-1810's reuse columns are both "what the
  machine did, by definition". They should be one report with two sets of
  columns, not two systems. Stage 0b uses a cargo feature for the
  per-instruction counts (§4.2), because they cost something on every
  instruction. SW-1810's per-frame counts can stay in `run --profile`.

**Native code** compiles the shared bytecode one instruction at a time
(`crates/native/src/n1.rs:1-11`). So:

| Change | Machine | Native | Format change? |
|---|---|---|---|
| §2.1 calls in the loop, §2.2 register stack | yes | no (it has real frames) | no |
| §2.3 C prepared form (conditional) | yes | no | no: machine-private |
| §2.4 hot primitive arms | yes | no (it has its own fast paths) | no |
| §2.5 A cheaper `Apply` | yes | no (it has `ApplyCache`) | no |
| §2.5 B specialising on lambdas | yes | **yes** | IR only, as today's copies |
| §2.6 freeing | yes | **yes** | no |
| §2.7 B validator | yes | **yes** (review F3) | no |

The rule I'd keep is that **the `Instr` set stays the shared contract**.
Machine-only speedups live in the machine, so native code never has to
mirror them. The review's F8 already counts three hand-mirrored helpers;
this plan adds none.

**The effect runtime** (`effect-runtime.md`, SW-593) enters the machine
through `push`, `apply` and the `Ret` variants. §2.1 keeps all of those, and
moves only `Ret::Reg` returns onto the fast path. The effect benchmarks'
allocation and effect counts must not change.

## 4. Measure first

### 4.1 The benchmark to add first

Today's recorded benchmarks (`bench/baseline.toml`, `crates/bench/src/programs.rs`)
measure checking and the kernel's evaluator. The two `run-` entries
(`run-prints`, `run-proof-fields`) print lines and thread a record through
200 inputs, which says little about the interpreter loop. Their `steps` are
the kernel budget's counter (`programs.rs:293-299`), not the machine's. The
`task native:bench` script (`bench/native/bench.sh`) has the right programs,
but it records best-of-N wall time only, with nothing deterministic to
compare against a baseline.

**Add `run-machine-*` benchmarks to the bench crate**, each recording:
- **machine instructions** (`machine::instructions_executed`,
  `machine.rs:315`): deterministic, and changes only when the bytecode does;
- **frames entered** (the machine's step counter): must not change in
  stages 1–3, which is a regression check on the limits;
- **allocations and peak bytes** (the bench's counting allocator, as for the
  others);
- **time** (median, loose threshold, as for the others).

The programs:

| Benchmark | Program | What it isolates |
|---|---|---|
| `run-machine-calls` | `bench/native/micro_call.sw` at 200,000 × 20 | calls and returns |
| `run-machine-loop` | `micro_tail.sw` at 4,000,000 | self tail calls, `Nat` arithmetic |
| `run-machine-closures` | `closures.sw` at 200,000 | `Apply`, `Captured`, closures |
| `run-machine-set` | `set_nat.sw` at 100,000 keys | `Map`/`Set` code: calls, `shape`'s arithmetic, freeing |
| `run-machine-aoc-*` | two or three AoC days on their committed inputs (below) | real programs |

Each should take about 0.2–1 s on the machine, so the whole group stays
under about 10 s.

**Which AoC days.** Pick days whose machine run is 1–4 s, with different
profiles, from these candidates:
- **2020 day 19**: 2.3 s after SW-1636 (closure calls and `Map` lookups);
- **2021 day 11**: 4.1 s, grid `Map` (`aoc/NOTES-2021.md:2739`);
- **2024 day 9**: cell-heavy, 3.6M cells with 15.6% reused
  (`in-place-reuse.md` §2.2), so stages 3 and 5 show there.

2021 day 15 (20 s) and 2020 day 15 (16 s) are the days users feel most, but
they're too slow for a recorded benchmark. The stage 0 lane should check
whether a bench `main` can run only part 1 of 2021 day 15 (10,000 positions,
`NOTES-2021.md:3662`) on the real input. If it can, that replaces 2021 day
11. If it can't, the two slow days are timed by hand at the end of each
stage, which is allowed because they're the stage's own measurement.

**Caveat on build features:** the bench binary is built with the dev feature
set, which turns on the allocation trace's hooks (`crates/bench/Cargo.toml`,
`crates/dev-features/Cargo.toml`). Those hooks add a branch at every cell
event. The shipped binary has none. So bench times are a slightly
pessimistic proxy, and stage 0b times the release `stitchwort` binary
directly.

### 4.2 The evidence to collect (stage 0b)

For each benchmark above:
1. **Host instructions and cycles** (`/usr/bin/time -l` on macOS gives
   both, as `native-compilation.md` N2a used). This checks §0 on the M1 Pro:
   host instructions per bytecode instruction, and instructions per cycle.
2. **An opcode histogram**: instructions executed by kind, `Prim` by
   operation, and `Apply` by outcome (exact closure, exact global, partial
   application, over-application, native). Use a cargo feature
   `machine-counts` that is **not** in the dev feature set, so it doesn't
   slow every test. A task such as `task machine:counts -- FILE` builds it
   on demand into its own target directory.
3. **Frame widths weighted by entries**: how many registers the frames
   entered have, as a histogram. This sizes §2.2's gain.
4. **A sampled profile with line tables** (`sample` on macOS, or
   Instruments), mapped to the `run` arms. It splits the call path
   (`push`/`release`/outer loop), `get!`/drops, `prims::eval` and freeing.
5. **Freeing**: of `Fields` drops of a unique cell, how many had only shared
   or shallow children (they would allocate nothing after §2.6).
6. **Specialisation**: how many `Apply`s run on a closure literal that
   §2.5 B could have specialised, and whether `COPIES` (64) is hit.

These decide the order of stages 1–4, which I set from the code. They also
decide whether stages 5 and 6 happen at all. The lane writes them up in
`docs/reviews/SW-N-machine-profile.md` (D2530).

## 5. Stages and estimated gains

The gains are **[inferred]** and multiply only roughly. Stage 0 replaces them.

| Stage | What | Machine gain (est.) | Native gain | Counts that must not change |
|---|---|---|---|---|
| 0a | Runtime benchmarks (§4.1) | — | — | — |
| 0b | Opcode counts, profile, the evidence of §4.2 | — | — | — |
| 1 | Calls and returns in the loop, register stack, self tail calls (§2.1 A, §2.2 A) | 30–50% fewer host instructions on calls; 10–20% on `Set` | none | steps, frames, allocations, output |
| 2 | Hot number primitive arms (§2.4 A) | 5–15% on arithmetic-heavy runs | none | steps (number words too), output |
| 3 | Freeing without work lists for shared children (§2.6 A) | 3–10% on `Map`/`Set` | similar | allocations go *down*; output |
| 4a | Cheaper `Apply` and `Captured` (§2.5 A) | 3–8% on closure-heavy runs | none | steps, output |
| 4b | Specialising recursive functions on capturing lambdas (§2.5 B) | up to ~2× on SW-1672-shaped loops | **same** | output; steps fall, as with today's inlining |
| 5 | *Conditional:* machine-private prepared form with fused pairs (§2.3 C) | 10–20% if decoding is over 20% after 1–3 | none | steps, output |
| 6 | *Conditional, D3060:* validator plus unchecked registers (§2.7 B) | 5–10% if checks are over 10% | the validator closes F3 | everything |

**Together (stages 1–4):** about 1.5–2× on `Set`/`Map`-heavy runs, 2–3× on
`micro_call`, more on closure loops that 4b catches **[inferred]**. For
comparison, native code is 3.6× on `Set` inserts and 5.8× on `micro_call`
(§0). An interpreter at about half of native's gain would be in line with
what good interpreters reach (wasm3 is 4–15× slower than compiled C,
`native-compilation.md` §2.10).

**How we'd know each stage worked:**
- the stage's benchmarks show the host-instruction drop;
- the machine-instruction and frame counts are unchanged where the table
  says so;
- the differential tests (`crates/rt/tests/machine.rs`, the machine against
  the reference evaluator) pass;
- for 3 and 4b, the native agreement tests (allocation traces) still agree.

## 6. Calls I made

- **Keep the `match` loop; no threaded dispatch.** The playground's wasm
  build would get slower, `become` isn't stable, and §0 says dispatch
  mispredictions aren't the cost. Revisit only with stage 0b's data and a
  stable `become`.
- **The shared `Instr` set doesn't change for machine-only speedups.** Fast
  paths are match arms (stage 2) or a private prepared form (stage 5).
  Native code never mirrors them.
- **Registers above the top frame are always `Erased`**, not stale (§2.2):
  a compiler bug keeps failing loudly.
- **Steps and frames stay exactly as counted today** through stages 1–3 and
  4a (`enter_frame` once per frame entered, a tail call included). So no
  limit runs out at a different point. Stage 4b changes them only as
  today's inlining does, which `fast-runtime.md` stage 4 already accepted.
- **Opcode counts are a separate cargo feature**, not in the dev feature
  set and not in `run --profile`, so tests and benchmarks don't pay for them.
- **Stage 1 is one lane, not two.** The call path and the register stack
  change the same functions.
- **Closures with inline captures (§2.5 C) are left to SW-593**, the
  representation work, because they change a layout native code reads.

## 7. Questions for Matt

- **D3060: Should the machine stay free of `unsafe`?** This would rule out
  stage 6's unchecked register access even if the profile shows the checks
  costing 10% or more. **[rec: yes for now.]** The review counts having no
  `unsafe` as one of the machine's strengths. The checks probably cost less
  than the work around them. I'd ask again only with stage 0b's number, and
  only after stages 1–3.
- **D3061: Is it worth about four lane-days to make the machine faster, given
  that `run --native` exists?** The alternative is to put the effort into
  making native the default runner. **[rec: yes, invest in the machine.]**
  The machine also runs `test`s, the counterexample search and the
  playground, which native code can't run (no JIT in wasm; tests and the
  search run inside the checker). So its speed reaches proofs and the
  browser, not only `run`. Stages 3 and 4b speed up native code as well.
  Making `run --native` the default is a separate question, which this note
  doesn't take up.

## 8. What this note didn't do

- No measurement: every number is from an earlier note, and the estimates
  are mine.
- It didn't read `run.rs`'s `IO` runner or the effect runtime's hot paths
  in detail. SW-593 owns effect-heavy programs: allocation is 49% there,
  dispatch 14%.
- It didn't look at the JS backend, which has its own runtime and doesn't
  use this IR.
- Typed node layouts (`native-compilation.md` §3.3, "another 5–6×") are a
  representation project for later, with SW-593.
- The precedents marked "from memory" (Lua 5, CPython 3.11, PEP 659, MLton,
  GHC) weren't re-checked for this note.

## Tickets to file

In order. Lanes on the same functions of `machine.rs` run one after
another.

1. **Stage 0a [Sonnet, 60 min]: runtime benchmarks.** Add
   `run-machine-calls`, `-loop`, `-closures`, `-set` and two or three AoC
   days (§4.1) to `crates/bench`. Record machine instructions and frames
   entered, beside allocations, peak and time, and re-record
   `bench/baseline.toml` for the new entries only. Check whether a part-1
   `main` for 2021 day 15 is possible.
   *Tests:* `crates/bench/tests/baseline.rs` and `repeat.rs` (the counts
   repeat); run the new benchmarks once.
2. **Stage 0b [Opus, 90 min]: the machine's profile.** Add the
   `machine-counts` feature and task (§4.2 item 2). Collect §4.2's six items
   on stage 0a's programs, on the release binary. Write
   `docs/reviews/SW-N-machine-profile.md`, confirming or reordering stages
   1–4 and saying whether stages 5 and 6 are worth doing.
   *Tests:* `task test:one` for any test the feature adds; the rest is
   measurement.
3. **Stage 1 [Opus, 90 min]: calls and returns inside the loop.** §2.1 A
   and §2.2 A: a register stack with the `Erased`-above-top invariant, a
   smaller `Frame`, the common returns inside the inner loop, self tail
   calls without `scratch`, the executed counter in a local. After 0b.
   *Tests:* `crates/rt/tests/machine.rs` targeted at calls, tail calls, deep
   recursion (the million-frame list), the frame limit and the effect
   runtime's tests; stage 0a's benchmarks show the gain with unchanged
   steps and frames.
4. **Stage 2 [Sonnet, 45 min]: hot number primitives.** §2.4 A: word-sized
   arms for `Nat` and `Int` arithmetic and comparisons, before the general
   `Prim` arm. After stage 1, since it touches the same `match`.
   *Tests:* the machine's arithmetic tests around 2^63 and 2^64, the
   counterexample search's number-words tests, and stage 0a's `-loop` and
   `-set`.
5. **Stage 3 [Sonnet, 45 min]: freeing.** §2.6 A in `value.rs`. It can run
   beside stage 1 (different file), and ideally after SW-1810 (§3).
   *Tests:* `value.rs`'s long-list and closure-chain freeing tests, the
   allocation-trace agreement tests between the machine and native code
   (regenerating snapshots if the `dec` order moved), and stage 0a's `-set`.
6. **Stage 4a [Sonnet, 45 min]: cheaper closure calls in the machine.**
   §2.5 A. After stage 1.
   *Tests:* the machine's closure, partial-application and
   over-application tests, and stage 0a's `-closures`.
7. **Stage 4b [Opus, 90 min]: specialise recursive functions on capturing
   lambdas.** §2.5 B in `opt.rs`. It absorbs SW-1672. Run it one after the
   other with SW-1812 (both add copies), and share their budget.
   *Tests:* the optimiser's tests, the IR-interpreter and validator sweeps
   over lowered definitions as the optimiser lanes run them, the
   differential machine tests on the closure programs, `run --native` on
   `closures.sw`, and 2020 day 15 timed once.
8. **Stage 5 [Opus, 90 min, conditional on 0b]: a machine-private prepared
   form with fused pairs.** §2.3 C.
9. **Stage 6 [Opus, 60 min, conditional on D3060 and 0b]: a bytecode
   validator plus unchecked registers.** §2.7 B. The validator half is
   worth doing alone for the review's F3.

Existing tickets: **SW-813** is this note and closes when it merges. **SW-1672**
is absorbed by stage 4b. **SW-814** (fused `balance`) and the native `Map`
work (SW-1824 to SW-1827) are unaffected: they cut instructions per insert,
and this plan cuts the cost of each instruction, so the two gains multiply.
