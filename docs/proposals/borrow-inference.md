# Borrowed parameters, inferred (SW-2518)

SW-2518, 9 Nov 2026, Opus, paper lane on `lane/SW-2518` from `main` at `0abd029bc`. Nothing was
built or run: the code was read, and the counts come from earlier profiles. Labels: **[read]**
seen in the code (file:line at `0abd029bc`), **[measured]** from a profile or run someone made
and wrote up (named), **[inferred]** worked out from the code, not run, **[estimated]** a guess
at an effect, with how it was made.

Builds on [fast-runtime.md](fast-runtime.md) ("As built (stage 4)": moves and reuse),
[reuse-across-calls.md](reuse-across-calls.md) (reuse tokens passed to copies of a function),
[native-compilation.md](native-compilation.md) (native code executes the machine's bytecode
decisions) and the profiles in `docs/reviews/SW-2513-mapops-profile.md` (mapops),
`SW-2371-map-rebuild-reuse.md` (dijkstra) and `SW-2492-expressions-scan-profiles.md`. The
external design is Ullrich and de Moura, "Counting Immutable Beans: Reference Counting
Optimized for Purely Functional Programming" (IFL 2019), as built in Lean 4
(`src/Lean/Compiler/IR/Borrow.lean`, `ExplicitRC.lean`).

## 0. Summary

**The problem, for a user.** Looking a key up in a `Map` that the program keeps (which is what
lookups are for) costs about 250-310 instructions a tree level natively, against a handful in
Lean **[measured, SW-2513 §1, §2.2]**. About half of that is reference counting: at each level
`Map.Tree.get` takes the node apart, finds it shared (the map is still alive), so it copies
every field it might use (two child pointers incremented, key and value copied), then drops the
three it didn't need **[measured: `inc` is 33% of `get`'s body, its two `Unpack`s 46%,
SW-2513 §2.2]**. `get` is 8-12% of mapops; dijkstra does 17.2 M such levels **[measured,
SW-2371 row 6, the machine on stock day 15]**. The same happens in every read-only walk over a
structure that is still in use: `contains`, `getOr`, `Set.contains`, `size`, `minKey`, folds
over a kept tree.

**The change.** The compiler works out, for each function parameter, whether the function only
*reads* it: matches on it, reads its fields, compares it, passes it on to other reading
positions, and never stores it, returns it, captures it or hands it to code that keeps it. Such a
parameter is *borrowed*: the caller keeps its reference and the callee takes none, so the
callee neither increments nor drops it, and the fields it reads from it are borrowed too. A
borrowed value that does escape (stored in a constructor, returned, passed to an owned
parameter) is incremented at that point, once. This is Lean's borrow inference, run over our
erased IR before the bytecode compiler, with three changes for Stitchwort: tail calls never
change (every `TailCall` stays a tail call, so step and frame counts are identical), a
function used as a value keeps today's owned code, and the machine stays safe Rust.

**What it should do.** `get` stops counting: a level becomes a tag test, the key comparison and
two loads, about 100-150 instructions instead of 250-310 **[estimated, SW-2513 §4.3: removing
`get`'s measured `inc`/`dec` share]**. Estimated: mapops -3.5 to -5.5% of instructions (before
or after SW-2514), dijkstra -5 to -12%, the core ten's geometric mean -0.5 to -2%, bench:aoc
-1 to -3% at the median with lookup-heavy days higher (§7, all **[estimated]**; stage B0
measures them before anything is built). Nothing a program means changes; step and frame
counts don't change; peak memory can rise slightly in a few programs (§8).

**Stages** (§6): B0 measure what would be saved (a dry-run inference and an elision counter,
about 3 h); B1 the inference, bytecode, machine and native changes with conservative rules
(about 1-1.5 days, Opus); B2 owned copies, so value uses and owned tail calls don't force
parameters owned (about 4 h); B3 borrowed reads of a live owned parent and of constants (about
4 h). Each stage has a measurement gate.

**Decisions for Matt** (§9): D3441 build it, inferred and with no syntax (rec: yes, after B0's
gate); D3442 the machine checks borrows instead of exploiting them, staying free of `unsafe`
(rec: yes); D3443 step and frame counts stay exactly as they are (rec: yes).

## 1. Today's ownership model

### 1.1 Every parameter is owned

A call gives the callee one reference per argument, and the callee is responsible for it
**[read]**:

- **Passing.** An operand read for the last time is *moved* (`MOVE` on the register,
  `code.rs:56`; the machine's `get!` takes it, `machine.rs:1099-1107`); any other operand is
  *cloned* (a reference-count increment for a cell, a copy for a small number). So a value
  passed while the caller still needs it costs an increment at the call.
- **Dropping.** Each body drops what it owns when it no longer needs it: a variable a branch
  doesn't use is dropped as the branch starts (`Instr::Drop`), and a frame's registers are
  dropped when it returns or is replaced (`machine.rs:1528-1533`, `release`, `replace` at
  `machine.rs:485-503`).
- **Native code** keeps the same rule: "the arguments are moved into native code, which owns
  them from then on" (`native_abi.rs`, module docs), and every move, clone and drop is the
  bytecode's (`n1.rs`, "The thesis").

### 1.2 Unpack and Field

A `match` on a constructor binds the fields its arm uses, all at the arm's start
(`code.rs:960-1015`; SW-2516 found that a nested match written to delay a field is folded back
into the same arm):

- **The scrutinee dies in the arm** (not used in the arm, not live after): `Instr::Unpack`. If
  the cell is uniquely owned, the fields are moved out and the emptied cell can be a reuse
  token; if it is shared, every bound field is cloned and the cell's count is decremented
  (`machine.rs:1384-1410`; natively `n1.rs:4674` on, the unique and shared paths inline).
- **The scrutinee lives on**: one `Instr::Field` per bound field, each a clone
  (`machine.rs:1427-1433`).

Either way, on a shared cell every field the arm might use is cloned, and those the path
doesn't use are dropped again.

### 1.3 Reuse tokens

`Unpack` and `DropReuse` keep a uniquely owned cell as a token, filled in place by `CtorReuse`
or passed to a copy of a function that builds one (`reuse.rs`). Soundness rests on: a token is
made only from a cell whose count was 1, lives only in a register the IR never reads, and
`CtorReuse` checks again at run time that the count is 1 (`reuse.rs:35-55`). Count 1 means "no
one else can see this cell". **Borrowing breaks that equation**: a borrowed reference is not
counted, so a cell with count 1 may be visible to a borrower. §4.4 is how the design keeps
the equation true wherever it is relied on.

### 1.4 What `get` does per level, today

`Map.Tree.get key tree` (`std/Map/Raw.sw:116-122`): `tree` is the scrutinee, dead in the arm,
so the `Bin` arm is an `Unpack` binding `l`, `kk`, `vv`, `r` (all four are used, in different
inner arms). On a map that is still in use, at each level **[inferred from `code.rs` and
`machine.rs`, agreeing with SW-2513 §2.2's `inc` share and SW-2371's 17.2 M "shared"
unpacks]**:

| Step | Today (shared node) | Borrowed |
|---|---|---|
| take the node apart | uniqueness test fails; clone `l` (inc), `kk`, `vv` (copies), `r` (inc); decrement the node | four loads, no test |
| `Ord.compare key kk` | `Test` on the two numbers | the same |
| `Less` arm | drop `kk`, `vv`, `r` (dec `r`) | nothing |
| `get key l` | tail call, `l` moved | tail call, `l` lent |

Two increments, two decrements, a failed uniqueness test and four 24-byte copies per level,
against none.

## 2. Lean's borrow inference, and what carries over

Lean compiles to an IR (λpure, then λRC with explicit `inc`/`dec`) where each function
parameter is *owned* or *borrowed* (`@&` lets a user annotate one). Borrow inference
(`Borrow.lean`) runs per mutual block, callees first, starting with every parameter borrowed
and marking them owned until nothing changes:

- `reset x` (the cell will be reused) marks `x` owned;
- a parameter stored in a constructor, a partial application, or passed to a closure
  application is owned (`ownArgsIfParam`);
- an argument passed to an owned parameter of the callee is owned (`ownArgsUsingParams`);
- for a projection `z := x.i`: if `x` is owned so is `z`, and if `z` is owned so is `x`;
- **tail calls** (`preserveTailCall`): if a tail call to a function *in the same block*
  passes an owned variable where the callee's parameter is borrowed, the caller would have to
  `dec` it after the call, which ends the tail call; so the callee's parameter is made owned.
  Calls to functions outside the block keep their (already fixed) annotations, and the `dec`
  after the call breaks the tail call: Lean accepts that.

`ExplicitRC` then inserts counts: a borrowed parameter is never `dec`'d, a projection of a
borrowed value is borrowed (no `inc`), an owned value passed to a borrowed parameter is passed
without an `inc` and `dec`'d after if dead, and a borrowed value passed to an owned position is
`inc`'d first. Functions used as closures get a `_boxed` wrapper that takes everything owned,
calls the function and drops the borrowed arguments after.

**What carries over unchanged:** the owned/borrowed flag per parameter, the fixpoint per
strongly connected component of the call graph, callees first; the projection rule; "owned
argument to borrowed parameter costs nothing at the call"; "borrowed value to owned position
costs one increment".

**What doesn't, and why:**

1. **Tail calls are a guarantee here.** Stitchwort counts a step per call and a frame per
   pending call, and a loop written as a tail call runs in constant frames; the frame limit
   is part of what a run means (`E-RESOURCE`), and native code counts exactly as the machine
   does (D1253). Demoting a tail call to call-then-drop, as Lean does across blocks, would
   change frame counts. Bounded in a first-order program (a cycle of tail calls is one
   component, where `preserveTailCall` applies), but through function values it is not: a
   closure-level loop whose steps went through a `_boxed`-style wrapper would grow a frame per
   step. So §4.3 never demotes one.
2. **Function values.** The wrapper approach is exactly such a demotion. Here a function used
   as a value either has all its parameters owned (B1) or gets an owned copy (B2, §4.3).
3. **Reuse is decided later.** Lean's `reset` is in the IR the inference sees; ours is decided
   by the bytecode compiler (`code.rs`, `wanted`). The inference asks the same question
   ahead of it (§3, rule O5).
4. **The machine is the reference.** Lean has one backend; we have two executors that must
   agree event by event (the allocation trace). §5.3 keeps them agreeing.
5. **Garbage-freedom.** Koka's Perceus keeps everything owned so that a value is freed as soon
   as it is dead ("garbage-free"); borrowing gives that up for the borrowed parameter's
   lifetime (the caller frees after the call). That is the right trade for read-only walks,
   but it is why §3 keeps a parameter owned whenever ownership could be used (reuse).

## 3. The design: which parameters are borrowed

Inference runs on the erased IR after `optimize`, `sums` and `trmc`, before `reuse`
(`lower.rs:199-202`), over the call graph of global functions, one strongly connected component
at a time, callees first. Every runtime parameter of a function starts borrowed, except those
of: lambdas (called through `apply`), constants, natives, TRMC loops and their twins (they use
hole operations), effect-runtime entry points, and the token parameter of a reuse copy. Then a
parameter `p` is marked **owned** if any of these hold anywhere in the body, and the component is
re-scanned until no flag changes:

- **O1 stored:** `p` (or an alias) is a field of a `Ctor`, a capture of a `Closure`, an
  argument of a `PartialApp`, the function or an argument of an `Apply`, or an argument of an
  effect native or a consuming native (`PrimOp::consumes`).
- **O2 returned:** `p` is the body's result on some path. (One move instead of an increment
  in the callee and a decrement in the caller. I have not checked whether Lean does the same;
  the paper's rules don't list this case.)
- **O3 passed to an owned parameter** of a direct `Call` or `TailCall` (the callee's flags are
  known: it is earlier in the order, or in this component with its current flags).
- **O4 tail-passed while owned:** inside the component, a `TailCall` to `g` passes, at
  position `i`, a value the caller owns (an owned parameter, a call's result, a constructor,
  a field of an owned value): then `g`'s parameter `i` is owned (Lean's `preserveTailCall`).
- **O5 reused:** `p` is the scrutinee of a `Match` whose arm would keep a reuse token: the arm
  builds a constructor of the cell's size or calls a function that wants such a token, by the
  same test the bytecode compiler uses (`code.rs`'s `wanted`, `reuse.rs`'s `wants`). This
  keeps `insertWith`, `remove`, `map`, `filter` and every other rebuilding function owned, as
  they are today.
- **O6 field escapes to an owner:** a field bound from matching `p` (or from a field of it,
  transitively) is passed to an owned parameter or tail-passed as in O4 (Lean's projection
  rule, `z` owned makes `x` owned). A field merely *stored* in a constructor or returned does
  not make `p` owned: it is incremented where it escapes (so `get`'s `Some vv` costs one
  increment per lookup, and `get`'s `tree` stays borrowed).
- **O7 used as a value (B1 only):** the function is named by `Expr::Global` or
  `Expr::PartialApp` anywhere in the program: all its parameters are owned. B2 replaces this
  rule with an owned copy (§4.3).
- **O8 tail-called from outside while owned (B1 only):** a `TailCall` from another component
  passes an owned value at a borrowed position. In B1 that position becomes owned; since the
  callee's flags were fixed before its callers were seen, this is a second pass: callers are
  scanned, the offending positions flipped, and the affected components re-inferred (only
  towards owned, so it terminates). B2 replaces it with the owned copy too.

Flipping a parameter to owned is always sound (a borrowed value passed there is just cloned,
as today); only borrowing needs care. So every cap, fallback or doubt resolves to "owned".

**Values inside a body.** A variable is *lent* (the frame holds it without a count) if it is a
borrowed parameter, or a field bound by matching a lent value; everything else is owned, as
today. (B3 adds lent reads of owned values, §6.) A lent value is:

- matched with loads only: no `Unpack`, no `DropReuse`, no token;
- passed to a borrowed parameter or a non-consuming native as is;
- **incremented where it escapes**: a `Ctor` field, a capture, an `Apply`/`PartialApp`
  argument, an owned parameter, or the body's result. The bytecode already clones any operand
  not marked `MOVE`, so the escape is "never mark a lent register `MOVE`", plus a clone into a
  temporary before `Return`.
- never dropped: when its last use passes, the register is simply forgotten (natively, its
  words are dead; the machine, §5.3).

**An owned value passed to a borrowed parameter** in a non-tail call is passed without `MOVE`
(no increment) and, if dead after the call, dropped right after it (`Instr::Drop`, which the
compiler already emits for dead variables).

**What this gives for std's Map** **[inferred by applying the rules to `std/Map/Raw.sw`]**:
`get`'s `key` and `tree` borrowed (the key is only compared; with a custom `Ord` the dictionary
is applied, so `ord` is owned until closures can borrow, §4.5); `size`, `minKey`'s tree,
`minValue`'s tree and the `contains`/`member` walks borrowed; `shapeL`/`shapeR`/`shape` borrow
the subtrees they measure (they read sizes only), which removes the clones `shape`'s
`size l` and `size r` make today while `l` and `r` are still needed; `insertWith`, `remove`,
`balance`, `rebuild`, `bin`, the rotations and `glue` owned (O1, O5). `foldLeft`/`foldRight` over
a tree own the tree only if their function argument would otherwise force it: the function is
applied to fields (O6 through `Apply`), so the tree is owned, as today. The `Map` wrapper
functions (`Map.get m k` reads `m`'s one field and tail-calls) are borrowed through.

## 4. IR and calling-convention changes

### 4.1 IR

- `Global` gets `borrowed: Box<[bool]>`, one per runtime parameter (empty for constants and
  natives), filled by the new pass `crate::borrow` and printed by `pretty.rs`.
- `validate.rs` checks the flags' shape (length = `params`, all false for TRMC bodies, reuse
  copies' token slot owned) and, at the bytecode level (§4.2), the discipline.
- No new `Expr`: whether an operand is lent is read off the callee's flags and the variable's
  kind, inside the bytecode compiler.

### 4.2 Bytecode

- **Operands.** A call's operand list gains a second flag beside `MOVE`: `LEND = 1 << 30` ("the
  callee borrows this; no increment, and the caller keeps it"). `Call` and `TailCall` mark each
  operand at a borrowed position `LEND`; other instructions never see it.
- **Borrowed field reads.** `Instr::Field` gets a `lend: bool`, or a sibling `Instr::Peek { dst,
  src, i }`: the field's words, no increment. A match on a lent scrutinee compiles to `Switch`
  and `Peek`s only, binding each field where the arm needs it (lent loads cost nothing, so the
  arm-start binding of §1.2 no longer costs anything here).
- **Each body's lent registers** are a static set (`Code::lent`): the borrowed parameters and
  the `Peek` destinations. A register is lent for the whole body or never, so the register
  allocator keeps lent temporaries apart from owned ones.
- **The discipline**, checked by `validate` on every compiled body (tests run it on everything
  they lower): a lent register is never `MOVE`d, `Take`n, `Drop`ped, `Unpack`ed,
  `DropReuse`d, used as a token, or passed to a consuming native; it is never the operand of
  `Return` (the compiler clones first); and an owned register passed `LEND` is not passed again
  `MOVE` in the same instruction.

### 4.3 Tail calls, owned copies and function values

The rule is **every `TailCall` stays a tail call**, so steps and frames are exactly today's:

- A tail call passing a lent value to a borrowed parameter: nothing to do (the owner is further
  up the stack, in a frame that made a non-tail call).
- A tail call passing a lent value to an owned parameter: clone, then tail call (today's code
  for a value still in use).
- A tail call passing an *owned* value to a *borrowed* parameter would need a drop after the
  call. Inside a component O4 forbids it; across components, B1 forbids it with O8 (the
  position becomes owned), and B2 calls the callee's **owned copy** instead.

**Owned copies (B2).** For a function with a borrowed parameter that is used as a value, or
tail-called across components with an owned argument at a borrowed position, the reuse pass's
copy machinery makes one more variant: the same body with every parameter owned, which is
exactly the function as compiled today. Its own recursive tail calls pass owned values, so they
stay in the owned copy (`get`'s owned copy is today's `get`). Function values (`Global`,
`PartialApp`, `Pap`, the native `value{g}` adapters, `sw_apply_prepare`) name the owned copy, so
`xs.filter visited.contains` keeps today's code while direct `visited.contains x` borrows. Like
reuse copies, owned copies are made only where some site uses one, are capped
(`MAX_COPIES`, `MAX_GROWTH`, shared with reuse), and when the cap is hit the function's
borrowed positions flip to owned (sound, §3). `Reuse::Copy` generalises to a variant `{ of,
token: Option<size>, owned: bool }` so an owned copy can also have reuse copies; planning
(`code::plan`) runs over owned copies like any other body.

Why not Lean's demotion: it changes frame counts, it grows a frame per step in loops through
function values (§2, point 1), and it would make native and machine runs fail at different
`--frames` than today's.

### 4.4 Reuse: a borrowed cell is never reused

A lent register can't become a token: `Unpack` and `DropReuse` never take one (§4.2's
discipline), and tokens come only from those two (`reuse.rs` soundness point 1). That is the
whole rule, and the validator checks it. Point 3 of `reuse.rs`'s soundness argument (the
run-time count check in `CtorReuse`) stays as a backstop for a wrong *choice* of token, but it
is **not** a backstop for a borrowed cell: a cell borrowed from a caller whose reference is the
only one has count 1, and `CtorReuse` would overwrite it. The validator rule is therefore
load-bearing, which is why §5.3's machine check exists.

The same holds for every uniqueness test: in-place `Array` updates (consuming natives, O1),
`Unpack`'s unique path, `DropReuse`. None may be reached through a lent register; all are
reached only through an owned one, and an owned reference to a cell that is also lent has
count at least 2 (the owner's and this one), so they see it as shared, correctly.

### 4.5 Closures and partial applications

No borrowing through them in this design. A lambda's parameters are owned (it is called by
`apply`, which can't know the callee). Captures are owned (O1). `Apply` takes its function
value and arguments owned: so `f` in `insertWith f key value tree` is cloned and dropped at every
level, and an `Ord` dictionary that isn't specialised away is owned because its `compare` field
is applied. Letting `Apply` borrow its function value (the callee's closure parameter lent) is a
separate calling-convention change to the native value convention and the apply stubs; it is
listed as a follow-up (§10), not part of this note.

### 4.6 Effects and handlers

Nothing in the effect runtime borrows. Stitchwort's effects are values (`Done`/`Call` trees
and `Bind` nodes the runner steps), not captured stacks, so no frame with live lent registers
is ever suspended and resumed: when a body returns a computation, its frame is gone. Everything
that outlives a frame (continuations, resumptions, handler state, the `Bind` node's `k`) is a
closure capture or an effect native's argument, so owned (O1); resuming twice re-reads owned
captures. Effectful functions' bodies build `Delay`/bind nodes from their parameters, so they
are owned by O1. Fused state-passing handlers (`fusion.rs`) are ordinary globals and are
inferred like any other; their state is usually rebuilt (O1/O5).

### 4.7 Native code

- **Signature:** unchanged (each argument as three words, `tail` calling convention). A lent
  argument's words are passed and the callee doesn't own them.
- **`full`** (`n1.rs`, the registers that may hold a value at each point, which writes,
  returns and exits drop): lent registers are never in it, so returns, error exits and the
  self tail call's jump never drop them. A `Peek` is three loads.
- **`LEND` operands:** no increment at the call; an owned register passed `LEND` stays full
  and is dropped after by the bytecode's `Drop`.
- **Trampolines:** `enter` runs the entry (no parameters); `apply` and the effect runtime's
  loop go through function values, which are owned (owned copies in B2). So nothing crosses the
  Rust/native boundary lent.
- **`trace_refcounts` mode:** unchanged; lent operations make no events.
- The module docs of `native_abi.rs` ("Ownership") and `n1.rs` ("The thesis") gain one
  sentence each: borrowed parameters and `Peek`s are the one place native code holds a value
  it doesn't own, exactly where the bytecode lends.

### 4.8 The JavaScript backend

Nothing to do: `crates/js` compiles core terms to JavaScript with the garbage collector, and
shares only erasure, specialisation and fusion with `crates/rt` **[read: `crates/js/src/lib.rs`
imports]**; it has no reference counts.

## 5. Making it safe

### 5.1 The invariant

A lent reference is valid while its owner holds an owned one. Owners are frames: a frame
lends only in a **non-tail** call (or in a tail call that passes on something it was itself
lent), so the owner's frame is below the borrower's on the stack for the borrower's whole life,
and the owner can't drop or consume the value until the call returns. Nothing lent is stored
anywhere that outlives the frame (it is incremented where it escapes). §4.3 guarantees no tail
call ends an owner's frame while it lends.

### 5.2 The checks

- **Static:** the validator's discipline (§4.2) on every compiled body, and the inference's
  own invariant (a lent parameter's flag is false everywhere it is tail-passed from an owner)
  re-checked after copies are made.
- **The machine as checker (§5.3):** every release of a lent value asserts the cell's count is
  above 1, so an owner that dropped early is a panic in tests, not a use after free in native
  code.
- **Allocation-trace agreement** (`alloc_trace.rs`, `trace_refcounts`): machine and native
  give the same `alloc`, `reuse` and `free` events in the same order, and the same `inc`/`dec`
  events apart from the machine's lent ones, which it tags.

### 5.3 The machine: check, don't exploit

The machine's registers are `Vec<Value>` and it has no `unsafe` today **[read: no `unsafe` in
`machine.rs` or `value.rs`]**. Holding a lent value there without a count means a bitwise copy
of an `Rc` that must never be dropped and on which `Rc::get_mut` must never be called (it would
see count 1): `unsafe` in the reference executor, and the playground's too.

Proposed instead: the machine **clones** lent values (a `LEND` operand, a `Peek`) and drops
them where the native code forgets them (at the frame's end, or at an explicit end of a lent
register's life), tagging those `inc`/`dec` events `lent` in the trace. It gets no faster, but:

- **Same decisions.** Its counts are native's plus the number of live lent copies. A uniqueness
  test is only ever made through an owned reference (§4.4); if a lent copy of that cell is live,
  its owner's reference is live too, so native sees at least 2 as well. Machine and native make
  the same reuse and in-place choices, so traces agree once `lent` events are filtered.
- **A run-time check of the invariant.** Releasing a lent copy asserts the count is above 1.
  If the compiler ever let an owner drop a value while it was lent, the machine panics with
  "borrowed value outlived its owner" where native code would read freed memory.

The machine is what `stitchwort run`, the tests and the playground use; native code is what
`build --native`, `bench:compare` and `bench:aoc` run. So the speed-up is native's only. Exploiting borrows in the machine (bitwise copies under
`unsafe`, forgotten instead of dropped) could be a later, separate decision, with Miri on the
machine's tests as the condition.

## 6. Stages, with gates

| Stage | What | Who, estimate | Gate |
|---|---|---|---|
| **B0** | Measure before building: the inference as a dry run (`crate::borrow` computing flags, printed by a dev dump, no codegen change) over std, `bench/compare` and `aoc/`; plus a dev counter in the machine of the `inc`/`dec` pairs B1 would remove (clones of operands at would-be-lent positions, `Unpack`/`Field` clones of would-be-lent scrutinees, and their matching drops) on mapops, dijkstra, the core ten and a bench:aoc sample. | Sonnet, about 3 h | Build B1 if mapops or dijkstra would lose at least 3% of their reference-count operations' instructions (converted at SW-2513's measured per-level cost), or the bench:aoc sample's median 1%. Report which std functions come out borrowed, and how many parameters O7/O8 force owned. |
| **B1** | The pass (O1-O8), `Global::borrowed`, `LEND`, `Peek`, lent register sets, the validator's discipline, the machine's checked clones and tagged trace events, native `full` and calls. No owned copies (O7, O8 force owned). Docs: `fast-runtime.md` "As built", `native-compilation.md`, the module docs named in §4.7. | Opus (soundness, calling convention), about 1-1.5 days | mapops -3% or better in instructions, dijkstra better, no core-ten or bench:aoc program worse than +1% (noise is 0.1%, SW-2463), step and frame counts identical on every runtime test (§6.1). |
| **B2** | Owned copies for value uses and cross-component owned tail calls (O7, O8 dropped); `Reuse::Copy` generalised. | Opus or Sonnet, about 4 h | B0's count of parameters forced owned by O7/O8 says whether it is worth it; then the same gates as B1, plus code size within `MAX_GROWTH`. |
| **B3** | Lent reads of owned values: a `Field` of an owned register that stays live past every use of the field, where every use is a lent position, becomes a `Peek` (no increment; never in a tail call's operands, since the owner's frame ends there). The same for `Global` reads of a computed constant (held by the run, never freed; ties in with constant-hoisting.md). This is what makes `w.map.get k` free when `w` is a live record (after SW-2514, `w.map` in an *update* is a move; a read of it beside other uses is still a clone). | Sonnet, about 4 h | mapops and bench:aoc; AoC's record-of-state house style is where it shows. |

Not staged here: closures borrowing their function value (§4.5).

### 6.1 Test strategy

All within the lane test budget (`task test:one`, `task test:lane AREA=…`); the batch verifier
and the daily tier do the rest.

- **Inference unit tests** in `crates/rt` on small programs: `get`-shaped walks borrowed;
  rebuilding functions owned by O5; a returned parameter owned; O4 on a mutual pair; O6 through
  a nested field; O7 and O8 forcing owned (B1) and making copies (B2); TRMC bodies untouched.
- **Validator negatives:** hand-built bytecode that `MOVE`s, `Unpack`s, `Return`s or tokenises
  a lent register is rejected.
- **The machine's check** runs in every test that runs compiled code (it costs a count read per
  lent release, in every build: the machine clones and drops lent values anyway).
- **Trace agreement:** the existing machine-versus-native allocation-trace tests, extended with
  programs that lend (lookups in a kept map, a lent value escaping into `Some`, an owned value
  lent then dropped after the call, a lent tail call), compared with `lent` events filtered.
- **Counts unchanged:** steps and frames of the runtime test corpus, before and after, must be
  equal (they are a strong regression check, since §4.3 promises exactly that).
- **Answers:** the runtime and AoC answer tests that touch Map and Set.
- **Compute mode:** the runtime differential fuzzers (`task fuzz:*`) with fresh seeds once B1
  is merged; the orchestrator schedules them.

## 7. Estimated savings

All **[estimated]** unless marked, and B0 replaces them with counts.

- **Per lookup level:** today 250-310 instructions natively, `inc`/`dec` 44% of `get`'s body
  **[measured, SW-2513 §1, §2.2]**. Borrowed: the two increments, two decrements, the failed
  uniqueness test and the 24-byte copies go; about 100-150 remain (the switch, the comparison,
  loads, the tail call's step and frame bookkeeping).
- **mapops** (`get` 8.1% of 24.24 G before SW-2514, 12.2% of 12.62 G after **[measured]**):
  removing the counted part of `get` saves 0.5-0.7 G after SW-2514 (-4 to -5.5%), and about
  0.85-1.3 G before it (-3.5 to -5.5%); `shape`'s borrowed `size` reads add a little (well under
  1%: its size fields are numbers, so today's clones there are copies, not counts).
- **dijkstra** (19.61 G instructions natively, SW-2426 **[measured]**): 17.2 M lookup levels and
  4.3 M `shape` unpacks on shared nodes **[measured on the machine, SW-2371, stock day 15]**. At
  130 instructions saved a level, 2.2 G, -11%; keys there are positions, so a level may count
  more (a key cell too) or the counts may have moved since SW-2371. Range -5 to -12%.
- **The core ten:** dijkstra as above; expressions, scan, matcher and bridge are parsing and
  effect work (closures and effect values, owned by design: under 1%); pidigits is `Nat`
  arithmetic in natives (already lent to natives: about 0); binary-trees walks a tree it then
  drops (lending changes where it is freed, not how much is counted: about 0, and a check
  that it doesn't get worse); memory-game is arrays; octopus and disk not profiled for this.
  Geometric mean -0.5 to -2%, dijkstra most of it.
- **bench:aoc:** most days keep a `Map` or `Set` and look things up in it while it is live
  (visited sets, grids as maps, memo tables); a day whose hot loop is lookups gains like
  dijkstra (5-12%), the rest little. Median -1 to -3%, lookup-heavy days -5 to -12%.

Overlaps: none with SW-2514 (it is about updates of a unique record; lookups on a live map are
unaffected), with SW-2513's target 2 (fused balance: owned code) or with constant-hoisting.md
and compiled-handler-dispatch.md (closures and constants; B3's lent constant reads are the only
contact). SW-1825 (native `Map.Tree` functions) would overlap completely for structural keys;
this helps custom `Ord` keys and every other read-only walk too.

## 8. What a user sees

- **Answers, effects, errors:** nothing changes. Borrowing changes only who drops a reference.
- **Steps and frames:** identical (§4.3), so `--steps`/`--frames` limits trip at the same
  points, and native and machine still count the same.
- **Speed:** native code faster on lookup-heavy programs (§7); the machine unchanged (§5.3).
- **Memory:** peak memory can rise a little where a function borrows a value that, owned and
  unique, it would have freed as it went, and builds something of a different shape from it
  (a tree turned into a list by a borrowed walk keeps the tree until the walk returns).
  Rebuilding functions stay owned (O5), so the common cases are unaffected. Not measured; B0's
  dry run can list the functions where this could happen (borrowed, and storing fields in
  constructors of another size).
- **Profiles:** `run --profile` and `profile:native` may list owned copies as separate bodies
  (B2), as they list reuse copies (`name[reuse]`, `reuse.rs:163`); naming them `name[owned]`
  and folding them into their original in user-facing summaries is the suggestion. The native
  instruction map gains `Peek` as a category; `inc`/`dec` shares fall.
- **Allocation trace and census:** fewer `inc`/`dec` events natively; the machine's are tagged.
- **Cache keys:** compiled outputs change (bytecode and native code), so native build caches
  are invalidated once; migration cost, which doesn't count (D2303).

## 9. Decisions for Matt

- **D3441: Build borrowed parameters, inferred by the compiler, with no syntax for them,
  starting with B0's measurement and building B1 only if it clears the gate?** [rec: yes. It is
  the general fix for the "read-only walk copies the node" cost that the mapops and dijkstra
  profiles both show, it changes no answer and no count, and it needs nothing from users.
  Lean also lets users write `@&` to force a borrow; we have no case needing it, and an
  annotation would be language surface to design and document, so not now.]
- **D3442: The machine checks borrows instead of exploiting them (no `unsafe` in the machine;
  it clones lent values, tags them in the trace, and panics if one outlives its owner), so only
  native code gets faster?** [rec: yes. It keeps the reference executor safe Rust and turns it
  into a run-time check of the one invariant that, if wrong, would be a use after free in
  native code. Exploiting borrows in the machine too can be decided later, on its own numbers,
  with Miri as the condition.]
- **D3443: Step and frame counts stay exactly as they are: a tail call is never demoted to a
  call (as Lean does for calls outside a mutual block), at the cost of forcing some parameters
  owned in B1 and of owned copies in B2?** [rec: yes. Frame counts are part of what a run means
  (the `--frames` limit, constant-space loops through function values), the native/machine
  agreement relies on them, and the cost is code size, capped as reuse copies are.]

Not for Matt, recorded as calls on the ticket: a returned parameter is owned (O2, unlike
Lean's published rules); a field stored in a constructor does not make its parent owned (O6,
as Lean); TRMC loops and lambdas don't borrow; owned copies share the reuse copies' caps; B0
before B1.

## 10. What I didn't check, and follow-ups

- **Nothing was run.** The per-level accounting in §1.4 is inferred from the bytecode
  compiler and the machine, consistent with SW-2513's shares and SW-2371's counts, not from a
  dump of `get`'s bytecode.
- **Lean's implementation** was described from my reading of `Borrow.lean` and the paper, not
  re-read for this note at a pinned version; in particular whether Lean owns returned
  parameters (O2) and how it treats exported functions.
- **dijkstra's current counts:** SW-2371's 17.2 M lookups were on the machine before later
  fixes; its key type (pairs, so possibly a counted key per level) was not checked.
- **How the reuse copies are shown in profiles** (that `[reuse]` names reach the user-facing
  profile unfolded) was read from `reuse.rs:163`, not from `profile.rs`.
- **The register allocator** may need more than a disjoint range for lent temporaries if
  temporaries are shared across branches in ways I didn't read (`code.rs`'s `temp`/`mark`).
- **Follow-up, `Apply` borrowing its function value** (§4.5): `insertWith`'s `f` and an
  unspecialised `Ord` dictionary are counted at every level; worth its own note once B1's
  numbers are in.
- **Follow-up, bind fields where they are used** (§1.2): independently of borrowing, an owned
  `Unpack` of a shared cell could clone only the fields the taken path uses. It helps owned
  walks on shared data, not `insertWith` (whose arms use every field). Not proposed here; worth
  a measurement after B1.
