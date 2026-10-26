# Fully native executables: no machine inside

**Status:** design note, 26 October 2026, after Matt's D1294. Nothing here
changes the compiler; the measurements used scratch scripts only. The
native track has no review stops (native-to-standalone), so the decisions
([at the end](#decisions), D1296–D1303) are **decided by Claude,
provisional**: work can go ahead on them, and each says what evidence would
overturn it.

**D1294 (Matt), which this note implements.** A standalone binary is fully
native: no interpreter inside, and `stitchwort build` fails rather than fall
back. In his words: "surely a compiler doesn't hedge its bets, the job is to
create a native executable, not a hybrid thing that may or may not run an
interpreter instead." This overturns D1287 (the hybrid as the architecture,
standalone-executables.md).

Claims are marked:
- **[ran]**: done for this note on the Apple M4 Pro (macOS 26, arm64),
  release build of `6bfd0114` with `--features stitchwort-cli/native`.
  The load average was 21–38, so times are rough; instruction counts are
  steady to 0.1%.
- **[source]**: read in this repository at `6bfd0114`.
- **[paper]**: read in the paper's full text (listed in §1.1), quoted.
- **[web]**: read in the linked page.
- **[inferred]**: my reasoning, not tested.

## 0. Summary

**What runs on the machine today [source].** The binary links the machine
and carries the lowered program (`sw_program`), and the machine runs:
- (a) `main`'s entry body, the glue that builds the `Delay` the runner steps
  (`n1::plan` skips `image.entry_code`);
- (b) every effect operation other than `bind`'s `Done` case (`foldComp`
  and its variants, `translate`, `runPure`), `Text.fold`, and every function
  value that isn't a global or a lambda (resumptions, `StateRun`, `StateK`,
  `JumpK`, `DoneK`, `DelayK`), through `sw_effect`, `sw_fold`,
  `sw_tail_effect`, `sw_perform` and `sw_apply_prepare` (`Work::Enter`);
- (c) the whole run, if `frames × level bound` may not fit the stack
  (`NativeIslands::fits`);
- (d) anything `census::n1_blocker` declines (nothing today, but the rule
  is there), and anything at all if `probe_layout` fails.

**The recommendation, in one paragraph.** Port the machine's effect runtime
to native code *as it is*: the same data (`Bind` nodes, the persistent
pending list, `Resume`, `StateRun`), so that outputs, effect counts and
allocation traces agree with the machine by construction. Only the
control moves. Every place the machine keeps a pending return in a `Ret`
(`Eff`, `Then`, `Inject`, `Step`, `Fold`) becomes the rest of a native
function after an ordinary call. Every place it continues in a tail
position becomes a Cranelift `return_call`. The routines that can call
program code are written as Cranelift IR by the compiler, as N3's `apply{n}`
stubs already are ("runtime bodies"). Rust keeps only leaf helpers, which
never call back into program code. Then compile the entry body, drive
compiled code from the existing Rust `IO` runner, size the stack from a
bound the build computes, and make every former fallback a build error.
The binary then carries no machine, no bytecode compiler, no codec and no
lowered program: about 164 KB of code and data leaves (§5), so about 1.9 MB stripped for the
roguelike instead of 2.08 MB.

**What it isn't.** It isn't fibers, CPS or evidence passing. The
literature's strategies (§1) each change what a computation is at run time,
so the native runtime would stop agreeing with the machine event for event.
Two of them (OCaml 5's fibers, WasmFX) are one-shot, and Stitchwort's
resumptions are multi-shot. Those strategies stay possible later, as
optimisations made in both runners together (§1.5).

**Performance, honestly.** Native-only is mainly about the architecture,
not speed. Today an effect-heavy run spends 3.7% of its time in compiled
code, 37% in the machine and about half allocating and freeing **[ran]**,
§1.6. A native runtime removes most of the 37%, but none of the allocation
the shared representation requires. Expect about 1.3–1.8× on
`effects.sw`, not 5× **[inferred]**. The big wins, of Koka's kind (10× for
tail-resumptive operations [paper]), are representation changes for later.

**Plan** (§6): seven stages, NO1–NO7. Fallback ends in NO5, for `build` and
`run --native` together. The machine stays in the compiler, as `run` and
as the oracle of the agreement tests.

## 1. A native effect runtime (the core)

### 1.1 What was read

Read **in full**, from PDFs downloaded to the session's scratch directory
(`papers/`):
1. Ningning Xie and Daan Leijen, *Generalized Evidence Passing for Effect
   Handlers: Efficient Compilation of Effect Handlers to C*, ICFP 2021
   ([PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf)).
   This is the reference for compiling multi-shot handlers to a target with no
   stack capture (C), which is our situation with Cranelift.
2. KC Sivaramakrishnan, Stephen Dolan, Leo White, Tom Kelly, Sadiq Jaffer
   and Anil Madhavapeddy, *Retrofitting Effect Handlers onto OCaml*, PLDI
   2021 ([arXiv 2104.00250](https://arxiv.org/abs/2104.00250)). This is the
   reference for fibers and for stack-overflow checks in a native runtime.
3. Serkan Muhcu, Philipp Schuster, Michel Steuwer and Jonathan Immanuel
   Brachthäuser, *Multiple Resumptions and Local Mutable State, Directly*,
   ICFP 2025
   ([PDF](https://se.cs.uni-tuebingen.de/publications/muhcu2025multiple.pdf)).
   This is the reference for multi-shot resumptions with stack switching,
   using reference counts, which we also have.

Consulted for specific claims, **not read in full**:
- Schuster, Brachthäuser and Ostermann, *Compiling Effect Handlers in
  Capability-Passing Style*, ICFP 2020 (the abstract and introduction);
- Phipps-Costin et al., *Continuing WebAssembly with Effect Handlers*
  (WasmFX), OOPSLA 2023 (the one-shot rule and the fiber layout, §2 and
  the implementation section).

Every full text was available; nothing had to be read from an abstract
alone.

### 1.2 The strategies, and what they cost here

| Strategy | Who | Capture / resume | Multi-shot | What it needs from the code generator |
|---|---|---|---|---|
| Fibers: a stack per handler, switched | OCaml 5, WasmFX | constant (one-shot) | no | stack switching, a stack check in every prologue |
| Segmented stacks, copied when shared | Effekt's LLVM backend (Muhcu et al.) | constant if resumed once; a copy otherwise | yes, not reentrant | its own stacks and calling convention, reference counts |
| Monadic translation: `Pure \| Yield`, bubbling yields | Koka (Xie and Leijen) | grows with the frames between operation and handler | yes | a "yielding?" check after each effectful call; nothing exotic |
| CPS with a meta-stack, trampolined | Effekt JS, Links | grows with the handlers crossed | yes | every effectful function in CPS |
| A run loop over `Bind` nodes and a persistent pending list | Stitchwort's machine (D1162), PureScript, cats | constant (a pointer) | yes, any number of times, reentrant | calls and tail calls |

The quotes behind the table **[paper]**:
- **OCaml 5 is one-shot by design.** "This example does not resume a
  continuation more than once. This also holds true for other use cases such
  as generators and coroutines. Hence, our continuations are one-shot, and
  resuming the continuation more than once raises an Invalid_argument
  exception" (Sivaramakrishnan et al. §3.1).
- **WasmFX is one-shot too.** "The resume instruction consumes its
  continuation operand, meaning a continuation may be resumed only once
  … (an extension to support multi-shot continuations would be
  interesting, but difficult to support efficiently or robustly in existing
  Wasm engines)" (Phipps-Costin et al. §2).
- **Effekt's LLVM backend gets multi-shot by copying.** "We only copy
  whenever we resume a shared continuation" (Muhcu et al. §1). Its limits
  are: "Resumptions are not reentrant, meaning that a continuation cannot be
  resumed, while it is already running. Our implementation leads to a
  runtime error in this case" (§1.2); and "discarding the continuation
  (e.g. exceptions) requires us to unwind the continuation in linear time"
  (§1).
- **Koka needs no runtime support.** The monadic translation "can be
  directly compiled to any target platform (including C/LLVM, WASM,
  JavaScript, Java VM, .NET, etc) without requiring special runtime
  mechanisms" (Xie and Leijen §1). The cost: "a multi-prompt monad is linear
  in the continuation points" (§1). In C, yielding is a flag checked after
  every effectful call: "we always return results normally assuming Pure,
  and set a (thread-local) flag to indicate yielding" (§2.11).
- **The fast paths that matter in Koka.** Tail-resumptive operations run in
  place: "tail-resumptive optimization speeds up the counter benchmarks by
  10×" (§5). Bind-inlining "speeds up the counter benchmarks by 25%"
  (§5). With bind-inlining, "if no operation performs a full yield, no
  allocation happens along this path and tail-recursive calls are
  preserved" (§2.10).

### 1.3 Why none of them replaces the machine's design here

1. **Multi-shot and reentrant.** `Each.collect` resumes twice, and a
   resumption may be stored and resumed later (effect-runtime.md §2). The
   machine's pending list is never changed, so resuming is taking a
   pointer, any number of times, even while another resumption of the same
   continuation runs. That rules out fibers (one-shot). Effekt's copying
   gives multi-shot but not reentrancy (the quote above).
2. **Agreement with the machine.** The n1–n4 tests require the same output,
   the same effect counts (`EffectCounts`: steps, pushes, pops, routes,
   resumes, binds, jumps) and the same allocation trace, event for event
   (`alloc_trace.rs` traces every constructor cell, which includes `Bind`
   nodes, `Done`/`Call` cells and the pending list's cells) **[source]**.
   - Fibers or segmented stacks build no `Bind` nodes and no pending cells,
     so their traces and counts would differ.
   - Koka's translation builds a resumption piece by piece while a yield
     bubbles (Xie and Leijen §2.7), not a pending list, so its traces would
     differ too.
   - To use any of these, the machine (the reference) would have to change
     with them.
3. **Nothing on the native stack needs capturing.** Since D1162, an effectful
   continuation is a heap value (a `Bind` node's `k`, a cell of the pending
   list) before any operation happens. Capture is "keep a pointer". The
   reason fibers and stack copying exist (the continuation lives in stack
   frames) doesn't arise.
4. **Cranelift has no stack switching** **[inferred]** (nothing in the
   `cranelift-codegen` 0.136 API we use switches stacks). Fibers would need
   assembly per architecture, as Wasmtime's fiber library has (WasmFX's
   implementation section: "Stack switching in the fibers library is
   implemented in x86_64 assembly code").

**So the native runtime is the machine's runtime, compiled.** That is
design A of effect-runtime.md, which the literature calls the free-monad
run loop. It is also what Xie and Leijen argue for at the level that matters
to us: control made explicit as ordinary functions and calls, which "can be
directly compiled to any target platform" (§1).

### 1.4 How each piece works without the machine

**The rule.** Every routine that can call program code is native code
emitted by the compiler (a *runtime body*), in Cranelift's `tail` calling
convention, like program bodies. Rust keeps only *leaf helpers*: they
allocate, take cells apart, build runtime values and drop, and they never
call program code. The apply stubs of N3 (`apply{n}`, hand-written IR around
`sw_apply_prepare`) are the precedent **[source]**.

Why not keep the loop in Rust and call compiled closures from it? Rust can't
make a guaranteed tail call. `become` is "currently implemented as part of
an experiment", behind `#![feature(explicit_tail_calls)]`
([tracking issue](https://github.com/rust-lang/rust/issues/112788))
**[web]**. So every tail position would need N4's tail requests, and every
callback a nested Rust frame. That nesting is why `NEST_ROOM` exists today:
4 KiB of stack allowed per counted frame, and 3,904 bytes measured for a
handler that resumes in a non-tail position (`native_abi.rs`) **[source]**.

**Each `Ret` becomes the rest of a native function after a call
[source, inferred].** The machine's frames are on the heap, so it keeps "what
happens to this result" as data, a `Ret`. A native routine keeps it as
the code after a call, with the values it needs in registers or spill slots:

| The machine (`machine.rs`) | Natively |
|---|---|
| `eff_run`: the loop over `Bind` / `Done` / `Call` | runtime body `rt_loop(c, pending, handler, state)`: a Cranelift loop. `Bind c k`: cons `k` onto `pending`. `Done x` with something pending: pop `k`, **call** `apply1(k, x)`, and go on with the result |
| `Ret::Eff(EffRet { handler, pending, state, ret })`, boxed per pop | nothing: `handler`, `pending` and `state` are live across that call in `rt_loop`'s frame. Up to about 7 boxes per `bump` go (effect-runtime.md §9.11) |
| `Done x`, nothing pending, `Handler::Fold` | `return_call apply1(done, x)` |
| `Handler::State`: `apply(done, x)` then `Ret::Apply([state])` | **call** `apply1(done, x)`, then `return_call apply1(result, state)` |
| `RunPure` / `Translate` / `Step` at `Done` | return `x`, or the `Done` cell as it is |
| `eff_call`, `Handler::Fold` | leaf `sw_resume(handler, rest, pending, op, lazy)` makes `k`; `return_call apply2(call, o, k)` |
| `eff_call`, `Handler::State`: `apply(call, [o, k, jump, s])`, `Ret::Step` | leaf helpers make `StateK` and `JumpK`; **call** `apply4`; then the jump test (`state_step`): a `Jumped(y, s′)` goes on with **call** `apply1(rest, y)` in the loop, anything else is returned |
| `eff_call`, `Handler::Translate`: `apply(inject, o)`, `Ret::Inject(k)` | **call** `apply1(inject, o)`; return the cell `Call(v, k)` |
| `resume` (a `Fun::Resume` applied), lazy | leaf: the cell `Bind (Done y) (Resume, not lazy)` |
| `resume`, eager; `Translate`'s `Ret::Then` | runtime body `rt_resume`: **call** `apply2(reply, o, y)` if translating, **call** `apply1(rest, y′)`, then continue as `rt_loop` with the resumption's pending list |
| `Fun::StateRun` applied | runtime body: `rt_loop` from `arg` (or **call** `apply1(rest, arg)` first) |
| `DoneK`, `StateK`, `JumpK`, `DelayK` applied | leaf helpers: each builds one value |
| `fold_start` / `fold_step`, `Ret::Fold` | runtime body `rt_text_fold(t, z, f)`: a loop over the characters from the end, **calling** `apply2(f, c, acc)` |
| `effect(op)` from a `Prim` | a direct call of the op's runtime body |
| `TailPrim` of an effect op (frame popped first) | `return_call` of the op's runtime body. This replaces `sw_tail_effect`, `TailRequest` and `sw_perform` |

`bind c k` stays as N4 made it: `sw_bind` takes `c` apart, and for `Done x`
the code applies `k` inline (the backend invariant of effect-runtime.md
§9.1.4).

**The apply stubs learn the runtime's function values.**
`sw_apply_prepare` today hands every `Fun` that has no code to the machine
(`Work::Enter`) **[source]**. Natively, the stub dispatches on the variant
byte: global and closure as now, `Resume`/`StateRun` to their runtime
bodies, and the four leaf kinds to their helpers. `Jumped` is never
applied, as on the machine.

**Stack depth stays bounded by the program's own calls [inferred].** A
runtime body is on the native stack only while it waits for one call it
made, so there is at most one runtime frame per pending program call. In a
tail position everything is a `return_call`, so the loop through a handler
runs in constant stack. That is the same property the machine has with
`Ret::Eff` and `TailApply`, and it is N4's 250,000-long effect loops under a
limit of 100 frames, which become the test of this.

**Counting.** The machine counts a step per loop iteration (`eff_run`:
`self.steps += 1` and the limit check) and a frame per body entered; a
`TailPrim` of an effect counts no step itself (`machine.rs`, the
`TailPrim` arm) **[source]**. The runtime bodies do exactly that, with the
steps in the pinned register as program bodies have them. They pass on the
caller's count of pending frames and enter none themselves, since the
machine pushes no frame for the loop either.

**Error exits.** This is the part most likely to be wrong first. The values a
`Ret` holds (an `EffRet`'s handler, pending list and state; a `Then`'s
`rest`; a `Step`'s resumption) are dropped by the machine with the frame
that holds the `Ret`, i.e. the callee's (`release_failed`: frames
outermost first, then registers) **[source]**. N2b solved the same problem
for the apply stub ("the apply stub's rest joins the callee's group"
**[source]**). A runtime body leaving with an error hands its held values
to the same unwind log, joined to its callee's group. The every-limit sweeps
of `n2b.rs` and `n4.rs` check this event by event. Without the machine, the
log is dropped by the runtime's own `release_failed` (a Rust leaf, which
calls no program code).

**Constants** move from `State::globals` to a cache table in the run's
context, filled by `sw_global_set` as now.

### 1.5 What this leaves for later, and in which runner

None of these are in the plan. Each is for both runners at once, so
agreement holds, and only with a benchmark:
- the state loop at an open row (effect-runtime.md §9.11 B; 36% fewer
  instructions measured at the empty row);
- no `translate` for a call that only widens its row (§9.11 C; 16%);
- Koka's tail-resumptive operations run in place (Xie and Leijen §2.6, 10×
  on their counter), i.e. evidence passing for clauses of the form `k e`.
  It needs the `under` frame, whose correctness "is subtle" (§2.12.2): the
  first formalisation "turns out to be unsound".

### 1.6 Performance: what is measured, and what to expect

**Today, `effects.sw` at 1,000,000 operations of each kind** (`bump` through
a state handler under `{IO}`, `ask` through a reader), whole runs less a run
with no operations; best of 3, all within 0.1% **[ran]**:

| | Instructions / op | Cycles / op |
|---|---:|---:|
| machine (`run`) | 22,470 | 4,330 |
| `run --native` | 19,740 | 3,940 |
| ratio | 1.14× | 1.10× |

**Where a native run's time goes**: macOS `sample` of `run --native` at
3,000,000 each, 3,083 samples on the run thread, by function on top of the
stack **[ran]**:

| | Share |
|---|---:|
| the machine (its loop, `apply`, `enter`, `eff_run`, …) | 36.7% |
| dropping and freeing values (`value::free`, `take_children`, drop glue) | 30.1% |
| the allocator (mimalloc) | 18.8% |
| compiled code | 3.7% |
| `sw_*` helpers and `native_abi` | 6.1% |
| `memcpy`, `Rc`/`Vec` plumbing, other | 4.6% |

**What to expect [inferred].**
- The machine's 37% becomes compiled runtime code. N1–N3 made plain code 3.3×
  to 4× cheaper in instructions than on the machine (native-compilation.md,
  "N4 as built"). Taking 3× here leaves about 12% of today's time.
- The EffRet boxes go (up to 7 of 45 allocations per `bump`).
- The cells stay: the trace requires them.
- That is about 1.3–1.8× on this benchmark: of the order of 11,000–15,000
  instructions per operation, from 19,740.
- To go further, allocate less per operation. That is §1.5's work, in both
  runners.

The note doesn't promise more, and stage NO3 records the real figure.

## 2. The entry glue, and the runner driving native code

**The entry is an ordinary body [source].** `Program::entry` is a `Body`
with no parameters. `code::compile` makes it the last code
(`entry_code`), and `Machine::entry` pushes a frame for it with `Ret::Host`.
`n1::plan` leaves it out ("glue the machine runs once"), but nothing in it
is special: it runs `main ()` and returns the `Delay`. Natively it is
compiled like a constant's body and called through a zero-argument
trampoline.

**The runner stays Rust, on an executor interface [source, inferred].**
`run.rs`'s `Runner` steps the `Delay` that `main` returns: `Delay`
frames, `foldD` handlers and their captures, routing `IO` operations, ticks,
the step budget per stretch, and live input. It uses the machine through
six things: `entry`, `call(f, args)`, `step_comp(c)`, `reset_steps`,
`shapes`/`program`, and `depth_report`. NO4 makes `Runner` generic over an
`Executor` trait with exactly these, which both `Machine` and a native
executor implement:
- `call` is an apply stub entered through a trampoline;
- `step_comp` is `rt_loop` with `Handler::Step`;
- `entry` is the compiled entry body.

Each call starts from the runner, near the top of the stack, so nothing
nests.

**Is the runner an interpreter?** It doesn't run program code. It takes
apart the value `main` returns, which is the meaning of `IO` at the top
level (partial.md §7.4), and calls compiled code for every function the
stepping needs. That is the same job OCaml's runtime does for a scheduler, or
the Haskell RTS for `IO`. D1298 asks whether this counts as "no
interpreter"; the recommendation is that it does.

## 3. Stack depth: fail cleanly instead of falling back

**Today [source].** The frame counter is the limit (D1253): the machine's
rules, the same points of failure. A stack-pointer check is behind it as a
safety margin. If `frames × level bound` doesn't fit the stack less
`HOST_ROOM`, `HELPER_ROOM` and a frame, the whole run goes to the machine
(`Crossing::fits`). `NATIVE_STACK` is 16 GiB of address space
(`crates/host`). The roguelike's widest body is 2,760 bytes.

**The options:**

| Option | Clean error? | Agrees with the machine? | Cost |
|---|---|---|---|
| A. The frame counter, with a stack sized so it always fires first, and the stack-pointer check as a backstop (today's mechanism, without the fallback) | yes: the counter's `E-RESOURCE`; the backstop's is the same error | yes, exactly, while the bound holds | none new; reserving address space |
| B. Guard page and a `SIGSEGV` handler on an alternate stack | only roughly: in a signal handler you can't flush a `BufWriter` or drop values safely | no: it fails where the stack runs out, not at the frame limit | a signal handler |
| C. Growable stacks: a check in every prologue, copying the stack on overflow (OCaml 5) | yes | yes | Cranelift spills to stack slots whose addresses are passed to helpers [source], so the stack can't move; a new stack layout and checks everywhere |
| D. Segmented stacks: switch to a new segment on overflow | yes | yes | stack switching that Cranelift doesn't have; a call through a thunk at each boundary |

The literature's numbers for C [paper]: the checks cost OCaml 5 "less than
1% slower than stock" on average, but "OCaml text section size … is 19%
more" (Sivaramakrishnan et al. §6.1). Stock OCaml, like option B, "relies on
the guard page at the end of the stack region to detect stack overflow" (§2).

**Recommendation (D1299): A, with the build doing the arithmetic.**
- `stitchwort build` knows the frame limit it embeds and the widest frame
  bound of everything it compiled, now including the runtime bodies. One
  counted level is a body plus at most one runtime frame (§1.4). With no
  nesting through the machine, `NEST_ROOM` goes (4 KiB less per level).
- The binary reserves `frames × level bound + HOST_ROOM + HELPER_ROOM`,
  rounded up. For the roguelike: the default limit of 2,000,000 frames (`budget.rs`) × about 3.3 KB (its widest body, 2,760 bytes, plus a runtime frame), so 6–7 GB of
  address space **[inferred]**, less than today's 16 GiB.
- If that exceeds a cap (64 GiB), `build` fails with a message naming the
  frame limit and the widest body, and suggests a smaller `frames` limit.
- If the reservation fails at start-up (the operating system refuses),
  the binary says so before running anything, and exits 2.
- The stack-pointer check stays as the backstop. If it ever fires, which
  would be a bug in the bound, the error is the same clean `E-RESOURCE` with
  the deepest-function note, never a crash.
- The deepest-function note: natively, each frame that leaves by the error
  exit reports its body's number with its values (`sw_unwind` gets one more
  argument). The runtime counts them, as `note_deepest` counts machine
  frames. Function names come from a table in the object (§5).

**Unverified: Linux.** Whether Linux with its default overcommit gives a
thread a many-GiB stack wasn't checked: there is no Linux machine here, and
it is the same open question S5 left. NO7 tests it. If it fails, the
fallback design is B as a backstop over a smaller stack, with a lower default
frame limit on Linux. That would be a change to `Limits`, so a decision for
Matt.

## 4. Build errors instead of fallback

Each former fallback becomes a build error (or, for what only the running
binary can know, a start-up error) with a plain message:

| Today | After NO5 |
|---|---|
| A body has an instruction `n1_blocker` declines: it and its callers run on the machine | `build` fails: "``Main.f`` uses `<instruction>`, which the native compiler doesn't compile yet" (none today, but the census keeps the rule honest) |
| `probe_layout` fails (`std`'s `Rc` or slice layout isn't as expected): no native code runs | Checked by `build` (the CLI and the runtime library come from one workspace build), which fails with the probe's message. The library checks again at start-up and exits 2 with "internal error: this executable can't run: …", as for a manifest mismatch |
| The frame bound may not fit the stack: the run is on the machine | `build` fails when the bound passes the cap (§3); the binary fails at start-up if it can't reserve the stack |
| A target Cranelift or the runtime doesn't support | `build` fails, naming the target. Supported: `aarch64-apple-darwin`, `x86_64-apple-darwin`, `aarch64-unknown-linux-gnu`, `x86_64-unknown-linux-gnu` (as S5) |
| Manifest or image-hash mismatch at start-up | Unchanged: exit 2, nothing run. The image hash becomes a hash of the object's tables (§5) |

`--verbose` keeps reporting what was compiled. The "ran on the machine"
notes stop existing. There is no `--allow-machine` flag (D1302).

## 5. What leaves the binary, and the size

**Leaves [source]:**
- the machine (`machine.rs`);
- the bytecode compiler (`code::compile`), which the binary runs at start-up
  today to rebuild the image;
- the codec (`codec.rs`, S1);
- the lowered program (`sw_program`).

**Moves into the object**, as read-only data written by `build`:
- the tables native code reads, `Tables`: `shapes`;
- the number tables;
- the operations list;
- a literal table, from which the runtime builds the constant pool's
  values (big numbers, texts, floats) once at start-up, about as much work
  as decoding them;
- arities of globals and lambdas (for `apply`);
- function names (for the depth note);
- the frame limit and step limit.

Today `TableStore::new` builds these from the image **[source]**.

**Measured** (the seeded roguelike, `build --native`, release library;
symbol sizes from `nm` address spacing) **[ran]**:

| Piece | Bytes |
|---|---:|
| `stitchwort_rt::machine` | 73,332 |
| `stitchwort_rt::code` (bytecode compiler) | 39,696 |
| `stitchwort_rt::codec` | 15,076 |
| `sw_program` (the encoded program) | 35,688 |
| compiled program code (241 bodies, adapters, stubs) | 907,968 |
| whole binary, linked / stripped | 2,470,656 / 2,080,208 |
| machine-only binary, linked / stripped | 1,516,640 / 1,137,664 |

**After [inferred].**
- About 164 KB leaves.
- Added: the entry body, about ten runtime bodies (tens of KB, by the size
  of N3's stubs), and the tables (of the order of `sw_program`'s size, which
  they replace).
- So the stripped roguelike goes from 2.08 MB to about 1.9 MB.
- Compiled program code (0.9 MB) is the bulk, and this note doesn't change
  it.

The library splits so the linker can't pull the machine in by accident.
`run.rs` and the effect types move to a crate (or feature) without
`machine.rs`. A test checks with `nm` that a built binary has no
`stitchwort_rt::machine` or `stitchwort_rt::code` symbol.

## 6. Staged plan

Each stage is one lane, with named tests only (test tiers). Until NO5 the
hybrid stays on main, shrinking each stage, so `build --native games/rogue`
keeps playing throughout. Every stage keeps the n1–n4, `s6.rs`, `n2b.rs`
and `crates/cli/tests/build.rs` agreement tests passing: the same output,
effect counts and allocation trace as the machine, at every step and frame
limit the sweeps try.

A counter of nested machine runs is added in NO1, as a debug-build
`NativeRun` field: it counts `machine::nested` calls, so each stage can
show that work left the machine.

**NO1. `Text.fold` and the leaf function values.**
- **What:** `rt_text_fold` as a runtime body, so `sw_fold` goes. The apply
  stubs handle `DoneK`, `StateK`, `JumpK` and `DelayK` with leaf helpers.
  Add the nested-run counter.
- **Done when:** the two `n1.rs` `Text.fold` tests and the `n4.rs` suite
  pass. A recursion through `Text.fold` to the frame limit fails exactly
  where the machine does, with zero nested runs.

**NO1 as built** (26 October 2026). Done as planned, with these
differences from the text above:
- **The counter is in every build, not only debug ones.** The test tiers
  run release binaries, so a debug-only field would be missing exactly
  where the tests read it. It's `NativeRun::nested_runs` (one increment per
  `machine::nested` call), added to a per-thread total when each crossing
  ends (`native_abi::nested_runs()`), and `run --native --verbose` prints
  it as "native: N nested runs of the machine".
- **`Text.fold` as a function value is compiled too.** `sw_apply_prepare`
  plans a `Text.fold` head as `FOLD_CODE`, and the apply stub calls
  `rt_text_fold` with no step or frame of its own, as the machine's
  `enter` runs `fold_start`. So `Text.fold` never runs on the machine, and
  `runs_on_the_machine` (which sets `nests`, and with it `NEST_ROOM` in
  the frame bound) no longer lists it.
- **`rt_text_fold` calls the function directly when it can.** `f` doesn't
  change during a fold, so it's looked up once (`sw_apply_cached`); a
  global function or closure taking two is then called directly, with the
  step and frame counted as `apply2` would, and anything else goes through
  `apply2`. The characters come from one leaf, `sw_text_last`.
- **The leaf function values are made in `sw_apply_prepare`, not
  dispatched in the stub's IR.** The stub's slow path calls
  `sw_apply_prepare` anyway, and it already made `DoneK`'s value; it now
  makes `StateK`'s, `JumpK`'s and `DelayK`'s with the same functions the
  machine's `enter` uses (`machine::done_k`, `state_k`, `jump_k`,
  `delay_k`), so they can't drift.
- **"Joined to its callee's group" needs one more case (§1.4, error
  exits).** If the call fails before its frame is pushed (out of steps or
  frames in `apply2`), the machine's `push` drops the `Ret` at once, and
  no group exists to join. `sw_unwind`'s mode 3 now drops the values at
  once when no frame has left yet, rather than panicking. Before a direct
  call, `rt_text_fold` drops the character, the value so far and `f`, in
  the machine's order.
- **The frame bound adds `rt_text_fold`'s frame** (368 bytes on aarch64)
  to each level when a program uses `Text.fold`: body or adapter, a stub,
  and the fold.

**Nested runs, before and after NO1** (release `run --native`, seeded
roguelike):

| Run | Before | After |
|---|---:|---:|
| roguelike, keys `jjlq` | 78 | 13 |
| roguelike, 27 keys | 216 | 82 |
| `effects.sw`, 1,000 of each | 1,004 | 1,004 |
| `effects.sw`, 1,000,000 of each | 1,000,004 | 1,000,004 |

The roguelike uses no `Text.fold`; its drop is the leaf function values
(`StateK`, `JumpK`, `DelayK`). The effects benchmark's runs are effect
operations, NO2's and NO3's work.

**NO2. The run loop, folds, `translate`, `runPure` and resumptions.**
- **What:** `rt_loop`, `rt_resume`, `sw_resume` and the per-op runtime
  bodies, for `Fold`, `FoldLazy`, `FoldIn`, `Translate` and `RunPure`.
  `TailPrim` of these becomes a `return_call`. Error exits join the callee's
  unwind group.
- **Done when:**
  - every `-- run:` line of `effect-runtime.sw` and `effect-handlers.sw`
    agrees (value, counts, trace);
  - `n4.rs`'s handler sweep at every limit agrees;
  - the 250,000-long effect loops pass under a limit of 100 frames;
  - the nested-run counter is zero on these.

**NO2 as built** (26 October 2026). All four done-when checks hold:
`n4.rs`'s `effect_examples_agree_with_the_machine` (every `-- run:` line of
`effect-runtime.sw`, `effect-handlers.sw` and `effect-state.sw`: value,
counts, trace), `handlers_agree_with_the_machine` and
`handler_traces_are_the_same` (the sweep at every limit),
`effect_loops_run_in_constant_stack` (250,000 each, 100 frames), and zero
nested runs on those loops (250,006 before). Differences from the text
above:
- **No per-op runtime bodies, and no `sw_resume`.** One leaf,
  `sw_eff_begin`, does what the machine's `effect` does for the five ops
  (one shared `machine::handler_for`, so they can't drift): it builds the
  handler and the computation, and `rt_loop` starts on them. A `Prim` of
  one calls `rt_loop`; a `TailPrim` releases the frame and `return_call`s
  it with one fewer frame and the frame's closure, which the loop drops at
  its first call or return, as the machine drops the popped frame. The
  resumption a fold's `call o k` gets is made inside `sw_eff_step`, the
  leaf that takes the computation apart each iteration (it does `eff_run`'s
  and `eff_call`'s clones and drops in their order, and answers again,
  apply, return, done, call or inject).
- **The handler is one word.** Native code holds `Rc<Handler>` as a raw
  pointer, and `pending` as a value in the loop's frame, instead of the
  `EffRet` box.
- **`rt_resume` is reached from the apply stub.** `sw_apply_prepare` plans
  an eager `Resume` as `RESUME_CODE` (when the code has the runtime:
  `Context::resumes`, the manifest's `FLAG_RESUMES`), and the stub calls
  `rt_resume` with the value and the resumption, as a tail call if nothing
  is left over. A lazy one is still a value from the leaf
  (`machine::resume_lazily`, shared with the machine). The stubs gained a
  parameter: a function value to drop once the callee is taken apart, which
  is when the machine drops the resumption it applies (the trace showed the
  difference: dropping it before the `rest` was taken apart moved one
  `dec`).
- **Error exits.** As planned, with NO1's extra case: a call that fails
  gives the loop's handler (`sw_unwind_handler`: kept in the unwind log as a
  resumption that nothing will run, since the log holds values), pending
  list and a `translate`'s `k` to the callee's group, or drops them at once
  if no frame has left. A callee's tail request (an effect native's
  function value, still run by the machine) is performed in the body.
- **The manifest has `flags`** (version 3): `FLAG_NESTS`, which was
  `nests`, and `FLAG_RESUMES`.
- **The frame bound.** Between two counted frames there can now be the loop
  or `rt_resume` and a second stub (a stub applying a resumption with
  arguments left over calls `rt_resume`, which applies the rest through
  another). The bound adds the larger of the two bodies and a stub, in
  place of the fold if that is larger. The loop and `rt_resume` together
  are on the stack only when a `bind`'s continuation is itself a
  resumption; the stack check behind the frame limit still stops that
  cleanly. On the roguelike, frames went from 2,760 to 4,272 bytes. With
  `NEST_ROOM` (still added, since `nests` remains for state handlers and
  effect natives' function values) that is 8,368 bytes for each of the
  2,000,000 frames, within 3% of the 16 GiB stack, so a little more would
  make `fits` refuse and the whole run fall back to the machine (as a
  first version did, at 4,800 bytes). NO5 removes `NEST_ROOM`.
- **Which runs nest.** `runs_on_the_machine` now lists only `FoldState`,
  `FoldStateComp` and effect natives' function values. The roguelike's and
  the benchmark's handlers are all folds (`Counter.from` has an open row,
  so it isn't a state loop), so they now nest nothing.

**Nested runs, before and after NO2** (release `run --native`, the seeded
roguelike as for NO1):

| Run | Before | After |
|---|---:|---:|
| roguelike, keys `jjlq` | 13 | 0 |
| roguelike, 27 keys | 74 | 0 |
| `effects.sw`, 1,000 of each | 1,004 | 0 |
| `effects.sw`, 1,000,000 of each | 1,000,004 | 0 |
| `n4.rs`'s effect loops | 250,006 | 0 |

**Instructions per operation** (best of 3, a run less the same run with no
operations, release build, aarch64 macOS):

| Benchmark | Machine | Native before NO2 | Native after NO2 |
|---|---:|---:|---:|
| `effects.sw`, 1,000,000 of each | 22,460 | 19,946 | 19,734 |
| `ask` alone, open row (`{IO}`) | 18,195 | 16,871 | 16,696 |
| `bump` alone, open row (`{IO}`) | 26,732 | 23,031 | 22,775 |
| `ask` alone, closed row | 12,985 | 11,772 | 9,359 |

The benchmark barely moves, and that's not the loop's cost. Its handlers
have an open row (`{e}`, here `{IO}`), so their resumptions are lazy: the
clause's `k v` gives back a `Bind (Done v) k′` cell, and the computation is
run by the loop of whatever handles `e`, which is the runner's, on the
machine, at the top (not a nested run). A `sample` of a 5,000,000-`ask` run
shows `Machine::finish` → `machine::run` → `eff_run` → `apply` → `enter` →
`cross` into native code for each operation. With a closed row
(`Env.give: (prog: () → {Env} a): a`), where the fold resumes eagerly and
`rt_loop` runs everything, an `ask` costs 20% less than before NO2 and 28%
less than on the machine. The open-row figure moves at NO4, when the runner
runs on an executor; §1.6's estimate is for then.

**NO3. State-passing handlers.**
- **What:** `FoldState`, `FoldStateComp`, `StateRun` and the jump test.
  `sw_effect`, `sw_tail_effect`, `sw_perform` and `TailRequest` lose their
  last users and are deleted.
- **Done when:** every `-- run:` line of `effect-state.sw` agrees, the
  nested-run counter is zero on the whole `n4.rs` suite and on the roguelike,
  and the effects benchmark is measured against §1.6 (instructions per
  operation, recorded in this note).

**NO3 as built** (26 October 2026). All three done-when checks hold:
`n4.rs`'s `effect_examples_agree_with_the_machine` (every `-- run:` line of
`effect-state.sw`, with the other two examples: value, counts, trace); zero
nested runs on every native run of the `n4.rs` suite (checked in
`common::native_on`, which all of n1–n4 use, and around each example's
native run); and on the roguelike, by a new guard test
(`build.rs`'s `the_roguelike_runs_natively`: `run --native --verbose` says
no part ran on the machine and `0 nested runs`, and `build --native
--verbose` doesn't say the executable will fall back). `sw_effect`,
`sw_tail_effect`, `sw_perform`, `TailRequest` and `NativeOut` are deleted.
Differences from the text above:
- **A state-passing fold is a leaf, not a runtime body.** Its value is a
  function of the state (a `StateRun`), so making it needs no loop:
  `sw_eff_state` does what the machine's `effect` does for `FoldState` and
  `FoldStateComp` (one shared `machine::state_handler`). The loop starts
  when that function is applied: `sw_apply_prepare` plans a `StateRun` like
  an eager `Resume` (`RESUME_CODE`), and `rt_resume` (mode 2) runs the rest
  of the computation in `rt_loop` with the state in a loop variable.
  `sw_eff_step` answers two more cases for a state loop, done (`STEP_STATE_DONE`)
  and an operation (`STEP_STATE_CALL`, which makes `k` and the jump), and
  `sw_state_step` is the jump test (one shared `machine::state_step`,
  which the machine's `State::state_step` now calls too). A recorded jump
  goes round the loop; anything else is the result.
- **No tail requests remain**, so the apply stubs lost their `tail`
  parameter, and `NativeIslands::call` returns the value. What native code
  still can't run (a body that isn't compiled: none today) is a nested run.
- **The frame bound.** `Plan::nests` is now "some body `main` reaches isn't
  compiled", false for every program today, so `NEST_ROOM` is no longer
  added: NO5's removal is brought forward in effect (the constant and
  `level_bound` stay for that case until NO5 deletes them). The loop's
  frame grew by the state's slots. On the roguelike, frames went from 4,272
  bytes (8,368 with `NEST_ROOM`) to 4,520 bytes; 2,000,000 frames are 9.0
  GB of the 17.2 GB above the floor, against 16.7 GB before.
- **The `-- run:` lines don't reach the native fold.** Each is lowered as an
  entry, and the entry inlines the call that holds the fold (`tallied
  codes` and the rest), so the fold runs on the machine until NO4 compiles
  the entry; only the resumptions they apply reach native code
  (`sw_state_step`, 75 calls under lldb, `sw_eff_state` none). A new test,
  `state_handlers_in_compiled_bodies_agree`, puts both folds in recursive
  functions (not inlined), as a `Prim` and a `TailPrim`, with tail,
  non-tail and stored resumptions, and checks output, trace and every
  limit (`sw_eff_state` 424 calls, `sw_state_step` 1,961).
  `effect_loops_run_in_constant_stack` gained a closed-row counter.
- **`build --native --verbose`** says when the executable will run
  everything on the machine (the crossing's own rule, from the frame bound
  and the frame limit), so the guard can check the binary too.

**Instructions per operation** (as for NO2: best of 3, a run less the same
run with no operations, 1,000,000 operations, release build of `stitchwort`
alone, aarch64 macOS; main is the commit before NO3, measured the same
day). The closed-row rows call the handler from a recursive function, so
its fold is in a compiled body; `bump` there is the state loop
(`Counter.run: (prog: () → {Counter} a): Nat → a`, and the `let run` form
of `effects.sw` at a closed row, which fuses the same way, within 0.5%).

| Benchmark | Machine | Native, main | Native, NO3 |
|---|---:|---:|---:|
| `effects.sw`, 1,000,000 of each | 22,642 | 19,719 | 19,253 |
| `ask` alone, open row (`{IO}`) | 18,273 | 16,588 | 16,202 |
| `bump` alone, open row (`{IO}`) | 26,916 | 22,657 | 22,108 |
| `ask` alone, closed row | 13,012 | 9,336 | 9,500 |
| `bump` alone, closed row (a state loop) | 17,271 | 15,801 | 12,239 |

The state loop costs 23% less than before NO3 (when the machine ran the
whole loop in one nested run) and 29% less than on the machine. Against
§1.6's estimate of 11,000–15,000: the closed-row state loop is inside it;
the benchmark (open rows) is not, and won't be until NO4, for NO2's reason
(the runner drives lazy resumptions on the machine). The closed-row `ask`
is 1.8% above main (the loop's larger frame and the state's slots, carried
on every iteration). D1297's check ("still above about 12,000 … and the
profile shows allocation") can't be settled yet: the only native-only
figure at or near it is the state loop's 12,239, and `sample` couldn't
attach to the process in this environment, so there is no profile; it
waits for NO4's open-row figures.

**NO4. The entry and the runner on an executor.**
- **What:** compile the entry body. Add the `Executor` trait (§2), with
  `Machine` and the native executor implementing it. Move the constants
  cache to the native context. `machine::nested` and `Work` lose their
  last users and are deleted.
- **Done when:** `run --native --verbose` reports 242 of 242 bodies for the
  roguelike, and a debug counter of machine instructions executed under
  `run --native` is 0 for the roguelike, AoC days 1–9 and the benchmarks.

**NO4 as built** (26 October 2026). Both done-when checks hold. `run
--native --verbose` on the roguelike (27 keys, seeded) says `running 242 of
the 242 bodies main reaches natively` and `the machine executed 0
instructions`. The same holds for AoC days 1–9 on their inputs (56 to 105
bodies each, output equal to `run`'s) and the five `bench/native` programs
(2 to 43 bodies). `common::native_on` asserts 0 machine instructions on
every native run of n1–n4, and `the_roguelike_runs_natively` checks the
line. `Runner` is generic over `run::Executor`, which `Machine` and
`native_abi::NativeExecutor` implement. The executor owns the constants
cache (`NativeRun::globals`). The machine lost all its native support:
`native`, `cross`, `nested`, `Work`, `defer`, `Unwound` and the native
checks in its loop. Differences from the text above:
- **All or nothing, now.** `plan` compiles the entry with the rest. If any
  body `main` reaches doesn't compile, nothing does, and the whole run is
  the machine's (`Plan::nests` is always false; NO5 deletes it with
  `NEST_ROOM`). A function value whose body isn't compiled is an internal
  error in `sw_apply_prepare`.
- **Three trampolines replace the per-arity ones.** `enter` (the entry,
  counting its step and frame as `Machine::entry` does), `apply1`/`apply2`
  (the apply stubs, for `call`) and `step` (`rt_loop` with `Handler::Step`,
  for `step_comp`). They are exported as `sw_cross_enter` and the others.
  The object's manifest is version 4: the four pointers replace the
  trampoline list. A program with no compiled code now has one (`hello`
  compiles its entry).
- **The counter counts instructions, not nested runs.**
  `machine::instructions_executed` is a per-thread total that every
  machine run adds to as it ends. It is in every build, since the test
  tiers run release binaries. The machine's own figures are about 2% below
  NO3's (below), since the native checks left its loop, so the counter
  costs at most that.
- **A drop-order bug the entry exposed.** With the entry compiled, the
  `-- run:` lines' folds run natively for the first time (NO3's last
  bullet). `effect-runtime.sw`'s `searchedIn [1, 2, 3]` (an open-row
  `collectIn` whose clause applies a lazy resumption twice) then made a
  different allocation trace: native code dropped a resumption's function
  value before the `rest` inside it was taken apart, and the machine drops
  it after. The machine's `apply`s nest in Rust, so the outer one drops its
  function value when the inner ones return. The apply stub now puts that
  function value off (`sw_defer_fun`) when it resumes, and compiled code
  drops what was put off (`sw_drop_deferred`, behind a context counter)
  right after the next function value it was given to drop. A run that
  fails drops anything still put off.

**Instructions per operation** (as for NO3: best of 3, a run less the same
run with no operations, 1,000,000 operations, release `stitchwort` alone,
aarch64 macOS; `effects.sw` per operation of either kind):

| Benchmark | Machine | Native, NO3 | Native, NO4 |
|---|---:|---:|---:|
| `effects.sw`, 1,000,000 of each | 22,200 | 19,253 | 15,488 |
| `ask` alone, open row (`{IO}`) | 17,929 | 16,202 | 13,312 |
| `bump` alone, open row (`{IO}`) | 26,456 | 22,108 | 17,677 |
| `ask` alone, closed row | 12,753 | 9,500 | 9,510 |
| `bump` alone, closed row (a state loop) | 16,951 | 12,239 | 12,240 |

The open rows improved, as expected: by 18% (`ask`) and 20% (`bump`), now
that the runner's lazy resumptions run natively. The benchmark is 20% below
NO3 and 30% below the machine. Against §1.6's estimate of 11,000–15,000 it
is just above (15,488). The closed rows didn't change: nothing there was on
the machine after NO3.

**Profile** (`sample` this time attached to a child launched from a script:
`run --native` of `effects.sw` at 3,000,000 each, 3 s, 2,531 samples on the
run thread, by function on top of the stack; functions with fewer than 5
samples aren't itemised by `sample`):

| | Share |
|---|---:|
| the allocator (mimalloc, `Rc` and `Vec` allocation) | 24.7% |
| dropping and freeing values (`value::free`, `take_children`, drop glue) | 24.0% |
| `sw_*` helpers (`sw_apply_prepare` 8.8%, `sw_eff_step` 5.3%, the rest 6.1%) | 20.2% |
| compiled code (at least) | 6.5% |
| machine helpers native code shares (`pair`, `field`, `arity`) | 4.7% |
| `memmove`, other | 2.5% |
| functions under 5 samples each (mostly compiled code's addresses) | 17.5% |

Against NO3's profile, the machine's 36.7% is gone. Allocation and freeing
together are 48.7% (48.9% in §1.6's profile, of a larger total). Dispatch
(the apply stub's plan and the loop's step) is 14%. So D1297's overturn
condition holds: the benchmark is above about 12,000 instructions per
operation, and allocation, not dispatch, dominates. Whether to change the
representation now (§1.5, §9.11 B) goes to Matt.

**NO5. Native only: no fallback, in `run --native` and `build`.**
- **What:** the build errors of §4, and §3's stack sizing and cap.
  `Crossing::fits` and the fallback paths go, as does `NEST_ROOM`. The
  deepest-function note comes from the unwind.
- **Done when:** tests show that:
  - a program over the cap fails to build with the message;
  - a deep recursion gives the machine's `E-RESOURCE` and note, both from
    `run --native` and from the binary;
  - a failed layout probe (forced by a test hook) fails the build.

**NO5 as built** (26 October 2026). All three done-when checks hold, in
`crates/cli/tests/build.rs`:
- `a_program_over_the_stack_cap_fails_to_build`: a recursive function of
  400 arguments, each live across its call. `build --native` and `run
  --native` both exit 1 with nothing written or run:

  ```
  error: the native stack would be too big: 2000000 frames (the frame limit) of up to 77392 bytes (`Main.wide`'s, the widest) need 144.2 GiB, over the cap of 64 GiB
    note: split `Main.wide` into smaller functions, or run the program on the machine with `stitchwort run`
  ```
  `run` (the machine) prints its answer.
- `native_code_out_of_frames_reports_as_run_does`: `count (5 * 1000 *
  1000)`, built `--native`, and under `run --native` and `run`: the same
  `E-RESOURCE`, status 2, and the same note, `the recursion was deepest in
  `Main.count` (1999999 frames pending)`, from all three.
- `a_failed_layout_probe_fails_the_build`: with
  `STITCHWORT_TEST_LAYOUT_PROBE_FAILS` set, `build --native` and `run
  --native` exit 1 with `error: the layout of values isn't as native code
  expects: forced by STITCHWORT_TEST_LAYOUT_PROBE_FAILS`; an executable
  built without it, started with it, exits 2 with `internal error: this
  executable can't run: …` and runs nothing.

`Crossing::fits`, `NativeIslands::fits`, `NEST_ROOM`, `level_bound`,
`level`, `Plan::nests`, `FLAG_NESTS`, the "ran on the machine" notes, the
factory `run_main_native` took (`NativeFactory`, `n1::factory`) and
`Options::stack_size` (the stack check is always compiled now) are
deleted. `run_main_native` takes the compiled code and the stack, and
callers compile first, so a refusal is an error before anything runs. The
plan no longer drops a body's callers when the body can't be compiled: any
such body refuses the program, naming each one ("`Main.f` uses `X`, which
the native compiler doesn't compile yet"). Differences from the text above
and §3–§4:
- **No `frames` limit to suggest.** §3's message was to suggest a smaller
  `frames` limit, but a program can't set one: `Limits::for_stack` fixes it
  at 2,000,000 and nothing (project file, flag) changes it. So the message
  names the limit and the widest function, and suggests splitting that
  function or running on the machine.
- **The roguelike's stack is 9.1 GB, not 6–7 GB.** §3's estimate used the
  frame bound before NO2 (2,760 bytes plus a runtime frame); with the
  effect runtime's bodies it is 4,536 bytes, so 2,000,000 frames and the
  rooms are 9,089,056,768 bytes (8,668 MiB), 13% of the cap.
  The guard test prints it.
- **Where the stack is sized.** `native_abi::native_stack` is the rule:
  the frame limit plus one, times the frame bound, plus `HOST_ROOM` and
  `HELPER_ROOM`, rounded up to a MiB; `n1::stack_for` turns it into the
  error. `build` writes it to the manifest (version 5: a `stack_size`
  word; `FLAG_RESUMES` is now bit 0), and the binary starts its run
  thread with exactly that, or says `error: this executable can't reserve
  its stack of N bytes: …` and exits 2. An executable built without
  `--native` runs the machine on 64 MiB, as `run` does (it had the 16 GiB
  native stack). `run --native` compiles and runs on the thread the CLI
  starts before the frame bound is known (moving the JIT's code, the
  program and the terminal to a second thread would mean making them
  `Send`), so that thread reserves the cap itself (`stitchwort_host::NATIVE_STACK`, now 64 GiB of address space),
  and the run's stack-pointer floor is placed by the sized stack, as in the
  binary, so the two stop at the same point.
- **The floor moved to the executor.** `NativeExecutor::new` takes the
  stack size and fixes the floor at its first crossing; the `Crossing` no
  longer knows its stack.
- **The depth note.** `sw_unwind` has a fifth argument, the leaving
  frame's body number (mode 2, one per counted frame), and the executor
  counts them with the machine's own `machine::deepest` and names them with
  `machine::depth_report`, now free functions both share. Function names
  come from the image the binary still rebuilds; NO6 moves them into the
  object (§5).
- **The backstop test.** `n2b`'s
  `a_stack_too_small_for_the_limit_stops_cleanly_at_the_stack_check`
  replaces the fallback test: given a stack a tenth of what the run needs,
  the stack-pointer check stops it with `RunError::Deep` and the note
  (`Main.deep`), not a crash.
- **The unsupported-target error** is a check against the four targets of
  §4 (`n1::check_target`), run before the layout probe; it can't fire on a
  machine the workspace builds for today, so no test forces it.
- **The guard test.** `the_roguelike_runs_natively` keeps its `run --native
  --verbose` checks (every body natively, 0 machine instructions) and now
  checks that the sized stack is under half the cap and that `build
  --native --verbose` reports that stack; its "fell back" checks went with
  the fallback.

**NO6. The binary without the machine.**
- **What:** `build` writes the tables and literals (§5). The runtime library
  builds `Tables` from them, with no `Program`, image or codec. The library
  is split so that `machine`, `code` and `codec` aren't linked.
- **Done when:** the roguelike's binary plays (the piped play-through equals
  `run`; the pseudo-terminal test passes); `nm` shows none of those modules;
  the size and the time per key are recorded against S5's table.

**NO6 as built** (26 October 2026). All three done-when checks hold, in
`crates/cli/tests/build.rs`'s `the_roguelike_built_native_plays_as_it_does_under_run`:
the seeded roguelike's `--native` binary plays (the piped game equals
`run`'s, and the pseudo-terminal test, now shared with the machine-only
test, passes on it), and `nm -C` finds no symbol of `stitchwort_rt::machine`,
`code` or `codec` in it. The machine-only binary's test checks the
opposite (the machine's symbols are there), so the check can see them.
What was built:
- **The tables and literals** are `stitchwort_rt::linked` (D1300): `build
  --native` writes `linked::encode`'s bytes into the object as `sw_tables`,
  in place of the encoded program. They hold the limits, `main`'s row, the
  shapes, each global's kind and body number (with its name, for a global
  with a body: the depth note's), each lambda's parameters, the entry's
  body number, the operations and number tables in `Numbering`'s order, and
  the constant pool. For the roguelike they are 12,050 bytes, where the
  encoded program was 35,688.
- **The runtime builds `Tables` from them** (`linked::decode`, then
  `TableStore::from_parts`), with no `Program`, image or codec. What the
  runtime around native code needs to know of the program is an `Outline`
  (shapes, `main`'s row, the globals' kinds, the lambdas' parameters, the
  bodies' names), which `NativeExecutor` now holds in place of the program
  and image. `run --native` makes its `Outline` from the program and image
  (`Outline::of`), so both paths run the same executor. The `Executor`
  trait's `program()` became `shapes()` and `main_row()`.
- **What the machine and native code share left `machine.rs`**: the
  limits, `NumTable`, `arity` (over an `Arities` trait both `Program` and
  `Outline` implement), `deepest` and the depth note are in `shared.rs`;
  the effect runtime's leaves (`handler_for`, `state_step`, `done_k` and
  the rest) are at the end of `effect.rs`. The small ones are `#[inline]`:
  without it, the machine-only roguelike ran 4% more instructions, since
  they were no longer in the machine's codegen unit.
- **The codec stays out (D1300 holds).** The bytes share only the codec's
  LEB128 integers, strings, operation tags and shapes, which moved to
  `wire.rs` (about 7 KB of code); the pool is written as its values' nodes
  in post-order and read with a stack, so a long `Chars` literal's list
  needs no recursion.
- **The manifest is version 6**: `run`, `data` and `data_len` replace the
  image's hash (there is no image to check). `run` is the address of the
  library's `sw_run_native` or `sw_run_machine`, written by the compiler as
  a relocation; `data` is the tables or the encoded program. The runtime
  checks instead that the tables were written by the same build of the
  runtime (the codec's build hash) and that their counts of globals and
  lambdas are the code's; tests in `crates/standalone/src/aot/tests.rs`.

Differences from the text above (§5):
- **The split is by entry point, not by crate or feature.** §5 has
  `run.rs` and the effect types move to a crate or feature without
  `machine.rs`. A feature doesn't work in this workspace: cargo builds the
  runtime library in the same build as the CLI, which needs the machine,
  and unifies features, so the library would get the machine anyway. A
  crate split would move about ten modules (values, IR types, natives, the
  runner, the effect runtime) for the same result. Instead C `main` refers
  to neither way of running: it calls the one the object's manifest names,
  and the linker's dead-stripping (`-dead_strip`, `--gc-sections`, already
  on) drops the other. The `nm` test is the guard §5 asked for. It works
  both ways: a machine-only binary now links no native code's runtime
  either (1,154,480 to 1,086,704 bytes stripped).
- **`nm` shows the machine's types in a few names.** LLVM merges identical
  instantiations of generic code under one of their names, so a closure of
  `Runner<NativeExecutor>` can be listed as `Runner<Machine>`'s, and a
  `RawVec` method under `code::Slots`; none of these is the machine's own
  code. The test counts the symbols the modules define (functions and their
  types' methods), not generics merely given one of their types.
- **More left than §5 estimated**: 233 KB stripped (2,080,640 to 1,847,456
  bytes), not 164 KB. Besides the machine (51 KB of symbols by `nm`
  spacing), the bytecode compiler (31 KB), the codec (15 KB), the program's
  validator (3 KB) and the encoded program less the tables (24 KB), the
  runner's instantiation for the machine went (`run`'s symbols, 51 to
  27 KB), with the standard library code only that path used.
- **`run --native` still reserves the full 64 GiB** on the CLI thread (NO5's
  note): NO6 doesn't change when the frame bound is known there.

**Measured** (the seeded roguelike, a 500-key piped game of 396,274
bytes of output, identical for both binaries and `run`; release build,
Apple M4 Pro, load 10–25; best of 3; `/usr/bin/time -l`). "Before" is
main at NO5, measured the same day with the same keys; S5's table (after
N4) used other keys, so its times aren't comparable, only its sizes.

| Binary | Wall | Cycles | Instructions | Size (stripped) | Build |
|---|---|---|---|---|---|
| `--native`, NO6 | 0.10 s | 0.40 G | 2.29 G | 2,196,880 (1,847,456) | 1.29 s |
| `--native`, before | 0.11 s | 0.43 G | 2.29 G | 2,469,984 (2,080,640) | 1.45 s |
| machine only, NO6 | 0.28 s | 1.09 G | 5.56 G | 1,447,152 (1,086,704) | 0.43 s |
| machine only, before | 0.27 s | 1.07 G | 5.58 G | 1,531,152 (1,154,480) | 0.46 s |
| S5: `--native` | 0.12 s | 0.50 G | 2.81 G | 2,468,320 (2,080,080) | 1.09 s |
| S5: machine only | 0.34 s | 1.36 G | 6.90 G | 1,497,800 (1,121,024) | 0.90 s |

A key costs 0.20 ms natively against 0.56 ms on the machine (wall; 0.81 M
against 2.18 M cycles). The native binary runs about the same instructions
(2.291 G against 2.295 G, best of 3): start-up no longer decodes the
program and compiles its image, but the game itself runs the same code. It
is 11% smaller.

**NO7. Linux and the record.**
- **What:** run NO5's and NO6's tests on Linux x86-64 (§3's open question),
  and update this note and standalone-executables.md (D1287 superseded).
- **Done when:** both pass there, or the Linux stack question goes to Matt
  with measurements.

**How `run --native` relates.** It goes native-only too, at NO5, in the
same change as `build` (D1301). It uses the same `plan`, runtime bodies and
executor, with the JIT in place of the object, so it tests exactly what
`build` ships. The machine stays in the compiler as `stitchwort run`:
- the reference that the agreement tests compare with;
- the runner of the playground (wasm), which has no native code;
- the way to run a program while a native bug is being found.

A hybrid `run --native` would be a third execution model to keep correct,
with no user.

## Decisions

All are **decided by Claude, provisional** (the native track has no review
stops). Each is one thing, with what would overturn it.

**D1296. Where does the native effect runtime live?** **In runtime bodies:
Cranelift IR emitted by the compiler, in the `tail` calling convention.
Rust keeps only leaf helpers that never call program code.**
- **Why:**
  - tail positions stay tail calls (`return_call`);
  - no Rust frames nest between program frames, so `NEST_ROOM` goes;
  - N3's apply stubs already work this way.
- **Overturn if:**
  - Rust's `become` becomes stable (then a Rust runtime with guaranteed
    tail calls is simpler to write and review); or
  - the IR builders for the runtime pass about 3,000 lines while a Rust
    version with measured stack use would be under half that.

**D1297. Which representation?** **The machine's, exactly: `Bind` nodes,
the persistent pending list, `Resume`, `StateRun`. Not fibers, segmented
stacks, CPS or evidence passing.**
- **Why:**
  - agreement with the machine (output, effect counts, allocation trace)
    holds by construction;
  - multi-shot and reentrant resumptions stay free;
  - fibers are one-shot (OCaml 5, WasmFX), and Effekt's copying isn't
    reentrant.
- **Overturn if:** after NO3 the effects benchmark is still above about
  12,000 instructions per operation and the profile shows allocation, not
  dispatch, dominating. Then change the representation in both runners
  together (§1.5), starting with §9.11 B.

**D1298. What counts as "no interpreter"?** **No bytecode, no image and no
`Machine` in the binary: every body of the program is machine code. The
Rust `IO` runner, which steps the `Delay` value `main` returns and calls
compiled code for every function, stays.**
- **Why:** it runs no program code. It is the runtime's top-level driver,
  as in OCaml's or Haskell's runtime. Compiling it would be a second large
  project with no measured benefit: the roguelike is bound by its input.
- **Overturn if:** Matt counts the `Delay` runner as an interpreter, or a
  profile of a partial-heavy program shows the runner's own stepping as most
  of its time.

**D1299. How does a deep recursion fail?** **At the frame counter, as on
the machine, on a stack the build sizes so that the counter always fires
first. The stack-pointer check stays as a backstop with the same clean
error. The build fails if the bound passes 64 GiB; the binary fails at
start-up if it can't reserve its stack.**
- **Why:** it is today's mechanism without the fallback; it agrees with
  the machine exactly; it costs nothing new.
- **Overturn if:** Linux (NO7) won't reserve stacks of this size. Then use
  a guard page with a clean report, over a smaller stack and a lower default
  frame limit, which is a `Limits` change for Matt.

**D1300. What replaces the lowered program in the binary?** **Tables and a
literal table written into the object by `build`; the constant pool is
built from the literals at start-up. No codec, no bytecode compiler.**
- **Why:** native code needs only these. Everything else the binary
  carries today exists to rebuild the image for the machine.
- **Overturn if:** the literal table needs most of the codec's cases anyway.
  Then keep the codec for the constant pool alone, still with no program and
  no bytecode compiler.

**D1301. What becomes of `run --native`?** **Native only, from NO5, the
same as `build`. `run` (the machine) stays as the reference and the
development fallback.**
- **Why:** it then tests what `build` ships, and there is one native
  execution model.
- **Overturn if:** a native-only `run --native` can't run something the
  tests or AoC need for more than one stage. Then that is a bug to fix, not
  a mode to keep.

**D1302. An escape hatch?** **None: no `--allow-machine` or similar flag on
`build` or `run --native`.**
- **Why:** D1294. And `stitchwort run` already is the way to run a program
  on the machine.
- **Overturn if:** Matt asks for one.

**D1303. When does fallback end?** **At NO5, for `build` and
`run --native` together, not earlier.**
- **Why:** until NO4 the roguelike needs the machine for its effects, so
  refusing earlier would break the M2 milestone's test for several stages
  and gain nothing; the hybrid on main only shrinks meanwhile.
- **Overturn if:** Matt wants `build --native` to refuse now, accepting a
  roguelike that doesn't build natively until NO4.
