# Perceus-style in-place reuse: what the runtimes do, what's left, and in what order

SW-1159, for Matt's D2270/D2271 ("a really promising direction to explore"). Survey of
3 Nov 2026 on `main` at `f6af2665`. No code changed. One temporary edit, reverted, is
described in §2.1. The measurements are allocation traces of release builds on the Apple
M4 Pro, taken with a load average of 75–114 (other lanes running). They count events, so
the load doesn't affect them. No times were taken.

Labels as in the rest of `docs/research/`: **[checked]** read in the code or the source
named, **[ran]** measured for this note, **[cited]** read in a fetched web page,
**[inferred]** my reasoning, untested.

**Result in one paragraph.** Stitchwort already has most of Perceus. The bytecode
compiler (`crates/rt/src/code.rs`) moves every value on its last use, drops dead
variables as each branch starts, and refills a unique cell it has just taken apart with
the next constructor of the same arity (`Unpack`, `DropReuse`, `CtorReuse`). Native code
and standalone binaries carry out the same decisions instruction by instruction. So the
question isn't whether to adopt Perceus. It is how to widen what we already have, and the
traces show where it falls short:
1. Reuse stops at function boundaries. A tree insert whose rebuilding is done by a
   helper reuses no path nodes: on `Set.fromList` of 1,000 keys, 11.7% of cells are
   reused. The same insert written with the constructor in the arm reuses 93% of its
   tree nodes.
2. Read-only calls cost an increment and a decrement each. `Map.Tree.balance` passes
   both subtrees to `shape` before rebuilding, which is about 2 increments per level.
3. On the effects benchmark, the effect runtime's own nodes and closures are most of the
   allocation, and a compiler pass doesn't reach them.

**Recommendation:** extend the existing design in stages, starting with a per-site reuse
report (half a lane-day). It is both the measurement and the diagnostic for accidental
sharing. Then add reuse across small helpers, hand reuse in the effect runtime (after
SW-593's decision), and borrowed parameters only if the report shows the increments
matter. D2273–D2277 are in §7.

## 1. Today

### 1.1 Values, counts and freeing in each runtime

| Runtime | Values | Counting | Reuse |
|---|---|---|---|
| Reference evaluator (`crates/core` `value.rs`, `run --reference`) | the checker's NbE values, `Rc`-shared fields ("Fields are shared, so copying a value … is cheap") | Rust `Rc`, scope-based (dropped when a Rust binding goes) | none, and none wanted: it is the oracle for the differential tests **[checked]** |
| Machine (`crates/rt`: `value.rs`, `code.rs`, `machine.rs`) | `Value`: 3 words, `repr(u8)`. Small numbers inline. A constructor with fields is `Data(tag, Fields(Rc<[Value]>))`, one allocation per cell. Closures are `Rc<Fun>` with `Box<[Value]>` captures (2 allocations). `Text` is `Rc<str>`. `Delay` and effect values are their own `Rc`s | exact `Rc` counts, changed at once (no deferral). Freeing never recurses: `take_children` and a work list (`value.rs` "freeing") **[checked]** | moves, early drops, `Unpack`/`DropReuse`/`CtorReuse` (below) |
| Native (`crates/native` `n1.rs`, JIT and AOT; `crates/standalone`) | the machine's values, same layout (`native_abi::probe_layout`) | "Clones and drops are inline (an increment, or a decrement unless the count is 1, when the runtime frees the value), as are the unique-cell paths of `Unpack` and `CtorReuse`" (`n1.rs` header) **[checked]** | the same decisions: "every move, clone and drop is the bytecode's" (`n1.rs`) **[checked]** |
| JS (`crates/js`) | `{ tag, …fields }` objects, `bigint` numbers (docs/core.md) | the JS engine's tracing GC | nothing to reuse: no counts, so no uniqueness test. The JS backend doesn't use the rt IR, so no change here affects it **[checked]** |

### 1.2 Where increments, drops and reuse happen

All of this is decided once, in `code.rs`, from liveness over the erased IR (`uses`,
computed once per body) **[checked]**:

- **Moves.** An operand read for the last time carries the `MOVE` bit and is taken out
  of its register. Any other read is a clone, which is an increment. A call's
  arguments are always owned: moved or cloned. No user function has borrowed
  parameters. Some `native_abi` helpers take arguments borrowed, but that is a
  convention of the runtime's helpers (compilation.md, C3 audit) **[checked]**.
- **Drops.** Variables that a branch doesn't need are dropped as the branch starts
  (`branch`, `Instr::Drop`). A parameter or `let` that is never read isn't dropped
  early. It goes when the frame returns or tail-calls (`body` drops nothing at entry).
  So the machine is garbage-free in Perceus's sense only up to unused bindings, which
  the simplifier mostly removes **[checked; how often it matters, inferred]**.
- **Reuse.** A `match` whose scrutinee is dead in the arm compiles to `Unpack`. If the
  cell is unique, its fields are moved out (no increments, the equivalent of Perceus's
  drop specialisation). If the arm builds a constructor of the same arity
  (`builds(body, n) > 0`), the emptied cell is kept as a token, and the first such
  constructor claims it (`CtorReuse`). A variable known to be a constructor from an
  enclosing match is dropped into a token as the branch starts (`DropReuse`). The
  uniqueness test is dynamic (`strong_count == 1 && weak_count == 0`): "A shared cell
  is never changed: its fields are copied and it's left alone" **[checked]**.
  - Any tag can reuse the cell, as long as the arity matches.
  - A token can't cross a call: `builds` counts only the constructors in the arm itself.
  - Tokens exist only for `Fields` cells. Closures, `Delay`s, resumptions, `Text` and big
    numbers are never reused.
  - A token no path claims holds an emptied cell (no children) until its register is
    overwritten or the frame ends. That is bounded by the frame, which is the property
    Lorenzen and Leijen ask for (compilation.md C4) **[inferred]**.
- **Hand-written in-place updates elsewhere** **[checked]**:
  - TRMC's destination cells: `prims::fill`, `unsafe`, justified as `Rc::get_mut_unchecked`'s
    rule and checked under Miri.
  - The effect runtime takes a unique `Resume` or state function apart in place
    (`effect.rs` `Rc::get_mut`/`try_unwrap` at 281, 363, 371, 398, 407), and so does
    `run.rs:940`.
  - Shared ASCII character cells: `TextToList` and friends give out one cell per
    character, which is safe because a shared cell is never changed (fast-runtime.md
    stage 4).
  - `Text.append` always copies (`prims.rs` `TextAppend`), and nothing appends in place
    to a unique `Text`.

Stage 4 measured what this bought (fast-runtime.md, "As built (stage 4)") **[checked]**:
moves and reuse took the merge sort from 0.435 s to 0.371 s, and "allocation has all but
gone from its profile … each cell `merge` builds reuses one it took apart".

### 1.3 The literature, against this

Checked for this note:
- The Perceus technical report: Reinking, Xie, de Moura, Leijen, MSR-TR-2020-42, the
  report version of the PLDI 2021 paper. I read the text extracted from the PDF.
- Lean's `dbgTraceIfShared`: the Lean reference manual.

Ullrich and de Moura (IFL 2019), Lorenzen and Leijen (ICFP 2022) and Lorenzen, Leijen
and Swierstra (FP², ICFP 2023) were read in full for compilation.md (cards C1, C4 and C5,
audited 30 Oct). I use those cards and didn't reread the papers.

| Perceus / Lean piece | Stitchwort today |
|---|---|
| Precise dup/drop insertion: "an object is freed as soon as no more references remain" (Perceus §2.2) **[checked]** | yes, except never-read bindings, which go at frame end (§1.2) |
| Drop specialisation, "only … if the children are used" (§2.3) | `Unpack`'s unique path moves the fields out. A drop that isn't a match goes through the generic `Drop` work list |
| Reset/reuse, drop-reuse (§2.4; Lean's reset/reuse, C1) | `Unpack`/`DropReuse` tokens, `CtorReuse`; same arity, inside one body |
| Reuse specialisation: skip writing unchanged fields (§2.5) | not done: `CtorReuse` writes every field |
| Borrowed parameters (Lean infers them, C1 §5.2. Koka declined inference because it "is not safe for space", C4 §4.2) | none for user code |
| FBIP, "functional but in place" (Perceus §2.6; FP²'s `fip` check, C5) | no check and no report |
| Thread-shared flag (Perceus §2.7.2) | not needed: a run is one thread (`Rc`, not `Arc`) |

Perceus's own evidence: on rbtree, Koka is "within 10% of … std::map" in C++, and the
version without reuse and drop specialisation "is more than 2× slower". "In benchmarks
with lots of sharing, like deriv and nqueens, the optimizations are less effective"
(Perceus §4) **[checked]**. Lean's ablation is in card C1: without reuse, rbmap is 3.23×
slower and const_fold 1.64×.

## 2. Measurements

### 2.1 Method

- **Build.** `cargo build --release -p stitchwort-cli --features alloc-trace`, then
  `stitchwort run … --alloc-trace FILE` on the machine. The trace counts `Fields` cells
  only. Closures, `Delay`s, resumptions, text and big numbers aren't traced
  (`alloc_trace.rs` header), so these are cell counts, not all heap blocks. Native code
  makes the same decisions and its trace must equal the machine's (native-compilation.md
  N4), so the counts hold for `--native` and `build` too **[checked; not rerun
  natively]**.
- **Temporary edit, reverted.** In `machine.rs`, the two `alloc_trace::alloc` calls of
  `Ctor` and `CtorReuse`'s fallback added 1,000,000 to the tag. That split cells built by
  compiled code from those built by the runtime: the effect runtime's nodes and natives
  through `Value::data`. Afterwards I restored the file with `git checkout`.
- **Analysis.** A scratch Python script read each trace. "Same-arity free just before"
  means an allocation preceded, since the previous allocation or reuse, by the freeing of
  a cell with as many fields. That is a dynamic upper bound on local reuse that was
  missed. Some of those frees happen in another function, or in the runtime, where no
  local pass can reach them.

### 2.2 Results **[ran]**

| Program | Cells built | Reused in place | Built by compiled code | Built by the runtime | Increments per cell | Compiled allocations right after a same-arity free | Runtime allocations right after a same-arity free |
|---|---:|---:|---:|---:|---:|---:|---:|
| `bench/native/effects.sw` (1,000 of each op) | 21,007 | 0 (0%) | 9,006 | 12,001 | 0.05 | 55.6% | 58.3% |
| AoC 2024 day 9, real input | 3,628,003 | 567,718 (15.6%) | 2,400,128 | 660,157 | 0.91 | 27.3% | 54.5% |
| AoC 2025 day 5, real input | 306,619 | 45,281 (14.8%) | 147,947 | 113,391 | 1.64 | 25.1% | 46.3% |
| `bench/native/set_nat.sw` (1,000 keys) | 11,916 | 1,389 (11.7%) | 10,524 | 3 | 1.62 | 9.5% | — |
| Roguelike, `Rogue.main` on 25 keys | 359,668 | 112,937 (31.4%) | 126,071 | 120,660 | 1.56 | 32.3% | 32.9% |

On the larger AoC days, the traces were too big for the time budget: day 9's trace was
268 MB, and 2024 day 5 and 2025 day 8 run 2–3× longer. They weren't traced.

**effects.sw, per operation.** About 10.5 cells per operation. One `bump` builds:
- in compiled code, `Done` twice and one `Call`;
- in the runtime's loop, three `Bind` nodes, three pending-list cells `[k, next]` and
  three more `Done`s.

The trace shows the runtime's pattern directly: `free` of a `Bind` (arity 2), then at once
`alloc` of a pending cell (arity 2). That is `eff_run` taking `Bind c k` apart and pushing
`k`. Against the 45 heap blocks per `bump` and 31 per `ask` that effect-runtime.md §9.11
("Option A as built") measured, cells are about a quarter of the allocations. The rest are
closures (two blocks each), resumptions, handler records and `EffRet` boxes. So on this
benchmark, cell reuse could remove about 5 of ~38 blocks per operation (the runtime's
`Bind` to pending cell, and pending cell to `Done`), about 13% of allocations. Allocation
and freeing are 49% of its time (native-only.md NO4), so that is perhaps 5–7% of the time
**[inferred]**. The remaining 87% is representation work, which is SW-593's (§5).

**Why `Set` reuses so little.** `Map.Tree.insertWith`'s arm `Bin s l kk vv r => …
Map.Tree.balance (insertWith … l) kk vv r` takes the node apart but builds nothing
itself. `balance` → `rebuild` → `bin` builds the new node in another function (std
`Map/Raw.sw:100-112`), so the token is never claimed and the cell is freed. The
increments, 1.62 per cell, are about 2 per `balance` call (19,249 increments for 9,521
nodes). `balance` passes `l` and `r` to `shape` (`Map/Raw.sw:91`), which only reads their
sizes, and then uses them again **[checked: source; the attribution of the increments is
inferred from the ratio]**.

**A controlled pair (scratch files, not committed).** Two versions of an unbalanced
search tree `Node size left key right` take the same 1,000 inserts:

| Version | Cells built | Reused | Fresh tree nodes |
|---|---:|---:|---:|
| A: `Node (s + 1) (ins key l) kk r` in the arm | 15,510 | 12,503 (80.6%) | 1,000 (one per new key) |
| B: the same through a recursive helper `mk 0 (ins key l) kk r`, so it isn't inlined | 14,510 | 1,000 (6.9%) | 12,503 |

So the same algorithm goes from reusing every path node to reusing none, depending only
on where the constructor is written. In B, 85% of allocations come straight after a
same-arity free **[ran]**. A also shows a smaller cost. Its TRMC loop does `reuse`, `inc`,
`dec` per level (16,511 increments for 15,510 cells): the destination cell is referenced
by the loop while the next one is filled **[ran; cause read from the trace]**.

**Lorenzen and Leijen's fragility example A** (C4: `match x | Some _ => match y | 0 => x
| _ => Some y`) reuses in place here: 1,000 `reuse` events in 1,000 calls. The token comes
from `DropReuse` at the inner branch, after liveness, which is the drop-guided placement
they recommend **[ran]**.

### 2.3 What a wider reuse pass could avoid

These are estimates **[inferred]** from the table, with the "just after a same-arity free"
column as the ceiling:
- **Compiled code:** 10–30% of compiled cell allocations on AoC-style programs. Most of
  the gain is in std's tree code (`Map`, `Set`), where helpers build the nodes. For
  `Set`/`Map` inserts it is close to the whole path (about 9 of 9.5 cells per insert),
  if the helpers' constructors can claim the caller's token.
- **The effect runtime's nodes:** about half of them, by hand in Rust (§4.2). That is
  18–37% of cells on the parse-heavy days and 57% on effects.sw.
- **Increments:** 0.9–1.6 per cell on every program except effects.sw. Borrowed
  parameters would remove the read-only share. The traces can't say how big that share
  is without the site report of §6, stage 1.
- **Not measured:** non-cell allocations on the AoC days (closures, `Text`). Day 2 and
  day 3's profiles earlier were dominated by `List Char` cells and closures
  (fast-runtime.md stage 4).

## 3. Design sketch

### 3.1 Where the passes would sit

The pipeline is `lower` → `opt::optimize` → `trmc::apply` → `validate` →
`code::compile` → the machine, or `n1` for `--native` and `build` (`lower.rs:180-185`,
`run.rs:249`) **[checked]**. Ownership isn't a separate IR pass. `code.rs` decides moves,
drops and tokens while it emits registers. That has served well: native inherits every
decision for free, and the trace agreement tests check it. So:

| Pass (Perceus / Lean name) | Where | What changes |
|---|---|---|
| dup/drop insertion | already `code.rs`. Add: drop never-read parameters and `let`s at entry | small; a few trace snapshots change |
| reuse analysis across a call | `opt.rs`: inline a non-recursive callee when the caller holds an unclaimed token of an arity the callee builds (`balance`, `bin`, `rebuild`), with a size and fuel bound like today's (24 nodes, 64 copies) | the IR only; native and machine follow |
| hand reuse in the runtime | `effect.rs` / `machine.rs` `eff_run`, shared with native's leaves (native-only.md: "the loop's leaves share the machine's code") | Rust `Rc::get_mut` refills, no `unsafe` |
| reuse specialisation (skip unchanged fields) | `CtorReuse` with a mask of fields that are already in place | `code.rs` plus one `n1` instruction; small gain (one store and one drop per unchanged field) |
| borrow inference | a new analysis over the IR before `code.rs` (Lean's `InferBorrow` rules: owned if reset, passed to an owned position, captured, or before a tail call, C1 and C2) | the calling convention of both runners. See §4.3 for the `unsafe` cost on the machine |
| drop specialisation | mostly there (`Unpack`). Native could inline the unique-cell free of known arity instead of calling `value::free` | `n1` only, trace-neutral |
| FBIP | a report, not a type (C5's steal: "a *report* of which functions run in place") | stage 1's report |

### 3.2 Runtime support

Everything above fits the current `Rc<[Value]>` cells. Two things would need a custom cell:
- reuse across arities (Perceus reuses by size, and here arity is the size), because the
  length lives in `Rc<[Value]>`'s fat pointer;
- a reuse token passed into a callee as a hidden parameter, the general form of "reuse
  across a call".

That custom cell means a hand-written header, count and length, all `unsafe`, in
`value.rs`, `native_abi.rs` and `n1.rs`'s layout probe. Not recommended until the cheaper
stages are measured.

### 3.3 Effects, partial code and the differential tests

- **Resumptions.** A `Resume` holds the pending list; a resumption applied twice shares
  it. Reuse stays correct because every uniqueness test is dynamic: while a resumption
  that can be resumed again is alive, its cells have a count above one and are copied,
  never changed. This holds for any added reuse that keeps the `Rc` test. It would fail
  for any reuse decided statically, such as a uniqueness type, or borrowing that skips the
  test (compilation.md already ruled out uniqueness types for this reason) **[inferred]**.
- **Partial code and ticks.** A tick is a `Delay` step, one per recursive call of a
  partial group (docs/core.md, `tick_counts.rs`). Reuse changes where memory comes from,
  never which calls run, so tick counts can't change. Inlining for reuse, though, changes
  the *steps*: the frames entered, the `E-RESOURCE` budget (fast-runtime.md: "The step
  count … falls with inlining"). Machine and native still agree, because native compiles
  the same bytecode. The reference runner is already compared only on "the same end", not
  the same point (docs/testing.md, `run_reference.rs`). The JS runner has no tick counter
  (`tick_counts.rs` header).
- **What the tests require.** Output and end are the same in all runners. Native and
  machine allocation traces must match event by event (N4). Every stage here changes the
  machine and native together, through `code.rs` or the shared leaves, so the traces stay
  equal. The snapshot traces (`crates/rt/tests/snapshots`) change once per stage and are
  regenerated.

## 4. Risks

### 4.1 Accidental sharing, and a diagnostic

Reuse is a performance property that one stray reference breaks silently:
- a value captured by a closure that is still alive;
- a list kept for a second pass;
- an input held by a resumption;
- an increment from a read-only call, such as `shape l r` above.

Perceus names the cliff: sharing-heavy programs gain least. Huisinga's `Array.groupBy`
copies on every `push` (compilation.md deep read 5.1).

Two possible diagnostics:
- **Lean's way.** `dbgTraceIfShared s a` "returns its argument unchanged, printing the
  provided trace message if the argument's reference count is greater than one" (Lean
  reference, Run-Time Code, Reference Counting) **[cited]**. In Stitchwort this would be
  a native that is the identity for the kernel and prints from the runners. That makes it
  a new trusted native, and the reference and JS runners need it as well.
- **Recommended first: a report needing no source change.** It would hang off the
  allocation trace's hooks and be keyed by bytecode site (global, instruction). For each
  site it counts:
  - `Ctor` allocations;
  - `CtorReuse` hits and misses;
  - `Unpack` of a unique cell and of a shared one;
  - increments by kind (a `Move` clone, `Field`, a shared `Unpack`).

  A shared `Unpack` at a hot site is the accidental-sharing signal. This covers what
  `dbgTraceIfShared` gives, plus the missed-reuse sites of §2.2, and it stays a hidden
  flag outside the trusted base.

### 4.2 Proofs

Nothing here reaches the kernel. Every pass works on the erased IR or the runtime, after
checking, and reuse keeps meaning because a shared cell is never changed. The proofs
touch this in two ways only:
1. A std rewrite *for* reuse (a zipper `insertWith`, compilation.md C6, or SW-814's fused
   balance) changes definitions, so their lemmas must be re-proved. Inlining for reuse in
   `opt.rs` (§3.1) gets most of that gain with no std change **[inferred from §2.2's
   pair]**.
2. Any std native added for diagnostics (§4.1) enters the trusted base like other natives.

### 4.3 `unsafe`

- **Stages 1–3 (§6): none new.** Moves, tokens, `Rc::get_mut` refills and inlining are
  all safe Rust. Native already emits the unique-cell paths inline in Cranelift.
- **Borrowed parameters need it on the machine.** A register holds an owned `Value`.
  Passing a borrowed one means putting a bitwise copy in the callee's window that must
  never be dropped, a `ManuallyDrop` or raw-word convention in `machine.rs`'s register
  vector, its frame teardown and every error exit. Native is easier: skip the increment
  and the decrement, as its helpers already do for borrowed arguments. But both runners
  must change, because traces must agree. SW-1124, borrowed raw pointers behind a safe
  API, is the recent reminder of how this goes wrong.
- **Cross-arity reuse or tokens passed to callees** need the custom cell of §3.2, which
  is the most `unsafe` of all.

## 5. Fit with SW-593 and native-only

- **native-only.md** is built through NO7 (26 Oct). Native executes `code.rs`'s decisions
  and shares the effect runtime's leaves, so every reuse stage lands in both runners at
  once with no native-specific design. The playground (WebAssembly) runs the machine and
  gets the same gain.
- **SW-593** (effect representation, §9.11 B: the state loop at an open row, measured at
  36% fewer instructions at the empty row) changes *how many* `Bind`, pending and `Done`
  nodes exist. Hand reuse of those nodes (§3.1) overlaps with it: done first, part of it
  would be redone. SW-593's deferral condition ("until NO5–NO7 finish") is met.
- **Overlap in what they fix.** On effects.sw, about a quarter of allocations are cells
  (§2.2). Only SW-593's kind of change (fewer nodes, closures in one block instead of
  `Rc<Fun>` plus `Box`, no `EffRet` boxes) reaches the other three quarters. Reuse is the
  bigger lever for pure code (trees, lists); SW-593 is the bigger one for effects.
- **Suggested order:**
  1. The report (stage 1), which serves both.
  2. Reuse across small helpers (stage 2a, pure code), alongside SW-593's decision.
  3. Hand reuse in the effect runtime after SW-593 settles the representation.
  4. Borrowing last, if at all.

## 6. Recommendation: a staged plan

| Stage | What | Size | Model | Measured by |
|---|---|---|---|---|
| 1 | **Reuse report** (§4.1): per-site counters on the trace hooks, behind `run --reuse-report FILE` (hidden, alloc-trace builds), sorted by missed reuse and shared `Unpack`s. It is also compilation.md's T2/D1921 (count RC operations), not yet done | 0.5 lane-day | Sonnet | the report on the five programs above; the first measurable stage |
| 2a | **Reuse across small helpers** in `opt.rs` (§3.1), plus dropping never-read parameters at entry. Tests: the A/B pair as a trace snapshot, `Set.fromList`'s reuse share | 0.5–1 lane-day | Opus (simplifier correctness, the source of the one stage-4 wrong answer) | `set_nat.sw` reuse from 11.7% towards 80%+; instructions per insert |
| 2b | **Hand reuse in the effect runtime** (`Bind` to pending cell, pending cell to `Done`) | 0.5 lane-day | Sonnet | effects.sw blocks per operation (today 45 and 31), after SW-593 |
| 2c | **Reuse specialisation** (skip unchanged fields) and native inline frees of known arity | 0.5 lane-day | Sonnet | report plus instruction counts; do only if stage 1 shows `CtorReuse` hot |
| 3 | **Borrowed parameters**: a design note first (Lean's rules, Koka's space objection, the machine's `unsafe`), only if stage 1 shows read-only increments are a large share | note 0.5 day; build 2–3 lane-days | Opus | increments per cell (today 0.9–1.6) |
| 4 | **FBIP in std** where the report shows misses that inlining can't fix (`Map.insertWith` by zipper, SW-814) | per function, with re-proofs | Opus | report |

Cross-arity reuse and a custom cell type (§3.2) are left out until stage 1–2 numbers
show a need.

## 7. Decisions for Matt

- **D2273.** Take this direction as an extension of the existing `code.rs` design
  (moves, tokens, dynamic uniqueness), in the stages of §6, rather than a rewrite into a
  separate explicit dup/drop IR? **[rec: yes.** Native and the playground inherit each
  stage, and the trace agreement tests keep holding.**]**
- **D2274.** Start with stage 1, the per-site reuse report, as the measurement and the
  diagnostic for accidental sharing, rather than a `dbgTraceIfShared`-style native?
  **[rec: yes.** It needs no source change, adds nothing to the trusted base, and closes
  D1921's T2. A native can follow if users need it in their own code.**]**
- **D2275.** Then stage 2a, inlining for reuse in `opt.rs` (with dropping unused
  parameters), before any std rewrite for in-place trees? **[rec: yes, if stage 1
  confirms `Map`/`Set` as the top missed sites.** The scratch pair shows 7% → 81% reuse
  from where the constructor is written alone.**]**
- **D2276.** Borrowed parameters: only a design note, and only if stage 1 shows
  read-only increments are a large share (say over 20% of reference-count operations)?
  **[rec: yes.** It needs `unsafe` in the machine, Koka declined it for space safety, and
  it can block reuse.**]**
- **D2277.** Order against SW-593: do the report and stage 2a now, and stage 2b (hand
  reuse of effect nodes) only after SW-593's representation is decided? **[rec: yes.**
  Cells are about a quarter of effects.sw's allocations. SW-593 is the bigger lever
  there, and 2b would partly be redone after it.**]**

## 8. What wasn't checked

- **Non-cell allocations on the AoC days and the roguelike:** closures, `Text`, `Delay`.
  The trace doesn't see them, and a counting allocator would need a separate test binary.
- **Native traces:** not rerun. The counts rely on N4's event-for-event agreement.
- **Time:** none of the savings is timed. The 5–7% for effects.sw and the per-stage gains
  are inferences from shares.
- **Larger AoC days:** 2024 day 5, 2024 day 10 and 2025 day 8 weren't traced (trace size
  on a loaded machine).
- **The papers:** not reread. The FP² and frame-limited papers and Counting Immutable
  Beans are used through compilation.md's audited cards C1, C4 and C5. Perceus was read
  from the technical report (v1, Nov 2020), not the PLDI camera-ready.
