# Fewer objects built by the effect runtime (SW-2444)

SW-2444, 8 Nov 2026, Opus, paper lane (nothing built or run). It follows
[SW-2422](../reviews/SW-2422-allocation-by-cause.md) (allocation by cause),
[SW-2425](../reviews/SW-2425-value-census.md) (the census) and
[SW-2417](../reviews/SW-2417-native-effect-share.md) (the effect share), and respects D3430
(operations in place stops after stage B; stages C and D dropped). Claims are marked
**[measured]** (a counter, census or profile, cited), **[read]** (seen in the code, file
and function named), **[inferred]** (worked out from measured numbers or the code, not
checked by running anything), **[estimated]** (a guess at an effect, with the rule given)
or **[lit]** (a paper, cited).

## 0. Summary

**The problem.** On `expressions` and `scan`, about half of native time goes on making,
freeing and copying objects (SW-2417, SW-2422). The effect runtime itself builds about
13–14 objects for every operation a parser performs. Most live for one loop step: a
resumption made in two parts, a cell pushed on a list and popped straight off, a `Done`
cell made only to be taken apart, a jump object returned and thrown away. On expressions
that is about 258 million objects of about 714 million made in a run (36%)
**[inferred from measured counts, §1]**.

**The change.** Five local changes to how the runtime builds and reuses those objects.
None of them moves an operation past a handler or runs a clause anywhere but where
today's loop runs it, so none needs the consumer link that stages C and D needed:

1. a resumption is one object, not two (R1);
2. the loop reuses the `Bind` node it takes apart as the pending-list cell it pushes (R2);
3. a forwarded operation reuses the `Call` cell it arrived in (R3);
4. `bind (Call o DoneK) k` becomes `Call o k` in place, the monad law, so a perform no
   longer makes a `Bind` node, a pending cell and a `Done` cell (R4);
5. a fused state handler whose clauses never mention `k` gets no resumption object at
   all, and its jump object is recycled (R5).

**What it should do** (all **[estimated]**, §2–§3): about 9–13% fewer native
instructions on expressions and scan (central about 11%), about 5–9% less time; 3–5% on
`bridge`; about 1% on `matcher` and `disk`; nothing on programs without effects. The
runtime's objects per operation fall from about 14 to about 3. Each step is measured
alone against its own prediction (§4).

That is a modest gain: about 1.1× on our two worst programs, not the 2–3× they need.
The note says so plainly. Bind continuations' closures (47% of these programs' bytes) are
the bigger lever, and they are not the effect runtime's (§2.9).

## 1. Where the effect runtime's objects come from

### 1.1 One operation, followed through

The common operation on `expressions` is a `Parse` operation (`span`, `next`, …)
performed in parser code under one or two `optional`s and answered by `runFrom`, the
fused state handler. Mean routes per operation are 2.64 before stage B and 1.08 after;
29.13 M of the 49.18 M routes are now skipped forwards **[measured, SW-2347, SW-2349]**,
so each operation passes about 1.56 skipping folds and then reaches `runFrom`.

| Step | Code | Objects made | Freed when |
|---|---|---|---|
| Perform | generated: `Call (L (Span p)) DoneK` | op cells, `Call` cell (generated code's; not counted here) | taken apart by a loop |
| `bind c k` in the caller | `sw_bind` (`native_abi.rs`) | `Bind` node `[c, k]` (2-field cell); `k`'s closure is generated code's | the loop's push takes it apart |
| Loop meets `Bind` | `sw_eff_step`, `STEP_AGAIN` | pending cell `[k, rest]` (`Value::data(0, …)`) | popped at the next `Done` |
| Loop meets `Call`, clause skipped (×1.56) | `sw_eff_step` → `effect::forwarded`, `effect::skipped` | `Rc<Resume>` (96 B), `Fun::Resume` wrapper (72 B), a new `Call o r` cell; the incoming `Call` cell freed | the outer handler's resumption holds them until it resumes |
| `runFrom` routes it | `sw_eff_step`, `Handler::State` | `Rc<Resume>`, `Fun::StateK` wrapper sharing it (the loop holds the `Resume` too, `resume_out`); `JumpK` shared since SW-2433 | `sw_state_step`, once the clause returns |
| The clause jumps | `effect::jump_k` | `Fun::Jumped(v, s)` (72 B) | `effect::state_step`, at once |
| `runFrom` goes on from `rest y` | `rt_resume` of each skipped fold's eager resumption, inner last | none | |
| Innermost loop: `rest` is `DoneK` | `sw_apply_prepare`'s `DoneK` fast path | `Done y` cell | the loop's pop, at once |
| Loop pops `k`, applies it to `y` | `sw_eff_step`, `STEP_APPLY` | none; the pending cell and the `Done` cell are freed | |

**[read]**: `crates/rt/src/effect.rs` (`skipped`, `resume_lazily`, `state_step`,
`state_k`, `jump_k`, `done_k`), `native_abi.rs` (`sw_bind`, `sw_eff_step`,
`sw_state_step`, `sw_resume_begin`, `sw_apply_prepare`), `machine.rs` (`eff_run`,
`eff_call`, the same through the shared leaves, plus a `Box` for `Ret::Step` per state
route, machine only).

### 1.2 Counts per run

Runs at the comparison sizes. Expressions' native instruction count is 310.99 G and
scan's 297.65 G after SW-2443 **[measured, SW-2443's commit]**.

| Object | Made by | expressions | scan | matcher | Source |
|---|---|---:|---:|---:|---|
| `Rc<Resume>` | every route and every skip | 49.18 M | 47.50 M | 2.54 M | census **[measured]** |
| `Fun::Resume` wrapper | skips, fold routes, lazy resumes | 30.5 M | about 25.1 M | small | census (scan **[inferred]**: other funs less three times 22.4 M) |
| `Fun::StateK` wrapper | state routes | 18.7 M | 22.4 M | small | census **[measured]** |
| `Fun::Jumped` | state clauses' jumps | 18.6 M | 22.4 M | small | census **[measured]** |
| `Fun::JumpK` | (shared since SW-2433) | 0 | 0 | 0 | was 18.6 M / 22.4 M |
| pending cell | each `Bind` the loop enters | 46.4 M | about 43 M | 2.0 M | call counts **[measured]** (scan and matcher: `sw_bind`) |
| `Call o r` cell of a skip | each skipped forward | 29.1 M | 21.25 M | | = forwards **[inferred]** |
| `Done y` cell from `DoneK` | each resumption whose `rest` is `DoneK` | 18.6 M | about 22.4 M | | `DoneK` applies **[measured]**; scan = performs **[inferred]** |
| `Bind` node (`sw_bind`) | each `bind` whose computation isn't `Done` | 46.6 M | 43.0 M | 2.0 M | call counts **[measured]** |
| `Handler`, `StateRun` | handler starts, non-tail state `k` | 0.27 M, about 0.5 M | small | small | census; `StateRun` **[inferred]** from the "other" bytes |
| **Runtime total, `Bind` nodes included** | | **about 258 M** | **about 247 M** | **about 9 M** | |
| **All allocations in the run** | | **about 714 M** | **about 680 M** | | **[inferred]**: cells + closures and paps ×2 (the `Rc<Fun>` and its captures) + other funs + resumes + texts |

Per operation first performed (18.65 M on expressions, 22.43 M on scan **[measured]**):
about 13.8 runtime objects on expressions and 11 on scan.

**The "190 M cells built by the runtime" needs a correction.** SW-2422 took the runtime's
cells as the census's cells less `sw_cell_new`'s calls less `sw_bind`'s. But generated
code takes cells from the cell cache (SW-2363) inline, without calling `sw_cell_new`
(`n1.rs`, `cached_cell`: only the miss calls the helper) **[read]**, so those cells were
in the residue. Stage 0 (§4.1) counted them **[measured]**: generated code's cache hits
are 50.2 M on expressions (not the 96 M this paragraph first inferred), and the runtime's
own cells are **117 M without `Bind` nodes, about 36% of the census's 322 M cells**, and
163.5 M (51%) with them. The 117 M is the 94 M of the sites in the table (46.4 pending +
29.1 skip `Call`s + 18.6 `Done`s) plus 23 M the table missed: rebuilt forwarded operations
(`effect::forwarded`, 0.79 cells per skipped forward). 22.8 M cells (7%) remain unexplained
by any counted site. So the runtime's cells are about 36% of the run's, not 59% (SW-2422)
nor 30% (this note's first correction). Its other objects (resumptions, wrappers, jumps:
about 117 M) are about as SW-2422 said.

### 1.3 What one object costs

- **About 140 instructions per small object made and freed [measured].** SW-2433 removed
  18.6 M `JumpK` allocations on expressions and 22.4 M on scan (childless, 72 bytes):
  321.24 G to 318.58 G and 307.64 G to 304.57 G, so 143 and 137 instructions each. An
  object with children (a `Resume`, a cell with pointers) costs more to free: I use
  140–200.
- **Fewer instructions are not the same share of time [measured, SW-2363].** The cell cache
  took 30% of binary-trees' instructions and 10% of its time: mimalloc's fast path runs at a
  high instruction rate beside generated code's chains of dependent loads. So I predict
  instructions, which are steady under load and are what each stage's go/no-go uses, and
  take time to be about half of that (0.35–0.7).
- **A loop step and a runtime apply cost about as much again.** `sw_eff_step` is 141.4 M
  calls and the effect-loop group 11.9% of expressions' time; `sw_apply_prepare` is 145.7 M
  calls and 8% self **[measured, SW-2417]**. I use 60–100 instructions per loop step
  saved and about 80 per `DoneK` apply saved **[estimated]**.

## 2. Options, each as an end state

Savings are of native instructions **[estimated]**, by the rules in §1.3. "General" means
any effectful program gains; "narrow" means one handler shape.

### 2.1 R1: a resumption is one object

**End state.** `Fun::Resume { lazy, handler, rest, pending }` and `Fun::StateK { handler,
rest, pending }` hold the resumption's fields themselves; `Rc<Resume>` stays only for a
`translate`'s resumption, which also needs the operation (`op`), and for the unwind
log's holders. A state route's loop holds a reference to the `StateK` function value
(the same `Rc<Fun>` as `k`) instead of a second reference to a shared `Resume`;
`state_step` takes that `Rc<Fun>` apart (moved out if unique, as now with
`Rc::try_unwrap` of the `Resume`). `sw_unwind_resume` then needs no wrapper either.

- **Layout.** `Fun` grows from 56 to 64 bytes (tag and flag, `Rc<Handler>`, two values),
  so an `Rc<Fun>` asks for 80 bytes instead of 72. mimalloc already rounds a 72-byte
  request up to its 80-byte class, so no run uses more memory **[inferred from
  mimalloc's size classes, not checked on a run]**. The census's byte totals would show
  +8 bytes per `Fun`.
- **Saves** 49.2 M allocations and frees on expressions, 47.5 M on scan: **2.2–3.2% on
  both**; matcher about 0.6% (2.5 M), bridge about 1% (9.5 M), disk about 0.6%.
- **Risk:** low. A representation change in the runtime, the same in both runtimes through
  the shared leaves; `probe_layout` checks the new layout; native code doesn't read a
  `Resume`'s fields, only `sw_resume_begin` does. `resume_lazily` copies three fields
  instead of one count (rare: lazy fold routes, about 1.4 M).
- **Effort:** Sonnet, 1.5–2 h (`value.rs`, `effect.rs`, `native_abi.rs`, `machine.rs`,
  the census hooks).
- **General.** Every handler's resumption.
- SW-2442 measured nothing for flipping the lazy flag in place: the flip was rare. This is
  the other half of its finding, the two allocations per resumption.

### 2.2 R2: the `Bind` node becomes the pending cell

**End state.** When the loop meets `Bind c k` and the node is unique, it takes `c` out,
writes the pending list in its place, and the same cell, now `[next, k]`, is the new
pending list. A pending cell's layout changes from `[k, next]` to `[next, k]`, so `k`
doesn't move. A shared node (a stored computation) is copied as today. Two sites build
pending cells (`sw_eff_step`'s `STEP_AGAIN`, the machine's `eff_run`) and two pop them
**[read]**; both use one new shared leaf in `effect.rs`.

- **Sound** because pending lists are persistent: a node is never changed once it is on
  a list, and the node reused here was unique, so nothing had seen it as a list.
- **Saves** one allocation and one free per push: 46.4 M on expressions, about 43 M on
  scan: **1.8–2.2%**; matcher about 0.3%. After R4 the pushes left are about 28 M and
  21 M, so about 1.1% and 0.8%.
- **Risk:** very low. **Effort:** Sonnet, 45 min. **General.**

### 2.3 R3: a forwarded operation reuses its `Call` cell

**End state.** A skipped forward (stage B) turns the incoming `Call o rest` into `Call o′
r`. When the incoming cell is unique, the loop writes `o′` and `r` into it instead of
freeing it and making another (`sw_eff_step` takes the cell apart with `effect::pair`
before it knows the clause is skipped, so the leaf is reordered: test the table, then
take apart or refill).

- **Saves** 29.1 M cells on expressions and 21.25 M on scan: **1.1–1.4% and
  0.9–1.1%**; bridge about 0.5% (2.8 M skips).
- **Risk:** very low. **Effort:** Sonnet, 30–45 min, with R2. **General** to forwarding
  folds, which are every `Std.Parse` handler but `runFrom`.

### 2.4 R4: a perform's `bind` is folded into its `Call`

**End state.** `bind (Call o DoneK) k` gives `Call o k`, with `k` written over `DoneK` in
the same cell when the cell is unique (a new cell `[o, k]` otherwise). Done in the
shared leaf that `sw_bind` and the machine's `bind` use.

- **Why it holds.** The tree says `bind (Call o r) k = Call o (y => bind (r y) k)`. With
  `r = DoneK`, `bind (Done y) k = k y`, so the continuation is `y => k y`: `k` up to eta.
  A resumption's `rest` is only ever applied to one value, as `k` is by the loop, so
  nothing can tell them apart. No handler is looked up, nothing is moved across a
  handler and no clause runs anywhere new, so computations as values are safe: a stored
  `Call o DoneK` is shared, so it is copied, not changed.
- **Who gains.** Every operation as the elaborator writes it is `Call O DoneK`, and
  `DoneK`'s applies equal the operations performed on expressions (18.6 M against
  18.65 M) **[measured]**. A perform inside a function (`Parse.span`'s body) still meets
  its caller's `bind`, since the function returns the `Call`. I assume 70–100% of
  performs reach a `bind` directly **[estimated]**; stage 0 counts it.
- **Saves**, per perform reached: the `Bind` node, the pending cell, the `Done` cell, the
  `DoneK` apply, and two loop steps (the push and the pop). On expressions, about 3–4.5%
  alone; after R2 (the pending cell is already free), **about 2.3–3.2%**. On scan,
  3.5–5% alone, **2.8–3.9%** after R2; bridge 2–3% (6.56 M performs).
- **What else changes:** effect counts (`binds`, `pushes`, `pops`, steps) and machine steps
  fall, in both runtimes alike; results and messages don't. Step limits are reached later
  or not at all (D2543), as for stage B. The JavaScript backend keeps its own `bind`.
  The runner's `Handler::Step` meets a `Call` with nothing pending and hands it out
  directly, so the `IO` runner gains too.
- **Risk:** low to medium: an equation of the tree applied by both runtimes, with count
  expectations regenerated. **Effort:** Opus (effect semantics, both runtimes'
  agreement), 1–1.5 h. **General.**

### 2.5 R5: a state handler that can't use `k` gets none

**End state.** When a fused state handler's step never mentions `k` (every `k v s′` became
a jump, and no other `k` is left: the test `clauses.rs` already makes for "Tail" and
"Abort"), the lowering marks the fold, and at an operation the loop passes `Erased` for
`k` and keeps the resumption's handler, `rest` and pending list in its own frame (stack
slots in `rt_loop`, the `Ret::Step` in the machine) instead of on the heap. If the call
fails, the loop gives those values up to the unwind log, as it gives up its handler today.
Separately, for every fused state handler, `state_step` keeps the unique `Fun::Jumped`
it has taken apart in a one-slot store on the run, and `jump_k` refills it in place
(`Rc::get_mut`) rather than allocating.

- **Why it holds.** A value passed for a parameter that the body doesn't mention can't be
  observed. The jump object is reused only when unique.
- **Who gains.** `Parse.runFrom` (fused; 6 Tail and 2 Abort clauses, no `k` left)
  **[measured, stage A census]**: every parser. Other closed-row state handlers that fuse;
  not `labelWholeFrom` or the open-row `IO` handlers, which aren't fused.
- **Saves** per state route the `Resume`, the `StateK` and the `Jumped`: 55.8 M objects on
  expressions, 67.2 M on scan: 2.5–3% and 3.2–3.8% alone; after R1 (one object fewer
  already), **1.7–2.0% and 2.1–2.6%**. Matcher, small.
- **Risk:** medium: `rt_loop`'s Cranelift (three values held across the call, the unwind
  path), the machine's `Ret::Step`, a new lowering flag. **Effort:** Opus, 2 h.
  **Narrow**, but the parsers all reach it.
- **How it differs from what D3430 dropped.** Stages C and D found the target handler
  where the operation was performed and ran its clause there, which needed the
  handler-entry stack, the consumer link, thunked fold bodies and the aimed unwind. R5
  changes none of that: the operation still travels to `runFrom` by today's route, and
  the loop calls the clause exactly where it does now. It only declines to build a
  resumption that the clause provably can't reach. It is Koka's idea, that a
  tail-resumptive clause needs no resumption, applied at the handler, not at the perform.

### 2.6 R6: the runtime's emptied cells go to the cell cache

**End state.** When the runtime takes a unique cell apart (`effect::pair`, `field`: pops,
`Done` cells, state routes' `Call` cells, about 75 M a run on expressions after R2–R4),
native code's run gives the emptied block to the cell cache, as generated code's `Unpack`
does, so a later generated `Ctor` takes it with no call.

- **Saves** about 1.5–2.4% on expressions and scan **[estimated: 60–100 instructions
  each]**, with the smallest time gain of any option here (SW-2363's lesson).
- **Moot under compact values C**, whose cell type makes the cache its own free path for
  Rust drops too (compact-values.md §3.1; cell-allocator.md stage C). Do it only if C is
  not coming. **Effort:** Sonnet, 1 h. **General**, native only.

### 2.7 Considered and not recommended

- **The pending list as an array** (Koka's "short-cut resumptions" kept "using a queue or
  array representation", Xie and Leijen 2021 §2.8 **[lit]**): a `Value::Array` pushed and
  popped in place while unique, copied when a resumption is shared (multi-shot). It
  frees as many objects as R2 does (one per `Bind` node), with more code and a copy on
  every multi-shot resume. R2 gets the same count for 45 minutes.
- **A resumption as a slice of stack** (OCaml 5's fibers). OCaml still "allocates a
  continuation object per resumption" (Xie and Leijen 2021 §5, citing Sivaramakrishnan et
  al. 2021 **[lit]**), its continuations are one-shot, and ours are multi-shot and
  persistent. In our runtime nothing is on the native stack between a perform and its
  handler: operations come back as values, and the frames still to run are already the
  heap's pending list. There is no stack slice to take.
- **Evidence passing, operations in place** (Koka's tail-resumptive optimisation, the
  dropped stages C and D). Not revived. What it would add beyond R1–R5 is the removal of
  the loop steps, routes and skip resumptions between the perform and the handler. Stage
  C measured that on the machine: 3.1× fewer loop steps for 1.11× time (SW-2350). The
  allocations of the skips that remain after R1 and R3 (one wrapper per hop) are its
  part of this pie.
- **The skip's resumption** (one `Fun` per hop, 29.1 M on expressions, after R1 and R3).
  It is what restores the skipped fold's loop when the outer handler resumes; removing it
  means not reifying the hop, which is the in-place design. Kept.
- **A jump "register"** in place of R5's recycled `Jumped`: correct only while fusion puts
  every `jump` in tail position. The one-slot store is correct with no such reliance.

### 2.8 Ranking

| | Expressions | Scan | Matcher | Bridge | Risk | Effort | Reach |
|---|---:|---:|---:|---:|---|---|---|
| R4 perform folded into its `Call` | 2.3–3.2% (after R2) | 2.8–3.9% | ~0.5% | 2–3% | low–medium; counts change | Opus 1–1.5 h | general |
| R1 one-object resumption | 2.2–3.2% | 2.2–3.2% | ~0.6% | ~1% | low | Sonnet 1.5–2 h | general |
| R2 `Bind` node reused as pending cell | 1.8–2.2% | 1.7–2.2% | ~0.3% | ~1% | very low | Sonnet 45 min | general |
| R5 no resumption for a state handler without `k` | 1.7–2.0% (after R1) | 2.1–2.6% | small | ~1% | medium | Opus 2 h | narrow (fused state handlers) |
| R3 skip reuses its `Call` cell | 1.1–1.4% | 0.9–1.1% | 0 | ~0.5% | very low | with R2 | forwarding folds |
| R6 runtime frees into the cell cache | 1.5–2.4% | 1.5–2.4% | small | small | low | Sonnet 1 h | moot under C |

Together, without R6: **about 9–12% of expressions' instructions and 9.5–13% of scan's**,
about 5–9% of time; bridge 3–5%, matcher and disk about 1%. The runtime's objects per
operation go from about 14 to about 3 (the skip wrappers and the `Bind` nodes of binds on
results that aren't a fresh perform) **[estimated]**.

### 2.9 What this leaves on the table

Closures are 47% of expressions' and scan's bytes and 8–10% of their time (SW-2422,
SW-2425); 106 M a run on expressions, two allocations each, most of them bind
continuations. Stage E (closures only when something pauses) went with D3430, since
before stage D nearly every bind sees a `Call`. The lever left is the closure's layout:
captures in the same allocation (SW-2422's cut 5, 4–6% **[estimated there]**), which is
compact values A's closure and can be done under E on its own. It isn't the effect
runtime's and isn't proposed here.

## 3. How this meets compact values (C, E, A)

- **Independent of the gate.** Every option here removes objects or reuses them; none
  changes how wide a value is. They help under today's three words, C, E and A alike,
  and none waits for SW-2441.
- **C:** R6 is moot under C. R2 and R3 reuse cells through `Rc::get_mut` today and would
  use C's own uniqueness test.
- **E:** R1's inline resumption is two values and a handler, 40 bytes under E plus the
  tag word: 48, while E's largest other `Fun` (a `Jumped`, a `Pap`) is 40. So under E R1
  would add 8 real bytes to every `Fun` (mimalloc's classes are exact up to 64): about
  0.85 GB more allocated on expressions, 2% of its bytes **[inferred]**. Two ways out,
  either fine: closures in one allocation of their own size (§2.9), after which `Fun`'s
  fixed size matters little, or R1's variant keeping the handler in the pending list's
  tail. Decide with E; no need now.
- **A:** the effect runtime's objects need headers under A anyway
  (compact-values.md §3.6); R1 makes a resumption one object, which is A's shape.
- **V4's model.** These cuts take instructions off the parsers that width doesn't
  touch, so width becomes a slightly larger share of what's left there: E's prediction on
  expressions and scan rises a little (from 1.06×, by perhaps 0.005×) **[estimated]**.
  Not enough to move the gate.

## 4. A staged plan

Each stage is one lane, measured alone with `task bench:compare -- --runs 3 --runners
native --instructions` on expressions, scan, matcher and bridge (plus the decision set,
to show the others don't move), before and after, on the same machine. The rule, as
D3435's: **kept if it delivers at least 60% of its central prediction in instructions and
no program is over 1% slower**; otherwise not merged, and the note is corrected before
the next stage.

| Stage | What | Predicted instructions (central, expressions / scan) | Go/no-go |
|---|---|---|---|
| 0 | **Counters** (Sonnet, 45 min): `call-counts` events for each runtime site of §1.2 (pending cells, skip `Call`s, `DoneK`'s `Done`s, `Resume`s, wrappers, `Jumped`s), for generated code's cell-cache hits, and for `bind`s whose computation is a fresh `Call o DoneK` | none | Runtime cells within 15% of 94 M on expressions, else rework §1.2. R4 reaching under 50% of performs halves R4's prediction before stage 3 |
| 1 | **R1** (Sonnet, 1.5–2 h) | −2.7% / −2.7% | kept at −1.6% or better on both |
| 2 | **R2 and R3**, two commits measured one by one (Sonnet, 1 h) | R2 −2.0% / −1.9%; R3 −1.25% / −1.0% | each at 60% of its own |
| 3 | **R4** (Opus, 1–1.5 h; count expectations regenerated) | −2.7% / −3.3% (after R2) | kept at −1.6% / −2.0% |
| 4 | **R5** (Opus, 2 h) | −1.85% / −2.35% (after R1) | kept at −1.1% / −1.4% |
| 5 | **Recount** (Sonnet, 1 h): SW-2422's profile and the census again; time on Overmind with `bench:compare` | total about −10.5% / −11.2% instructions, −5 to −9% time | the record for V4's rerun. R6 only if compact values C isn't scheduled by then |

Stopping at any stage leaves a complete end state. Stages 1 and 2 can run side by side
(different files mostly: `value.rs` and the resume paths against the loop's push and
skip); 3 after 2 (both touch the push); 4 after 1 (both touch the state route).

## 4.1 Stage 0 results (SW-2461, 9 Nov 2026, Sonnet)

**[measured]** throughout, with the new counters (below), native executables built with
`--count-bodies` against a runtime library with the `call-counts` feature, at the
comparison sizes of `bench/compare/programs.toml`. One run each; the counts are
deterministic (identical between the two runs of expressions that were repeated).

**What was added.** All in the existing `call_counts` report (`STITCHWORT_CALL_COUNTS=1`),
nothing when the feature is off:

- `Made`: objects the effect runtime builds, per allocation site (a new section of the
  report, "objects built by the effect runtime, by allocation site"): the `Bind` node of
  `sw_bind` and of the applied `bind` native, the pending cell, a skip's `Call`, `Handler::Step`'s
  `Call`, `DoneK`'s `Done`, a lazy resumption's two cells, rebuilt forwarded operations
  (`forwarded`, `renamed`), `Rc<Resume>` per route kind, each `Fun::Resume` / `StateK` /
  `Jumped` wrapper, `StateRun`, `Handler`.
- `Event::CellCacheHit`: generated code's inline hits in the cell cache. The hit is decided in
  compiled code, so a body compiled with `Options::count_bodies` (`build --count-bodies`)
  calls `sw_count_cell_hit` in the hit block; without the option the code is unchanged.
- `Event::BindOf*`: what a `bind` that isn't answered at once (not a `Done`) was given:
  `Call o DoneK` with its `Call` cell unique or shared, `Call o r`, a `Bind` node, else.
- `Event::LoopCallDoneK` / `LoopCallOther`: the `Call` cells `sw_eff_step` meets, by whether
  `rest` is `DoneK`. Counted at the loop, so it is the number of performs in their original form
  however they got there; against `BindOfPerform*` it gives the share bound directly.

**Counters cost nothing off.** Native instructions retired (`/usr/bin/time -l`, counting off,
same commit with and without this change, both built through kache as lane worktrees are):
expressions 310.69 to 310.95 G over six runs with, against 310.66 to 310.70 G over four without
(about +0.02%, inside the spread of repeats); matcher 68.176 G against 68.179 G and 68.212 G against
68.214 G. See the second finding at the end on why "built through kache" matters.

### Counts

| | expressions | scan | matcher | bridge |
|---|---:|---:|---:|---:|
| `Bind` nodes made (`sw_bind`) | 46.37 M | 40.90 M | 2.01 M | 13.88 M |
| pending cells | 46.37 M | 40.90 M | 2.01 M | 13.88 M |
| skip `Call` cells | 29.13 M | 21.25 M | 1.40 M | 2.83 M |
| `Done` cells from `DoneK` | 18.65 M | 22.43 M | 1.14 M | 6.56 M |
| rebuilt forwarded operations, cells | **22.95 M** | 5.25 M | 1.63 M | 0 |
| **runtime cells, with `Bind` nodes** | **163.5 M** | 130.7 M | 8.2 M | 37.2 M |
| runtime cells, without `Bind` nodes (the note's "94 M" is pending + skip + `Done`) | 94.1 M, or **117.1 M** with rebuilt operations | 84.6 M / 89.8 M | 4.5 M / 6.2 M | 23.3 M |
| `Rc<Resume>` (all routes and skips) | 49.18 M | 47.50 M | 2.54 M | 9.52 M |
| `Fun::Resume` wrappers | 30.53 M | 25.07 M | 1.40 M | 2.96 M |
| `Fun::StateK` wrappers = `Fun::Jumped` | 18.65 M | 22.43 M | 1.14 M | 6.56 M |
| `Rc<Handler>` (fold and state handlers starting) | 4.75 M | 4.10 M | 0.28 M | 1.20 M |
| generated code: cell-cache hits | **50.18 M** | 54.74 M | 17.53 M | 22.02 M |
| generated code: `sw_cell_new` calls (misses and uncached arities) | 85.65 M | 75.35 M | 16.91 M | 39.19 M |
| `bind`s of a fresh perform `Call o DoneK`, `Call` cell unique | 20.05 M | 26.25 M | 1.15 M | 6.69 M |
| the same, `Call` cell shared | 0 | 0 | 0 | 0 |
| `bind`s of a `Bind` node | 26.32 M | 14.65 M | 0.87 M | 7.20 M |
| `bind`s of `Call o r`, `r` not `DoneK`, or of anything else | 0 | 0 | 0 | 0 |
| `Call o DoneK` met by the loop | 20.05 M | 26.25 M | 1.15 M | 6.69 M |
| `Call o r` (other `r`) met by the loop | 29.13 M | 21.25 M | 1.40 M | 2.83 M |

### What the counts say

- **§1.2's per-site counts hold.** `Rc<Resume>` (49.18 M and 47.50 M), `Fun::Resume`
  wrappers (30.53 M; scan 25.07 M, the note's inferred 25.1 M), `StateK` and `Jumped`, skip
  `Call`s, `Done`s (18.65 M; scan 22.43 M) and pending cells (46.37 M; scan 40.90 M against
  the note's inferred "about 43 M"; the 2.05 M difference is `sw_bind` calls answered at once
  with a `Done`) all agree with the note to within rounding. The three cell sites the note
  summed to 94 M sum to **94.14 M**. The go/no-go's first test, "runtime cells within 15% of 94 M",
  passes on those sites.
- **But the note undercounted one site: rebuilt forwarded operations, 22.95 M cells on
  expressions** (0.79 per skipped forward; scan 5.25 M, matcher 1.63 M, bridge none). The note had
  "a little from lazy resumes, `translate` and rebuilt forwarded operations". `forwarded` returns
  the operation it was given only when the forward's table says the same constructor under one `L`;
  otherwise it builds `outer a` and its wrappers afresh, one cell per layer. Counting those, the
  runtime's cells without `Bind` nodes are 117.1 M, +24% on 94 M, and with `Bind` nodes **163.5 M**.
- **Against the census's 322 M cells on expressions** (SW-2422: 85.6 `sw_cell_new` + 46.6 `sw_bind`
  + 190.1 residue): generated code's cache hits are **50.2 M, not the 96 M of the correction**.
  Generated code's cells are 85.65 + 50.18 = 135.8 M (42%), the runtime's counted sites are 163.5 M
  (51%), and **22.8 M (7%) remain unexplained**: not an effect site; probably primitives that
  build lists (`TextToList` 3.28 M calls on expressions) and `StateRun`'s comp-form `Done`
  (**[inferred]**, not counted). So the runtime builds about half of the run's cells, not 30%
  (the correction) nor 59% (SW-2422). The correction in §1.2 should read: runtime cells about 117 M
  without `Bind` nodes, 36% of the census's cells; 51% with them.
- **The note's total of runtime objects, 258 M, is 285 M** (expressions): the rebuilt operations
  (+23 M) and the 4.75 M handlers, which the census counted as 0.27 M because a fold's handler is
  made with `Rc::new`, not `value_census::new_handler`.
- **R4 reaches every perform.** `Call o DoneK` is met by the loop 20.05 M times on expressions and
  was bound directly, with a unique `Call` cell, 20.05 M times: **100%**, on all four programs, not
  the assumed 70-100%; no `Call o DoneK` is ever shared at its bind, and no `bind` is given a
  `Call o r` with another `r`. 18.65 M of the 20.05 M are the first performs; 1.4 M are
  `bind (Call O DoneK) k` in the clauses of fold routes (the "2 routes" chains). So R4 saves, per
  perform, the `Bind` node and pending cell (20.05 M each), the `Done` cell (18.65 M) and the `DoneK` apply
  (18.65 M): the note's 18.6 M, +8% on the first two. What R4 does not touch is the other **26.32 M
  `bind`s, of a `Bind` node** (57% of expressions' binds; 36% of scan's, 52% of bridge's):
  left-nested binds from `do` blocks. After R4 the pushes left are 26.3 M on expressions
  (the note's "about 28 M") and 14.65 M on scan (the note: 21 M).
- **R5's objects** are exactly the note's: 18.65 M state routes make three each (55.9 M), 22.43 M on scan
  (67.3 M).
- **Matcher and bridge**: matcher's effect objects are small (8.2 M cells, 2.5 M `Resume`s); its
  cells are mostly generated code's (34.4 M, half from the cache). Bridge: 37.2 M runtime cells beside
  generated code's 61.2 M.

### The options after stage 0

| | verdict | why |
|---|---|---|
| R1 one-object resumption | unchanged | 49.18 M and 47.50 M `Rc<Resume>`, as estimated |
| R2 `Bind` reuse | unchanged | 46.37 M pushes; scan 40.90 M, not 43 M, so its saving is about 5% under the note's |
| R3 skip reuses its `Call` | unchanged, and **a neighbour appeared** (below) | 29.13 M and 21.25 M |
| R4 perform folded into its `Call` | **at the top of its range**: 100% of performs, unique, so the in-place write always applies | savings per perform as estimated; see the 26.3 M left-nested binds it does not remove |
| R5 no `k` for a state handler | unchanged | 55.9 M and 67.3 M objects |
| R6 emptied cells to the cache | worth a second look only if C is not coming | the cache already serves 50.2 M of generated code's 136 M cells; the runtime's emptied cells (pops, `Done`s) go to the allocator |
| **R7 (new): rebuilt forwarded operations** | worth costing | 22.95 M cells on expressions (0.79 per skip), 5.25 M on scan; **[estimated]** 140 instructions each, at most 1.0% of expressions' instructions and 0.25% of scan's if all went; an operation that is unique could take its new tag and argument in place (`Rc::get_mut`, as R3) or the forward's table could be applied to the one cell, not rebuilt |

The go/no-go of stage 0 asks whether to rework §1.2: the table's per-site counts need no change,
the "94 M" footnote and the correction above do, and the one real gap is R7. Stages 1 and 2 can go as
planned. Stage 3 (R4) is stronger than planned, since its reach is certain.

**Findings that belong elsewhere**, filed from the stage:

- The value census's `Rc::new(Handler::Fold { .. })` in `effect::handler_for` is not counted
  (`new_handler` is): the census says 0.27 M handlers where there are 4.75 M.
- The same commit built outside `.claude/worktrees/` (plain `cargo`, no kache) runs expressions in
  **320.5 G** instructions; built in a lane worktree through kache, **310.7 G** (-3.1%), matcher and the
  others alike in direction. Whatever the compiler cache changes (codegen units, inlining), a
  benchmark number from the main checkout and one from a lane differ by 3% for the same source. Not
  investigated here.

## 4.2 Stage 1 results (SW-2462, 9 Nov 2026, Sonnet): R1, a resumption is one object

**[measured]** throughout: native instructions retired (`/usr/bin/time -l`), five runs of each
program, the baseline and the changed executables both built in the lane worktree through
kache with the same commands (`stitchwort build --native` against the release runtime
library), at the comparison sizes of `bench/compare/programs.toml`.

**What changed.** `Fun::Resume(bool, Resume)` and `Fun::StateK(Resume)` hold the resumption's
fields (`handler`, `rest`, `pending`) themselves; `Rc<Resume>` is gone. Differences from §2.1:

- `translate`'s resumption needs the operation too. Rather than a fourth field in every
  `Resume` (which would make every `Fun`, closures included, a word bigger), it is a new
  variant, `Fun::TranslateK(Rc<TranslateResume>)`, with `TranslateResume { resume, op }`:
  two objects, on a path these programs hardly take (matcher: none).
- The lazy flag comes first in `Fun::Resume`, so the fields fill the word after the tag:
  `size_of::<Fun>()` is 64 and a compile-time assertion keeps it there (`Rc<Fun>` is 80 bytes,
  the size class it had).
- A state route's loop keeps a second reference to the `StateK` function value (the same
  `Rc<Fun>` as `k`) in place of the second `Rc<Resume>`; `state_step` moves `rest` and
  `pending` out of it when it is unique (`Fun` has a destructor, so the handler is cloned
  and dropped with the function). `sw_unwind_resume` pushes that function value as it is.
- `resume_lazily` copies the three fields (a lazy resumption's apply), as predicted.
- Counters: the `Rc<Resume>` and wrapper rows of the stage 0 report are now one row per
  route kind, "resumption (Fun::Resume / StateK)". The value census no longer has a
  `resume` row.

**Instructions retired** (G; five runs each, min to max):

| | before | after | change | the note's estimate |
|---|---|---|---|---|
| expressions | 310.639 (310.638 to 310.643) | 305.434 (305.377 to 305.548) | **-1.68%** | 2.2 to 3.2% |
| scan | 297.625 (297.530 to 297.737) | 292.885 (292.799 to 292.973) | **-1.59%** | 2.2 to 3.2% |
| matcher | 68.213 (68.193 to 68.224) | 67.971 (67.962 to 67.982) | -0.36% | about 0.6% |
| bridge | 106.699 (106.653 to 106.751) | 105.899 (105.864 to 105.981) | -0.75% | about 1% |

The runs agree to 0.02% before and 0.04% after (bridge 0.1% and 0.1%), so the differences are
not noise. The bar for keeping the change was 60% of the low estimate, 1.3%: expressions and
scan clear it, at 76% and 72% of the low estimate (52% and 50% of the high one, 3.2%). The
saving is **105 instructions per resumption removed** on expressions (5.2 G over 49.2 M) and
100 on scan (4.74 G over 47.5 M), under SW-2433's 143 for a childless object and this note's
140 to 200 for one with children. A likely reason: the removed `Rc<Resume>` was made and
freed beside a `Fun` that still takes the same path, and the `Fun` now has 24 more bytes to
write and read back. Not tested; the next stages' estimates should use about 100 instructions
per object, not 140.

**Objects built** (call counts, expressions; before from stage 0, after from the same
report on this change):

| | before | after |
|---|---|---|
| `Rc<Resume>` | 49.18 M | 0 |
| `Fun::Resume` wrappers | 30.53 M | 30.53 M (now the resumption itself: skips 29.13 M, fold routes 1.41 M) |
| `Fun::StateK` wrappers | 18.65 M | 18.65 M (the resumption itself) |
| resumption objects in all | 98.4 M | **49.18 M** |

Scan: 47.50 M resumptions (21.25 M skips, 3.82 M fold routes, 22.43 M state routes) where
there were 47.50 M `Rc<Resume>` besides their wrappers. Matcher: 2.54 M. Bridge: 9.52 M. The
step and effect counts (`steps`, `pushes`, `routes`, `forwards`, `resumes`...) are
unchanged: the effect tests of `stitchwort-rt` pass as they were, with no snapshot touched.

## 5. Recommendation

**The problem.** Our two slowest programs, both parsers, spend about half their time
making and freeing small objects. A third of all the objects they make are built by the
effect runtime for its own bookkeeping, and nearly all of those are thrown away within one
step: about 14 for every operation the parser performs (measured counts).

**The change.** Stop making the ones that aren't needed, without changing how operations
find their handlers: a resumption made as one object instead of two; cells the runtime
takes apart reused for the next cell it builds; a perform's `bind` folded into the
operation itself, as the monad laws allow; and no resumption at all for the parser's state
handler, whose clauses can't use one. Five small lanes, about 7–8 lane-hours with the
counters, each measured before the next.

**What it should do.** About 11% fewer instructions on expressions and scan (estimated,
range 9–13%), about 5–9% less time (estimated): from about 23× and 55× CPython to about 21×
and 51×. Bridge 3–5% faster, matcher and disk about 1%, the rest unchanged (estimated).
Results, messages and proofs don't change; effect and step counts do (§2.4).

**Open questions** (for the orchestrator to number):

1. *Start the plan with stages 0–2?* They change no counts and need no decision beyond
   this one. **Recommendation: yes.**
2. *May R4 change effect and step counts, as D3412 allowed for stages B–D?* Results and
   messages are unchanged; step limits are reached later or not at all. **Recommendation:
   yes, the same rule as D3412.**
3. *Is a 1.1× gain on the parsers worth about 8 lane-hours, given D3430's "biggest slice
   of the pie"?* The slice here is the runtime's 36% of objects, inside the 50% that is
   memory work: it is the biggest slice the runtime itself owns. Closures (§2.9) are the
   next. **Recommendation: yes; run stage 0 first, which costs 45 minutes and checks the
   counts every estimate rests on.**

## 6. What I didn't cover

- Nothing was run; every saving is estimated from SW-2433's measured cost per object, and
  the "70–100% of performs reach a `bind`" in R4 is a guess that stage 0 checks.
- `translate`'s routes and lazy resumptions on these programs weren't counted apart
  (assumed small from the census's `Fun::Resume` total).
- mimalloc's size classes are from its bin scheme as I know it, not checked on a run.
- Divergence-indexed folds (`foldCompD`) and open-row handlers run the library's fold
  (operations-in-place.md §10); R4 helps them (it is in `bind`), R5 doesn't.
- The JavaScript backend is untouched, as D3410 decided for stage B.

## Sources

- Ningning Xie and Daan Leijen, "Generalized Evidence Passing for Effect Handlers",
  ICFP 2021 ([PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf)):
  §2.8 short-cut resumptions as a queue or array; §2.10 bind-inlining, "if no operation
  performs a full yield, no allocation happens along this path"; §5 "both Koka and OCaml
  still allocate at each operation (for example, OCaml allocates a continuation object
  per resumption)", and the tail-resumptive optimisation off makes Koka "always allocate a
  resumption … 10× slower".
- K. C. Sivaramakrishnan et al., "Retrofitting Effect Handlers onto OCaml", PLDI 2021
  ([arXiv](https://arxiv.org/abs/2104.00250)): small heap-allocated fibers, one-shot
  continuations.
- Effekt (capability passing), Eff, Lean's `EStateM`: as summarised in
  operations-in-place.md §4; nothing here depends on them. Lean's reset/reuse
  (Ullrich and de Moura, "Counting Immutable Beans", IFL 2019) is the model for R2 and
  R3: reuse a unique cell just taken apart for the next one built **[lit, from memory]**.
