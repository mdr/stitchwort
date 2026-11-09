# SW-2565 review: borrowed parameters, stage B1

Independent Opus review (paper lane, 9 Nov 2026) of `lane/SW-2565` at 5cbd08397 against its
base d5bd2f09d. I read the code only: no builds, no tests, no runs. Every claim below comes from
reading the code, and confidence is stated for each.

## Summary

The core argument holds. A lent value's owner is always a frame further down the stack that made
a non-tail call. It is never a tail call, a function value or a host crossing:

- the inference keeps every owned value out of a tail call's borrowed position (O4, O8);
- function values are fully owned (O7);
- the rewrite turns every count, unpack, reuse and escape of a lent register into a `Peek`,
  `Lend`, `Forget` or `Own`;
- `check` re-derives the register states and rejects the counting and reuse cases that matter.

I found no path where native code frees, reuses or writes over a value while it is lent.

The problems are on the edges:

- **F1.** A pattern in valid programs makes the compiler panic.
- **F2.** The machine's error exit got very slow when it runs out of frames deep in a borrowing
  function.
- **F3.** The machine's check has gaps.
- **F4.** One fallible instruction doesn't save its position.
- **F5.** The host-call trap is unguarded, but nothing reaches it today.

**Verdict: fix first (F1, F2, F4: three small fixes, about an hour in all), then merge with
follow-ups (F3, F5-F9 and the tests in §6).**

Top five:

1. **F1:** `g x x`, where `x` is lent and `g` takes it first borrowed and then owned, makes the
   compiler panic. Fix the rewrite and add a test.
2. **F2:** `release_failed` runs a full dataflow pass and a scan of the constant pool for every
   frame. Out of frames at the machine's 2,000,000-frame limit, that is seconds to minutes.
   Compute it once per body.
3. **F4:** `TailApply`'s exact path doesn't `save!()`, so the error exit can forget the wrong
   registers.
4. **F3:** the machine's check covers `Forget` only. `Own` and `Peek` are unchecked, and `check`
   lets `Forget` drop an owned (`Shared`) register.
5. **F5:** guard the host crossing: a `Fun::Global` with borrowed parameters must never be
   applied from outside.

| # | Finding | Severity | Confidence | Size |
|---|---|---|---|---|
| F1 | Same lent register at a borrowed and then an owned position of one call: compiler panic | medium-high | high | S |
| F2 | Error exit's `lent_at` is O(frames × (pool + body)) | medium | medium | S |
| F3 | Machine check sees only `Forget`; `check` accepts `Forget` of a `Shared` register | medium | high | S |
| F4 | `TailApply` exact path: no `save!()`, so `lent_at` reads a stale pc | low-medium | medium | S |
| F5 | Host `global(g)` then `call` into a borrowing global: unguarded (not reachable today) | low | high | S |
| F6 | A body that jumps back is scanned only in part, silently (latent) | low | high | S |
| F7 | `STITCHWORT_NATIVE_PARTS` no longer exercises lending bodies; the rewrite can push them past the large-body bounds | low | high | S |
| F8 | Not rebased onto SW-2559 (exact cell-cache room); numbers predate it | low | high | S |
| F9 | 2021/01 +1.16%: likely a static `Shared` that is unique at run time (perf only) | low | low | M |

## 1. Soundness of the inference

What I checked, and found sound:

- **Tail calls passing a lent value on (O4, O8).** `rules` marks the callee's parameter owned for
  any tail call that passes a value with `owned(st)` at a borrowed position, whether marked
  `MOVE` or not. The outer loop reruns every group, and the bodies that take no part (lambdas,
  constants, the entry), until no mark lands on an earlier group. `check` rejects "tail call
  lends owned register" independently. `Plain` (loaded from a pool entry that holds no
  reference) is allowed. That is right: such a value needs no drop, and the machine's `forget`
  passes it (`usize::MAX`). Native `TailCall` now hands only owned-position operands to
  `count_step`'s exit. Lent operands are in neither `live` nor the fetched list, so nothing drops
  them. The self tail call's jump to `top` passes words, and `maybe_full`'s start set leaves out
  borrowed parameters.
- **Jumps that merge lent and owned paths.** `join` errors on lent meeting owned, `Plain`
  meeting lent, and two lent values with different roots. The inference turns each into *merge*
  marks, so at the fixpoint the rewrite's `forward` never meets one. It panics if it does, and
  `check` reports it again. `Lent` meeting `Empty` gives `Lent`. On the empty path the machine
  then `Forget`s an `Erased` register (it passes) and native code does nothing, which agrees with
  native's may-hold sets.
- **Effects and continuations.** Every operand list other than a direct call's goes through
  `operands` with no borrowed positions:
  - a lent register moved there is `Own`ed first, and one not moved is cloned (an increment), in
    `Closure`, `Pap`, `Ctor`, `CtorReuse`, `Apply`, `TailApply`, effect `Prim` and `TailPrim`;
  - `check`'s `kept` rejects any `MOVE` of a lent register at an owned position.

  Nothing suspends a frame and resumes it later. An effect with `Ret::Reg` waits as a call does,
  and multi-shot resumption works on closures, which own what they capture. So a lent value can't
  outlive its owner through a resumption.
- **Partial application.** `Pap` and `Global` instructions anywhere make the named global (and
  its reuse copies) fully owned (O7). Every runtime `Fun::Global` comes from `function_value`.
  Its callers are the machine's `Global` and `Pap` instructions, native `sw_global` and `sw_pap`
  (the same instructions), and the host's `Machine::global` and `NativeExecutor::global` (F5).
  The constant pool holds no function values (`code.rs` builds only `Fun::DoneK` there).
- **Reuse and uniqueness.** O5 owns any root unpacked with a token or dropped for reuse. The
  rewrite asserts that a lent `Unpack` has no token and turns it into `Peek`s, so a lent cell
  never reaches the unique path. An owned value lent and also moved in the same call has its
  `MOVE`s stripped and is cloned at the owned position, so the callee sees a count of at least
  2. `check` rejects "lends owned register and moves it".
- **Unused fields of an `Unpack`.** These are the fields with no register (`NO_REG`; the brief
  attributes their drop to SW-2511). A lent `Unpack` skips them, so it neither drops nor
  increments them, which is right because the cell isn't consumed. An owned `Unpack` is
  unchanged.
- **In-place reuse copies.** `Fixed::Last` keeps the token owned, and the other parameters of a
  copy may borrow.
- **Writes over a lent register** (`write_dst`). The rewrite emits `Forget` first. When the
  instruction also reads the register, it writes a scratch register and then `Take`s it. A call
  whose destination is the register of an owned value it lends has no `Drop` after: native
  `assign` drops the old value after the call, and so does the machine's assignment. Both are
  sound and leak nothing.
- **Error exits and E-RESOURCE.**
  - Native code: lent registers are never in `full`, so exits don't drop them. The `live` set at
    a `Call` keeps the owned values it lends, so a callee's failure releases them in the caller.
  - Machine: `release_failed` forgets every frame's lent copies before releasing any register,
    so the `count > 1` assertion holds. It also forgets a failed tail call's arguments at
    borrowed positions. F2 and F4 are about how it finds the lent registers.
- **Large bodies (SW-2557).** SW-2557 is already in the base: 814145c7c and 22cecd1eb are
  ancestors of d5bd2f09d. A body that lends always uses Cranelift variables (`in_file =
  !lends && …`), so the register file's exit, which drops every register, never sees a lent
  value. A body that doesn't lend can still be in a file and call a lending function. Its kept
  owned arguments stay in the file and are dropped on exit, which is correct.
- **Consumers of the bytecode.** Only `n1.rs`, `machine.rs`, `census.rs`, `code.rs` and
  `borrow.rs` match on `Instr`, and all of them handle the new instructions. Jump tables and
  number tables are remapped. Operands of instructions that weren't rewritten still index
  correctly, because `new_ops` starts as the old list.

## 2. The host-call issue (F5)

All the entry points the brief lists:

| Entry | How it reaches code | Lends? |
|---|---|---|
| driver `test_run` (machine and native) | `global(g)` of a test, a constant with no parameters | no arguments |
| partial tests | `global(g)` of a constant giving a `Delay`; `run_partial_on` steps closures | function values: O7 |
| `run NS.name` | the program's entry term, lowered with `Global`/`Call` instructions | entry has no parameters |
| native trampolines (`enter`, `enter_constant`, SW-2543's per-test ones) | entry or constant, no parameters | no arguments |
| effect loop (`run.rs`: `k`, `done`, `rest`, `reply`, `inject`, `call`) | function values the program built | O7 |
| counterexample search | `machine.call(function, args)`, with `function` from the entry's pair: a `Global` instruction | O7 |
| playground (`crates/web/src/live.rs`) | runs the entry; no `.call(` | none |
| rt tests (`effect_runtime.rs`, `state_match.rs`, `effect_alloc.rs`) | `lower_global` makes the entry the global's value, then `call` | O7 |

**None is reachable today.** The one direct `Machine::global(g)` + `call` with arguments is the
lane's own test (`the_machine_catches_a_loan_outliving_its_owner`, `check` given `Nat(5)`). It
works because a `Nat` isn't counted.

If one became reachable:

- **The machine** would panic at the callee's `Forget` whenever the host's argument is the only
  reference.
- **Native code** (`sw_apply_prepare` or a `value{g}` adapter calling the body with owned words)
  would never drop the argument, so it leaks one reference. It would not corrupt memory: an `Own`
  of it only increments a live cell.

**Recommendation: mark, and assert.**

- Mark: have `borrow::apply` treat every global the host may name as used as a value: the
  program's roots from `lower_roots`, tests and exports. O7 then owns their parameters, at no
  cost to the inner calls.
- Assert: in the machine's `apply` and in `sw_apply_prepare`, panic with an internal error when a
  `Fun::Global` whose code has any borrowed parameter is applied. A future host path then fails
  loudly in tests instead of leaking natively.

"Lend on entry" (the host keeps its arguments and drops them after the call) would touch
`put_args`, `apply` and every native apply stub. It isn't worth it while no host path needs it.

## 3. What the validator and the machine catch, and what slips past both (F3)

`check` holds the discipline for every instruction kind. I went through `check_one` arm by arm:

- moves, drops, counted fields, unpacks, reuse and tokens of a lent register are rejected;
- returning one, or a frame ending while it holds one, is rejected;
- `Peek`, `Lend` and `Own` must read a lent register;
- a call's lending is checked against the callee's flags (the same `Code::borrowed` that native
  code and the machine read);
- the read-only instructions (`Switch`, `Test`, `NatPred`, `IntOfNat`, `IntNegSucc`,
  `TextChars`, non-consuming `Prim`s) read by reference in the machine and need no rule.

Gaps:

1. **`check` accepts `Forget` of a `Shared` register** (`borrow.rs:1627`: only `Own`, `Fresh`
   and `Plain` are refused). Native code would leak it. The machine would drop it quietly with
   the assertion passing (`Shared` means there is another reference). The allocation trace would
   agree, because neither side records an event. So all three nets miss a leak of this kind. The
   rewrite never emits it today. Fix: `Forget` accepts only `Lent` or `Empty`.
2. **The machine checks only at `Forget`.** `Own` (machine.rs:1594) increments in the trace
   without checking. Suppose an owner let go early and the borrower then `Own`s the value
   (returns it, stores it). Native code increments a freed cell, and the machine carries on with
   a count of 1. `Peek` and passing a value on are unchecked too, but the chain usually ends in a
   `Forget`, which does catch it. Fix: assert `strong_count > 1` in `Own` (before it becomes
   owned) and in `Peek`'s source. Both are cheap, and both use the logic `forget` already has.
3. **Wrong uniqueness decisions are invisible to the machine by design.** Its counts are native
   code's plus the number of live lent copies. So if a future bug let a frame's own reference be
   tested for uniqueness while that frame also lends it, native code would see 1 and reuse the
   cell, and the machine would see 2 and copy it. The only net is allocation-trace agreement
   (`same_trace`), and only on the programs it runs. Today `check` rules out the one way this
   could happen in a single instruction, and a frame can't act during its own call. Follow-up:
   run `same_trace` under the fuzzers (`task fuzz:*` in compute mode), so it isn't limited to
   the hand-written programs.
4. A failed `check` is a panic in the user's compile, by design ("internal error"). I'd keep that
   rather than fall back silently, so that a bug shows up. It makes F1 user-visible.

## 4. Interaction with SW-2559 and the in-place paths

- **SW-2559** (03865e32f, exact cell-cache `room`) landed on main after this branch's base. The
  branch hasn't been rebased onto it.
  - Textually, both touch `n1.rs` near line 4341: the branch adds the new instruction arms just
    above `other => unreachable!`, and main adds the `room` update in the cell-take code. Expect
    at most a trivial conflict.
  - Semantically there is no interaction: a lent value never reaches `Unpack`'s unique path, the
    cell cache or `full()`.
  - But *fresh* exists because of the cell cache: a fresh value is freed into it as the callee
    walks it. SW-2559 changed what a full cache costs (it now frees the cell directly). The §12
    numbers and the binary-trees result should be measured again after the rebase (F8).
- **Unpack's unused-field drop:** sound (§1).
- **In-place reuse copies:** sound (§1).

## 5. The 2021/01 +1.16% regression (F9, perf only)

1.16% of 117 M is about 1.36 M instructions. Over 2,000 input lines that is about 680 per line,
too many for a few counts per list cell. So the cost is per line or per character, in
`Parse.eachLine` / `token nat`, and not in `increasesOver`'s zip and count.

There, *fed* and *fresh* own the zipped list and `depths` as before, and `drop` now borrows,
which is a gain.

The likeliest mechanism is the lane's own binary-trees mechanism, reached a different way.
*fed*'s exception treats a register in state `St::Shared` as "known to have another reference".
That state is set by `Move` and by `Field` or `Unpack` of a shared or live value. It is never
undone when the other reference dies: after a `Move` whose copy is later moved away, the source
stays `Shared` though it is unique.

A parameter fed only such values stays borrowed. The callee walks it with `Peek`s, and the caller
then frees the whole structure through the runtime's `Drop`, where before the callee freed it
cell by cell into the cell cache. Per line, the candidates are the line's character list and the
parser state's `rest` in `Parse.eachLine` → `Parse.whole` (`chars` is kept for the error arm).

Confidence is low. To confirm: `STITCHWORT_BORROW_DUMP=Parse` on 2021/01, plus a diff of
the allocation trace's `free` events (inline versus runtime) before and after. A likely fix is to
track `Shared` through the death of the other copy, or to treat `Move`'s source as `Shared` only
while the destination is live.

## 6. Code quality and tests

Code quality is good:

- the module docs state the rules and their reasons;
- one dataflow (`forward`) serves the inference, the rewrite, the check and `lent_at`, so they
  can't drift apart;
- `Reason` names each rule.

Smaller points:

- `rewrite` is about 400 lines, mostly a near-identical arm per instruction kind: `operands` +
  `push_ops` + `write_dst` + `post`. A helper taking a constructor closure would halve it. This
  is optional.
- `lent_at` rebuilds `plain` from the whole pool on every call (part of F2).

Missing tests:

1. **F1's shape:** `g x x`, with `g` borrowing its first parameter and owning its second, and `x`
   lent in the caller. Cover both the tail and the non-tail call.
2. **Errors inside a borrowing body, machine against native.** Out of steps at a `TailCall`, a
   `TailApply` and a `Call`, and out of frames in a non-tail borrowing recursion such as
   `length`. Use `same_trace`, which also covers F4. Time the out-of-frames case at the default
   limit (F2).
3. **A function both called directly and partially applied, or used as a value** (O7),
   end-to-end on native code. Today only the inference-level unit test covers it.
4. **A lent value captured in a closure and in an effect operation's arguments,** with a
   resumption run twice (a search handler), under `same_trace`.
5. **Lent and owned meeting at a jump target** in a real program (merge), under `same_trace`.
   Today this is a unit test only.
6. **A test that `check` refuses `Forget` of an owned or shared register,** after F3.1.
7. **`STITCHWORT_NATIVE_PARTS` coverage** (F7): either keep lending bodies out of that mode on
   purpose and say so in its comment, or add a variant that turns borrowing off, so the
   large-body tests still run every body in parts.

## Findings in detail

### F1. A lent register at a borrowed and then an owned position of one call: compiler panic

`borrow.rs:1462-1480` (`operands`), `check_one` at `borrow.rs:1636-1655`. Severity
medium-high, confidence high, size S.

The bytecode compiler marks `MOVE` on a register's last occurrence in an operand list
(`code.rs:788-796`). Take `h x = g x x`, where:

- `x` is borrowed in `h`: every caller of `h` lends it, keeps it, or passes a field;
- `g` borrows its first parameter and owns its second: for example, it rebuilds its second
  argument (O5) or stores it and is fed elsewhere.

The operands are `[x, x|MOVE]`. `operands` emits `Own x`, because position 1 is owned, moved
and lent. Position 0 isn't in `kept`, because `lent(x)` is still true in the pre-instruction
state. After `Own`, `check` sees `x` as `St::Own`:

- for a non-tail call, "call lends owned register x and moves it";
- for a tail call, "tail call lends owned register x".

`apply` panics with "internal error: borrowed code … breaks the discipline" while compiling the
user's program. The inference never marks this (position 1 is only an `Escapes` reason), so
nothing prevents it. Nothing in the tree hits it: the bench programs, the 56 AoC days and the
tests passed.

The program itself would be sound: after `Own` the count is at least 2. Only the check refuses
it.

**Fix (S):** when a lent register is both at a borrowed position and moved to an owned one in
the same call, leave the owned occurrence unmoved, so it is cloned (an increment).
- In a tail call, put the `MOVE` on the last *borrowed* occurrence (`all_lent`'s `rposition`
  should prefer a borrowed position).
- In a non-tail call, `Forget` the register after the call (in `post`).

Add test 1 from §6.

### F2. The error exit computes lent registers per frame from scratch

`machine.rs:363-377`, `borrow.rs:980-1000`. Severity medium, confidence medium, size S.

`release_failed` calls `lent_at` for every frame. Each call rebuilds `plain` from the whole
constant pool and runs `forward` over the body, which allocates a state vector at every jump
target and a `HashMap`. `lent_at` returns at once only for bodies with no borrowed parameter.
But a non-tail recursive read-only walk (`length`, `size t = size t.left + size t.right`) is
exactly a borrowing body, and exactly what runs out of frames.

At the machine's default 2,000,000 frames that is millions of passes. I estimate seconds to
minutes before the error is reported, where it was about one pass over the registers. This is
estimated, not measured.

**Fix (S):**
- compute `plain` once;
- memoize per code index a table of lent registers at each pc (computed lazily, or kept beside
  `Code` when it is rewritten);
- or record the lent set only for the distinct `(code, pc)` pairs on the stack.

### F3. Machine and `check` gaps

See §3. Severity medium, confidence high, size S:
- `Forget` accepts only `Lent` or `Empty`;
- assert in `Own` and in `Peek`'s source;
- the `same_trace` fuzzing follow-up.

### F4. `TailApply`'s exact path doesn't save its pc

`machine.rs:1347-1355`. Severity low-medium, confidence medium, size S.

The lane added `save!()` before `TailCall`'s `replace` so that `release_failed` can read where
the frame stopped. `TailApply`'s exact path also calls `replace(...)?`, which can fail out of
steps, with no `save!()`. Every other fallible instruction saves.

In a borrowing body, `lent_at` then answers for the last saved pc: the frame's entry, or its last
call. Its answer can name a register that held a lent value then and now holds an owned one. The
compiler's registers are reused, and owned registers not passed are released by `replace`, not
before. `forget` then drops an owned value quietly. That is either a false "a borrowed value
outlived its owner" panic, if the value is unique, or a missing `dec` event in the allocation
trace.

**Fix (S):** add `save!()` before the exact path's `replace`, and add test 2 from §6.

### F5. Host crossing unguarded

See §2. Severity low (not reachable today), confidence high, size S.

### F6. A body that jumps back is scanned only in part, silently

`borrow.rs:765-781` and `check` at `borrow.rs:1541`. Severity low (latent: the compiler
emits only forward jumps), confidence high, size S.

`forward` returns `false` at the first backward jump. For the `others` bodies, `infer` ignores
that and keeps the marks from the prefix it scanned, so an O8, *fresh* or *fed* mark from the
rest of the body is lost. `check` returns `Ok` for a body that doesn't borrow after checking only
that prefix. A future backward jump (a loop instruction) would then let an owned value reach a
borrowed position in a tail call unchecked.

**Fix:** make `false` an internal error everywhere, or own all of that body's callees'
parameters.

### F7. The large-body test mode and the bounds

`n1.rs:1245-1263`. Severity low, confidence high, size S.

- `STITCHWORT_NATIVE_PARTS=n` is documented as "every body has a register file". Bodies that
  lend are now exempt, so that test mode no longer covers them.
- `MAX_REGS` and `MAX_INSTRS` are checked *before* the rewrite, which adds `Forget`, `Own`,
  `Lend` and `Drop` instructions and a scratch register. A lending body can end up somewhat past
  `VARIABLE_REGISTERS` (128) and `PART_INSTRS` (512) and still be compiled with variables in one
  function, which is what SW-2557 guarded against. It is bounded at about +25% or less, so it is
  minor.

**Fix:** check the bounds after the rewrite, or leave headroom; and correct the comment.

### F8. Rebase onto SW-2559 and measure again

See §4. Severity low.

### F9. 2021/01

See §5. Perf only; a follow-up ticket with the measurement plan.

## Calls I made

- I didn't raise a D question. "Panic or fall back to owned when `check` fails" is a trust
  question, but keeping the panic (the lane's choice) is the conservative default, and F1 removes
  the only way I found to trigger it.
- I recommend "mark the roots, and assert", not "lend on entry", for F5.

## Tickets to file

- **Lane A, before merge (Opus, near the calling convention; about 60 min):** F1 with its tests,
  F2, F4 with error-path `same_trace` tests, and F3.1.
- **Lane B (Sonnet, about 45 min):** F3.2 (assertions in `Own` and `Peek`), F5 (mark the roots
  and assert in the machine's `apply` and `sw_apply_prepare`), F6 (assert forward-only), F7
  (bounds after the rewrite, `NATIVE_PARTS` comment or variant). Add tests 3-5 from §6.
- **Lane C (Sonnet, about 60 min, after the rebase onto SW-2559):** measure B1 again, and look
  into 2021/01 (F9): the borrow dump plus a diff of where `free` events happen.
- **Compute mode:** run `same_trace` across the fuzzers' programs with borrowing on (F3.3).
