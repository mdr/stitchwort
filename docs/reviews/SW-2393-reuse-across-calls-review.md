# SW-2393: independent review of "reuse across calls"

SW-2393, 8 November 2026, Opus, paper lane: code and documents read,
nothing built or run. It reviews
[docs/proposals/reuse-across-calls.md](../proposals/reuse-across-calls.md)
(SW-2384). I had no part in writing that note.

Labels: **[checked]** read in our code for this review, **[inferred]** my
reasoning, untested, **[not re-checked]** from memory, not looked up today.

## Verdict

**Sound with changes.** Passing the emptied cell to a copy of the callee
adds no new way for a live cell to be overwritten. Tokens are still made in
only two places (`Unpack` and `DropReuse`), and only from a cell with a
count of 1. They are still only moved, and every consumer still checks the
count. The note's soundness argument is right on the main point. It is
wrong, or incomplete, in three places that the implementation has to fix
first:

- the run-time check does not cover plumbing mistakes (F1);
- built executables would lose the variants (F2);
- programs whose maps are shared would get slower (F3).

The variant count also needs a real bound (F4). The estimate's upper end is
not supported (F7).

None of the findings is a hole in memory safety. F1 is the one that could
give wrong answers, and only if the implementation has a bug; it can be
made structurally impossible.

## What I checked, and why it holds

**What "count 1" means after the fields are moved out.** The count is the
number of references to the cell itself. Fields moved out of the cell don't
point back into it. So a count of 1 at `Unpack` still means nobody else
holds the cell, however many of its old fields are still in use
(`machine.rs` `Unpack`; `n1.rs` `unpack`) **[checked]**. I looked for
uncounted aliases and found one kind: TRMC's hole cells
(`prims::fill_hole`, which writes through `Rc::as_ptr`). They are never a
token. A hole cell has a count of at least 2 while the loop runs (its
predecessor's field and a register, and `Fill` clones the new cell in). The
twin never matches on it, so no `Unpack` or `DropReuse` is ever applied to
it **[checked: `trmc.rs` module comment, `machine.rs` `HoleOp::Fill`]**.
The statement "count 1 means unique" will stop being true if borrowed
parameters arrive (in-place-reuse.md stage 3, which the note itself
mentions for `shape`). When they do, `Unpack` must not make a token from a
borrowed value. That applies to today's local tokens too, but passing
tokens down makes a mistake there travel further.

**Each case in the brief:**

| Case | Holds? | Why |
|---|---|---|
| Shared cell | yes | `Unpack` on a shared cell copies the fields and leaves the token `Erased`. A passed `Erased` token makes the callee's `CtorReuse` allocate (`machine.rs` matches `Value::Data` with `unique`; `n1.rs` tests `TAG_DATA`, the length and `unique`) **[checked]**. |
| The cell's fields still read after the call | yes | The fields were moved into slots (unique case) or cloned (shared case). The callee overwrites the cell's field array, which no slot points into. |
| A closure captured the cell | yes | While the closure is alive its environment holds a reference, so the count is at least 2. Tokens can't enter a closure: `builds` doesn't look into lambda bodies, and a `Closure` captures only IR expressions, which never name the token slot **[checked: `code.rs` `builds`, `Expr::Closure`]**. |
| Multi-shot resumption | yes | Continuations are lambdas (heap data). A resumed body reads its captures through `Captured`, which clones them, so the count is at least 2 while the environment lives. The effect natives run functions on fresh frames that finish before they return, and the runner's captured frames never include a function's (`trmc.rs` "Effects"; `machine.rs` `TailPrim` releases the frame, token included) **[checked]**. A function holding a token across a non-tail effect `Prim` keeps it in its own frame, which no resumption copies. |
| Error exit, out of steps or frames | yes | Native exits release every register that may hold a value. `maybe_full` starts with every parameter full, so a token parameter is included (`n1.rs` `maybe_full`, `exit_now`). The machine clears its frames and registers **[checked]**. |
| Tail call | yes | `TailCall` copies its operands out, then releases the old frame (`machine.rs` `replace`; `n1.rs` releases `left` before `return_call`). A self tail call in native code is a jump with the arguments as block parameters, so the token parameter is passed again **[checked]**. |
| TRMC | yes, if twins are excluded | The note leaves twins alone. The pass must also skip the `[cells#N]` helper copies, and must never make a variant of a twin. A twin may still call another function's variant with a token of its own, which is fine. |
| A variant calling itself | yes | There is at most one variant per (global, size), so recursion calls `g′` again and the fixed point terminates. Each frame holds at most its passed token and its own, which is frame-limited. |
| A token the callee never uses | freed, later than today | The callee's `Return`/`TailCall` releases it with the frame. Today an `Unpack` that keeps no token (`NO_REG`) frees the cell at once. So an unspent passed token lives until the callee's frame ends, for example minView's `Tip` case. That is still one cell per frame. Both back ends release in the bytecode's order, so allocation traces still agree. |
| A token claimed in one arm, then listed again after the join | yes (as today) | `code.rs` restores `self.tokens` after each arm. Code after a non-tail `match` can claim a register that the arm taken at run time has already emptied with `mem::take`, so it sees `Erased` and allocates. Passing that `Erased` value to a variant is equally harmless. |

**Steps and frames (D1253).** I agree with the note: they don't change. A
call to `g′` enters one frame where the call to `g` did, the pass runs after
`optimize` and `trmc::apply`, so no inlining decision changes, and both
runners count one step per frame entered **[checked: `lower.rs` line 186,
`n1.rs` `Call`/`TailCall`]**. What does change: allocation traces (more
reuse events, and frees that come later), lowering snapshots, call counts,
profile rows, and depth notes (F6).

## Findings

### F1. The run-time check doesn't cover plumbing mistakes (high: required before implementation)

The note says "even if the analysis were wrong … the run-time test in
`CtorReuse` falls back to allocating". That is true for mistakes about
*whether* a token gets spent. It is not true for mistakes about *which
register* holds it, and the new pass adds exactly that kind of code: it
renumbers slots to make room for a parameter, and it makes a call carry an
extra operand.

- **Native code trusts that a token's fields are already empty.**
  `n1.rs` `ctor_reuse`'s fast path writes the new fields over the old ones
  without dropping them. Only `Unpack` and `DropReuse` make tokens, and both
  empty the cell first, so this is correct today. The machine assigns
  through `Rc::get_mut` and so drops the old fields. Suppose a unique `Data`
  value with live fields reaches the token parameter, through a renumbering
  slip or a variant called with its arguments shifted. Native code would
  then leak those fields and the machine would free them. The two back ends
  would disagree, though memory stays safe.
- **The IR reading the token slot gives wrong answers.** Suppose the
  renumbering leaves an original slot at index `params`. Then the body's own
  `let x := …` writes the token register, or reads the emptied cell back as
  `x`. `CtorReuse` then takes `x` with `mem::take` while the IR still needs
  it. Example: `def f (t: T) := let x := g t; Pair x x` with `x` at slot 1,
  and a variant whose token is also slot 1.
- **A variant used as a function value would receive a real argument as its
  token.** `Global`, `Pap` and `Closure` of `g′` must never happen.

**Required:**

1. `Program::validate` checks, for every variant, that the token slot is
   never read or bound by the IR, and that no `Global`/`PartialApp` names a
   variant.
2. `code.rs` asserts in debug builds that the operand in the token position
   of a variant call is a token register: a `Unpack`/`DropReuse` token
   temporary, or the body's own token parameter.
3. Reuse a tested slot-shifting routine (trmc twins add two parameters, so
   the precedent exists) rather than writing a new one.

### F2. Built executables would lose the variants (medium: required)

§4 (b) step 3 says nothing changes in `codec`/`wire` or the standalone image
format. But `stitchwort build` embeds the *lowered `Program`*, and the
reader rebuilds the bytecode with `code::compile`; the image itself isn't
written (`codec.rs` module comment) **[checked]**. The proposed side tables
`reuse_variant`/`token_param` are new data on `Program`. If they aren't
encoded, a built executable calls `g` everywhere and never fills a token. It
stays sound, but it is slower, and its allocation trace differs from
`run --native` on the same source.

**Required:** keep the information on the global itself rather than in side
tables, for example `GlobalKind::Function { params, token: Option<(Slot,
usize)> }`, and give each original call site its redirect target. Encode
it, bump the format version, and validate it in the decoder ("reading is
total"). Equivalently, the redirect can be decided in `code.rs` from the
global's own flag. Then `compile` needs nothing beyond the program it
already reads.

### F3. Shared maps would get slower (medium: required)

Under (b), every constructor in a variant that was a plain `Ctor` becomes a
`CtorReuse` on the passed token. In native code a failed `CtorReuse` takes
the cold path: spill the operands and call the runtime helper
`sw_ctor_reuse` (`n1.rs` `ctor_reuse`, `slow` block) **[checked]**. A plain
`Ctor` builds the cell inline (`new_cell`). So wherever passed tokens are
mostly `Erased`, each rebuild trades an inline allocation for a helper call.

- **Shared tree:** `let m2 := m.insert k v; use m m2`, with `m` still live.
  Every unpack on the insert path finds the cell shared, so every level
  passes an `Erased` token down, and every `Keep` rebuild misses. matcher
  (backtracking holds the message), memo tables and any search that keeps
  old states are in this class. The note scores matcher "≈ 0". It could be
  slightly negative.
- **Every insert, once:** at the bottom of each insert, the `Tip` arm's new
  leaf (`Bin 1 Tip key value Tip`) claims the passed token, because it is
  the only one in hand. That level's `balance′` is then called with the
  emptied register, and its `rebuild` misses. The count of reuses is the
  same either way; the miss costs one helper call.

**Required:**

1. In native `ctor_reuse`, test for an `Erased` token (tag 0) before the
   shape test and branch to the inline `new_cell` path. An `Erased` token
   needs no drop.
2. Benchmark a shared-map program alongside dijkstra, and expect no
   regression.

### F4. The number of copies needs a stated bound (medium: required)

"Wants a token of size `n`" is transitive up the call graph: `g` wants `n`
if it builds an `n`-field constructor that no local token claims, *or*
calls something that wants `n`. For sizes 1 to 3 (`Some`, cons cells,
pairs, triples, records), almost every function wants a token, because
almost everything eventually builds a pair or an option. Variants are made
on demand, wherever a caller has a spare token of that size and calls a
wanting function, and so on down. So the number of copies is bounded only
by globals × distinct sizes, and that is the bound for native compile time
too, since Cranelift compiles every body that `main` reaches. The note cites
`COPIES = 64` and Mercury's two versions as precedents, but sets no bound of
its own **[inferred]**.

**Required:**

1. A depth limit: a token goes into `g′` only if some path spends it within
   `d` direct calls. `Map.Tree` needs `d = 4`: `insertWith`, then `%match1`,
   `balance`, `rebuild`, then `singleL`/`doubleL` (with `bin` inlined; check
   that against the printed IR).
2. A cap on variants per program, and on IR growth (say +25% of nodes), the
   same kind of cap as `COPIES`.
3. A variant count printed for dijkstra, disk and a sample of AoC days,
   plus native compile time before and after.

### F5. The claim order between a local constructor and a call needs specifying (low-medium: required)

`code.rs` compiles a constructor's arguments before the constructor claims
its token (`Expr::Ctor` calls `operand_ops`, then `rposition`)
**[checked]**. A variant call nested in the arguments (`Node (insert x l) y
r`, or `(h a, b)` where `h` builds a pair on a rare path) would therefore
take the token, leaving the certain local reuse to allocate. The note's
"prefer local constructors … a small change to the claim order" is the
right intent. It needs a precise rule, decided before the arm's code is
compiled: an arm's calls get only the tokens beyond what its local
constructors need on one path. That means adding a `builds_local`, which
counts only `Ctor`, beside the new `builds`.

This keeps the A/B pair at today's 80.6%. It doesn't touch `Map.Tree`,
whose arms that call `balance` build nothing locally.

A related cost: the `DropReuse` heuristic in `branch` counts tokens in
hand. A passed token can therefore suppress a `DropReuse` that would happen
today, even when the passed token turns out `Erased` at run time. That is a
small loss, but it should be in the same rule.

### F6. User-visible names (low)

Variants show up in the depth note of an `E-RESOURCE` error (`shared.rs`
`deepest`/`body_name`, by body), in `run --profile` and in call counts.
Recursion that enters `g` once and then `g′` splits its frames between two
bodies in the depth note, which could change the function the note names.
`[cells]` twins already have this problem.

Fold variants into their original by name or `def` in the depth note and
the profile. Snapshots of lowered IR will change too (D2303: that churn
doesn't count against the change).

### F7. The estimate (low: restate)

- **The 15% upper end isn't supported.** The note's own arithmetic is
  10–15 ns × 23 M ≈ 0.23–0.35 s of about 3.0 s. That is 8–12%, not 8–15%.
- **The 3.0 s base isn't traced to a run.** SW-2388 reports dijkstra in
  instructions (44.0 G); SW-2371's seconds (4.49 s, 7.15 s) are older
  scales.
- **Uniqueness was measured on the p1 micro-benchmark, not on dijkstra.**
  SW-2388 measured all-unique unpacks in `insertWith`/`minView` on p1, and
  dijkstra may still share some of its maps.
- **Costs the note leaves out:**
  - three more words per call along each chain: `balance`'s four arguments
    are already twelve words plus the context and frames, likely past the
    argument registers of Cranelift's `tail` convention, so the token words
    probably go on the stack [inferred];
  - the F3 miss at the bottom of each insert;
  - tokens held to frame end instead of freed at `Unpack`.
- **The cross-check is on another base.** The SW-2371 B scratch measured
  about 25 ns saved per reused node, but on a base 2.5 s slower than std
  that nobody has explained, and including saved calls. Its percentage
  can't be carried over.

My estimate is **4–10% on dijkstra [inferred]**: an absolute saving of
0.15–0.35 s, if the cells are unique there. It is about half that after the
cell cache (d), as the note itself says. This is still worth doing, and it
also helps the other structures, but the lane should report instructions
*and* reuse counts per site, so that a small gain can be attributed.

### F8. "Who else benefits" is overstated (info)

- **Lists get nothing.** `List.map`, `filter` and `append` are TRMC twins,
  and twins are excluded.
- **Small record methods already reuse.** `state.withPosition p` is far
  under `INLINE_SIZE` = 24 (`opt.rs`), so it is inlined and reuses locally
  today. (b) adds only helpers too big to inline, or recursive ones.

The note should say so, so that nobody expects list or record speed-ups.

## Alternatives the note may have passed over too quickly

- **The token as an extra parameter of the original, with no copy.** There
  is no code-size risk. But function values (`Global`, `Pap`, `value{g}`
  adapters, `exact`) assume the source arity. They would then need an
  adapter that passes `Erased`, or a wrapper frame, and a wrapper frame
  changes step counts. Copies are simpler. The note's choice stands.
- **The cell cache (d) first.** It adds no new soundness surface, it helps
  binary-trees, which (b) can't, and it is already scoped (60–90 min). The
  note's own figure is that (d) takes half to two thirds of (b)'s dijkstra
  gain. Since D3413 is still open, the order is a real choice. Both are
  worth having (D3420 asks for the invisible optimisation), and they touch
  different code, so they can run in parallel. This is a sequencing call
  for the orchestrator, not a reason to drop (b).
- **(a)+(c), inlining.** The note's analysis is right: inlining `balance`
  alone puts the `Bin` next to the wrong `Unpack`, because of the lifted
  `%match1`. Once (c) is in, (a) would also save the calls, which (b)
  can't. It stays the fragile option, sensitive to sizes, but it is what
  the note's step 3 measures anyway. I agree with the order.

## Prior art

The note says nobody passes a token across a call automatically. For *reuse
tokens in a reference-counted language* I found nothing either (a search on
8 Nov 2026 turned up only the intraprocedural Perceus and frame-limited
reuse papers). The *mechanism*, though, is well trodden, which makes this
less of a leap than the note suggests:

- **Mercury CTGC:** automatic and across calls, with *procedure copies*
  ("reuse versions") selected at call sites. That is the same structure as
  `g[reuse]`, in the other direction (the callee takes apart the caller's
  dead data). **[as cited by the note]**
- **Destination-passing style:** the caller supplies the memory the callee
  builds its result in, as a hidden argument. Shaikhha et al., FHPC 2017,
  do it automatically for array programs, and OCaml's and our TRMC are DPS
  for one hole **[not re-checked]**.
- **MLKit region inference:** region-polymorphic functions take the regions
  to allocate into as hidden parameters, inferred automatically
  (Tofte–Talpin) **[not re-checked]**.
- **Hofmann's LFPL `◇`** (ESOP 2000) and **Koka FP²'s reuse credits:** the
  same thing explicit and typed: the space of a dead cell, passed to a
  function that builds **[not re-checked / cited by the note]**.

So the novel part is inferring it, without annotations, on top of Perceus-style
dynamic checks. The dynamic check is what makes inference safe to get
wrong.

## Required changes before implementation

1. F1: validation of the token slot and of variants as values, a debug
   assertion on token operands, and a reused slot-shifting routine.
2. F2: variant information on the global, encoded, versioned and validated
   in the codec.
3. F3: an inline miss path for `Erased` tokens in native `ctor_reuse`.
4. F4: a depth limit, a cap on variants and on IR growth, with counts
   reported.
5. F5: a precise rule that local constructors claim first (`builds_local`),
   covering the `DropReuse` heuristic too.
6. Exclude TRMC twins and their `[cells#N]` helper copies explicitly.
7. Restate the estimate (F7) and "who else benefits" (F8) in the note.

## What the implementation lane's tests must include

Each test checks results, step and frame counts, and machine against native
allocation traces (with `trace_refcounts` where leaks matter):

1. **Map paths:** a `Map.insert` path, a `popMin`/`minView` path, and inserts
   that force `singleL`, `doubleL` and `doubleR`. Check the per-site reuse
   counts.
2. **A shared map:** `(m, m.insert k v)`, with both maps then read. Results
   must be correct, no shared cell may be reused, and native instructions
   must not regress (F3).
3. **Held tokens:** a token held across recursion (`minView`), across an
   `Apply` of a user closure (`insertWith`'s `f`), and across an effect
   operation whose handler resumes twice. The two-resumption case is checked
   against the reference evaluator.
4. **Unspent and early exits:** an unspent token must be freed by the end of
   its frame, with a balanced trace and no leak. A run that hits the step or
   frame limit midway through a token chain, in native code, must not leak.
5. **Tail calls:** a variant reached by tail call, and a variant's self tail
   call (the native jump path).
6. **Claim order:** a variant call inside a constructor's arguments. The A/B
   pair must stay at 80.6% or better.
7. **Validation:** `validate` rejects a variant whose body reads the token
   slot, and a `Global`/`Pap` of a variant. A codec round trip of a program
   with variants gives the same bytecode.
8. **Exclusions and naming:** TRMC twins get no variant (`List.map`'s
   lowering is unchanged), and a snapshot shows `[reuse]` naming and the
   depth-note folding.
9. **Size:** the variant count and IR growth on dijkstra and a sample of
   AoC days stay within the cap.
10. **Benchmarks:** `bench:compare` on dijkstra, disk, binary-trees (which
    should be unchanged) and a shared-map case.

## Decisions

None that are Matt's beyond D3420, which already covers going ahead. One
small user-visible point can be settled by the orchestrator, or by Matt if
he wants it: whether `run --profile` shows `[reuse]` variants as rows of
their own or folds them into their definition. I recommend folding, with
the variant split available behind the profiler's detail flag (SW-1810).
