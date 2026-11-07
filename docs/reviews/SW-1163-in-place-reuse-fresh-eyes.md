# SW-1163: the in-place reuse plan, with fresh eyes

A review of [docs/research/in-place-reuse.md](../research/in-place-reuse.md) (SW-1159,
3 Nov 2026) and its questions D2273–D2277, for Matt's decision (D2582). Read on `main` at
`92025b0e8`, 7 Nov 2026. **Reading only: nothing was built or run.** Where a number
matters and isn't in the repo, the review says how to measure it and what result would
change the recommendation.

Labels: **[checked]** read in the code or a commit, **[inferred]** my reasoning,
**[not re-checked]** from what I know of other languages, not looked up for this review.

## Summary

- **The direction is still right.** Since 3 Nov, `code.rs`'s reuse logic has changed in one
  line, and that line extends the same design: arrays' consuming natives take their operands
  the way calls do, moved in on their last use (SW-1637). Nothing in the note is wrong. Two
  parts are stale: where the report lives, and what it reports first.
- **Arrays changed the stakes.** A missed cell reuse costs one allocation. A missed in-place
  array update costs a copy of the whole array. The copy counter already says *that*
  copies happened (`prims.rs` `array_copy_note`), but not *where*. So the cheapest stage 1
  that pays is to name the site in that note, in the shipped binary. The note's hidden
  `--reuse-report` flag would only work in `alloc-trace` builds, which users don't have.
- **SW-1678 isn't day 15 itself.** Day 15's `Game.say` makes 0 copies (SW-1637, test
  `an_array_in_a_record_is_changed_in_place`). The copying program is `pushPop` in
  `examples/extract/arrays.sw`. Its `None` arm returns `state` whole, so the old array
  really is still reachable when `pop` runs. No stage of the plan fixes that, and nor would
  Lean, Koka or Roc **[not re-checked]**. It needs the diagnostic plus a documented idiom.
  A related shape, a record or pair that is only ever projected, can be fixed in the
  compiler (D2591), but no real program has shown it yet.
- **Decisions:** D2273 yes. D2274 yes, but the report moves into the shipped binary
  (D2590). D2275 yes, with its condition checked on days 17, 19 and 20 as well. D2276 yes.
  D2277 yes, since SW-593 is still in the backlog. New: D2590–D2592.

## 1. Is the note's direction still right?

**Yes.** The note's case was that `code.rs` already decides moves, drops and tokens in one
place, that native code and the playground inherit every decision, and that the trace
agreement tests keep holding. All of that still holds **[checked]**:

- `git log --since=2026-11-03` on `code.rs`, `opt.rs`, `machine.rs`, `value.rs` and `n1.rs`
  shows no change to `Unpack`, `DropReuse`, `CtorReuse`, `builds` or `branch`. The one
  change to `code.rs` is `5bbb22404` (SW-1637). `Expr::Prim` now passes
  `op.consumes()` as `moves`, so an array read for the last time reaches `set`, `push`
  or `pop` with a count of 1. That is the note's design applied to a new kind of value. It
  isn't a second mechanism.
- `opt.rs` hasn't changed since 3 Nov. `INLINE_SIZE` is still 24, `FUEL` 200, `COPIES` 64.
  The projection fold the arrays note relies on (`let_with`, "a projection out of a record
  or pair: the body moves into the arm") is unchanged.
- `Map/Raw.sw`'s `insertWith`, `balance` and `shape` are as the note quotes them. The
  file's last change, on 5 Nov, didn't touch them. So §2.2's diagnosis of `Set` (11.7% reuse
  because `balance` builds the node in another function) still stands **[checked: source;
  the numbers weren't re-run]**.

**What has changed since 3 Nov:**

1. **Arrays (SW-1637, SW-1638, SW-1639).** `Value::Array` is one `Rc<Vec<Value>>`, changed
   in place when `Rc::get_mut` succeeds and copied, with a count, when it doesn't
   (`prims.rs` `unshared`). Day 15 went from 357 s to 27 s on the machine and from 84 s to
   7 s native, with 0 copies (SW-1637's ticket). This is now the place where sharing costs
   the most: an O(n) copy, not one allocation.
2. **The copy counter and its end-of-run note** (`array_copy_note`: 10 or more copies of
   1,000 or more elements). It is in the release binary. It says how many copies and how
   large, but not which line. For SW-1678 it fires and leaves the user to guess.
3. **The runtime profiler (SW-1528, `run --profile`).** It ships, gives a row per
   definition, costs one `None` test per frame entry when off, and lists "allocation counts
   per row" as its stage 4 (`docs/proposals/run-profiler.md`). That is a better home for the
   reuse report than a hidden flag in `alloc-trace` builds.
4. **Where AoC time goes now.** Day 15's `Map` cost is gone. What's left on the `Map`/`Set`
   path, which is where helper inlining (stage 2a) would help: day 17 at about 20 µs an
   `insertWith` (8.4 s against Python's 0.24 s), day 19 at 6.5 s, day 20 at 5.9 s
   (`docs/research/aoc-2020-friction-days-10-20.md` §B). Day 11 is 5.4 s on array-backed
   grids, which only read.

**Stale or wrong in the note:**

- **§6 stage 1, "hidden, alloc-trace builds".** That was right when the report was only for
  us. Now the copy note sends users looking for the place, and they run the release binary.
  See D2590.
- **§2.2's programs** don't include an array program, and the report's counters (§4.1)
  cover only `Fields` cells. Array copies, and the increment that caused each one, should
  be the report's first event kind. The arrays note (§5 item 1) already said they belong
  together.
- **`docs/research/README.md`** lists the note's questions as "D2272-D2276". The note and
  the ticket say D2273–D2277. That's a one-line fix.
- **§1.2's "`Text.append` always copies"** is still true (`prims.rs` `TextAppend`), and it
  can't be fixed in place on `Rc<str>`, whose length is fixed. No measurement shows it hurts,
  so it stays a footnote.
- **The guide's arrays section** (`docs/guide/06-namespaces-and-library.md`, "In place")
  still says that under `--js` "every operation runs as written, on the list". SW-1638
  replaced that with version arrays. That isn't this note's error, but it is worth a ticket
  (§5, T9).

## 2. Does the plan fix the cases users actually hit?

### 2.1 SW-1678: `pushPop`

```
let drain := (List.range 0 n).foldLeft (pushed, 0) (state i =>
  match state.fst.pop with
    | Some (rest, x) => (rest, state.snd + x)
    | None => state)
```

What happens **[checked: `code.rs` `Expr::Match`, lines 763–838]**:
- `state.fst` inlines to a match on `state`.
- `state` is still live: the `Some` arm reads `state.snd` and the `None` arm returns
  `state`. So the match isn't an `Unpack`. It is `Instr::Field`, a clone of the array,
  which takes its count to 2.
- `pop` finds the array shared and copies it, once per turn.

**No stage of the plan fixes this,** and it shouldn't try to:
- **Inlining across helpers (2a)** doesn't apply: there is no constructor to reuse.
- **Borrowed parameters (3)** don't apply. `pop` must own the array to change it, and
  borrowing `state` doesn't stop it holding the array.
- **The `None` arm.** It returns the original `state`, array included, so the old array
  really is needed on that path until the branch is known. And the branch depends on
  `pop`'s result. A compiler would have to know that `pop` gives `None` only on an empty
  array to see that the copy isn't needed. Lean, Koka and Roc all decide uniqueness the same
  dynamic way, and would copy here too **[not re-checked]**.

What would fix it:
1. **Say where.** The copy note should name the definition and the native: "in
   `Main.pushPop.λ`, `Array.pop`". That is T1 below. It costs nothing on the path that
   doesn't copy, because only the copy path records the site.
2. **An idiom in the guide.** Destructure first, then don't refer to the old pair again:

   ```
   (state i => match state with
     | (array, total) => match array.pop with
       | Some (rest, x) => (rest, total + x)
       | None => (Array.empty, total))
   ```

   Here `state` is dead at the outer match, so it is an `Unpack` and the array moves out
   with a count of 1 **[inferred from `code.rs`; not run]**. The example in
   `examples/extract/arrays.sw` should be written this way too, or keep its current form
   with a comment saying it shows the copy.
3. **Only if the shape recurs, a compiler fix for the projected-only case** (D2591). Take
   the `Some` arm alone: if `state` were never used whole afterwards, only through
   `state.snd`, then matching on `state` once, at its first projection, would make every
   field read a move. `opt.rs` already does this for `let x := s.field` (the projection
   fold). Extending it to projections in argument and scrutinee positions is a pure IR
   rewrite (single constructor, total, no failure path). It wouldn't help `pushPop` as
   written, because of the `None` arm. It would help an always-give-back
   `pop: Array a → (Array a, Option a)` with `(rest, state.snd + x)` in both arms.

### 2.2 What real programs hit

- **Arrays.** Two users so far: day 15 and `Aoc.Common.Grid`, which only reads. Both make
  0 copies. Application code follows D2363 and uses domain records. Outside proofs, `.fst`
  and `.snd` appear in AoC code only in short maps over pairs **[checked: `git grep`]**.
  So today the pair-sharing cliff is the example's problem, not a user's. It will come back
  as more days use arrays, which is why T1 comes first.
- **`Map`/`Set` trees.** Every tree-heavy day pays here (days 17, 19 and 20, and §2.2's
  2024 day 9 and 2025 day 5). Stage 2a is aimed squarely at this, and the controlled pair
  in the note (7% against 81% reuse, depending only on where the constructor is written) is
  the strongest evidence in it.
- **The effect runtime.** That is SW-593's ground, as the note says.

## 3. D2273–D2277

**D2273. Extend `code.rs`'s design in stages, not a new dup/drop pass? [rec: yes]**
- Why: still the right call. Arrays just extended the design in one line, and native code
  and the playground got it for free. A separate explicit-RC IR would be a rewrite of both
  runners' calling conventions for no gain the stages can't reach.
- What would change it: if stage 2a's inlining can't lift `set_nat.sw` above about 60%
  reuse within the size bounds, because callees are too big to inline. Then the next step
  is a token passed into the callee (§3.2's custom cell). That would still be an extension
  of `code.rs`, not a new pass, so even then the answer stays yes.

**D2274. Start with the per-site report, not a `dbgTraceIfShared`-style native? [rec: yes,
in a changed form, D2590]**
- Why: still the cheapest step that measures and diagnoses at once. A native would need the
  kernel, the reference runner and JS to agree, for less information.
- The change: split the report in two, and put both halves in the shipped binary.
  - Stage 1a: the copy note names its sites.
  - Stage 1b: reuse counters per definition, under `--profile`.
- What would change it: if counting at `Ctor` under `--profile` costs over about 10% even
  when on, count only the cold paths (a token miss, a shared `Unpack`, an array copy). Then
  combine them with the profiler's exact call counts and `code.rs`'s static record of which
  `Ctor` sites have no token.

**D2275. Then inlining for reuse in `opt.rs`, before std rewrites? [rec: yes, if 1b shows
`Map.Tree.insertWith`/`balance`/`rebuild` among the top three missed sites on `set_nat.sw`
and at least two of days 17, 19 and 20]**
- Why: the A/B pair. Same algorithm, 7% against 81% reuse. No std proofs change, whereas a
  zipper `insertWith` or SW-814's fused balance means re-proving lemmas.
- What would change it:
  - If the top misses are elsewhere, for example `List` cells in parsers or `Text`, aim at
    those instead.
  - If they are `Map` but in `rebuild`'s rotations, which are too large to inline, SW-814's
    fused balance becomes the better first move.
- Keep dropping never-read bindings at entry in the same stage, or as its own small ticket
  (T5).

**D2276. Borrowed parameters only as a design note, and only if read-only increments are
over about 20% of count operations? [rec: yes]**
- Why:
  - It needs `unsafe` in the machine's registers and frame teardown.
  - Koka declined inferring it, for space safety **[not re-checked]**.
  - Arrays add no reason to do it, since array reads are primitives that already borrow
    (arrays.md §5 item 3).
- The 20% can only be measured once 1b classifies increments: by instruction (call
  argument, `Field`, `Ctor` argument, shared `Unpack`), and, for call arguments, by whether
  Lean's rules would borrow that parameter. The rules can run as an analysis only, with no
  change to code generation.
- What would change it: over 20%, and on a day whose time is dominated by counting. A
  `perf` profile showing `inc`/`dec` above about 10% of samples would count.

**D2277. Report and 2a now; reuse of effect nodes (2b) only after SW-593? [rec: yes]**
- Why: SW-593 is still in the backlog (`board show 593`), and cells are about a quarter of
  `effects.sw`'s allocations. 2b would be partly redone after SW-593.
- What would change it: if SW-593 is dropped or deferred indefinitely, 2b becomes a cheap
  standalone win (about 13% of that benchmark's allocations, by the note's estimate).

## 4. A staged plan

| Stage | What | Success measure |
|---|---|---|
| 1a | The copy note names its sites | `pushPop`'s note names `Main.pushPop` (its lambda) and `Array.pop`; no change to any run that doesn't copy |
| 1b | Reuse and count columns in `run --profile` (machine) | totals equal the allocation trace's on `set_nat.sw` and the note's A/B pair; profiling off, day 11 within noise |
| 1c | The measurement: the report on §2.2's five programs and 2020 days 15, 17, 19 and 20 | a table that decides D2275 and D2276, and D2591 if copies appear |
| 2a | Inlining for reuse in `opt.rs` | `set_nat.sw` reuse from 11.7% to 80% or more; day 17 timed |
| 2 (small) | Drop never-read parameters and `let`s at entry | trace snapshots change; peak cells on the A/B pair fall |
| 2 (cond.) | The projection hoist (D2591) | a pair state with only projected uses makes 0 copies |
| 2b | Hand reuse in the effect runtime, after SW-593 | `effects.sw` blocks per operation |
| 2c, 3, 4 | As in the note, each gated on 1c | as in the note |

**The stage 1 success measure in one line:** the report reproduces §2.2's cell totals
exactly on `set_nat.sw` and the A/B pair, names the top three missed sites on days 17, 19
and 20, and gives the read-only share of increments. The decisions for D2275 and D2276 can
then be taken from it, not inferred.

## 5. Tickets to file

- **T1. The copy note names its sites** (stage 1a)
  - `unshared`, the copy path only, records the current definition (the machine's frame,
    as the profiler names it) and the native. The end-of-run note lists the top three sites
    by copies.
  - Native code reaches the same helper, so it passes the site, or the note says "run
    without `--native` to see where".
  - Test: `pushPop` on the machine. Update the guide's example note.
  - Sonnet, about 60 min. Epic performance.
- **T2. Reuse columns in `run --profile`** (stage 1b)
  - Per definition: cells built, cells reused, token misses, shared `Unpack`s, array
    copies, and increments by kind.
  - Machine only. The profiler's off cost must stay one test per frame entry. Measure the
    on cost against plain `--profile`.
  - A test that the totals equal the `alloc-trace` counts on a small program.
  - Opus (it touches the machine's hot loop and the trace agreement), about 2–3 h. It
    extends run-profiler.md's stage 4.
- **T3. The measurement** (stage 1c)
  - T2's report on the note's five programs and 2020 days 15, 17, 19 and 20, written into
    in-place-reuse.md §2 as a new dated table.
  - It also answers the read-only share for D2276. That needs Lean's borrow rules run as
    an analysis only: a small part of T2, or its own ticket.
  - Sonnet, about 60 min, after T2.
- **T4. Inlining for reuse in `opt.rs`** (stage 2a, if D2275)
  - Inline a non-recursive callee where the caller holds an unclaimed token of an arity
    the callee builds, with size and fuel bounds.
  - Tests: the A/B pair as a trace snapshot, and `set_nat.sw`'s reuse share.
  - Opus, 0.5–1 lane-day.
- **T5. Drop never-read parameters and `let`s at entry** in `code.rs` `body`. Trace snapshots
  regenerate. Sonnet, about 60 min. Independent of the rest.
- **T6. The projection hoist** (D2591, conditional on T3 finding copies or token misses from
  projected-only records). Generalise `opt.rs`'s projection fold to projections in argument
  and scrutinee positions when the local is never used whole afterwards. Opus.
- **T7. `pushPop` and the guide idiom**
  - Rewrite `examples/extract/arrays.sw`'s `pushPop` to destructure first, or comment it as
    the copying case. Its machine run should make 0 copies.
  - Add "destructure the state first" to the guide's arrays section, beside the copy note.
  - Sonnet, about 30 min. It closes SW-1678 together with T1.
- **T8. Fix in-place-reuse.md and the research README**
  - The D numbers (D2272–D2276 against D2273–D2277).
  - Stage 1's home (the shipped `--profile`, per D2590).
  - A link to this review.
  - Orchestrator, mechanical.
- **T9. The guide's arrays section on `--js` is stale**
  - It still says operations "run as written, on the list"; since SW-1638 they are version
    arrays, O(1) on the newest version.
  - The feature-tour figure says day 15 takes 16 s, against SW-1637's 27 s on the machine.
    Check which run that was.
  - Sonnet, small.

## 6. New questions

- **D2590.** Put the reuse report in the shipped binary? That means the copy note's sites
  always on, and the reuse columns under `run --profile`, instead of a hidden
  `--reuse-report` flag in `alloc-trace` builds only. **[rec: yes.** The copy note already
  sends users to look for the place. They run the release binary, and the profiler is
  already their tool for "why is this slow".**]**
- **D2591.** Add the projection hoist (T6) to stage 2, but only once T3 or a user program
  shows copies or token misses from a record or pair that is only projected? **[rec: yes,
  conditional.** It is a small, pure rewrite next to an existing one. But no real program has
  shown it yet: day 15's records already work, and `pushPop`'s case isn't this one.**]**
- **D2592.** Add an always-give-back `Array.pop` (`Array a → (Array a, Option a)`) to std
  now? **[rec: no, not now.** The guide idiom (T7) covers the case at no API cost. Revisit
  if T1's site names show `pop` copying in more than one real program.**]**

## 7. Other languages, briefly [not re-checked]

- **Lean 4.**
  - Reset/reuse is inserted within one function, for constructors of the same size. Reuse
    across a call comes from `@[inline]` and `@[specialize]` before that pass, which is the
    same idea as stage 2a.
  - Borrowed parameters are inferred (`InferBorrow`), and `@&` marks them by hand.
  - Arrays change in place when unique. The documented cliff is the shared array, with
    `dbgTraceIfShared` to find it.
  - Lean would copy in `pushPop` too.
- **Koka.**
  - Perceus, with drop-guided reuse (Lorenzen and Leijen, ICFP 2022), and reuse
    specialisation to skip unchanged fields.
  - Inlining before reuse analysis lets helpers like `balance` reuse the caller's cells.
  - Borrowing is by explicit `^` annotation, not inferred, for space safety.
  - `fip`/`fbip` (FP², ICFP 2023) checks that a function runs in place, counting reuse
    credits by size. That is the type-level form of what this plan does as a report.
- **Roc.**
  - Reference counting with in-place update of unique lists and records, and Perceus-style
    reset/reuse.
  - Morphic, its alias analysis, removes some dynamic uniqueness tests and borrows where it
    can prove them safe.
  - Its documentation warns about the same accidental-sharing cliff.

The common lesson from all three is the one the note took. Reuse within a function, plus
inlining so that small helpers count as within, gets most of the gain. Every one of them
still copies when a program genuinely keeps the old value, so a diagnostic that names the
site matters as much as the optimisation.

## 8. What wasn't done

- Nothing built or run. The note's §2.2 numbers weren't re-measured. The `code.rs` paths
  behind them are unchanged, so they should hold **[inferred]**. T3 re-measures them.
- The destructure-first idiom (§2.1) wasn't run. Its 0 copies are read from `code.rs`. T7's
  test confirms it.
- Lean, Koka and Roc weren't looked up (§7).
