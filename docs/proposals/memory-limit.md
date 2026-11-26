# Proposal: a memory limit for one operation

**Status:** design note for Matt's decision (SW-4887, 26 Nov 2026). No code.

## The problem

A few-line file can use all of a machine's memory before any limit stops it.
Native, that is a crash ("memory allocation failed", no diagnostic); in the
browser the check's worker dies. Neither is `E-RESOURCE`, which D2543 promises
for running out of anything. From the ticket (Overmind, the same at
c3f9c13d4, so not new):

```
def count: Nat → Nat
  | Zero => Zero
  | Succ n => Succ (count n)

theorem countBig: count 6000000 = 3000000 := byComputing
```

ends `E-REFL` at a 2.7 GB peak; with `count 2^128` (and two similar cases:
a decreasing `innerN`, and `grow` building a tree) the CLI aborts at about
11 GB after 22 to 52 s, having taken 250 to 500 million of its 10 billion
steps. So these programs hold 22 to 44 bytes per step: the step limit would
allow hundreds of gigabytes. The frame limit sees nothing either: pending
frames stay constant.

## Where the memory goes (measured)

Release CLI at 046f7bdc3, `check --no-cache`, one namespace per run,
`/usr/bin/time -l` "peak memory footprint" (mimalloc, the CLI's allocator).
`count 10 = 5` peaks at 134 MB: loading std.

| Program | Peak | Over baseline, per link |
|---|---|---|
| `count 1000000 = 500000` | 711 MB | |
| `count 2000000 = 1000000` | 1,124 MB | 413 B (1M→2M) |
| `count 4000000 = 2000000` | 1,954 MB | 415 B (2M→4M) |
| `count 6000000 = 3000000` | 2,790 MB | 418 B (4M→6M) |
| `count 1000000 = 1000000` (true; accepted) | 449 MB | 315 B |
| `count 2000000 = 2000000` (true) | 739 MB, then `E-RESOURCE` depth | 290 B |

With `count 2000000` against 5, 1,999,999 or 2,000,001 the peak is the same
1.12 GB: the comparison forces the whole chain whatever the right side, and
memory is linear in the links forced. This confirms Fable's reading
(docs/reviews/SW-4881-rule-e-reads.md, last section): each forced call keeps
its unfolding (`Value::Call`'s `Rc<Unfolding>`, value.rs), the unfolding is
`Succ` of the next call, and the theorem's own value holds the root, so the
whole chain lives until the check ends. 290 to 315 bytes a link when the
comparison succeeds is Fable's estimate (a call and its spine, the argument's
number, an `Unfolding` cell with its `Kept` and modes, a constructor and its
field array). The failing comparison costs about 100 bytes a link more; I
didn't find what (perhaps a second pass on the failure path), and it doesn't
change the design. Not measured: a heap profile by site. The bench's counting
allocator gives totals only, and mimalloc hides the CLI's heap from macOS's
`heap` and `leaks`.

The kept unfoldings are one case of a general hole, not the hole: nothing
bounds the live heap per step. A loop that builds a long list with an
accumulator, or `grow` building a tree, holds constructors, not unfoldings,
and the frame limit doesn't see them either.

## Options

**(a) A deterministic count charged at the evaluator's allocating sites.**
`Shared::new`, `Values`, `Spine`, `Rc<Unfolding>` and environments add a
fixed weight to a counter and their `Drop`s take it off; the operation is
refused past a cap. It must count *live* units: a count that only grows is a
second step limit and would refuse long loops that allocate and free in
constant memory (most AoC days allocate many gigabytes in all). Deterministic
on every target, like steps. But it covers only the sites it instruments: the
elaborator's own structures, metavariable solutions, `CallMemo`, hash maps and
any value type added later escape it, so a program can still crash through a
path it misses. It touches every value constructor and destructor in the
evaluator's hottest code.

**(b) Not keeping some unfoldings.** Results are unchanged by construction
(an unfolding is only a cache; `Kept::fits` already recomputes when it may not
be used). It would let `count 6000000` run in constant memory. But step counts
change, and an inner attempt that runs out of steps answers "no"
(`check.rs:7575`), so changing steps can change what the elaborator chooses;
sharing that programs rely on (compute-once) can turn linear work exponential;
no cheap test at keep time says an unfolding is the head of a long chain (each
is a small `Succ (call)`); and it does nothing for the list and tree cases.
Not a fix for this ticket. As an optimisation for later, only with the
evaluator measured first.

**(c) Live bytes per operation, counted in the allocator.** The global
allocator (`crates/alloc`, mimalloc, native; the default dlmalloc in the
browser, wrapped the same way) adds each block's requested size to a
thread-local live count and takes it off on free, as `crates/bench`'s
counting allocator already does. An operation records the count when it
starts; the budget compares the growth with the cap at its existing poll
points (`Budget::arm`, every `POLL` = 16,384 steps, made unconditional) and
in `nesting`, so the evaluator's fast path is unchanged. Past the cap, a new
`ResourceError::Memory` ("it used more memory than allowed"), sticky like the
others. It sees every allocation the checking thread makes, whatever made it.
It overshoots by at most what 16,384 steps allocate (a few megabytes).

- *Determinism.* The count is the same on every run of a given build for a
  given target: block sizes and the order of allocations and frees are the
  program's (requested sizes, not mimalloc's size classes). It is not the same
  across targets: wasm32's pointers are half the size, so the browser counts
  roughly 0.6 of the native bytes (estimated), and a debug build counts
  differently again. That is the class the stack limit is already in
  (`Limits::stack` counts bytes; check-cache-trust.md accepts a
  build-dependent `E-RESOURCE` as "a resource result, not a different
  accepted theorem"). The rule that keeps it so: `Memory` is passed on like
  `Depth` and `Deadline`, never taken as "no" by an inner attempt, so it can
  refuse a declaration but never change what one means or which branch the
  elaborator takes.
- *Cost.* A thread-local add on every allocation and free, and a load and
  compare at each poll: estimated 1 to 3% on allocation-heavy checks, to be
  measured in the bench (instructions there are exact) before it merges.
- *Threads.* Values are `Rc`, so a check allocates and frees on one thread;
  per-thread counts don't depend on `STITCHWORT_JOBS`. A process-wide cap
  would: which namespace hit it would depend on scheduling.

**(d) (c) plus a process backstop.** A second, process-wide figure (say 75% of
physical memory) refusing whichever operation crosses it. It turns the crash
that `jobs × cap` can still cause on a small machine into `E-RESOURCE`, but
which declaration it refuses depends on timing, like the deadline. Worth it
only if (c)'s per-thread cap proves not enough; not proposed now.

## Recommendation: (c), with fixed caps

**Default caps:** 4 GB of growth per operation native, 2 GB in the browser,
fixed constants (not a share of the machine's memory, so a result doesn't
depend on the machine's size within a target), with `STITCHWORT_MEMORY_LIMIT`
for tests as `STITCHWORT_WORK_LIMIT` is.

- 4 GB native is over three times the largest ordinary peak recorded in the
  repo (examples that run the size limit out: 0.35 to 0.53 GB; the biggest
  bench and log entries about 1.2 GB, whole process), above what the frame
  limit already allows (2 million frames, about 1.5 GB), and above the 2.7 GB
  of `count 6000000`, which stays `E-REFL`.
- 2 GB in the browser: wasm32 has 4 GiB of address space for the whole
  worker, std and the session included. At about 0.6 of native bytes, 2 GB
  there is roughly 3.3 GB native.
- On the ticket's cases: `count 2^128`, `innerN`, `grow` give `E-RESOURCE` at
  about 4 GB, after an estimated 8 to 20 s, instead of crashing at 11 GB after
  22 to 52 s. Results and step counts don't change anywhere.

**Stages.** 1: the counter and a report (`STITCHWORT_TRACE_MEMORY=1` prints
each operation's peak growth), with no refusal; Overmind runs it over std,
`aoc/` and `games/rogue` to find the largest operation, and the bench
measures the cost. 2: the refusal at the caps above (or at four times the
largest operation found, if that is higher), a `reject/` example under a low
`STITCHWORT_MEMORY_LIMIT`, docs/core.md's resource row and the error guide.
Estimated an hour or two of agent time each.

## Decisions for Matt

- **Scope (D3688).** In the browser and on a small machine this only replaces
  a crash. On a big machine (Speedwell has 32 GB) it refuses an operation that
  grows past 4 GB and would finish today: a narrowing, so yours. None is known
  in the repo (the nearest: the fuzz finding `dev/fuzz-findings/2468-12893.sw`
  peaks at 4.5 GB for the whole file, per operation unknown); stage 1 measures it before anything is refused. Recommended:
  yes, with the caps above.
- **A build-dependent limit.** The browser and native can disagree on a
  program within a factor of about 1.7 of the cap, as they can today on stack
  depth. The alternative that agrees everywhere is (a), at the price of
  incomplete coverage. Recommended: accept it, as for the stack.
