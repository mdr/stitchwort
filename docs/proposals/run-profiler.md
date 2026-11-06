# A profiler for `stitchwort run` (SW-1528)

Status: stage 1 built (SW-1528, D2458). Later stages are open.

## The problem

A program that runs slowly gives no hint why. The 2020 AoC lanes found
their hot spots by timing variants of `main` by hand: day 11's 42 s were
72,000 `Grid.lookup`s and 9,000 `Position.around`s a round (found with
ten-round variants), day 15's 357 s were nearly all `Map` work, and day
19's were a record method rebuilding a `Map` on every call
(docs/research/aoc-2020-friction-days-10-20.md, theme B).
`STITCHWORT_TIMINGS` covers checking, not running.

## Stage 1: what it does

`stitchwort run --profile FILE` runs `main` on the fast runtime as usual,
then prints a table on standard error: for each definition, how many times
it was entered, and its self and total time, sorted by self time.

(The real output for three AoC days is under "Trying it" below.)

- **calls** are exact: every frame the machine enters, a tail call
  included (a loop of 1,000 iterations is 1,000 calls).
- **self** is time with the definition's own code running (the top frame),
  **total** the time with it anywhere on the stack, each counted once per
  sample however deep its recursion goes, so neither double counts and
  total is never over 100%.
- Times are **sampled**: a timer thread raises a flag every millisecond,
  and the machine, at the next frame it enters, charges the time since the
  last sample to the stack it has then. Each sample is weighted by the
  real time since the one before, so the columns add up to the run's
  time.
- **Names** are the definitions' full names. The optimiser's copies of a
  function (`Std.Map.insertWith[2]`, a copy for a known dictionary) are
  counted as the function, and so is a `match` the elaborator made a
  function of (`Std.Map.Tree.get.%match1` is `Std.Map.Tree.get`). A
  lambda is charged to a row of its own named after the definition that
  makes it, `Day11.step.λ` (all of a definition's lambdas share the
  row). `(entry)` is `main ()` itself, with whatever was inlined into it.
- `--profile-top N` shows the first N rows (default 25; 0 for all).
- **Interrupted runs** report too: `timeout 60 stitchwort run --profile`
  or Ctrl-C prints the profile so far before the process ends, so a
  program that would take minutes can be profiled for a minute.

## What it doesn't do yet, and why

- **The fast runtime only.** It's the runtime lanes use daily, the one
  whose code we control instruction by instruction, and the only one
  where we can name every frame. `--profile` with `--js`, `--native` or
  `--reference` is refused. For `--js`, `node --cpu-prof` works on the
  generated module today; it needs plumbing and name mapping (stage 3).
- **No file:line.** The machine's code knows a definition's name and
  `DefId`, not its span; the name is enough to find a definition, and a
  span would need the session's source map threaded into the report
  (stage 2).
- **Natives aren't rows.** A native (`Text` and number primitives, an
  `IO` operation) runs inside the frame that calls it, so its time is
  that caller's self time. `Map` and `Set` are ordinary Stitchwort code,
  so their functions are rows.
- **Inlined functions aren't rows.** The optimiser inlines small
  non-recursive functions (`opt.rs`, `INLINE_SIZE`), whose time and calls
  are then their caller's. Profiling the program the optimiser made, not
  a de-optimised one, keeps the times true (GHC's cost centres do the
  opposite: they block inlining, and change the program measured).
- **A tail call keeps its caller on the stack, approximately.** A tail
  call replaces its caller's frame; the profiler remembers, per frame, the
  definitions that ran in it (up to 8), so `lookup`'s total includes the
  `Map.getOr` it tail-calls. A chain longer than that loses the middle.
- **No allocation counts, no call graph.** Both are possible later; the
  flat table answers "where does the time go" first.
- **`stitchwort test --profile`** isn't offered: tests don't run through
  `run_main`, and a profile per test needs its own report; it wasn't
  trivial, so it waits (stage 5).

## The design

- `crates/rt/src/profile.rs` holds the profile: per code (a global's, a
  lambda's, the entry's) a row; per row the calls, self and total time in
  nanoseconds, as relaxed atomics, written only by the machine's thread
  and read by whoever reports (the end of the run, or the signal thread
  on an interrupt).
- The machine's state has `profile: Option<Box<Profiler>>`. The hook is
  in the four places a frame starts (`push`, `Call`, an exact `Apply`, and
  `replace` for tail calls): with profiling off it's one test of a field
  that is `None`, beside the step count and limit test each frame entry
  already makes.
- With profiling on, a frame entry adds to its row's calls, records the
  code in the per-depth chain (cleared on a push, appended on a
  replace), and, if the timer's flag is up, takes a sample: walks the
  frames, adds the time since the last sample to the top frame's row's
  self time and once to every row on the stack's total (a generation
  stamp per row keeps recursion from counting twice).
- Rows are made from the `Image` before the run: a global's code is
  named by the global (its `[…]` and `.%matchN` suffixes dropped); a lambda's by the code
  whose `Closure` instruction makes it, found by walking every code once,
  up to the enclosing global.

Prior art: GHC's cost centres (`-prof`, `+RTS -p`) give exact entries and
sampled time per cost centre, as here, but by recompiling; Lean's
`profiler` option times elaboration, not runs; OCaml's landmarks are
manual; Node's `--cpu-prof` and `perf` sample the native stack. Exact
calls with sampled time is GHC's split, and costs nothing when off.

## How to read it

Start from the top of the self column: that's where the machine spends
its time. Then look down the total column for your own definitions: day
11's `Grid.lookup.λ` at 60% total and 1.6% self is a function whose
callees are the cost (`Map.Tree.get`). Divide time by calls for the cost
of one call: 14.5 s over 113.6 M steps of `get` is 128 ns. A definition
with a surprising number of calls (a record method called once per
element that rebuilds a `Map`) is often the finding.

## Trying it: three AoC days

**2020 day 11** (the seating simulation, 20 s): the lane found its cost
by timing variants of `main`; the profile names it at once. Two thirds
of the run is `Map.Tree.get`, called through `Grid.lookup`'s lambda (60%
total, 1.6% self), one lookup per neighbour per seat per round:

```
profile: 21.247 s in the program, 15,782 samples every 1 ms
  self %    self s   total %   total s          calls  definition
   68.3%    14.517     68.3%    14.517    113,607,401  Std.Map.Tree.get
   10.1%     2.156     72.1%    15.310      9,789,020  Std.List.foldLeft
    3.0%     0.640     97.8%    20.778      3,234,903  Std.List.map
    2.6%     0.544      2.6%     0.544      3,045,338  Std.List.withIndexFrom
    2.5%     0.526      4.0%     0.844      1,492,400  Std.Map.Tree.joinBuilt
    2.3%     0.488     61.9%    13.154      8,347,578  Std.List.count.λ
    1.8%     0.379     83.2%    17.686      9,771,000  Aoc.Year2020.Day11.Layout.round.λ
    1.6%     0.342     59.6%    12.671      8,515,402  Aoc.Common.Grid.lookup.λ
```

**2020 day 15** (357 s for both parts; part 1 is 2,020 turns and takes
no time, so this is the whole `main` stopped by `timeout 30`): all of it
is the `Map`, and the rows split it: `insertWith` 68% total, of which
the rebalancing (`shape`, `rebuild`) is most; `get` 21%. Under 3% is the
game itself.

```
profile: 28.336 s in the program, 20,101 samples every 1 ms
  self %    self s   total %   total s          calls  definition
   25.0%     7.076     25.0%     7.076     34,679,193  Std.Map.Tree.shape
   23.5%     6.656     23.7%     6.725     34,679,193  Std.Map.Tree.rebuild
   20.5%     5.822     20.5%     5.822     36,901,805  Std.Map.Tree.get
   19.4%     5.490     68.1%    19.291     36,901,817  Std.Map.Tree.insertWith
    4.1%     1.157      4.1%     1.157     15,355,303  Std.List.lengthOnto
    2.8%     0.793    100.0%    28.336      2,559,213  Std.Nat.iterate
    2.4%     0.690     23.0%     6.511      5,118,403  Aoc.Year2020.Day15.Game.reply
    1.0%     0.285     69.1%    19.576      2,559,211  Aoc.Year2020.Day15.Game.say
```

**2020 day 19** (6.5 s): the slow variant the lane tried (a record
method rebuilding a `Map` on every call) wasn't kept, but the profile of
today's program finds the next thing: 86% of the run is `List.lookup`,
the association-list lookup of a rule by number (`Rules.rule`, inlined
into `Rules.leftAfter`), 48 million steps of it.

```
profile: 6.493 s in the program, 5,167 samples every 1 ms
  self %    self s   total %   total s          calls  definition
   85.8%     5.569     85.8%     5.569     48,149,931  Std.List.lookup
    4.2%     0.270     97.4%     6.324      2,437,109  Std.List.map
    3.1%     0.199      4.5%     0.294      2,434,519  Std.List.concat
    1.7%     0.108     97.4%     6.324        618,176  Aoc.Year2020.Day19.Rules.leftAfter
```

**Cost.** With the flag off, the machine's only new work is one test of
a `None` field per frame entered. Day 11 (flag off), the base commit's
binary against this one, run alternately three times each: 19.45, 19.47
s against 19.40, 19.64, 19.44 s user (the base's first run, 24.0 s,
re-checked the project for its new binary hash): no difference beyond
noise. With `--profile`, alternating with the flag off: 22.47 against 23.36 s,
then 19.43 against 20.20 s (the machine was busier during the first
pair): about 4%.

## Later stages

2. Spans: `file:line` beside each name, and lambdas named by their line
   (`Day11.step.λ@42`), with the session's source positions.
3. `--js --profile`: run Node with `--cpu-prof`, map the generated
   functions' names back (they are already the definitions' names,
   mangled), and print the same table.
4. Natives as rows (count `Text.split`, big number arithmetic), allocation
   counts per row, and a call-graph view (callers of a hot row).
5. `stitchwort test --profile`, and a machine-readable output
   (`--profile-out FILE`, a speedscope or pprof file).
