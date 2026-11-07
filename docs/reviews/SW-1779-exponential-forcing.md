# SW-1779: exponential forcing of `P(i) x := P(i-1) x ∧ P(i-1) x`

## Summary

- **Real code is affected, but not by the duplicated-call pattern itself.**
  No definition in std, aoc/, games/rogue or the examples nests a
  parameter-dependent call deeply enough for the doubling to matter. What
  real code does hit is the mechanism underneath: three places compute a
  value all the way down when they only need part of it. The worst is the
  elaborator reading back every context type in full for each `auto`
  argument. Fixing it cuts aoc's evaluation steps by 18% (1,342 M to
  1,098 M) and its `check` from 74 s to about 63 s of wall time. Two
  Day 6 (2024) proofs go from 2.9 s and 2.3 s to under 0.1 s.
- **Cause:** none of the three candidates in the brief. Values are shared
  well enough; the cost comes from evaluating or reading back glued calls
  (`Value::Call`) where nothing needs their unfolding.
  `P(i-1) x ∧ P(i-1) x` holds two separate calls, so unfolding everything
  takes 2^i steps, while kept as calls it is one node.
- **Fixed on the branch** (three small changes, below). The cases go from
  0.7 s (`g18`) and over 100 s (`g25`) to 0.17 s each.
- **Left:** the kernel still evaluates a closed type unglued, because
  `Def::ty_value` is kept. That costs Day 22 (2024) 4.4 s of kernel time,
  in a computation that isn't exponential (below, and a proposed ticket).

## Measurements

Release build, `STITCHWORT_TIMINGS=decls`, `stitchwort check` (default
cache) in aoc/ and games/rogue, plus the SW-1743 cases.

### The cases

| case | before (elab / kernel ms) | fixes 1–2 | all three (whole `check`) |
|---|---|---|---|
| `g16` | 170 / 38 | 41 / 0 | 0.17 s |
| `g18` | 701 / 152 (19.9 M steps) | 160 / 0 | 0.17 s |
| `g20` | 2842 / 599 | 644 / 0 | 0.17 s |
| `g25`, `g25b` | > 100 s | 21 s / 0 (`g25`) | 0.17 s |

Each two levels multiplied the time by 4, exactly 2^n. `g18b` (no call)
spent all its 152 ms in the kernel. The elaborator's cost came only with
the `auto` argument of `needs 3`.

### Real code

- **std:** the slowest std declaration takes 0.5 ms of kernel time. The
  slow ones (`Std.Parse.runFrom…`, ~0.4 s of elaboration) have terms of
  about 90,000 nodes, so their cost is in proportion to their size.
- **games/rogue:** 3.8 s of elaboration and 0.6 s of kernel time in all.
  Nothing has many steps for few nodes.
- **examples:** `case-tree-chains.sw` is a deliberate 2^30 chain, already
  handled by the call memo (SW-395). A static scan for definitions whose
  unfolding is many times their text found nothing else.
- **aoc:** the outliers have many steps for few nodes:

| declaration | elab ms before → after | kernel ms | cause |
|---|---|---|---|
| 2024 Day06 `part2Correct` | 2863 → 3.9 | 0.4 | fix 1 |
| 2024 Day06 `trapSetsSame` | 2291 → 76 | 0.6 | fix 1 |
| 2021 Day08 `readShown` | 760 → 179 | 28 → 19 | fix 1 |
| 2024 Day23 `largestFromAnswers` | 2867 → 2092 | 655 | fix 1, in part |
| 2024 Day22 `digitChangesPossible` | 0.2 | **2750** | kernel closed type, not fixed |
| 2024 Day22 `bestTotalCorrect` | 0.2 | **1625** | the same |

aoc in all, with fixes 1 and 2: 1,342 M steps → 1,098 M, elaboration
58.5 s → 48.2 s, kernel 15.1 s → 14.7 s, wall 74 s → 63 s. Fix 3 changes
aoc's steps by +640 in all, so it matters only for the synthetic case.
(Its timed run was on a loaded machine, load average 9 to 13, so steps are
the reliable comparison.) All 11,491 declarations have the same node
counts before and after, and `check` passes.

## The three causes, and the fixes

### 1. `ignorable_arguments` read back every context type unfolded (elab)

For each `auto` argument, `check.rs` `ignorable_arguments` reads back the
goal and the type of every variable in scope, only to see which variables
they mention. It used `quote`, which forces every glued call. So a
hypothesis `h: P18 n` was written out as a 2^18-node term at each `auto`
argument in its scope, and in aoc any big glued value in a hypothesis was
written out in full (Day 6's lab, routes and sets).

**Fix:** read back with `quote_folded`, which keeps the calls.

**What it changes:** a call's arguments mention every variable its
unfolding mentions, and possibly more (an argument the definition
ignores). So the set of mentioned variables can only grow, and an
argument marked ignorable can only become not ignorable. `ignorable` only
*permits* unification to drop a non-variable argument when it solves an
`auto` argument's proof (SW-323). With the change, that permission can be
lost where the statement mentions the lambda's variable only through a
call that ignores it. The kernel checks every result, so this can't make
anything unsound. At worst it rejects a contrived program that was
accepted before. Every aoc declaration elaborated to the same number of
nodes, and `hash_stability prelude`/`examples` pass, so nothing real
changed. **This is the one change that isn't answer-preserving by
construction; it is D-question 1 below.**

### 2. `declare_def` evaluated binder types unglued (kernel)

`declare_def` checks the signature with gluing off (`in_kernel_modes`).
`check_type` of `(h: P18 n) → …` evaluates `P18 n` to bind `h`, and
unglued evaluation unfolds every call as soon as it is made: 2^18 calls.

**Fix:** check the signature with gluing on, as `admit_group` already
does for bodies (D483, `folded-calls.md`). The stored `Def::ty_value` is
still made unglued by `push_def`, so the invariant "nothing glued outlives
the check" holds.

**Why it changes no answer:** the values made with gluing on live only in
the checking context and are dropped. The checked term is rebuilt from the
input terms, except in one place: `Eq(None, …)`, whose inferred type is
read back with `quote`. `quote` reads glued calls back as their unfolding,
the same term the unglued value reads back to. Comparing glued values
(`conv`) uses the same rule the kernel already trusts for every body
(D483): two calls of the same definition are compared by their arguments
first, then by their unfoldings, which are the definition applied to them.
Gluing changes when something is computed, not what is equal. Only step
counts differ, so a signature that ran out of budget before can now pass.

### 3. Instance search forced every local's type unglued (elab)

`interfaces.rs` `locals` lists the dictionaries in scope by forcing each
variable's type and looking for an interface. `decide`, which `auto` uses
for `3 ≠ 0`, runs unglued (D2535). So forcing `h: P18 n`'s glued type
evaluated it all the way down, 2^18 steps, just to find that it isn't an
interface.

**Fix:** look at the head glued first, and skip a local whose head isn't
an interface. An interface is forced unglued, as before.

**Why it changes no answer:** forcing glued and forcing unglued give the
same head (gluing only delays the calls under it), so the same locals are
skipped. One side effect: the glued force caches the call's unfolding in
its shared cell, and a later unglued force of the *same call value* reads
that cache. The cache already mixes the two modes this way whenever the
elaborator forces glued and then decides (`force_now` takes the cached
unfolding in either mode), so this adds no new kind of value. An
interface-typed local is almost always a `Value::Data` already, with no
call to cache.

## Not fixed: the kernel's closed type values

`theorem digitChangesPossible: HoldsDigitChanges (sequencesOf
possibleChanges)` takes 2.75 s of kernel time for a 10-node term.
`push_def` evaluates the closed type unglued for `Def::ty_value`, which
builds all 19^4 = 130,321 `Changes` records. The body check then infers
the same proposition glued and compares it with that value, which forces
the calls and walks the list again. `bestTotalCorrect` (1.6 s) pays again
when it passes `digitChangesPossible` as an argument: its stored type is
the unfolded list, which `conv` compares with the glued
`HoldsDigitChanges possible` there. A 6-line reduction:

```
def Holds (xs: List Nat): Prop := (a: Nat) → a ∈ xs → a = a
def many: List Nat := List.range 0 100000
theorem holdsAll (xs: List Nat): Holds xs := a _ => rfl
theorem holdsMany: Holds many := holdsAll many   -- 125 ms kernel, 6 nodes
```

Fixing this means keeping glued values in `Def::ty_value`, which breaks
the invariant that nothing glued outlives a kernel check. That invariant
probably matters for opacity: a call's cached unfolding is shared, so one
forced while a body can see an opaque definition could be read where that
definition is hidden. It also matters for memory (cached unfoldings would
live as long as the definition). That is a kernel design question, so it
needs a note in `docs/proposals/` on Opus. 4.4 s is 29% of aoc's kernel
time, all in one day.

## Recommendation

- Merge the branch. Fixes 2 and 3 are answer-preserving. Fix 1 can only
  withhold a permission, and the D question below is whether to accept
  that.
- File the closed-type-value issue as a design ticket (proposal first,
  Opus), with the reduction above.
- `test:affected` doesn't run at the moment: nextest rejects its filter
  because it names `stitchwort-rt::codec`, `::machine`, … as separate
  binaries, and the rt tests are now one binary (`it`). That needs a
  ticket.
