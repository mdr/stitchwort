# Proposal: stuck field calls `(f x).i` remember their call

**Status:** draft 1, 7 November 2026, for Matt's decisions D3020 and D3021 ([§8](#8-decisions)).
Ticket SW-1914, from the core review's F1 and F12 ([code-review-core.md](../reviews/code-review-core.md))
and the as-merged review's F1 and F9 ([record-eta-as-merged.md](../reviews/record-eta-as-merged.md)).
Written against `main` at `a1f8470f8`, with SW-2095 (match-call-field stage 1) read on
`lane/SW-2095` at `b4d307fb4`. Nothing was run for this note: it is read only (the shared
machine was checking proofs).

Related: [record-eta.md](record-eta.md) §6.4 (rule 2, and fields as projections of the scrutinee
*as it was*) and §6.5 (glued calls); [match-call-field.md](match-call-field.md) (D2990 to D2992,
and its stage 2, SW-2096); [folded-calls.md](folded-calls.md) (glued calls and their cells).

Labels: **[checked]** read in this repository at the place given; **[cited]** read in the note
named; **[inferred]** my reasoning from the code, not run, with a confidence where it matters.

## 0. Summary

**What users get.** Nothing they can see today, and that's the point: this is a growth risk
removed before it bites. A field of a record that some function returns, `(f x).i`, is checked
by running `f x` again every time it's compared or written out, once per field. 2020 day 20's
proofs do this 19,261 times, cheaply, because the `f` there is mostly the accessor
`Parse.State.at`. When `f` is expensive, or one such call is nested in another, the cost
multiplies with each level: a simulation proof comparing `(step (step s)).pos` pays for the
outer step once per field compared, and for the inner step once per field of *that*. That's
the shape that made SW-1829 exponential, in the two places SW-1829 didn't reach.

**Why.** The elaborator and the kernel keep a call `f x` as a *glued call*, with a cell that
holds what it computes to, so every copy of the call shares one computation. When a field of
such a call is forced and the call is stuck, the field becomes a plain stuck term,
`(f x).i`, that keeps the call's name but **drops its cell** (`value.rs:1649-1654`). Every
reader that needs to see what that field means then runs `f x` from scratch.

**The change** (design A, §3.1): the stuck field keeps a link to the call it is a field of,
cell included, on its last projection. Conversion, the unifier, `cases`, the unfolded
read-back and SW-2095's applied-field step read the call's cell instead of running it again.
Nothing users see changes: the same values, the same terms, the same hashes; only the work
done shrinks.

**Stages.** 0: count the re-runs, by site and kind, and write a growth test (§6). 1a: give
`Elim::Proj` the link, always empty (mechanical). 1b: fill and read it. 2 (only if stage 0
shows it matters): a per-comparison memo for the projections that have no call to link to.
3: the typed view that F9 asks for. All after SW-2095.

**Decisions for Matt.** D3020: the elaborator only reads the link, and the kernel re-runs as
today [rec: yes]. D3021: close D2992's revisit: no general form `(f x).i a` [rec: yes].

## 1. The problem, in plain words

**An example.** `Parse.State` is a record of five fields (`Parse.sw:71`), and its first, `at`,
is itself a record, `Parse.Mark`. A proof about a parser mentions `state.at.offset` for an
unknown `state`. While checking, Stitchwort keeps `state.at` as the call `Parse.State.at
state` (a glued call: `Value::Call`, `value.rs:41-49`), and its `.offset` as a *field of that
call*. Forcing the field forces the call: the accessor's `case` on the unknown `state` takes
its only branch by rule 2, and the call's cell now holds `state`'s projection. Because the
answer is stuck (it's about an unknown), the field becomes the stuck term
`(Parse.State.at state).offset`, written in the value as `Neutral(Def Parse.State.at, [state,
.offset])` **[checked: `Frame::CallField`, `value.rs:1627-1657`; `eta_fields` presets the
same, `1974-1990`]**.

That stuck term is a *name*: it means "field `offset` of whatever `Parse.State.at state`
computes to", and `is_folded` treats it as something to unfold when it's compared with anything
that isn't the same name (`value.rs:2152-2163`). Unfolding it means running
`Parse.State.at`'s case tree again from `state` (`unfold_folded`, `value.rs:2237-2273`), though
the call's cell, a few pointers away in the value it came from, already holds the answer. The
name kept the call's definition and arguments and left the cell behind.

**Why it's cheap today.** An accessor's re-run is one `case` and rule 2: a handful of steps.
So 19,261 re-runs cost little.

**Why it's a growth risk.** Nothing limits the re-run to accessors. Take `step: State →
State` on a 6-field record, stuck on an unknown input, and a proof that compares
`step (step s)` with a record literal. Rule 1 (record-eta.md §6.3) compares field by field, and
each field of the outer call is a name, so each comparison re-runs `step (step s)`. That re-run
produces the inner call's fields as names too, and each of those, compared in turn, re-runs
`step s`. With `k` fields compared at each of `d` levels, that's on the order of `k^d` runs
of `step` where one per level would do (code-review-core.md F1's scenario **[cited; the
multiplication is inferred, medium-high: each step checked, the composition not run]**).
SW-1829 was this shape in the forcing path, with 2024 day 11's `Map.foldLeft` proofs taking
whole-AoC checking from 62 s to over 400 s; it was fixed by presetting the field's own cell
(`eta_fields`). The two paths below were left.

## 2. Where the base call is re-run, and why

### 2.1 The two forms

- **(N) Named fields**: `Neutral(Def f, [args…, .i])`, made from a glued call's field when
  the call is stuck, by `Frame::CallField` (`value.rs:1649-1654`) and by `eta_fields`'
  preset (`1983-1985`). The glued field `Value::Call(f, [args…, .i], u)` had a cell `u`
  whose `base` is the call's own cell (`project_call`, `1924-1934`; `Unfolding::base`,
  `77-80`). The named form keeps neither. (After SW-2095, `Frame::FieldOf` also returns this
  form when the call is stuck in its own case tree.)
- **(B) Bare projections of a stuck call**: `project(d, i, n)` of a stuck call `n =
  Neutral(Def f, args)` gives the same shape, `Neutral(Def f, [args…, .i])`
  (`value.rs:1902-1905`). These are made by rule 1 in conversion (`3157-3170`, which projects
  the unknown side once per field), by `ProjForced`/`ProjReady` and `ReplayElim` in the
  machine, and by evaluating a `Term::Proj` of a stuck call: with or without gluing, in the
  kernel as much as the elaborator. There was never a cell to keep: the call is the stuck
  value itself.

`is_folded` can't tell them apart (both are "a definition applied to all its parameters, then
projected", `2154-2160`), so both are unfolded the same way. For (B) the re-run is futile
whenever the call is stuck in its own case tree, which, in the kernel (no metavariables), is
always **[inferred, high: a stuck `Neutral(Def f, args)` with `f`'s body visible and not
folding can only come from `f`'s own tree getting stuck, and re-running it in the same modes
gets stuck the same way]**.

### 2.2 The sites

| # | Site | What it re-runs | Forms |
|---|---|---|---|
| R1 | Conversion: `conv_step` meets a name against anything but the same name (`value.rs:2973-2985`) and calls `unfold_folded` (`2237-2273`), which runs `f`'s case tree from its arguments, then takes the fields of the result. If the tree is stuck, the run is thrown away (`2257-2261`) and the next comparison pays again. `CallMemo` doesn't help: it keys on `Value::Call` cells only (`2881-2890`). | the whole call, per comparison | N, B |
| R2 | The unifier, the same way (`unify.rs:1340-1355`), and `cases` (`cases.rs:1287`, `1348`, `1504`, `1719`). | the same | N, B |
| R3 | The unfolded read-back (`value.rs:2600-2616`): a name is written as its fields of the call read back unfolded, and the call is rebuilt as `Value::Call(id, call, Rc::default())`, a **fresh cell** (`2614`), so each field read back computes the call again. Each field's term also gets its own copy of the call's unfolding, which may be part of SW-1762's term growth **[cited: record-eta-as-merged.md F1]**. | the whole call, per field read back | N, B |
| R4 | After SW-2095: applying a name, or `J` on it, computes it first (`unfold_field_for`, `lane/SW-2095` `value.rs:2263-2288`), by running the call's tree in the machine. match-call-field.md §4.1 names this "one more instance" of the shape and leaves it to this ticket. | the whole call, per application | N |
| R5 | `Frame::CallField` when the call matches at once (`value.rs:1637-1641`): the base was just forced, and `unfold_once` computes its first step again, per field (core review F12). | one step of the call, per field | (glued fields) |

R1 to R4 are the same omission: a reader holds the name and not the cell. R5 is a smaller,
separate duplicate: one tree walk with calls kept glued, bounded by the call's first step.

### 2.3 Where this runs: the kernel too

`value.rs` isn't elaborator-only code. The kernel turns gluing on to check every definition's
body and type (`check.rs:1828`, `1882`; `machine.rs:22-29`), so glued calls, `Frame::CallField`,
`eta_fields`, names and `unfold_folded` all run inside the kernel during admission. Form (B)
also arises with gluing off. So any change to these readers is a change to code the kernel
runs; §4 says how each design keeps the kernel's trust where it is.

## 3. Designs

### 3.1 A: the name keeps a link to its call (recommended)

**The change.** A named field remembers the glued call it's a field of, with that call's cell.
Concretely, the projection at the end of its spine carries an optional link:

```rust
Elim::Proj(DataId, usize, Option<Rc<FieldOf>>)
// FieldOf: the call without this projection: its spine (shared, the same Rc the
// call has) and its cell. Set only on the last projection of a named field.
```

- **Where it's set.** `Frame::CallField` and `eta_fields` make the name from a glued field
  `Call(f, [args…, .i], u)`; the link is the base call, `Call(f, [args…], u.base)`, which is
  exactly what `force_call` forces to compute the field (`value.rs:984-1003`). SW-2095's
  `FieldOf`, which returns a name when the call is stuck, keeps the link it was given.
- **Where it's read.** A name with a link means `project(d, i, force(base))`, and forcing the
  base uses its cell when the cell fits (`Kept::fits`, `value.rs:115-131`) and recomputes and
  keeps it otherwise, as for any glued call. So:
  - `unfold_folded` (R1, R2): force the base; if it gives the base stuck in its own tree (a
    `Neutral(Def f, s)` whose spine is the base's own, the test `Frame::Unfolding` already
    makes, `1685-1690`), the name is stuck too: `None`, with no tree run. If it gives a name
    itself (a nested `(f x).i.j`), unfold that one by its own link; otherwise take field `i`
    of what it gives, unfolding a folded result as today.
  - The unfolded read-back (R3): write the projections and visit the base call **with its
    cell**, not a fresh one. This is the core review's F1 (a).
  - `unfold_field_for` (R4): `Control::Force(base)` and then `Frame::FieldOf`, instead of
    running the tree.
  - Without a link (form B, or a name built some other way) every reader does what it does
    today.
- **Invariants.**
  - *A name links to its base, never to its own cell.* The field call's cell holds the name
    (that's SW-1829's preset); a link from the name back to that cell would be a reference
    cycle, which `Rc` never frees. The base's cell holds what the base computes to, which was
    made before the name and can't contain it. Nested names chain through `Unfolding::base`.
  - *The link changes no answer.* Every comparison, hash and identity test of spines
    (`spine_pairs`, `identical`, `shape_hash`: `value.rs:3215`, `4204`, `4222`, `3772`)
    ignores it, so two names are equal exactly when they are today.
  - *No stale answer.* The link is only a way to reach the cell; the cell's own epoch and
    modes check (`Kept::fits`, SW-1782, D2570) decides whether its answer may be used, and
    otherwise the base is computed again, as forcing any call does.
- **F12 (R5)**: keep the step. When the base matches at once, the forced base came from one
  tree walk, and `Frame::CallField` can take the step from the `Frame::Unfolded` that
  computed it rather than calling `unfold_once` again. Small, and in the same function, so
  stage 1b does it if it fits; otherwise it's its own small ticket.

**What it should do.** Each glued call whose fields are named is computed at most once per
epoch and set of modes, however many of its fields are compared or read back, so the `k^d`
of §1 becomes `k·d`. We'd know from stage 0's counters (R1 to R4's re-runs on named fields
fall to about zero on 2020 day 20) and from the growth test (tree runs grow linearly with
depth).

**What it costs.**
- A sweep of the 51 places that build or match `Elim::Proj` (25 in `value.rs`, the rest in
  `unify.rs`, `reference.rs`, `omega.rs` and five other files). The compiler finds every one;
  most become `Elim::Proj(d, i, _)`. That's stage 1a, with no behaviour change.
- Memory: a name now keeps its call's unfolding alive for as long as the name lives. The glued
  field it came from did the same, and the two usually live together **[inferred, medium]**.
  Stage 1b reports peak memory on its timing runs.
- `Elim`'s size shouldn't change: an application (`Value` and `Icit`) is the largest variant,
  and the link is one pointer **[inferred, not measured]**.

**What it rules out.** Nothing later. It doesn't help form (B), which has no call to link to
(design B covers that, if needed), or fields of folded calls (§5).

### 3.2 B: a memo per comparison

**The change.** The outermost `conv` (and the unifier's equivalent) keeps a table of what
`unfold_folded` gave for each name it unfolded, keyed by the definition and its arguments
compared by `identical`, as code-review-core.md F1 suggests as an alternative. The unfolded
read-back keeps a table per read-back from a call's arguments to one cell, so all fields of one
call read back in one term share it.

**For.** No change to the value representation; and it covers form (B), which A can't:
rule 1's `k` projections of one stuck call cost one run instead of `k`.

**Against.** It only shares work inside one comparison or one read-back. A proof's goals,
hypotheses and unifier problems are compared in thousands of separate operations, and each
starts with an empty table; whether 2020 day 20's 19,261 re-runs are mostly repeats inside one
operation or across many is exactly what stage 0 measures, and I expect "across"
**[inferred, low-medium]**. The keys cost a walk of the arguments per lookup. And it's a second
cache beside the cells that already hold the answer.

**Where it's still right:** form (B) in conversion, if stage 0 shows it's a real share. That's
stage 2, conditional.

### 3.3 C: a general form `(f x).i a` (match-call-field.md option 1b, D2992's revisit)

**The change.** Names accept any eliminations after the projection: `(Cave.tiled cave).level
position` stays a name, instead of computing first as SW-2095 makes it. `is_folded`,
`folded_parts`, `unfold_folded`, the read-back, and the readers F9 lists accept `[args…, .i,
more…]`. This is Agda's spine shape **[from memory]**.

**Against it now.** D2992 chose 1a "for now" partly because 1a re-runs the call once per
application, and asked SW-1914 to revisit. With design A, 1a's application reads the call's
cell (R4), so the cost reason is gone. What's left is a difference in what goals show after a
function field is applied: `(the inside of cave.tiled).level position`, against keeping
`cave.tiled.level position`. No proof has needed the latter since SW-2095 (it was written to
make 2021 day 15's proofs check as written), and C would change every reader that F9 calls
fragile. So: no general form. If a display complaint turns up, A's link makes C cheaper later,
since a name with any eliminations could carry the same link. (D3021.)

### 3.4 Considered and ruled out

- **D: the forced field stays a `Value::Call`** (F9's "one representation", the core
  review's (b) read literally). "A forced value is never a call" is relied on throughout:
  `unreachable!` at `value.rs:2695` and in `call_args` (`715-726`), and every `_ =>` arm in the
  elaborator that takes a forced value apart would quietly treat a call as "something else".
  The compiler can't find those. A gets the same sharing with a change the compiler checks.
- **E: don't name fields of accessor calls.** `(Parse.State.at state).offset` and
  `state.at.offset` print the same, so naming buys nothing there, and this alone would remove
  most of 2020 day 20's re-runs. But it changes the terms the elaborator writes (`Proj` where
  an accessor call was), so hashes and `rewrite`'s keys change across aoc/, and it does nothing
  for the expensive case of §1. Ruled out.

### 3.5 How others do it

From memory, not checked for this note:

- **smalltt and elaboration-zoo's glued evaluation** (Kovács) keep a lazily computed unfolding
  next to every top-level neutral, and a projection of a glued value projects both the neutral
  and the lazy unfolding, which stays shared. That's design A: the unfolding travels with the
  stuck form.
- **GHC** gets this sharing for free: the call is a thunk, and every field selector forces the
  same thunk.
- **Lean 4**'s kernel and `Meta` layer cache weak-head normal forms keyed by expression
  (structurally, with cached hashes), across a whole declaration. That's a global design B; it
  works because Lean's expressions are terms, not closures, and are cheap to hash.
- **Agda** represents `(f x).i a` as one head with a spine of applications and projections
  (design C's shape) and has no cache of reductions for it.

## 4. The trust boundary

**Plainly.** The kernel already trusts glued calls' cells: when it forces a glued call during
admission it uses the kept answer instead of recomputing (`force_now`, `value.rs:589-597`).
Design A reaches the same cells by one more route, so it adds no new *kind* of trust. It does
add a new reader of those cells, and a bug in setting a cell would then matter in one more
place.

**What I recommend (D3020): the link is read only when the elaborator runs, not inside the
kernel.** `in_kernel_modes` (`machine.rs:65-79`) already resets the modes on entry to the
kernel; it would also turn off a new mode that says "names may be read through their link",
and the readers in §3.1 check it. The kernel then re-runs as today: slower, but trusting
exactly what it trusts now. The elaborator and the kernel can't disagree, because the link
only ever gives what the re-run would (that's what `Kept::fits` guarantees), so anything the
elaborator accepts with it, the kernel accepts without it.

**What that leaves.** The kernel's own share of the re-runs stays. Stage 0 measures it
(R1 to R4 counted inside and outside the kernel). If it's large, Matt can extend the reading to
the kernel later: that's the one-line removal of the mode check, plus a review (D2364: changes
that generate or decide kernel terms get an Opus review).

**Design B** is the same: a memo in `conv` is in the kernel's path, so it's gated the same way
for the elaborator, or argued as `CallMemo` is (it holds only the result of a deterministic
function inside one comparison, which can't solve a metavariable). Its form (B) target is
mostly the kernel's, so if stage 0 says it's worth doing, that's where its D question would
be.

**What no design changes.** The terms the elaborator writes, so hashes and the proof cache;
the reference evaluator (`reference.rs`), which has its own `unfold_folded` and keeps
re-running, so the differential tests still compare the machine with an independent
evaluator; and the kernel's checks of every term.

## 5. What this assumes about SW-2095, and what comes after

**SW-2095** (match-call-field stage 1, `lane/SW-2095` at `b4d307fb4`) makes an applied or
`J`-eliminated name compute first (`apply_field`, `unfold_field_for`, `Frame::FieldOf`), only
while gluing (`computes_field`). This proposal assumes, and stage 1b relies on:

1. it's merged first: both change `Frame::CallField`'s neighbourhood and the name's readers in
   `value.rs`, so stage 1a starts from `main` with SW-2095 in it;
2. names stay "a call, then projections only": SW-2095 computes an applied name rather than
   pushing the argument onto it, so `is_folded`'s shape (`value.rs:2154-2160`) still describes
   every name, and the link sits on the last projection;
3. `unfold_field_for` is the one place the machine computes a name's field for an
   elimination, so R4 is one function to change; and `FieldOf`'s stuck test (the call's spine
   by pointer) is the same test A's readers use.

If SW-2095 changes before merging, stage 1b's brief re-checks these three points.

**SW-2096** (match-call-field stage 2: rule 2 names fields of *folded* calls, `decreasing`
definitions and `Quot.lift` leaves) makes names whose call isn't glued, so there's no cell to
link to; match-call-field.md §4.2 accepts one re-run per comparison there. Design A doesn't
remove it. A cell for folded calls would be a different change (folded calls are deliberately
never glued, `unfold_now`, `value.rs:2061-2075`), worth considering only if stage 0, re-run
after SW-2096, shows those re-runs matter. SW-2096 and stage 1b both edit `eta_fields`, so they
run one after the other, in either order; whichever is second adapts.

**SW-1838** (the bounded reader's `find`) is unaffected: it treats names as calls
(match-call-field.md §5), and A changes only how a name is unfolded, not what it is.

## 6. The measurement to collect (stage 0)

This is evidence for stage 1's go-ahead and for whether stage 2 is needed. It changes no
behaviour.

**Instrumentation**, behind an environment variable (`STITCHWORT_FIELD_METRICS`, read once,
as `STITCHWORT_DEBUG_FORCE_UNGLUED` is at `value.rs:2329-2336`), printing a table at exit. For
each re-run of a name's call, count it under:

- **site:** R1 (`conv`), R2 (unifier, `cases`), R3 (read-back), R4 (`unfold_field_for`, once
  SW-2095 is in), R5 (`CallField`'s step);
- **form:** named (N: the value came from `Frame::CallField`, `eta_fields` or `FieldOf`) or
  bare (B). Telling them apart needs a mark: stage 0 can carry a debug-only flag on the
  projection, or, simpler, count at the point each form is made and match by spine pointer;
  the lane picks;
- **outcome:** stuck again (the run thrown away) or unfolded;
- **where:** inside the kernel (`in_kernel_modes`) or the elaborator;
- **cost:** machine steps spent in the re-run (the budget's step counter before and after);
- **sharing:** whether a link would have hit (the base call's cell held a fitting answer at
  the time, which stage 0 can't see without the link, so for R3 and R1 it records whether the
  same definition and arguments were re-run earlier in the same outermost operation, which is
  design B's hit rate, and across operations, which bounds A's);
- **the top definitions** by steps.

**Runs.** `task audit:touched -- Aoc.Year2020.Day20` (the 19,261), `-- Aoc.Year2024.Day11`
(SW-1829's `Map.foldLeft` proofs) and `-- Aoc.Year2021.Day15` (applied fields, R4), each with
the variable set, and the total check steps and wall time beside the counts. Not the whole of
aoc/: that needs Matt's OK, and these three cover the shapes.

**The growth test.** A core unit test in the style of SW-1829's `eta_fields` test: a stuck
`step` on a 4-field record, nested `d` deep for `d` from 1 to 8, compared by rule 1 with a
literal, counting tree runs of `step` (the test-only counters, `machine_runs`,
`value.rs:920-933`, or a new one). In stage 0 it prints the counts, so the shape is on record;
stage 1b turns it into an assertion that the count is at most linear in `d`.

**What it decides** (my call, not a D question):

- Stage 1 goes ahead if the growth test grows faster than linearly (expected) or any of the
  three namespaces spends over 1% of its check steps in re-runs. If neither, the numbers go on
  the ticket and it waits in the backlog.
- Stage 2 goes ahead only if form (B) re-runs are over 1% of a namespace's steps.
- If the kernel's share of R1 to R4 is over half, that goes to Matt with D3020's revisit.

## 7. Stages

Sequencing is mine to decide, so these are decided: 0 can start now (it only adds counters,
in a corner of `value.rs` SW-2095 doesn't touch, but its R4 counter waits for SW-2095, so
start it after SW-2095 merges if that's within the hour); 1a after SW-2095; 1b after 1a; 2
and 3 after 1b, 3 last since it rewrites the readers 1b touches.

**Stage 0: measure.** As §6. Sonnet, 60 min. Tests: the new growth test, `task test:one` on
it; the three `audit:touched` runs with the variable set (those are the measurement).

**Stage 1a: the link's slot.** `Elim::Proj` gains `Option<Rc<FieldOf>>`, always `None`; every
comparison, hash and identity test ignores it. No behaviour change. Sonnet (near the kernel,
mechanical but wide), 40 min. Tests: `cargo test -p stitchwort-core value` (the evaluator's
unit tests, about a minute); `task snap:hashes` showing no change.

**Stage 1b: fill and read it.** §3.1: set in `Frame::CallField`, `eta_fields` and `FieldOf`;
read in `unfold_folded`, the unfolded read-back and `unfold_field_for`; the mode `in_kernel_modes`
turns off (D3020); F12 if it fits. Opus (core evaluator, D2506), 90 min. Tests: the growth
test as an assertion; SW-1829's `eta_fields` test; `cargo test -p stitchwort-core eta`;
`task test:one --` the record-eta examples and SW-2095's `conv-call-field-applied`,
`match-call-field-applied` and `match-as-written-under-field`; `task snap:hashes` and the
`hash_stability` test with no change (no term changes); `audit:touched` on 2020 day 20 and
2024 day 11 with stage 0's variable set, timed against `main` (one run each), counters and peak
memory in the report. Opus review after (D2364: it changes code the kernel runs, even gated).

**Stage 2 (conditional): a memo for bare projections.** §3.2, for form (B) in `conv` and the
unifier only. Opus, 60 min. Tests: a unit test (rule 1 against a stuck call of a 6-field record
runs the call once), `cargo test -p stitchwort-core conv`, `audit:touched` on whichever
namespace stage 0 found the cost in.

**Stage 3: F9's typed view.** One function that reads a call's or name's spine as `Call { args
}` or `Field { args, fields, link }`, replacing `is_call_field`, `folded_parts`, `call_args`
and the guards around them (as-merged review F9), so the shape is checked in one place and
the `unreachable!`s become types. Sonnet, 60 min. Tests: `cargo test -p stitchwort-core`,
`-p stitchwort-elab unify` and `cases`; the examples of stage 1b.

## 8. Decisions

- **D3020: only the elaborator reads a name's link to its call**; inside the kernel names are
  unfolded by running the call, as today (§4)? **[rec: yes, because the kernel's trust stays
  exactly where it is, the elaborator and the kernel can't disagree, and the kernel's share of
  the cost is unmeasured; revisit if stage 0 shows it's most of it]**
- **D3021: close D2992's revisit: an applied function field keeps computing first (1a), with
  no general form `(f x).i a`** (§3.3)? **[rec: yes, because design A removes 1a's one cost,
  the re-run, and the general form would change every reader F9 calls fragile for a display
  difference no proof has needed]**

## 9. Calls I made

- Design A over B as the main fix: B shares work only inside one operation, and the cells A
  reads already exist.
- The link goes on the last projection, not on the head or in a new `Value` variant: `Head` is
  `Copy` and hashed, and a new variant meets the same `_ =>` arms as design D.
- The link points at the base call, never the field's own cell (no cycle).
- Stages 1a and 1b are split so the wide mechanical part is reviewed apart from the part that
  needs care.
- F12 rides with 1b if it fits; it isn't worth a lane on its own unless stage 0 shows R5's
  steps are large.
- Stage 2 and any cell for folded calls wait for numbers.
- The go thresholds in §6 (1% of a namespace's steps, or superlinear growth).

## 10. Tickets to file

| Order | Ticket | Model | Estimate | Tests | Replaces or absorbs |
|---|---|---|---|---|---|
| after SW-2095 | Stage 0: count stuck-field re-runs by site, form, outcome, kernel or elaborator, steps (`STITCHWORT_FIELD_METRICS`); growth test printing counts | Sonnet | 60 | the growth test; `audit:touched` on 2020 day 20, 2024 day 11, 2021 day 15 with the variable set | — |
| after 0 | Stage 1a: `Elim::Proj` gains an empty link slot, ignored by every comparison and hash | Sonnet | 40 | `cargo test -p stitchwort-core value`; `snap:hashes` unchanged | — |
| after 1a, if §6 says go | Stage 1b: names link to their glued call; `unfold_folded`, unfolded read-back and `unfold_field_for` read the call's cell, elaborator only (D3020); F12 if it fits | Opus | 90 | as §7 | SW-1914 itself; core review F1 and F12; as-merged review F1 |
| after 1b, if §6 says so | Stage 2: per-comparison memo for bare projections of stuck calls (rule 1) | Opus | 60 | as §7 | — |
| after 1b | Stage 3: typed view of a call's or name's spine | Sonnet | 60 | as §7 | as-merged review F9 |
| — | Board edit, no lane: SW-2096's brief notes that its folded-call names have no link (§5), and that it and stage 1b both edit `eta_fields` | orchestrator | — | — | — |
| — | Review after 1b (D2364) | Opus | 30 | — | — |

## 11. What this note didn't do

- **No numbers of its own.** The 19,261 is the ticket's; how it splits between the kernel and
  the elaborator, between named and bare forms, and within or across operations is stage 0's
  job. The `k^d` of §1 is reasoned from the code, not run.
- **`Elim`'s size** after the change is inferred, not measured (stage 1a can add a
  `size_of` assertion).
- **SW-2095's diff** was read for the three points of §5 only, not reviewed.
- **The reference evaluator** was read only enough to see it has its own `unfold_folded`
  (`reference.rs:360`), so it needs no change.
- **Folded calls' names** (SW-2096) are left with their re-run; §5 says when to revisit.
