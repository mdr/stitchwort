# Stuck values that say what they wait on

**SW-1845**, 7 Nov 2026, from SW-1321's audit (D2603). Design only: nothing was built or run,
and no number here is measured; each says how to measure it. Written against `main` at
`437852b04`; line numbers are from that commit. Labels: **[checked]** (read here),
**[cited]** (from the review or ticket named), **[inferred]** (my reasoning), **[not
re-checked]** (other systems, from memory). Its questions are D2620 to D2623 (§5).

## Contents

1. [The problem](#1-the-problem)
2. [Options](#2-options)
3. [Interactions](#3-interactions)
4. [Recommendation and stages](#4-recommendation-and-stages)
5. [Questions for Matt](#5-questions-for-matt)
6. [What this note did not do](#6-what-this-note-did-not-do)

## 1. The problem

### 1.1 The sites

SW-1321's audit ([docs/reviews/SW-1321-stale-stuck-calls.md](../reviews/SW-1321-stale-stuck-calls.md))
found eight places that read a call as stuck after the unknown it was stuck on had been
solved. None is unsound. Each gives a wrong failure or a needless wait. **[cited]**

| # | Site | What goes wrong | Ticket |
|---|------|-----------------|--------|
| F1, F1b | `unify.rs:1150` `stale_within`, `:1223` `blocked_within` | an unknown inside a constructor argument (`pickHead [?b] 5`) isn't seen: the pair fails instead of being evaluated again (F1) or put aside (F1b) | SW-1842 |
| F2 | `value.rs:124` `Kept::fits` | a glued call's kept unfolding, stuck when it was kept, is served after its unknown is solved: the epoch counts solutions taken back, not solutions added | SW-1843 |
| F3 | `unify.rs:1540`, the same-head arm | two stale calls of one definition compare by arguments; the failing argument pair isn't stale, so nothing is evaluated again | SW-1842 |
| F4 | `unify.rs:2353` `rename` | a stale spine can mention the unknown being solved, or an out-of-scope variable, that computing would drop | SW-1847 |
| F5 | `queue.rs:905` `tactic_or_wait` | `ring`, `rewrite`, `cases` take the goal as it is on their first run: `ring` sees `pick True x` as an atom apart from `x` | SW-1844 |
| F6 | `dot.rs:112-119` | `.field` on a receiver whose type is a stale stuck call: "can't look up" | SW-1846 |
| F7 | core `conv` from the elaborator (~25 sites) | a wrong "different" where a side predates a solution | SW-1848 |
| F8 | `named.rs:116` | named arguments take the "stuck" path for a type that computes to a `Pi` | none |

### 1.2 The one cause

A case tree that meets an unsolved unknown stops and returns the call as it was:
`Value::Neutral(Head::Def(f), spine)` (`stuck_tree`, `value.rs:1985`). **[checked]** That value
has no record of *why* it stopped. So `force` (`value.rs:581`), which every shape-reading site
calls first, has nothing to go on: `needs_forcing` (`:1796`) is true only for a solved unknown
at the head or a glued call, and a stuck `Neutral(Def)` is neither. Once the unknown is solved,
the value stays stuck until someone reads it back and evaluates it again (`unify::afresh`,
`interfaces::refresh`, `omega::recomputed`, `Ctx::conv_now`, the queue's resumes). Each site
that cares has its own refresh; the eight above don't, or not in every case.

The same cause explains F2: the kept unfolding *is* such a stuck value, and `Unfolding::get`
serves it because nothing says it has gone stale.

So the fix is to give the stuck value the one fact it is missing, and let `force` act on it.

### 1.3 One unknown is enough

A stuck case tree stops at exactly one scrutinee. **[checked: `branch`, `value.rs:1805`]**
That scrutinee, forced, is one of:

- an unsolved unknown, possibly with eliminations (`?r.items`, from record eta's rule 2):
  the tree waits on that unknown;
- a call that is itself stuck: it waits on whatever that call waits on;
- `k + x` with `x` stuck (a number case): it waits on what `x` waits on;
- a variable, or a call stuck on one, or a folded call (opaque, a dictionary, a theorem):
  nothing will change it within this context: it is **rigid**.

Call this one unknown the value's **blocker**. It is exact in the direction that matters:

> While its blocker is unsolved, a stuck call is still stuck, at the same place, with the
> same value. **[inferred]**

The walk is deterministic, and every scrutinee before the stuck one was a constructor or a
number, which more solutions can't change. Within a meta epoch solutions are only added
(`MetaStore::solve_meta`, `metas.rs:178`; `metas_taken_back` is the only thing that moves the
epoch, `:185`) **[checked]**. So the value can't have gone stale until its blocker is solved.
Once the blocker is solved, it *may* compute: evaluating the tree again either takes a step,
gets stuck on a new blocker, or becomes rigid.

So one meta index per stuck call answers "is this current?" exactly, with no set and no
counter. Agda needs blocker *sets* (`UnblockOnAll`, `UnblockOnAny`) because its blockers are
for constraints that mention many metas. A whnf is stuck on one thing.

## 2. Options

The kernel must not depend on elaborator unknowns. The core already knows about them in one
narrow way: `Head::Meta(usize)` exists in values, and solutions come in through the `Metas`
trait (`ev.rs:23`), which the kernel's admission fills with `NoMetas` (every solution `None`,
epoch 0). **[checked]** Each option is judged by whether it keeps to that.

### (a) Stuck calls carry their blocker, set when they get stuck

**The change.** `Head::Def(DefId)` becomes `Head::Def(DefId, Blocker)`, where `Blocker` is a
`u32` newtype with `Blocker::NONE = 0` and `Blocker::on(m)` storing `m + 1`, as `Apart` does
for variables (`value.rs:210`). Like `Apart`, it is a fact about the call, not part of it:
`Head`'s `PartialEq` and `Hash` ignore it (`value.rs:174-198` already do this for `Var`'s
`Apart`). Then:

1. **Set:** `branch` passes the forced scrutinee's blocker to `stuck_tree`:
   `blocker_of(v)` is `m` for `Neutral(Meta(m), _)`, `b` for `Neutral(Def(_, b), _)`,
   `blocker_of(x)` for `NatAdd(_, x)`, and `NONE` otherwise. The `Quot.lift` leaf
   (`Frame::LiftReady`) and the native fallback (`unfold_now`'s last line, when
   `native::run` returns `None`: the first argument that isn't a number) do the same.
   Everything else that builds a `Neutral(Def)` (partial applications, opaque and folded
   definitions, the elaborator's own constructions) gets `NONE`, which is today's behaviour.
2. **Kept:** a stuck call keeps its head when eliminations are added. A stuck `J` pushes
   onto the spine and returns `Neutral(head, spine)` with the head it had (`Frame::JBase`,
   `value.rs:1670`) **[checked]**, and so, I expect, does `project` **[inferred]**. `apply_step`'s `Neutral(Def)` arm pushes the
   argument and goes to `Control::Unfold(id, spine)`, whose fallback rebuilds
   `Head::Def(id)` and would drop the blocker; a call with a blocker is already at its
   arity, so that arm returns the neutral with the argument added instead, keeping the head.
3. **Acted on:** `needs_forcing` gains one arm: `Neutral(Def(_, b), _)` needs forcing if `b`
   is set and solved. `run`'s `Control::Force` then evaluates the call again:
   `Control::Unfold` on the first `arity` eliminations, unglued (as `force_call` does,
   `value.rs:975`), with `Frame::Replay { spine, next: arity }` (`:1699`, the frame a solved
   unknown already uses) for any eliminations after them.
4. **Kept unfoldings (F2):** `Unfolding::get` doesn't serve a kept value that needs forcing
   for this reason, so `force_call` computes it again and keeps the new value. The epoch check
   stays: it is still what protects against solutions taken back.
5. **`force_solved`** (`value.rs:616`, the folded read-back's force) does step 3 too, for a
   bare stuck call (not a `Value::Call`, which it keeps as written). See D2621.
6. **A cheap test:** `Metas` gains `fn is_solved(&self, m: usize) -> bool` (default:
   `solution(m).is_some()`). Today `needs_forcing` clones a solution to test it
   (`MetaStore::meta_solution`, `metas.rs:120`, clones the `Value`). **[checked]** The
   store's version also answers `false` for an index past the end, so a blocker that
   outlived its unknown (a restore drops unknowns, `metas.rs:198`) is inert rather than a
   panic.

**Memory.** None per value. `Head` is 16 bytes today: `Var(usize, Apart)` sets its size, and
`Def(DefId, Blocker)` (8 + 4 bytes) fits in the same 16. `Value` doesn't grow. **[inferred:
`DefId(pub usize)`, `term.rs:15`; `Apart(u32)`]** To measure: `const _: () =
assert!(size_of::<Head>() == 16)` and the same for `Value`'s current size, both added in
stage 0 before the change and kept after.

**Speed.** Setting a blocker costs a match on a value already forced (the scrutinee), once
per stuck call. Testing it costs one comparison with 0 per `force` of a `Neutral(Def)`, plus
an `is_solved` lookup when it's set. The kernel never sets one (below), so for it the cost is
the comparison. Evaluating again costs one walk of the tree up to where it stops, at most what
getting stuck cost the first time, and only when the blocker has been solved since. Under
gluing almost every stuck call lives inside a `Value::Call`'s cell (`unfold_now` returns a
`Call` for any definition at its arity, `value.rs:2056`), so the cell is updated once and
every copy shares it. A bare stuck call (gluing off, or a caller that stored a forced value)
is evaluated again on each `force` of that copy; that is the one repeated cost.

To measure: `task bench -- --no-time` (counts only, about 80 s; D2623) before and after
stage 1, looking at steps and allocations; and a counter `stale_reruns` in the session
statistics (next to `tactic_waited`), read on the examples lane, to see how often step 3
fires.

**What it guarantees.** After `force(v)`, `v`'s head is not a call stuck on a solved unknown.
Every site that starts with `force` (all of them, by the codebase's rule) sees stuck calls as
current at the head, and quote, conv and the tactics, which force each part as they reach it,
see them current all the way down. No site needs its own refresh for this reason again.
Deeper parts that are stale are evaluated again when something forces them, which is the
usual laziness of a weak head.

**Kernel and elaborator.** The blocker is a meta index, the same kind of thing as
`Head::Meta`, which the core already has. The kernel's admission evaluates with `NoMetas`,
so: no value it builds has an unknown at a scrutinee, so it never sets a blocker; and even if
a value with one reached it, `NoMetas::is_solved` is always false, so the blocker is never
acted on. Its answers can't depend on blockers. What the trusted base gains is one arm in
`needs_forcing`, `blocker_of`, and the re-evaluation in `run`; each can only cause a value to
be evaluated again, never to mean something else. A wrong blocker (a reused unknown number,
say) costs either a needless re-evaluation or a missed one (today's behaviour), never a wrong
answer.

**The cost of the change.** About 156 uses of `Head::Def(` in 33 files. **[checked: grep]**
Patterns become `Head::Def(id, _)` and constructions `Head::def(id)`. Mechanical (stage 0).
Where elaborator code rebuilds a stuck call from an old one's head and a new spine, it should
keep the old head; stage 1 reads each construction in `crates/elab` for this (there are a
handful: `omega.rs:530`, `unify.rs:3498`, `effects.rs:230/248`). **[checked: grep]**

**Where else the blocker could live**, and why not:

- *In the spine's shared allocation* (`Spine(Option<Rc<Elims>>)`, `value.rs:293`): no
  sweep, but 8 bytes more in every spine allocation, including every partly applied
  definition while a program runs, where the comment at `:296-300` records that one extra
  allocation cost 7%. And `Var`- and `Meta`-headed spines would carry it for nothing.
- *A new `Value` variant for stuck calls*: every site matching `Neutral(Head::Def)` would
  miss it, which is worse than a sweep that the compiler checks.
- *Stuck cases as eliminations on the blocking unknown*, as in the elaboration-zoo family,
  where a stuck `case` is a frame in the spine of the meta it waits on: then `force` on the
  head would find it with no new field. But Stitchwort's reduction policy keeps a stuck
  definition folded as its name and arguments (`value.rs:5-7`), which conversion,
  `same_stuck_trees`, the `TreeMemo`, printing and the folded read-back are all built on.
  **[inferred]** Not worth giving that up.

### (b) A cheap "may have gone stale" check: a solutions counter

**The change.** `Metas` gains `fn solutions(&self) -> usize` (the trail length; 0 for
`NoMetas`), as SW-1321's F2 fix proposes. `Kept` records it; `fits` refuses a kept stuck
call whose count has moved. For bare stuck calls, the count would have to be stored in the
value (the same `u32` in `Head::Def` as (a)), and `force` would evaluate again any stuck call
whose count is behind.

**Memory and speed.** The same zero bytes if stored in `Head`. But every new solution makes
every older stuck call "maybe stale", including the many stuck on variables or on unknowns
that have nothing to do with it. And a bare copy can't be updated: the re-evaluated value has
the new count, but the copy it came from keeps the old one, so it's evaluated again on every
`force` for the rest of the declaration. The cost grows with forces × solutions.

**Guarantees.** The same as (a) at the head, at a much higher cost. Applied to `Kept` only,
it fixes F2 and nothing else.

**Kernel.** `NoMetas` answers 0 always: fine.

### (c) Blockers returned by `force`/whnf, not stored

**The change.** A `force_blocked(v) -> (Value, Option<Meta>)` that says, for a stuck result,
what it is stuck on; sites that want it (the unifier's `blocked`, the queue's `head_meta`)
ask. This is how Agda's `reduceB` (`Blocked`/`NotBlocked`, with a `Blocker`) and Lean's
`getStuckMVar?` work. **[not re-checked]**

**Memory and speed.** Nothing stored. But for a value that is already stuck, finding the
blocker means walking the case tree again from the arguments: the same work as evaluating
it again. Lean can do it cheaply because its terms keep the matcher application and
`getStuckMVar?` looks at the major premise directly; Agda's terms are syntax, reduced again
on demand anyway. Stitchwort's values are the *result* of evaluation, so the information is
gone unless it was kept. **[inferred]**

**Guarantees.** Only at the sites that ask; everything else (`conv`, tactics, `dot`) stays
stale. This is the per-site approach with a shared helper.

**Kernel.** Untouched.

### (d) Per-site fixes only

**The change.** SW-1842, SW-1843, SW-1844, SW-1846, SW-1847 and SW-1848 as filed. About 5.5
hours of lanes by the audit's estimates. **[cited]**

**Memory and speed.** Nothing stored; each fix adds a refresh (`afresh`, `conv_now`) at its
site, each a read-back and evaluation, the most expensive way to refresh.

**Guarantees.** Each named site, as far as its own test (F1's walk is "64 parts", for
example). Every new site must remember to refresh, and the audit already lists conv sites it
didn't read. The next record-eta-sized change will find more.

**Kernel.** Untouched, except SW-1843's change to `Kept`.

### Side by side

| | (a) stored blocker | (b) counter | (c) returned | (d) per site |
|---|---|---|---|---|
| bytes per value | 0 | 0 | 0 | 0 |
| cost when nothing is stale | one compare per force of a stuck call | one compare | 0 | 0 |
| re-evaluations | once per solved blocker per cell (per copy if bare) | per new solution per copy, repeatedly | at each asking site, every time | at each site, as a read-back |
| covers | every `force` | every `force`, wastefully | the asking sites | the named sites |
| kernel | inert under `NoMetas` | inert | untouched | untouched |
| change size | ~156-use sweep + core change | same sweep + core change | a helper + each site | six tickets |

## 3. Interactions

**Glued unfoldings and the cache's epoch (F2).** Step 4 of (a): a kept value that needs
forcing because its blocker is solved isn't served, so it is computed again and kept. The
epoch stays as SW-1782 made it: it protects against solutions *taken back*, which a blocker
can't see (an unknown solved, used to compute further, then unsolved by a restore). Both
checks are needed, and each covers what the other can't. For a field of a call (`base`,
record eta), each `Kept` is checked on its own as today: a field kept as stuck on `?b` is
recomputed, and recomputing it forces the base, whose own check decides whether it is
recomputed too. The modes check is unaffected. **[inferred]**

**Postponement wake-ups.** Nothing in the queue changes in stage 1. `ready` and `head_meta`
(`queue.rs:1204-1226`) force `needs`, so a stuck call whose blocker was solved is now
evaluated again there, which can only make an item ready sooner. The resumes that evaluate
afresh "so that what was stuck computes" (`Comparison::resume`, `queue.rs:1117`;
`WaitingTactic::resume`, `:936`; `WaitingMatch::resume`, `matching.rs:840`) become redundant
for that reason; stage 2 removes them where staleness was their only reason. The queue's
placeholders are frozen unknowns: a call stuck on one has it as its blocker, and filling it
(`Elaborator::fill`, a `solve_meta`) makes the call compute at its next `force`, which is
exactly the case the resumes' comments describe.

A new possibility, not in stage 1: `head_meta` could return the blocker of a stuck `needs`,
so a check could wait on `Box ?b` as it now waits on `?T`. That would turn some of today's
errors (F6 when `?b` is still unsolved, say) into waits. D2622.

**The unifier.** `stale`/`stale_within` and the `stale` branch of `run` (`unify.rs:276`) go:
`force` does it. `blocked(v)` becomes "forced, `v` is a stuck call whose blocker is unsolved
and not frozen", O(1), with no depth limit, which covers F1b exactly. That is narrower than
today in one way: a call stuck on a *variable* whose argument happens to be an unsolved
unknown (`f x ?a`, stuck on `x`) counts as blocked today and won't. Solving `?a` can't make
it compute, so failing it at once is right, but it may change which error a user sees; stage
1's examples lane shows whether any example notices. F3's same-head arm sees only current
stuck calls after `force`. F4's `rename` forces through `force_solved`, which, by D2621, now
evaluates a stale call again before writing it. **[inferred]**

**Bounded read-back (D2541, D2543).** Re-evaluating is computing, so it is D2541's "compute
to decide", and it never chooses between answers. Its steps count against the same budget as
any evaluation: a re-evaluation that runs out is an `E-RESOURCE` like any other, and D2540's
stage 0c, which lists where a recovered `E-RESOURCE` changes what is elaborated, covers it.
The reader (`mentions`, `unfold_where`, `find`, not yet built) walks values as written with
`force_solved`; with D2621 a stale bare call is walked as its current value, and a
`Value::Call` stays as written, as D2542 means. Its memo of negative answers is per question
(SW-1828's recommendation), and a question solves nothing, so a new solution can't leave a
stale "doesn't mention" behind. If the memo ever outlives one question, it must be keyed by
something that moves with new solutions, not by the epoch alone. **[inferred]**

**Record eta projections.** A tree stuck on a field of an unknown record (`?r.items`, from
rule 2) has that unknown, `?r`, as its blocker: `blocker_of` reads the head of the
projected neutral. `eta_held` calls (`value.rs:1958`) stuck on purpose get their blocker too,
which is right: they are still stuck while it's unsolved, and may compute when it is solved.
`Elim::Proj` after a stuck call keeps the call's head, and re-evaluation replays it
(`Frame::Replay` hands a projection to `ReplayElim`, `:1725`). **[checked the frames;
inferred the rest]**

**The check cache and hashes.** Nothing about a blocker reaches a hash. Values are never
hashed for the check cache; terms are, and `quote` writes a `Head::Def` as `Term::Def(id)`,
with no field for the blocker. `Head`'s `Hash` and `PartialEq` ignore it, so `shape_hash`,
the `TreeMemo` key and `identical` see a stale and a current stuck call alike. `shape_hash` hashes a
neutral's head through `Head`'s `Hash` (`value.rs:3808`) **[checked]**, so it ignores the
blocker with no change. What can move is elaborated
terms: where a stale stuck call was read back *unfolded* into output, it is now read back as
what it computes to, so some term hashes may change. `snap:hashes` and `hash_stability`
record that once. The `TreeMemo` keeps only "equal" by epoch, and the unifier's `CallMemo` is
keyed by the trail length (`unify::effects`), so neither can keep a stale answer. **[checked
`MemoKey`, `value.rs:3517`; cited for `CallMemo`]**

**Undo.** A restore drops unknowns, and their numbers are reused. A blocker naming a dropped
unknown is answered `false` by `is_solved` past the end. One naming a reused number may cause
a needless re-evaluation, never a wrong result. A value computed further using a solution
that's since been taken back is today's problem, solved as today (the epoch for kept cells;
the elaborator discarding an attempt's values on restore). **[inferred]**

## 4. Recommendation and stages

**Recommendation: (a).** It is the only option that fixes the cause for every site at once,
costs no memory, costs the kernel a compare, and makes six of the seven tickets unnecessary.
(b) is (a) with more re-evaluation; (c) is (d) with a helper. Skip the per-site fixes D2603
recommended doing first (SW-1842 to SW-1844): stage 1 costs about as much as the three
together (165 min by the audit's estimates) and they would be deleted by it. Their repros
become stage 1's tests.

Decided here, as implementation detail: the blocker lives in `Head::Def` (§2a, "Where else");
`blocked` becomes exact (§3, the unifier); `Metas::is_solved` replaces the clone in
`needs_forcing`.

### Stage 0: the sweep (no behaviour change)

- **Goal:** `Head::Def(DefId, Blocker)` everywhere, always `Blocker::NONE`; `Head::def(id)`;
  `Head`'s `PartialEq`/`Hash` ignore the blocker; `size_of` assertions for `Head` and
  `Value`; `Metas::is_solved` with the store's out-of-range-safe version, used by
  `needs_forcing`.
- **Tests:** `task test:lane AREA=core`, `task test:lane AREA=elab`, and the extract crate's
  `bound_to_the_prelude` tests (core edits can unbind a native).
- **Model:** DeepSeek, from a goal-level brief (mechanical, compiler-checked); Sonnet as
  fallback. **Estimate:** 40 min.
- **Success:** builds, clippy clean, those tests pass, the assertions hold, no hash moves
  (`task test:lane AREA=hashes`).

### Stage 1: blockers set, kept and acted on

- **Goal:** §2a steps 1-5; `Unfolding::get` refuses a stale kept value; the unifier's `stale`,
  `stale_within` and `blocked_within` replaced by the blocker (`blocked` exact, `stale` gone,
  `run`'s stale branch gone); `rename`'s stuck-call arm forces first; a `stale_reruns`
  counter. Each `Neutral(Head::Def(..))` construction in `crates/elab` read, keeping the old
  head where it rebuilds a stuck call.
- **Tests** (SW-1321's repros, each in the audit's text; not run there):
  - `examples/accept/solved-after-stuck.sw` (SW-1315's, existing): still passes.
  - `examples/accept/solved-after-stuck-nested.sw` (F1: `pickHead [b] 5`) and
    `solved-after-stuck-nested-later.sw` (F1b: the conjuncts swapped).
  - `examples/accept/solved-after-stuck-same-head.sw` (F3: `pick ?b 0` against `pick ?c 0`;
    the audit has low confidence the file shows it; keep it if it passes, note it if it
    passed before too).
  - `examples/accept/solved-after-stuck-ring.sw` (F5: `pickBoth x (Both rfl ring)`) and a
    `cases` twin.
  - `examples/accept/solved-after-stuck-dot.sw` (F6: `(mk rfl 3).succ`).
  - core unit tests in `value.rs`'s tests (they already build a `Metas`, `:4466`): a glued
    call forced while its unknown is open, the unknown solved, forced again, computes (F2);
    the blocker of a call stuck inside a constructor argument is that unknown; a stuck call
    applied to one more argument keeps its blocker and computes once it's solved (the
    `Replay` path); a stuck call evaluated under `NoMetas` has no blocker; `conv` of a stale
    call against its value is true (F7).
  - a unifier unit test for F4 (`rename` on a stale call whose dead branch mentions the
    unknown being solved), with the hand-built values `unify.rs`'s tests use.
  - Then `task test:one -- solved-after-stuck`, `task test:lane AREA=core`, `AREA=elab`,
    `AREA=examples NAME=postpone,stuck,later` (the postponement examples, for the narrower
    `blocked`), `snap:hashes` and `hash_stability` for the new examples, and
    `bound_to_the_prelude`.
- **Model:** Opus (the core evaluator and the unifier, D2506). **Estimate:** 150 min.
- **Success:** every repro above passes; SW-1846, SW-1847 and SW-1848's cases pass with no
  site-specific change; `task bench -- --no-time` (if D2623 allows) shows steps and
  allocations within 2% of the baseline on every benchmark, and if any is over, the
  `stale_reruns` count for it says why.

### Stage 2: the refreshes that only existed for staleness go

- **Goal:** remove or simplify each refresh whose only reason was a stale stuck call, keeping
  each that also does something else (zonking, re-reading a dictionary just found, a new
  cell): `unify::afresh` in `Task::Later` (`unify.rs:283`), the three resumes' `eval(quote_folded(…))`
  (`queue.rs:936`, `:1117`, `matching.rs:840`), `ring_goal`'s fallback (`ring.rs:1279`),
  `omega::recomputed` (`omega.rs:2418`), `Ctx::conv_now`'s second try. Each removal says in
  its commit why it was only for staleness; where in doubt, it stays.
- **Tests:** stage 1's, plus `task test:lane AREA=elab` and `AREA=goals`, and each removed
  site's own examples by name (`task test:one -- ring`, `omega`, `rewrite`).
- **Model:** Sonnet (judgement per site, several files). **Estimate:** 60 min.
- **Success:** the tests pass with the refreshes gone; steps on the benchmarks the same or
  lower (each removed refresh was a read-back and an evaluation).

### Stage 3 (only if D2622 is yes): checks wait on a stuck type's blocker

- **Goal:** `queue::head_meta` returns the blocker of a stuck `needs`, so `.field`, record
  literals and method sections wait on `Box ?b` as on `?T`; `Comparison::blockers` reads
  blockers instead of quoting the pairs where it can.
- **Tests:** a `postpone-…` example per kind (K1-K3) with the type a stuck call on an unknown
  solved later; `task test:lane AREA=examples NAME=postpone`.
- **Model:** Opus (the queue's invariants). **Estimate:** 90 min. A short design section in
  `docs/proposals/postponement.md` first, as part of the lane.
- **Success:** the new examples check; no existing postponement example changes its output.

### Tickets

- SW-1842, SW-1843, SW-1844: closed as covered by stage 1, their repros its tests.
- SW-1846, SW-1847, SW-1848: closed once stage 1's tests show their cases pass. SW-1848's
  sweep of `conv` sites isn't needed for staleness; if a site uses `conv` where it should
  unify, that is another ticket.
- F8 (`named.rs`) has no ticket and needs none.
- New: stage 0, stage 1, stage 2; stage 3 if D2622 is yes.

## 5. Questions for Matt

- **D2620: fix stale stuck calls systemically, by recording the blocker in stuck calls (option
  a), instead of the per-site tickets?** This answers D2603 differently from its
  recommendation: not "both", but stage 1 instead of SW-1842 to SW-1844, and SW-1846 to
  SW-1848 closed when stage 1's tests show them fixed. Stages 0-2 are about 4 hours of
  lanes against the per-site tickets' 5.5, and leave no site to remember. **[rec: yes]**
- **D2621: does the folded read-back (`force_solved`) also evaluate a stale bare stuck call
  again?** Yes means a goal or message never shows `pickHead [True] 5` where the value is
  `5`, and `rename` (F4) needs no fix of its own. A glued call (`Value::Call`) is still
  written as the call, as D2542's "as written" means; a bare stuck call is already the
  result of evaluation, not something the user wrote. No means the read-back writes stale
  calls as today and `rename` gets its own `force`. **[rec: yes]**
- **D2622: should checks that wait (`.field`, record literals, sections) also wait on the
  unknown a stuck *type* waits on (stage 3)?** It would turn some "can't look up" errors on
  types like `Box ?b` into waits. No AoC day is known to hit it, so the benefit is unmeasured.
  **[rec: not now: file it in backlog, and schedule it when a friction note shows the case]**
- **D2623: may stage 1's lane run `task bench -- --no-time` (counts only, about 80 s, once
  before and once after)?** The bench isn't a test tier, but it is wider than the lane's own
  tests, so the test budget wants your say. It is the measure of the one cost this design
  adds (re-evaluations, and the compare in `force`). **[rec: yes]**

## 6. What this note did not do

- Built nothing and ran nothing: the sizes (16-byte `Head`), the costs, and whether each repro
  fails today are inferred from the code, as the audit's were.
- Did not re-check the other systems: Lean 4's `instantiateMVars` and `getStuckMVar?`, Agda's
  `Blocked`/`Blocker` and `wakeConstraints`, Idris 2's re-normalisation of glued values with
  constraints retried in `solveConstraints`, Rocq's `whd_evar`/`EConstr.kind sigma`
  (instantiating defined evars at the head on each view, as `force` does). From memory, for
  context only.
- Did not read every one of the 156 `Head::Def(` uses, nor `project`'s handling of a stuck
  call's head (§2a step 2 expects it to keep the head, as `J` does).
