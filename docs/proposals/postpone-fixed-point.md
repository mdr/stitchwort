# Failed proof searches that wait, without hiding the failure a retry needs

SW-1014, 7 November 2026. A design note, read-only: no code was built or run. Line numbers
are on `main` at `e33f65b64`. It builds on [postponement.md](postponement.md) ("Stage 7:
design" and "As built (stage 7)", where D2140 stopped part (b) of D2128), on the elab
checking review ([code-review-elab-checking.md](../reviews/code-review-elab-checking.md),
F3 and F5) and on [row-settling-order.md](row-settling-order.md), and doesn't repeat them.

Labels: **[read]** read in the source at the line given; **[note]** taken from
postponement.md's as-built record of the SW-1010 lane, which ran it (its trace isn't kept
anywhere else); **[inferred]** my reasoning, not tested; **[memory]** another system's
behaviour as I remember it, not re-fetched for this note.

## Summary

**What users get.** A proof inside a lambda whose goal is only fixed by a *later* argument
will check when nothing is expected of the call (case 4, AoC 2021 day 10, SW-963 (2)):

```
let fact := eachStep _ (a b found => rewrite <- Option.someInjective _ _ found in omega) xs rfl x y h
```

Today the `omega` runs while `eachStep`'s `_` is still unknown and fails. The workaround is
to move the lambda to the end. Nothing that checks today changes: no hash, message or
outcome, which a corpus run can confirm.

**Why D2140 stopped part (b).** The elaborator has about ninety places that try one way and,
if it fails, undo it and try another (postponement.md §5.7, T1). The *after-expected path*
is one of them. An argument that fails in place is set aside, the call's type is compared
with the expected type, and the argument is checked again. Part (b) changed "fail" into
"wait", so these places stopped seeing the failure that sends them to their second way. At
`std/List/Grid.sw:52` the second way was what made the proof check, so the proof broke
[note].

**Recommendation: design B, "wait only where nothing would try again".** A failed search
waits on any unsolved unknown (part (b)) only when no enclosing try-and-undo site would act
on its failure. Inside such a site it fails exactly as it does today. A counter of open
sites, kept by a guard, decides which case applies.

B changes nothing for any program that checks today. Main takes the same path through such
a program (§4.2's argument). B only changes what happens where main would already have
reported an error. The 14 sites that broke are all inside an after-expected retry or
another open site [inferred, checked by stage 0], so they check as they do today.

**Not recommended: the brief's design A,** which runs the expected-type comparison at a
fixed point at the end of every call. That comparison already runs once the call's
arguments are done, in `fallback_named`'s `compare` (`check.rs:5379-5392`) [read]. With
part (b) on, it ran and `?48` still wasn't solved [note]. The missing piece is not a
comparison. It is the *second elaboration* of the lambda, against a goal that is now known
[inferred, medium confidence]. A would also add a comparison to programs that check today,
so it changes them.

## 1. The problem, plainly

**Case 4.** `eachStep`'s first parameter `f` is written `_`. Only the later argument `rfl`,
of type `List.map xs f = List.map xs next`, says that `f` is `next`. The lambda comes first,
so it is checked first. After the `rewrite`, the `omega` inside it faces a goal that still
holds the unknown (`a < ?x a`, roughly), and it can't prove that. Nothing is expected of a
`let` without a type, so there is no second try. As a theorem's body the same call checks,
because the after-expected path checks the lambda again.

**What part (b) did.** Stage 7's rule 2 lets a failed `rewrite`, `cases`, `omega` or `ring`
wait instead of failing (`queue::tactic_or_wait`, `queue.rs:898-929`) [read].

- Part (a), built: it waits only on an unknown the declaration is sure to settle, one of the
  queue's or an unproved obligation's (`search_pending`, `queue.rs:835-846`).
- Part (b) widened that to any unsolved unknown. Case 4 then works: the `omega` waits,
  `rfl` solves `f`, and the end of the call (W1) runs the `omega` again.

But (b) broke `std/List/Grid.sw:52`, four sites in `std/Parse/Reads.sw` and 9 sites in 7
AoC proof files [note]. At `Grid.sw:52`, a `rewrite` sits inside two lambdas passed to
`List.anyElim _ _ …`.

- On main, the `rewrite` fails, so the lambda fails in place. The after-expected path then
  compares the call's type with the goal and checks the lambda again. The second time the
  `rewrite` sees a known goal and succeeds.
- With (b), the `rewrite` waits on `?48` instead. The lambda "succeeds", so the second check
  never happens, and nothing ever solves `?48` [note].

**The general shape.** A wait is invisible to whatever encloses it. Any enclosing code that
would have *done something different* because of the failure now doesn't. The
after-expected path is the one the trace caught. It isn't the only such place (§3).

## 2. What the code does today

- **Application elaboration** is `apply_args_postponing` (`check.rs:2785-3061`) [read]. It
  has three ways to delay an argument:
  - **Lambdas** are checked in place. Where something is expected of the call and the
    lambda's type has unknowns (`late_able`, `:2831-2833`), a snapshot is taken first. On
    failure the lambda is undone and held, with a placeholder (`:2840-2854`).
  - **Other arguments** do the same under a snapshot (`:2933-2956`).
  - **Proof searches** are held unconditionally and checked last (rule 1, `:2902-2906`,
    `check_searches_last` at `:3115-3150`).
- **The end of a call** runs in a fixed order:
  1. W1, which resumes the call's own waiting checks (`:3004`);
  2. the searches (`:3005-3008`);
  3. only if something was held after a failure (`:3009`), the comparison of the call's
     type with the expected one (`unify`, then `unify_solving_arguments`, then
     `compare_waiting`), followed by the held arguments, checked again (`:3038-3046`).

  The comparison in step 3 runs **only after a failure**: `after_expected` is filled
  nowhere else.
- **`expecting` exists only when `infer_expecting` set it** (`check.rs:5453-5473`). That is,
  the call is checked against a known type that isn't a bare unknown. A `let` without a type
  has none, so case 4 has no after-expected path.
- **Before the arguments**, `fallback_named` (`check.rs:5363-5392`) first tries `propagate`
  (`:5890`). It compares the result type with the expected type up front, when the result
  mentions no argument, or only arguments written `_` (`by_holes`, `:5943-5951`).
  - `propagate` is itself a try-and-undo site. If the propagated elaboration fails, it is
    undone and the call is elaborated again with propagation off (`:6037-6071`).
  - Either way, the call ends with `compare` (`:5762`). This is the comparison that runs
    after W1 under (b), and it uses no `unify_solving_arguments`.
- **Waiting searches** (`WaitingTactic`, `queue.rs:928-951`) are resumed at four points:
  - an enclosing call's W1 (`resume_application`, `:1294`);
  - each round of the obligations loop (W3, `auto.rs:108-141`);
  - before lifting (W2);
  - the end of a part (W4, `settle_queue`, `queue.rs:1477`).

  Each point resumes only items whose unknown is solved (`resume_from`, `:1317-1345`). A
  resumed search runs again on its goal read afresh. One still waiting at W4 reports the
  error it first gave (`tactic_or_wait` passes `e` to `queue`, `:917`).
- **A `match` doesn't wait for an ordinary unknown in its expected type**
  (`matching.rs:735-748`) [read]. Such a `match`'s type is an unknown that only its
  alternatives fix, so the alternatives' goals stay unknowns.

## 3. Why each of part (b)'s breakages happened

**Two kinds of unknown.** A waiting search is resumed when an unknown in its goal is solved.
That only helps for unknowns that some later step solves:

1. **Unknowns a later comparison solves.** In case 4, `rfl` compares `List.map xs ?f` with
   `List.map xs next`. A wait resolves these.
2. **Unknowns that only a second elaboration removes.** They exist only because the first
   elaboration ran with less information: a `match` checked against an unknown, a call
   inferred because its expected type was a bare unknown (`infer_expecting`'s early return,
   `check.rs:5459-5464`), or a propagation turned off after a failure (`:6045`, `:6056`).
   The second elaboration doesn't solve them. It undoes them (`snapshot.restore`) and makes
   new, known goals. A wait can never resolve one of these: nothing will ever solve it.

**Grid.sw:52 is kind 2** [inferred, medium confidence].

- The evidence: under (b), the call's own last comparison (`compare` after W1) ran, and
  `?48` stayed unsolved [note].
- The likely cause: the `rewrite` is inside two `match`es inside two lambdas, so it sits
  under exactly the shapes kind 2 comes from.
- I couldn't confirm which of the three shapes it is without running the code. Stage 0
  confirms it.

**Which try-and-undo site each breakage went through.** Only `Grid.sw:52` was traced, and it
went through the after-expected path [note].

- The four `Reads.sw` sites are `rewrite`s inside `Witness`/`Both` terms in lambdas given to
  calls with `_` arguments. That is the shape `propagate`'s own comment cites
  (`Parse.readsBind _ _ _ _ reads (x => …)`, `check.rs:5935-5936`). So some may go through
  `propagate`'s second alternative rather than the after-expected path [inferred, not
  traced].
- The 9 AoC sites weren't analysed one by one.

This matters for the choice. A fix aimed at the after-expected path alone (design C below)
would miss any breakage that went through `propagate`'s second try. The same goes for
`retrying` (`check.rs:2755-2781`), the local-definition retries (`lib.rs:2451-2476`) and
the total-row re-check (`lib.rs:2639-2657`).

**Why stage 7's assumption W1 failed.** The assumption was that "an unknown still unsolved
at the end is an error anyway, so waiting on it can't turn an accepted program into a stuck
one". It treats the wait as the only thing that changes. But the failure was also a signal
to the enclosing site. Remove the signal and that site takes a different path.

## 4. Designs compared

### 4.1 A: the expected-type comparison at a fixed point (the brief's)

**The change.** The end of a call becomes a loop:

1. W1.
2. If something is expected of the call and any of its own items waits on an ordinary
   unknown, compare the call's type with the expected type (`unify`, then
   `unify_solving_arguments`, then `compare_waiting`), at most once.
3. W1 again, until nothing moves.

Option (iii) of the as-built note adds one more rule: an argument whose check left a search
waiting on an ordinary unknown counts as failed in place, so it is held and checked again
after the comparison.

**What it should do.** Kind-1 waits get their unknowns solved inside the call, not only at
an outer W1 or at W3/W4. With (iii), the Grid shape gets its second elaboration back.

**Problems.**

- Without (iii), Grid stays broken. The comparison A adds is what `compare` already does
  after W1, except for `unify_solving_arguments`, and under (b) that comparison didn't solve
  `?48` [note].
- With (iii), A fixes the after-expected path only. The other sites of §3 still lose their
  failure signal.
- The comparison runs on programs that check today: every call with an expected type whose
  arguments queued a waiting search. `unify_solving_arguments` takes solutions from the
  arguments of two calls of the same function, which is a choice. So hashes may change, and
  a program could fail that checks now.
- There is no clean argument that it is safe, only "the corpus didn't break".

**Termination** would be easy: one comparison per call, one re-check per held argument
(T2's existing kind).

### 4.2 B: wait only where nothing would try again (recommended)

**The change.** The elaborator keeps a count of open try-and-undo sites, "speculation",
whose second way would run if the code inside them failed. `tactic_or_wait` uses it when a
search fails on an unknown that isn't in `search_pending`:

- **count > 0:** fail, as today. The enclosing site gets its failure and does what it does
  today.
- **count = 0:** wait on every unsolved, unfrozen unknown in the zonked goal, woken by any
  of them. This is part (b) as SW-1010 built it.

Part (a)'s waits, on `search_pending` unknowns, are unchanged at any count.

**Why it is safe: the conservative-extension argument** [inferred, checkable].

1. Take any program that main accepts, and follow main's run.
2. Main and B differ only at a search that fails on an ordinary unknown while the count is
   0.
3. Count 0 means that no enclosing site would take another way on that failure. So main
   passes the error up to the declaration, and the declaration fails.
4. That contradicts acceptance. So main's accepting run meets no such point. B makes the
   same choice at every point and builds the same terms, with the same hashes.

B only changes programs that main rejects. There, a failure becomes a wait, and the program
may check (case 4), or fail later with a better message, or fail with the same error.

**The proof has one premise: the count must cover every site that acts on a failure.**

- Over-counting is safe: B fails where it could have waited, which is main's behaviour.
- Under-counting is the risk.
- So the guard is on by default and a site opts out with a written reason (§5.2).
- A missed site shows up as a count-0 wait inside a program main accepts, which the corpus
  check counts (§6).

**Case 4 under B.** At its `omega` the count should be 0 [inferred]:

- the call is a `let` value with nothing expected, so it has no `late_able` snapshot and no
  `propagate`;
- it has no list of numbers, so no `retrying`;
- the `rewrite` around the `omega` checks its body after its rules, outside their snapshots
  (`rewrite.rs:322-323`).

Stage 0 measures it.

**`reject/lambda-after-expected-unfolded.sw`** becomes an accepted program under (b)
[note]. Under B it should too [inferred]:

1. The lambda fails in place (count > 0) and is held.
2. The comparison and re-check run as today.
3. The re-checked `rewrite` (count 0 now, if nothing else is open) waits on `?f1`.
4. `compare` finds the `Add` dictionary and solves `?f1`, and the `rewrite` resumes at W3.

The program is correct, so accepting it is right.

**What it costs.**

- One `Cell<usize>` on `Decl`, set by a guard. Elab review F2/F4 says "put back what's
  set": use `ScopedCell`, and `Decl::leftover` asserts it is 0.
- An audit of the ~90 sites.
- A zonk of the goal at each count-0 failure, which is rare.

**What it rules out.** A search inside a speculative region still fails as it does today,
even where waiting would have worked. One example is a lambda inside a call whose by-holes
propagation is being tried, if that lambda needs a later argument's unknown and no retry
supplies it. Every such program is rejected today, so nothing is lost. It is just not
gained either (D2932).

### 4.3 C: part (b) only outside the after-expected path

**The change.** This is the as-built note's option (ii): a flag set while an argument is
checked in place with an after-expected retry possible.

**It is B with a one-site count.** It fixes Grid and case 4. It misses the breakages that go
through `propagate`, `retrying` or the declaration-level retries (§3), and there is no
argument that it is safe. Not recommended: the extra cost of B over C is the audit, and the
audit is what makes B safe.

### 4.4 D: re-elaborate the enclosing lambda when its search can run

**The change.** Instead of the search alone waiting, the enclosing argument waits as
syntax. When an unknown in the search's goal is solved, the whole lambda is elaborated
again. Agda and Lean do this: they wait as syntax (Agda's `CheckExpr` problems, Lean's
postponed terms; postponement.md §3).

**What it gives.** Kind-2 unknowns too, inside speculative regions.

**Costs.**

- It reverses §5.2's end state: a lambda checked in place, with only its stuck pieces
  waiting.
- It re-elaborates bodies, which is the doubling at every level of nesting that
  `propagate`'s by-holes rule was added to avoid (`check.rs:5935-5942`).
- It needs its own isolation argument.

Not now (D2932).

| | case 4 | Grid and the other 13 | programs that check today | safety argument | cost |
|---|---|---|---|---|---|
| A (fixed-point comparison) | yes | Grid only with (iii); others unknown | may change | corpus only | medium |
| **B (wait where nothing retries)** | **yes** [inferred] | **yes, by construction** | **identical** | **§4.2, plus a counter** | **audit + small change** |
| C (after-expected flag) | yes | Grid; others unknown | may change | none | small |
| D (re-elaborate) | yes | yes | may change | new | large |

## 5. The recommended design in detail

### 5.1 When the expected-type comparison runs

The brief asked when it should run. Under B it **doesn't move**:

- **before the arguments**, by `propagate`, when the result type mentions no argument or
  only `_`s (as today, D2129);
- **after the arguments**, on the after-expected path, when an argument failed in place
  (as today);
- **as the call's last step**, by `compare` (as today).

What changes is the signal that starts the second of these. Inside a site that would retry,
a search still fails, so the after-expected path still sees its failure. No comparison is
added and none is moved, which is why accepted programs can't change. D2140 asked for "a
rework so that the after-expected comparison doesn't depend on a failure". B keeps the
dependence, and makes sure the failure still arrives wherever something depends on it.

### 5.2 What counts as an open site

The default is to count, so the guard goes in the primitives. Two kinds of site don't take
a `Snapshot`, and stage 0 lists them:

- **Sites that catch an error without a snapshot.** These are the `Err(e) if e.code == …`
  sites of review F5 (`numbers.rs:1568` and others), and any `.ok()` or `is_err()` on a
  check of user syntax.
- **Declaration-level retries:**
  - `with_local_retries` (`lib.rs:2451-2476`), open while local definitions remain to
    preadmit;
  - the total-row re-check (`lib.rs:2639`), open once a rigid divergence has been noted;
  - the partial-test retry (`Elaborator::test`), which catches `E-PARTIAL` only.

| kind | rule | examples |
|---|---|---|
| `Snapshot` held while user syntax is elaborated, with another way after a failure | counts (the guard in `Snapshot::take`, released when it is dropped or restored) | `late_able` (`check.rs:2840`), argument after expected (`:2933`), `propagate` (`:5933`, `:5950`), `retrying` (`:2759`, `:2766`), `transaction`/`attempt` (`undo.rs:144-166`) |
| a site that restores and passes the same error on | opts out, with the reason in a comment | `tactic_or_wait`'s own `before` when its goal holds no `search_pending` unknown (it decides the wait; checked on the restored state, `queue.rs:906-908`, so the condition is exact at entry) |
| a site that catches only given codes, none of which a search failure can become | opts out, naming the codes | `pure_first` (`E-ABILITY`, `check.rs:1764`, review F5's `:1815`/`:1840`), the partial-test retry (`E-PARTIAL`) |
| a snapshot used only as a mark (to restore on success, or to measure) | opts out | `rewrite.rs:758`, `:810` (rule re-elaboration marks) [inferred: stage 0 checks each] |
| a catch with no snapshot | a guard by hand | F5's code-choosing sites |
| declaration-level retries | a condition consulted at the failure, not a guard | the three above |

Whether a code-filtered site is transparent depends on which codes a search failure can
arrive as, after error frames (`queue::framed`) map it. When D2653's internal error kinds
land, each site will declare the kinds it catches and this table becomes code. Until then,
stage 0 writes the list down. I decide this myself, as an implementation detail. The safety
argument doesn't depend on it, since over-counting is safe.

### 5.3 What a count-0 wait waits on

A count-0 wait waits on every unsolved unknown in the zonked goal (`zonk_keeping`, as
`search_pending_in` does at `queue.rs:859`), except frozen ones: a helper's call, a local
definition, an open goal. Elaboration never solves those (`matching.rs:745-747`). The wait
is woken by any of them (`Check::wakes`), as stage 6's waiting comparison is
(`queue.rs:1160`). This is what SW-1010 built and measured [note].

### 5.4 Termination: by counting, never by the clock (D2543)

B adds no attempt site and no loop. The count is structural: it is the nesting of sites
open at that moment, a pure function of the syntax and the state. A count-0 wait is an
existing kind of item (`WaitingTactic`), so T1 to T4 (postponement.md §5.7) hold
unchanged, given one fact about waking:

- **An item is resumed only after an unknown it waits on is solved.** Within one branch
  (no restore), each unknown is solved at most once.
- **Each resumption either finishes, fails, or waits again** on the unknowns of its goal as
  re-read, all unsolved at that moment.

So in one branch an item is resumed at most once per unknown solved in that branch. The
branch's elaboration is finite (T4), so the resumptions are too.

This needs one check. `wakes` must compare against the unknowns the item waits on *now*,
not the ones it first waited on. Otherwise an item whose unknown was solved, and which
waited again, would be woken by the same solved unknown on every round of `resume_from`
(`queue.rs:1330-1341`). That would be an infinite loop in a progress-driven loop.

Make it a counted check, not a `debug_assert`: no tier runs those (review F3, SW-1903). Each
resumption of a `WaitingTactic` records the trail length. If a wake finds no solution since
that length, that is an internal error. The step budget stays the only limit (`budget.step`,
§5.7), and running out is `E-RESOURCE`, which is fatal (`undo::fatal`, `undo.rs:115-117`).
`tactic_or_wait` passes fatal errors on without waiting (`queue.rs:906`), so a search that
runs out never becomes a wait and never selects a path.

### 5.5 Errors

- **Programs that check today:** nothing changes (§4.2).
- **A count-0 wait that later succeeds:** the program checks (case 4).
- **A count-0 wait resumed that then fails:** the error is the search's own, against the
  goal now known, as `search-after-call-false.sw` shows for rule 1. This is better: fewer
  `?N` in goals.
- **A count-0 wait still waiting at W4:** the error it first gave, as built
  (`queue.rs:917`, reported by `stuck_report`, `:1712`).
- **A count-0 wait, then a hard error later in the same declaration:** on main the search's
  error came first and elaboration stopped. Now elaboration goes on, and the later error
  ends the declaration.
  - **Rule:** the later error comes first. Each search still waiting follows it as a
    further error (`branch_errors`, the existing limit of two more), in creation order.
  - The later error is sometimes the cause (a later argument that doesn't fit), and the
    search is then a consequence.
  - Stage 1 lists the reject examples whose output changes because of this. I decide this
    myself.

### 5.6 Determinism

The decision depends on the count and the goal's unknowns. Both are functions of the
syntax and the elaboration state, never of time or of address order. The wake set is only
asked "is any solved" (a `bool`), so hash-set iteration order never reaches a choice.
Resumption stays in creation order. The deterministic collections
(`core/src/collections.rs`) cover the rest.

### 5.7 The queue's invariants

Add **invariant 9, "no wait under speculation"** to `queue.rs`'s list (`queue.rs:68-110`):

> A search waits on an unknown that the declaration isn't sure to settle only where no
> enclosing site would act on its failure.

`undo.rs`'s rule for callers (`:39-45`) gains a sentence: a new try-and-undo site counts as
open (the default) or says why not.

## 6. What would prove it safe

**Before the implementation lane (stage 0, instrumentation only).** Add the count and its
counters with behaviour unchanged. Then, with part (b) behind a scratch switch that isn't
merged:

- Count, over std, the examples and the 7 AoC files, the searches that fail on an ordinary
  unknown, split by count 0 and count > 0. Expected: all 14 breakage sites at count > 0;
  case 4 and `lambda-after-expected-unfolded.sw` at count 0.
- For `Grid.sw:52`, name the open site and the kind of `?48` (§3). For each of the other 13,
  name the open site. If any breakage turns out to be at count 0, B doesn't fix it, and the
  site that should have counted is missing from the audit.

**Before merging (stage 2, the corpus check).** The conservative-extension argument predicts
two exact results. Both are measurable:

1. **Identical output on every program that checks today:**
   - std, every accept, soundness, goals and extract example, every AoC namespace
     (`check --no-cache`), rogue;
   - the same outcomes, the same messages and warnings, and the same hashes (hash
     snapshots unchanged, no `snap:hashes` update except new examples).
2. **Zero count-0 waits over that corpus**, as a `STITCHWORT_TIMINGS` counter (not a debug
   assertion). One count-0 wait inside a declaration main accepts means a site is missing
   from the count.

Then a diff of every reject example's output against main, each change listed with its
reason. Expected: `lambda-after-expected-unfolded.sw` moves to accept/, and a few messages
change where §5.5's ordering applies. The elaborator fuzzer (`crates/driver/tests/fuzz_elab.rs`,
step limit and a 60 s watchdog) checks termination from outside. The watchdog is a test
harness's limit, not the elaborator's, so D2543 is kept.

**Cost.** Whole AoC with no cache took about 69 s after SW-1829 (its merge message). With the
examples and rogue, I'd expect a few minutes [inferred: to be measured on main first]. This
is broader than a lane's test budget, so it needs Matt's OK (D2931).

## 7. How other systems do it

- **Lean 4** [memory, beyond postponement.md §3's cited facts]:
  - Postponing is allowed only while the context's `mayPostpone` is set. `withoutPostponing`
    clears it where a caller needs a definite answer.
  - A resumed postponed term that fails while `postponeOnError` is set is restored and
    counts as no progress (`resumePostponed`, cited in §3). A final pass with postponing off
    commits or reports.
  - `by` blocks run after everything else (stage 7, [L1] `:590-598`), so a tactic never
    triggers a second elaboration. Lean has no after-expected path to starve, and its
    `match` postpones on an unknown expected type. These are the two places Stitchwort
    differs.
  - Termination is by progress, and the only limits are counted (heartbeats, recursion
    depth), not timed.
  - B's count is Lean's `mayPostpone`, derived from the open sites instead of set by hand.
- **Agda** [memory, plus §3's citations]:
  - Postponed problems and constraints wait on a blocker, any of several metas
    (`wakeupConstraints`, [A3] `:246-251`), which is §5.3's wake rule.
  - Speculative checks (a conversion tried to choose between ways, instance candidates) run
    under `noConstraints`. It turns any constraint the attempt would leave into a failure of
    that attempt. **That is B's rule**: inside a site that may try again, a wait is a
    failure.
  - Agda has no defaulting and reports unsolved constraints at the end, as W4 does for a
    count-0 wait.
- **Idris 2:** `delayOnFailure` tries first and delays on a matching error ([I1]), which is
  `tactic_or_wait`'s shape. Its delayed elaborators are retried while there is progress,
  then once more reporting all errors (`elabTermSub`, [I3] `:110-148`).

## Questions for Matt

- **D2930: Make part (b) safe by letting a failed search wait on any unknown only where no
  enclosing try-and-undo site would act on its failure (design B)? This replaces moving the
  expected-type comparison to a fixed point (design A).** [rec: yes. B keeps every program
  that checks today exactly as it is, by an argument we can check with a counter, and it
  covers all the retry sites, not just the after-expected one. A adds a comparison that
  changes programs that check today, and doesn't fix the Grid shape on its own.]
- **D2931: Before stage 1 merges, a one-off corpus check as an agreed exception to the lane
  test budget?** It would cover whole AoC with `--no-cache`, rogue, every example and the
  hash snapshots, and expect zero changes on accepted programs and zero count-0 waits.
  [rec: yes. Equivalence with main is B's whole claim, and only the full corpus tests it.
  Probably a few minutes; the lane measures main first.]
- **D2932: Accept B's limitation: a search inside a region that may try again still fails as
  today, rather than re-elaborating the enclosing lambda when its unknown is solved, as
  Agda and Lean do (design D)?** [rec: yes. Nothing that checks today is lost. D reverses
  §5.2's end state and doubles the work at each level of nesting. Revisit only with a
  measured case that needs it.]

Decided here, as implementation details:

- the guard's default is "counts", with written opt-outs (§5.2);
- the error order when a wait is followed by a hard error (§5.5);
- the wake check is counted, not a `debug_assert` (§5.4).

## Tickets to file

In order. SW-1014 becomes the parent; these are its stages.

1. **Stage 0: count of open retry sites, measured only** (Opus, 75 min).
   - `Decl::speculation` as a `ScopedCell` count, guarded in `Snapshot::take`, with the
     opt-outs of §5.2, the hand guards for F5's code-choosing sites, and the three
     declaration-level conditions.
   - Counters in `STITCHWORT_TIMINGS`: searches that fail on an ordinary unknown, at count 0
     and at count > 0. No behaviour change.
   - With part (b) behind an unmerged scratch switch, classify the 14 breakages and case 4
     (§6).
   - Write the site table into the stage-1 brief.
   - Tests: `task test:one` for the queue and undo unit tests; `stitchwort check` with
     timings on `docs/proposals/postponement/stage7/lambda-before-later.sw`,
     `examples/reject/lambda-after-expected-unfolded.sw` and std (which loads `Grid.sw` and
     `Reads.sw`); the namespaces of the 7 AoC files only.
   - Stops if any breakage is at count 0 and no missing site explains it.
2. **Stage 1: part (b) where nothing would retry** (Opus, 60-90 min; after stage 0 and
   D2930).
   - `tactic_or_wait` waits on any unsolved, unfrozen unknown at count 0, woken by any, with
     §5.4's counted wake check and §5.5's error order.
   - New accept example with case 4 (`lambdaFirst`); `lambda-after-expected-unfolded.sw` to
     accept/ if it checks, its comment rewritten.
   - Queue unit tests: "a failed search inside an open site fails", "outside one it waits",
     "a woken item that waits again isn't woken by the same unknown".
   - Invariant 9 in `queue.rs`, the sentence in `undo.rs`, an "As built (SW-1014)" section
     in postponement.md.
   - Tests: the new examples via `task test:one`, `snap:hashes` for the new example files
     and the `hash_stability` test, the queue unit tests, the 14 breakage sites' files.
   - It closes SW-963 (2).
3. **Stage 2: corpus check of B** (Sonnet, 30-45 min; after D2931). The runs of §6: outcome,
   message and hash diff against main over std, every example, whole AoC with `--no-cache`
   and rogue; the count-0 counter over the accept corpus; the reject-example diff listed.
   - If it finds a count-0 wait in an accepted program, it stops and reports the site,
     which goes back to stage 1's Opus lane.
4. **Later, absorbed into D2653's sweep:** the code-filtered opt-outs of §5.2 become
   declared error kinds. Not a separate ticket.

Related tickets:

- **SW-1903** (queue invariants in the test tiers): §5.4's wake check is a counter, so it
  doesn't wait for SW-1903.
- **SW-1009** (case 6, stage 6's flex-flex waiting) and **SW-1008** (case 7, folded expected
  types) are not affected.

## What this note doesn't cover

- **The 13 breakages other than `Grid.sw:52`, one by one.** Nobody has traced them; stage
  0 does.
- **Which kind `?48` is.** §3's reading is inferred from the as-built record, not from a
  trace.
- **The exact list of the ~90 sites.** The kinds and examples are in §5.2; stage 0 writes
  down each site.
- **Lean's and Agda's facts marked [memory].** I didn't re-fetch `mayPostpone`,
  `withoutPostponing` or `noConstraints` for this note; postponement.md's sources are at the
  commits listed there.
- **Whether `propagate`'s second elaboration should exist at all.** That is stage 5's
  question. As retry sites are removed, more searches reach count 0 and B accepts more
  without any change.
