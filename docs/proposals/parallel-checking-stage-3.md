# Parallel checking, stage 3: statements first, proofs side by side (SW-4753)

Fable paper lane, 24 November 2026, after D3730 (the end state is stage 3; its kernel form
"comes back to him"), D3731, D3732 and D3733. It continues
[parallel-checking.md](parallel-checking.md), sections 8 to 11, and is a file of its own
because it is the note that goes back to Matt for decisions and the parent is 2,200 lines.
The code was read at `0fa2cb1ca`, with the pilot on `lane/SW-4730`; nothing was built and no
check was run. Marks: **[measured]** by a run that is cited; **[verified]** read today;
**[estimated]**; **[not verified]**. "The parent" is `parallel-checking.md`.

## 1. Summary

**The problem.** `check --jobs` checks files (namespaces) side by side, but a file can't
start until every file it uses has finished, proofs and all. The formatter's files form a
chain 25 deep, so however many cores there are, the run can't be shorter than that chain:
97 s on one job, 40 s on four, and no better on eight (46 s) **[measured 24 Nov,
`measured-2026-11-24/jobs.txt` and `stage2-step2.txt`, library cached]**. Yet 78% of the
work is proofs **[measured, `shares.txt`]**, and nothing that comes later can look inside a
proof.

**The change.** Each file is checked in two pieces. An *interface pass* checks its
definitions and the statements of its theorems, skips the proofs, and hands the result to
the files above at once. A *proof job* is today's whole check of the file, run whenever a
worker is free. The chain then carries only definitions and statements, and all the proofs
run side by side. For the length of one run, a file can be checked against a theorem whose
proof hasn't been checked yet. Nothing is reported from those workers: as now, the answer
comes from the ordinary one-at-a-time check at the end, which believes only files whose
every proof passed, so an unproved theorem can cost time and never a wrong "checked".

**What it should do.** The formatter, library cached, on 8 jobs: **20 to 33 s, against 46 s
today (and 97 s on one job)**, so about 3x to 4.8x where stage 1 gives 2.4x; on 4 jobs about
30 to 35 s against 40 s **[estimated from the measured shares; section 8]**. The gain grows
as proof files are added, because they no longer lengthen the chain. **AoC gains nothing**
(its graph is flat already: 38 s to 8 to 9 s on 8 jobs **[measured]**), nor does a check
after a small edit. A measurement that costs about 20 minutes comes before any building and
decides whether to build (section 9, step 0).

**For Matt:** three decisions (section 10): the trust change, the rule for a `def` written
inside a proof, and when results are saved.

## 2. What is already there

- **Stage 1** (section 9 of the parent, `crates/driver/src/parallel.rs`): worker threads,
  each with its own session kept for the whole run; a board of namespaces that are ready,
  running, written or left; a claim table so two workers don't elaborate one library file;
  then the ordinary sequential check over the same store (the *last pass*), which produces
  every message, the summary and the exit code **[verified]**.
- **Stage 2** (section 10, SW-4734 and SW-4735): the *stated theorem*, a final theorem with
  its statement and no proof in this session, made by one kernel function,
  `check::admit_trusted_stated` (`crates/core/src/check.rs:4150`), called only by the
  cache's replay (`Elaborator::admit_stated`, `crates/elab/src/cache/mod.rs:4686`) for an
  entry this build wrote exactly. An entry has two parts, A (what a dependant can read) and
  B (proofs); workers load dependencies from part A alone. Every command that uses what it
  loads asserts its session holds no stated theorem (`holds_stated_theorems`, `:465`)
  **[verified in the code and in `docs/reviews/SW-4735-fable-review.md`]**.
- **Not there:** `check::leave_stated` (10.2 of the parent, item 2), and anything that makes
  a stated theorem from a proof that has not been checked. D3732 left that to this note.
- **The pilot** (section 11, SW-4730): leaving out the proofs of lone, non-recursive
  theorems gives the same interface digest as the full check in 148 of 150 `tools/fmt`
  namespaces and 291 of 291 of `aoc` **[measured, `interface-pilot-fmt.txt`,
  `interface-pilot-aoc.txt`]**. The two that differ have one cause, an `equation_skips` row
  (SW-4751, being fixed). The pilot left out 4,527 proofs in `tools/fmt` and elaborated
  1,051 anyway (recursive, mutual or `decreasing`: 19%), and 2,364 against 505 in `aoc`
  (18%) **[measured, summed from the same files]**. SW-4752 is testing whether those can be
  left out too; its result was not in when this was written.

## 3. The interface pass

**What it does.** It is the ordinary elaboration of a namespace, in source order, against
the interfaces of the namespaces below, with one difference: for a theorem that can be
*deferred* it elaborates the statement (the kernel's `declare_def` checks it is a type and a
proposition, as now) and then calls `check::leave_stated` on it, where the full check would
elaborate the proof and call `define_group`. Later declarations of the same namespace see a
finished theorem, exactly as they see one loaded from part A (Lemma B′, 8.2 of the parent;
the seven "has it a body?" tests already go through `Def::defined()`). At the end it encodes
the namespace as a part A with an empty part B, computes the interface digest with the
cache's own digest pass, and publishes the result as an **interface entry**.

**Which theorems are deferred.** The rule must be decidable before the proof is looked at,
and must be the same in every session. A theorem's proof is deferred when all of these hold:

1. It is a `theorem` of a project namespace (not the prelude or a library file).
2. It carries none of the marks stage 2 refuses to load as stated: an instance, `fold`,
   `opaque`, `tailrec` or parameter-default mark, an `unfolding` list, a run body or a
   validator (`stated_on_load`, `cache/mod.rs:2392`). These are attributes of the
   declaration **[not verified that each is known before the proof is elaborated; step 2
   checks, and any that isn't goes on the elaborate-anyway side]**.
3. Its proof contains no local `def` or `theorem` (decision B; the pilot's cause 2).
4. Its source component holds only theorems. A theorem in a group with a computing
   definition is never deferred: the definition's hash covers the theorem's proof (10.2 of
   the parent, "A theorem in a group").
5. *Until SW-4752 says otherwise:* it is alone in its component, not recursive in the
   source, and has no `decreasing` clause.

Every other declaration, and every theorem that fails a rule, is elaborated in full in the
interface pass, as the pilot did.

**Recursive, mutual and `decreasing` theorems.** Their statements don't depend on their
proofs any more than a lone theorem's does; what the proof adds is the termination check,
which belongs to the proof job. So the end state is to defer them too (drop rule 5), and
that is what this design assumes **if SW-4752's run shows the digests still match**. If it
shows a difference (the digest reading a group's shape or a `recursive` flag for a sealed
theorem), there are two ways on: fix the digest so it doesn't read those for a sealed
theorem (they are facts about the proof), or keep rule 5. Keeping rule 5 is safe and is the
pilot's measured behaviour; it leaves about a fifth of the theorems' proofs on the chain
(section 8 gives both figures). A theorem whose *elaborated* proof turns out to call itself
though the source shows no recursion (`byWalking`) is already deferred by the pilot and
matches once SW-4751 is in.

**What the kernel gains: `leave_stated(id)`.** It takes a *pending* theorem, the one
`declare_def` has just made, and makes it final and stated, keeping its name, path and
type. It refuses anything that isn't pending, isn't a theorem, or whose type isn't a
proposition by the kernel's own mark, as `admit_trusted_stated` does. For a component of
several theorems it is called on each. Nothing turns a stated theorem back; the proof job
runs in a session that doesn't hold this one. This is the only new trusted function, and
unlike `admit_trusted_stated` it is reached from ordinary elaboration, not from the cache's
trust boundary, so who may call it is the point of decision A and of the review (section 9).

**The interface entry.** Same format and decoder as part A of a whole entry, under its own
unit kind, with these differences, each of which the review must check:

- A deferred theorem's record has no body, no group and **no full hash** (the proof isn't
  known). Stage 2's `admit_stated` refuses a record without a recorded hash; the interface
  entry needs its own admission that records "no full hash", and asking for the full hash
  of such a theorem is an internal error, never "no hash" (SW-4744 was a failed hash written
  as none). References to a theorem hash by its statement (`hash::interface_hash`), so a
  check should never ask **[not verified: a reader of a dependency's full hash during a
  check would be found by the byte-compare tests or by this error]**.
- Proof-private helpers (a `match` in a deferred proof) aren't in it: they were never made.
  A whole entry's part A still carries them (SW-4735's deviation). So a worker's session
  differs by whether it loaded `D` from `D`'s interface entry or from `D`'s whole entry.
  Nothing outside a proof can reach its helpers (the cache's stage C), so the entries
  written above must be the same bytes; the random-schedule byte-compare is the test.
- It is kept **in memory, for the run, and never written to disk** (decision C). Only fill
  workers can read it: it lives in a store wrapper that `parallel.rs` alone constructs, as
  the `--no-cache` map and the claim table do.

**When no interface pass is run.** For a namespace nothing in the target uses (most `aoc`
proof namespaces, tests), nobody needs the interface. For a namespace with no deferrable
theorem (`Syntax`: 4.2 s, no theorems **[measured]**), the interface pass would be the whole
check, so the proof job's whole entry serves as its interface, as in stage 1. Both are known
from the parse and the graph.

## 4. The scheduler

**Workers are stage 1's**: the same threads, one kept session each, the same board and claim
table. There is no thread per proof and no new pool; "side by side on threads" means proof
jobs of different namespaces on different workers. Proofs *within* one namespace stay on one
worker (option B of the parent stays out).

**Two kinds of job per namespace `N`:**

- `I(N)`, the interface pass. Ready when every namespace `N` uses directly has an interface
  available: an interface entry from this run, or a whole entry (found before the fill or
  written in it).
- `P(N)`, the proof job: stage 1's job unchanged, today's whole check of `N`, writing `N`'s
  whole entry through the code that writes it today. Ready on the same condition. It does
  not use `I(N)`'s result: it elaborates `N` again from the top, so each proof sees exactly
  the declarations before it, which is what keeps `auto` and the instance scans from
  finding a later theorem (8.2 of the parent, last paragraphs).

So definitions and statements of a namespace that has both jobs are elaborated twice, as
Rocq's are. For `tools/fmt` that is 13 to 22 s of extra CPU spread over the workers
**[estimated, section 8]**.

**What a worker loads.** For a dependency `D`: `D`'s whole entry's part A if it exists, else
`D`'s interface entry. The key of `N` needs each dependency's digest, which is in the header
of either. A session keeps what it loads, as now.

**Which job a free worker takes.**

1. An interface job before any proof job (interfaces unlock work; proofs unlock nothing),
   by stage 1's rule: longest chain above, then most of the closure held, then canonical
   order.
2. Otherwise a proof job for a namespace its session does not hold, lowest in canonical
   order first. A session that holds `N` as a dependency can't check `N`; lowest-first means
   workers that only run proof jobs never meet that (a worker holds only what is below what
   it has checked, and anything below was ready earlier and so taken earlier).
3. Otherwise (a worker that has climbed the chain doing interface passes holds most of the
   project) the proof job whose namespace is nearest the top of its session: it rewinds to
   before that namespace, which is stage 1's rewind, and checks it. Going top-down, what a
   rewind drops is mostly what is already done.

Rule 3's rewinds and the loads after them are the main unknown cost. `Fill` gets counters
for them, and `--timings` shows loading per worker already. A whole `tools/fmt` load
without proofs is 2.1 s and 0.94 GB **[measured, `stage2-step2.txt`]**; that is the most
one rewind can cost.

**Memory.** As stage 2: each worker holds at most the project without proofs plus its
working peak. Stage 2 measured 3.1 to 4.1 GB at 4 jobs on `tools/fmt` **[measured]**; 8
jobs were 5.1 to 6.9 GB before stage 2 **[measured]**. The interface entries add one
project's part A in memory, perhaps 50 to 100 MB **[estimated]**.

**Library files** are unchanged: loaded on demand inside a check, claimed, whole. A cold
library (about 16 s on one thread, 8 s more than a warm one at 4 jobs **[measured]**) is
then the largest single piece of a cold run. Statements-first for library files is the same
idea one level down and is not in this design.

## 5. Trust: what a dependant loads, and what "checked" means

**The change.** In stages 1 and 2 every stated theorem in every session has had its proof
checked by this build's kernel before the entry that carries it was written. In stage 3 a
worker's session can hold a stated theorem whose proof is still running on another worker,
has not started, or will fail. Two things make one: `leave_stated` in an interface pass (the
namespace's own theorems), and the admission of an interface entry (a dependency's).

**What keeps that from reaching a report.**

1. *Workers report nothing.* As in stage 1, a worker's only output is entries. Messages, the
   summary line `checked N namespaces of P` and the exit code come from the last pass, a
   separate session on the main thread made with the defaults.
2. *The last pass can't see an interface.* Interface entries are not in the store it reads.
   It loads whole entries only, and has a digest for a namespace only from that namespace's
   whole entry or from checking it itself.
3. *The join is the key chain* (10.5 of the parent). A proof job of `M` that ran against
   `iface(N)` writes `M`'s entry under a key made from the digest `iface(N)` claimed. The
   last pass computes `M`'s key from the digest in `N`'s *whole* entry. So it finds `M`'s
   entry exactly when `N`'s proof job passed with no error and no goal **and** produced the
   interface the interface pass claimed. Otherwise `M`'s entry is simply not found and the
   last pass checks `M` itself. Nothing has to remember to join.
4. *Sessions that use what they load hold no stated theorem*: the existing assertion
   (`assert_holds_no_stated_theorem`), unchanged.

**So "checked" means, at the end of a run with `--jobs N`:** every namespace the summary
counts has a whole entry reached through whole entries all the way down, each written only
after this build's kernel accepted every declaration and every proof in it, against
statements whose proofs were accepted the same way; or was checked by the last pass itself.
That is stage 1's sentence. What is new is only the order in time: `M`'s proofs may have
been accepted before the proofs of a theorem they use. It is reported once, by the last
pass, after every proof job has ended. Nothing before that says "checked"; the only earlier
output is the "still checking" notes. A run stopped with Ctrl-C reports nothing, as now.

**Invariant W, restated.** W today: an entry is written only by a session with no error, no
goal and nothing relying on one. In stage 3 a worker's session treats a not-yet-proved
theorem as a leaf that relies on nothing, so `M`'s entry can be written while `N` below
has a `?`. W becomes **W′: an entry says "this namespace is finished, given whole entries
for everything in its key"**, and every reader reaches an entry only through its key. That
is in fact what an entry already means on disk today: break a proof in `N` after a clean
check, and `M`'s entry is still there, keyed on `N`'s unchanged interface digest, while `N`
has no entry; the last pass doesn't find it, because it has no digest for `N`. Stage 3
makes such entries in a new way (before `N` was ever clean) but not a new kind of entry.
The readers that find entries by something other than the exact key are carried-over
entries (same key, another build: `cache/mod.rs:48-54` **[verified in the doc comment
only]**) and `--recheck`; both go through the key too. The review re-reads each.

**When a deferred proof fails** (an error, a goal, `E-RESOURCE`, in `P(N)`):

- `N` gets no whole entry. Jobs above `N` already running finish and write their entries
  (harmless by the key chain, and reusable once `N` is fixed with the same statements). No
  *new* job above `N` is started: the last pass has to check those itself anyway, and a
  failing run should get to its messages. The rest of the graph is still filled.
- The last pass checks `N` and everything above it on one thread, in order, and prints what
  a one-job check prints, byte for byte, because it *is* the one-job check: `N`'s error,
  and "relies on `t`, which has an error" above it. This is stage 1's fallback and today's
  cost for a failing run; stage 3 doesn't make it worse or better.
- An interface pass that fails (an error in a definition or a statement) leaves `N` and
  what is above it to the last pass, as stage 1 does, and `P(N)` isn't started.

**When the two digests differ** (`P(N)` passes but its interface digest isn't the interface
pass's): that is a bug in the deferral rule or the digest, never expected. The entries
above `N` written against the claimed interface are not found; the fill stops handing out
work above `N` and the last pass checks it. It costs time, not correctness. It must not be
silent: the fill counts it, `STITCHWORT_CACHE_DEBUG` names the namespace and the tests and
the whole-project compare require zero.

**`--no-cache --jobs N`** (D3731): the same, with whole entries in the run's memory map as
now. The byte-for-byte test and the ground-truth check stay on one job.

**Step counts** (D3733): a proof checked against stated theorems forces kept types at other
moments than a sequential check, so the `E-RESOURCE` statement of 9.4 item 4 stands
unchanged: a declaration within a kept type's forcing cost of its limit could pass on one
schedule and stop on another. Nothing false is accepted.

## 6. The cache: what is written, and when

- **Interface entries: never written to disk.** They exist in memory for one run. A later
  run that needs `N`'s interface gets it from `N`'s whole entry if `N` was clean, and runs
  the interface pass again if it wasn't. This is what keeps Rocq's `.vos` problem out: no
  file on disk ever stands for "statements whose proofs nobody checked".
- **Whole entries: written when the namespace's own check passes**, as now, even if proofs
  below are still running (decision C). They are not marked: the key is the mark (W′).
  After a kill, the cache holds some entries above a namespace with none; the next run's
  workers find them once that namespace's interface pass has produced the same digest, and
  the last pass finds them once its proofs have passed.
- No format change beyond what the interface entry needs in memory (a record flag for "no
  full hash"); the disk format is stage 2's.

## 7. Other commands and the editor

- `check --jobs N` with N > 1 uses stage 3 whenever stage 1's fill would run; there is no
  new flag. A debugging switch (`STITCHWORT_STATEMENTS_FIRST=0`) turns the interface jobs
  off for comparison. `--jobs 1`, `--recheck`, `--carry-over` and the other one-job rules
  of 9.2 never run an interface pass. The default job count stays the orchestrator's call.
- `--timings` gets a row per interface pass (`N (interface)`), so a namespace with both
  jobs has two rows. "Still checking" notes can come twice for one slow definition, once
  from each job; the sink should print a declaration once **[small, the orchestrator's]**.
- **The editor does not use it.** `LiveProject` checks one namespace per step, starts no
  threads (`crates/driver/src/live.rs:17-18` **[verified]**), and loads with proofs because
  it answers questions about them. If the follow-up "fill a cold cache at server start-up"
  (9.2 of the parent) is built, it gets stage 3 for free, since it is the same fill. What
  the editor wants is narrower: re-check only the proof being edited, which is option B
  (proofs within a namespace) and a separate design.
- `test`, `run`, `build`, `axioms`, `audit`, `doc`: unchanged; they load whole entries.
- **The proving loop is unchanged.** A warm check after editing one proof re-checks one
  namespace, and a run with a goal or an error still ends in the one-thread last pass over
  that namespace and what is above it. Stage 3 produces clean entries above a broken proof,
  which a later design could let the last pass reuse (the digest cache's stage D; SW-4736's
  note points the same way). Not in this design.

## 8. Predicted gain

All from the 24 Nov measurements; one-job times are with the library cached.

**`tools/fmt`.** Measured: 97 to 102 s on one job, 40 to 43 s on four, 46 s on eight; the
one-thread work in the project is 93.9 s, of which the chain is 37.1 s; theorems are 84.7 s
of 109.1 s; the project's work that isn't theorems is 8.6 s; the largest namespace is 8.7 s
and the largest theorem 3.8 s.

| Piece | Figure | Basis |
|---|---|---|
| Definitions and other non-theorem work in the project | 8.6 s | measured |
| Theorem statements | 4 to 13 s | **not measured**: 5% to 15% of theorem time, a guess |
| Proofs the interface pass must still elaborate, if rule 5 stays | 8 to 25 s | **not measured**: 19% of theorems by count; their share of time is unknown |
| Interface work in all | 13 to 22 s (rule 5 dropped), 21 to 47 s (kept) | sum |
| Interface chain, wall time | 6 to 15 s (dropped), 10 to 30 s (kept) | estimated: between the chain's 40% share of all work and most of it, since the base namespaces are on the chain |
| All work, with statements done twice | 107 to 116 s (dropped) | 93.9 s plus the interface work |
| That work over 8 workers | 13 to 20 s | divided by 8, times 1.0 to 1.35 for workers slowing each other (the process run's own time rose 35% at 6 processes, measured) |
| Last pass, loading, rewinds | 3 to 8 s | stage 1's measured run is about 3 s over its bound at 4 jobs; rewinds are new |

Wall time is roughly the larger of "the interface chain, then the proofs that could only
start late" and "all work over the workers", plus the last line:

| `tools/fmt`, library cached | Stage 1 and 2 (measured) | Stage 3, rule 5 dropped (SW-4752 succeeds) | Stage 3, rule 5 kept |
|---|---|---|---|
| 4 jobs | 40 to 43 s (2.4x) | 30 to 35 s (2.8x to 3.2x) | 32 to 40 s |
| 8 jobs | 46 s (2.1x) | **20 to 33 s (2.9x to 4.8x)** | 22 to 40 s (2.4x to 4.4x) |

With the library cold add 8 to 16 s to each (it is 111 s on one job and 49 s on four today
**[measured]**), so about 2.3x to 4x on 8 jobs. All **[estimated]**. The wide range is the
two unmeasured rows; step 0 measures both directly, and earlier predictions of this kind
have run high (stage 2's loading gain came in at 19% of a load's time against a guessed half
or more).

**What SW-4752 changes:** only the middle rows. If recursive and `decreasing` theorems can
be deferred, the interface chain loses 8 to 25 s of proof work **[estimated]** and the top
of the range comes down from 40 s to 33 s. If they can't, stage 3 is still ahead of stage 1
at 8 jobs unless those theorems turn out to hold most of the proof time, which step 0 shows.

**`aoc`.** 38 s on one job, 12 s on four, 8.3 to 9.2 s on eight **[measured]**; its graph
is 5 deep and its limit is the one largest proof namespace (5.4 s) and the worker count.
Stage 3 adds nothing: proof namespaces have no dependants, so no interface pass is run for
them. Expect the same times within half a second **[estimated]**. With a cold library `aoc`
is bound by the library block (51 s to 19 s on eight **[measured]**), which stage 3 doesn't
touch.

**Who sees it.** Cold whole-project checks of `tools/fmt` and projects shaped like it: the
orchestrator's check after a push, Matt's own, and any future project with long chains of
proof files. Lanes don't pass `--jobs`.

## 9. Build plan

Estimates are agent time, set from SW-4719 (Opus, 61 min against 75), SW-4734 and SW-4735
(about 40 and 50); past actuals run about a third of estimates, so the 4 hours below are
probably under 2.

| Step | What | Who, estimate |
|---|---|---|
| 0 | **Measure before building.** On the pilot branch (`lane/SW-4730`, or SW-4752's if it lands): print each namespace's interface-pass time and the time of the theorems it elaborated anyway; `ns_graph.py` computes the interface chain. Count theorems that fail rule 2. The orchestrator runs it on `tools/fmt` (about 4 minutes of machine time, twice a cold check). **Gate:** if the interface chain for `tools/fmt` is over about 25 s, stage 3 buys little over stage 1's 37 s; stop and bring the figures to Matt. Record the prediction of section 8 beside the outcome | Sonnet, 20 min |
| 1 | The kernel: `check::leave_stated`, its refusals and tests; `docs/core.md` ("Stated theorems": the second maker, and that a session holding one from an unchecked proof reports nothing). No caller outside tests. All of `examples::soundness` | Opus, 30 min; Fable review, 20 min |
| 2 | The interface pass in the elaborator: the deferral rule from the source, `leave_stated` in place of the proof, the encoder writing a part A for a namespace with stated theorems of its own, the interface entry and its admission ("no full hash" as an error to ask for). Tests: for each fixture the interface pass's digest equals the full check's; a proof-local `def`, an instance theorem, a theorem grouped with a definition are elaborated, not deferred | Opus, 60 min |
| 3 | The driver: two job kinds on the board, the in-memory interface store, the pick rules, the failure and mismatch rules, counters, `--timings` rows. Tests (each named, seconds): the byte-compare of `parallel.rs` under 20 random schedules with interface jobs on (every entry and message equal to one job's; mismatches 0); a proof error and a goal in a low namespace with dependants (output and exit as one job; no entry for it; the last pass checks what is above); a statement error; a forced digest mismatch (a test hook) costs a re-check and is counted; a worker panic | Opus, 60 min |
| 4 | Fable review of 2 and 3: who can read an interface entry; every way an entry is found (exact key, carried over, `--recheck`) against W′; the reliance walk in a worker; that the last pass's session cannot hold an unproved theorem | Fable, 30 min |
| 5 | The measure: `measure_jobs.sh` on `tools/fmt` and `aoc`, 4 and 8 jobs, with the switch on and off, output and cache compared with one job; a performance-log entry (D3444); `docs/proposals/check-cache-trust.md` and the guide's performance notes | orchestrator's run; Sonnet, 20 min |

Needs first: SW-4751 merged; SW-4752's answer (it decides rule 5, not whether to build).
Steps 1 to 3 touch `crates/core/src/check.rs`, `crates/elab/src/lib.rs` and
`cache/mod.rs`, and `crates/driver/src/parallel.rs`, so they run one after another.

**Risks, in order.** (1) The gain is under the prediction because statements and kept
proofs are a bigger share than guessed, or rewinds and loading eat it: step 0 and the
counters. (2) The interface pass and the full check disagree for some shape of declaration
the pilot's two projects don't contain: caught as a mismatch, loudly in tests, at the cost
of a slower run. (3) A reader that finds an entry without its key, or a session other than
a worker that can reach an interface entry: this is the one that could give a wrong
"checked", and is what step 4 is for.

**The orchestrator's calls, with my recommendations:** no new flag, on with `--jobs` above
1 once step 5's compare is clean; no new work above a failed proof; a digest mismatch ends
on the last pass and is counted, not warned about; library files stay as they are; the
editor's start-up fill and `test` remain follow-ups.

## 10. Decisions for Matt

The orchestrator numbers these.

**A. Using a theorem before its own proof has been checked, within one run.** **Decided: D3735 yes (Matt, 24 Nov 2026: "Yes, that sounds perfectly reasonable.")**
*The problem:* to check every file's proofs side by side, a file has to be checked against
theorems from the files below while their proofs are still running. Until now, a theorem
without its proof in memory was always one whose proof had already been checked and saved
(D3732). *The change:* during a `--jobs` run, a worker may hold a theorem that has only its
statement, with the proof still to be checked elsewhere in the same run. That includes
recursive theorems, whose "does it terminate?" check is part of the proof. Workers never
report anything. The answer still comes from the ordinary one-at-a-time check at the end,
which reads only saved results for files whose every proof passed, and can only find a
file's result if the files below it passed with exactly the statements that were promised.
"Checked" is printed once, there, after every proof job has ended. *What it should do:*
make stage 3 possible. If a proof fails or never runs, the files above it are checked
again on one thread and the messages are the same as today's, byte for byte; the cost is
time. The way it could go wrong is a mistake that lets a session other than a worker pick
up an unproved theorem; a Fable review of exactly that comes before it is switched on, and
the one-job check stays the reference it is compared against.
**[rec: yes]**

**B. A `def` or `theorem` written inside a proof.**
*The problem:* a definition written inside a theorem's proof can be named from other files
(`t.go`), so it is part of the file's public face, and the only way to know it is there is
to work through the proof. Neither the formatter nor AoC has one **[measured: the pilot
would have flagged it]**. *The options:* (a) keep the language as it is; a theorem whose
proof contains a local `def` or `theorem` has its proof checked in the first pass instead
of being put off. It costs only those proofs, which today is none, and is a few lines.
(b) Change the language so that what is defined inside a theorem's proof can't be named
from outside it. That is tidier (a proof's insides would be fully private, and editing a
proof could never disturb the files above), but it is a language change with its own
design, docs and error message, and nothing measured needs it. *What it should do:* either
keeps stage 3 correct; (a) does it now at no cost.
**[rec: (a); raise (b) as its own proposal only if such proofs become common]**

**C. Saving a file's result while proofs below it are still unchecked.**
*The problem:* a worker finishes file `M` while a proof in file `N` below is still running.
Should `M`'s result go into the cache now, or wait? *The options:* (a) save it at once, as
today's code does. It is filed under a label made from `N`'s statements, and a later check
can only look it up after `N`'s own proofs have passed with those same statements, so it
can't be believed early. The cache already holds results in this state whenever someone
breaks a proof in a file that was clean. If `N`'s proof fails and is then fixed, the work
done above it is reused. (b) Hold results in memory until everything below has passed,
and throw them away if something fails or the run is stopped. The cache on disk then never
holds anything whose foundations weren't fully checked at the time, at the price of
re-doing that work. Either way, the statements-only results that workers pass between
themselves are never written to disk. *What it should do:* (a) reuses the most work, which
is what you asked for in D3733; (b) is the more cautious reading of "checked".
**[rec: (a)]**

## 11. What I could not verify

- Any gain: nothing was run. The two unmeasured rows of section 8 (statement time, and the
  time of recursive and `decreasing` theorems), the interface chain's length and the cost
  of rewinds are step 0's and step 5's.
- SW-4752's result (whether recursive, mutual and `decreasing` theorems can be deferred
  with the digest unchanged). The design is written for either answer.
- That every mark in rule 2 is known before a proof is elaborated, and how many theorems
  fail it.
- That no check asks for the *full* hash of a dependency's theorem (the interface entry has
  none for a deferred proof).
- That a session which loaded a dependency from its interface entry writes the same bytes
  as one that loaded the whole entry's part A (helpers present or absent). Argued from
  stage C's privacy rule; the byte-compare tests it.
- The carried-over and `--recheck` paths against W′: read in the doc comment and the stage 2
  review, not traced.
- The pick rule's claim that proof-only workers never need a rewind: argued, not simulated.
- Whether the standard library has proofs with local definitions (it is not a project
  namespace, so stage 3 doesn't apply to it, but option (b) of decision B would).
- The pilot's whole-project figures are the orchestrator's runs, read from the committed
  files; I summed the deferred and kept counts from them.
