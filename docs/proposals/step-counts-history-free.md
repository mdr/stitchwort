# Proposal: step counts that don't depend on what the session did before (SW-4721)

Design note only, 24 Nov 2026. Nothing here is built. It follows up
SW-4718's finding (docs/proposals/parallel-checking.md §3, "Step counts
depend on history", and §9.4 item 4) and the statement in `docs/core.md`
("Kept types are glued"): "the steps a declaration's check takes can depend
on which earlier check already forced a call in a kept type, so on whether
those were checked or replayed from the cache. Results don't."

## 0. Summary

**The problem.** A declaration's step count is not a function of the
declaration and what it depends on: it also depends on which other
declarations the same session checked first. Measured below, one
declaration takes 934,788 steps in a cold check and 2,804,304 (3×) after
an edit to its own file, or under `check --jobs 2`. Near the limit of
10 billion steps, the same source can pass in one run and stop with
`E-RESOURCE` in another; and inside the elaborator, whose bounded attempts
(20,000 to 20 million steps) take running out as "no", a different count can
in principle change what is elaborated, so a hash or a message, not just
the verdict.

**The change (recommended).** Two rules. (1) A kernel unfolding of a call
in a kept type is reused only inside the operation that computed it, as
the elaborator's already are: the kernel's kept unfoldings get an epoch per
operation instead of the shared epoch 0. (2) The answers remembered per
definition for the whole session (erasure, proof positions, the
elaborator's result heads, abilities and congruence lemmas) are worked out
in their own operation, with fixed limits and fixed modes, so whoever asks
first pays nothing more than whoever asks later.

**What it should do.** Every declaration's step count becomes a function of
its own source and its dependencies' interfaces: the same in a cold check, a
warm check, `--jobs N` and the language server. In the probe, the user's
count would be 2 × 934,788 in every schedule (estimated: its own
elaboration plus its own kernel forcing; the first-asker charge leaves it).
The cost is time: the kernel recomputes a kept call once per declaration
that forces it, where today it may reuse an earlier declaration's. That is
what the elaborator already does today, and what a warm re-check already
pays; how much it adds to a cold check of `std/` and `aoc/` is not measured
(§5 says how).

## 1. How steps are charged today

A component (one or more declarations checked together) is one *operation*
with fresh counters (`crates/elab/src/module.rs:521`,
`Budget::start`, `crates/core/src/budget.rs:735`): its elaboration and its
kernel check share one limit, 10 billion steps
(`Limits::for_stack`, `budget.rs:375`). Inside it, the elaborator runs
*attempts* with small limits, where running out means "no" (unifier's cheap
read-backs and unfoldings, 100,000, `unify.rs:4181`, `:4391`; search,
200,000, `search.rs:42`; `omega` and `ring`, 20,000; side checks,
1,000,000, `assume.rs:73`; equations, 5,000,000; case analysis, 20,000,000,
`cases.rs:191`). A nested operation (a library file loaded on demand, an
`aside`) sets the outer count aside and restores it (`Budget::start` /
`restore`), so it charges the outer nothing.

Work done once and remembered for the rest of the session is charged to
whichever operation did it first. Later askers pay nothing. That is the
whole problem: every such memo whose lifetime is longer than one operation
is a site.

## 2. The sites

| # | What is remembered | Lives | Charged to | History-dependent? |
|---|---|---|---|---|
| S1 | A call's unfolding in a kept type (`Def::ty_value`, glued since D3680), made by the kernel (`Kept`, epoch 0, `value.rs:316-361`) | the definition | the first kernel check that forces it | **Yes, measured** (§3): a dependency checked in this session leaves it forced, one replayed from the cache doesn't |
| S2 | Per-definition erasure and proof positions (`EvalCaches::erasure_defs`, `proof_positions`; `erase.rs:231`, `:273`), both through `def_telescope`, which forces the top of the kept type | the session | the first operation that runs an erased program calling it, or hashes a term calling it (`hash.rs:228`, `:501`, `:528`) | **Yes, measured** (§3): the first user in a session pays, later ones don't |
| S3 | The elaborator's `Caches`: `result_heads` (`auto.rs:1577`, forces each candidate's type), `performs` (`effects.rs:2689`), `cong_candidates` (`congruence.rs:84`, validates each lemma) | the session (cut on rewind) | the first operation that asks, often inside a bounded attempt (decision search) | Yes, by reading; not probed |
| S4 | Content and interface hashes (`EvalCaches::hashes`, `interfaces`) | the session | nothing: hashing charges stack depth (`Budget::nesting`), not steps | No, except the proofless hash through S2 |
| S5 | The elaborator's own kept unfoldings | one declaration: `clear_metas` bumps the metavariable epoch before each (`state/metas.rs:296`, `Kept::fits`) | that declaration | No |
| S6 | Memos inside one comparison or read-back (`CallMemo`, the tree memo, rule K's `cast_answers`, the sum-reading memo) | one comparison | that comparison | No |
| S7 | `decision_order` (`auto.rs:1446`) | the session | nothing: it lists ids, evaluates nothing | No |
| S8 | Library files loaded on demand | the session | their own operation, set aside | No for counts; what they add to the environment is invariant I1's subject (parallel-checking.md §2), already guarded for decision search by `library_reach` |
| S9 | Stated theorems (SW-4734, SW-4735) | the session | n/a | No: every theorem is sealed while checking (rule F), and while running a call of any proposition-typed definition is erased at any arity, body or not (`erases_proof`, SW-4734 F1), so a stated and a proved theorem cost the same |

Not covered by this search: every `Cell`/`RefCell` in `crates/elab` (about
290). I read the elaborator's `Caches`, the kernel's `EvalCaches` and
`Kept`, the attempt sites and the per-declaration resets. §5's test is what
would find a site this table misses.

Two smaller points found on the way:

- `Kept::fits` lets an unfolding made glued serve a reader with gluing off.
  Its result is the same, but its cost isn't what the unglued reader would
  have paid, so under rule 1 that reuse stays inside the operation too.
- `in_own_view` (`erase.rs:208`) fixes the gluing, erasure and transparency
  a per-definition answer is worked out in, but not `Machine::kernel` or the
  epoch: whether a kernel or an elaborator caller asks first decides which
  cells it forces. The answer is the same; its cost isn't. Rule 2's fixed
  modes cover this.

## 3. Probes

Release binary of 24 Nov 16:33, project in the lane's scratch folder, per
declaration steps from `--timings=all`. `X` = 934,788 steps, the cost of
forcing `Box (fib 22 == 17711)` once.

```
namespace Lib                              namespace Use
def fib: Nat → Nat                         import Lib (..)
  | 0 => 0                                 def c: Type := a
  | 1 => 1                                 def c2: Type := a
  | Succ (Succ n) => fib n + fib (Succ n)
def Box: Bool → Type 1                     (and in a second probe, a sibling
  | True => Type                            namespace Other, importing Lib,
  | False => Type                           with def d: Type := a)
def a: Box (fib 22 == 17711) := Nat
```

| Run | `Lib.a` | `Use.c` (elab / kernel) | `Use.c2` |
|---|---|---|---|
| `--no-cache`, one job | 2,804,507 | 1,869,565 (2X / 0) | 934,788 |
| cold, writing the cache | 2,804,507 | 1,869,565 (2X / 0) | 934,788 |
| after an edit to `use.sw` (`Lib` replayed) | cached | **2,804,304** (2X / X) | 934,788 |

With `Lib`, `Use` (`c`) and `Other` (`d`), `--no-cache`:

| Run | `Use.c` | `Other.d` |
|---|---|---|
| `--jobs 1` | 934,788 | 934,788 |
| `--jobs 2` | **2,804,304** | 934,788 |
| `--jobs 3` | **2,804,304** | 934,788 |

(In this project `Lib.b: Type := a` came first and took the first user's
charge, so `c` and `d` were second users.)

Reading them:

- The kernel's X (S1): `c`'s kernel check pays nothing when `Lib.a` was
  checked in the same session, X when `Lib` was replayed or checked by
  another worker. Wall time follows (`c` kernel 0.0 ms against 31.6 ms).
- The elaborator's extra X (S2, probably proof positions or erasure through
  `def_telescope`; not attributed with a counter): the first user of `a` in
  a session pays 2X to elaborate, every later one X, whether `Lib` was
  checked or replayed. So which declaration pays depends on which ran
  first in that session, which differs between workers.

**Can a verdict differ today?** Yes, in principle, and the shape is easy:
add own work `Y` to the user. Its count is `Y + 2X` in a cold sequential
check and `Y + 3X` under `--jobs 2` or after an edit, while the owner `a`
costs `3X`. With `X` = 1 billion (fib 37 is about 1.27 billion) and `Y` =
7.5 billion, the user passes cold (9.5 billion) and stops with `E-RESOURCE`
warm and under `--jobs 2` (10.5 billion). I did not run it: about 30 billion
steps, 15 minutes of CPU, past the lane's two-minute probe limit. No
declaration in the repo is known to be in that band: the parallel stage 1
byte-compare (SW-4719) is what would find one. For the elaborator's bounded
attempts I have no repro: a flip there needs a first-asker charge (S2, S3)
inside a 20,000 to 200,000-step attempt that is within that charge of its
limit, which is rare but would change an elaborated term rather than a
verdict.

## 4. Options

**A. Scope reuse to the operation (recommended for S1).** A kernel
unfolding fits only the operation that made it: `Kept` records an operation
serial (the budget's, bumped by `Budget::start`) instead of epoch 0, and
`fits` compares it, as it already compares the elaborator's epoch. Inside
one declaration nothing changes: a call is still forced once and shared by
every copy. Across declarations each one forces what it uses. Exact by
construction (no reuse, so nothing to account for), small (`value.rs`
`Kept`, `Budget`), and it makes the kernel behave as the elaborator already
does (S5). Cost: kernel time where a later declaration used to reuse an
earlier one's forcing, at most what a warm re-check already pays today.

**B. Work out per-definition answers in their own operation (recommended
for S2, S3).** `of_def`, `proof_positions`, `result_head`,
`def_performs_after` and `congruence::candidates` run their work in a
nested operation with fixed limits (the default 10 billion) and in fixed
modes (the definition's own view, kernel mode on, as `Replay::of_def`'s
`KernelModes` already does), so the asker's count is unchanged whether the
answer was there or not. Remember the answer either way, running out
included (its fallback, as today), since a fixed-limit operation in fixed
modes gives the same outcome in every session; today a failure isn't
remembered and would be recomputed at full cost each time. The answers are
unchanged; only who pays moves, from the first asker to nobody. Work per
definition is bounded by one fixed limit, once a session.

**C. Charge a remembered result's recorded cost on reuse.** Each kept
unfolding and remembered answer carries the steps its computation took; a
reuse from an earlier operation charges them, once per operation. Keeps the
time savings, but to equal a fresh computation's count it must not count a
call shared by two of its parts twice, which needs each result's set of
inner calls. The cheap version (count each part's recorded cost in full)
counts shared parts once per path, exponentially in a chain of diamonds, so
a declaration that passes now could run out where nothing more is computed.
It also has to report running out at the reused call the same way in both
paths (a hit doesn't know which inner definition the fresh computation
would have been in), which changes `E-RESOURCE` messages. Not recommended:
A is exact and much smaller; C is worth reopening only if §5's measure shows
A costs real time.

**D. Scope reuse to the namespace.** A's rule with a serial per namespace
instead of per operation. Fixes cold against warm and `--jobs` (each is
namespace-granular) and keeps reuse inside a namespace. But the language
server rewinds inside a namespace, keeping unfoldings forced by
declarations it then rechecks or drops, and `check --only` skips
theorems, so both keep a history inside the namespace. A fallback if A's
measured cost is large and the language server's counts don't matter.

**E. A budget that is a function of the term alone** (by size, say).
Rejected: the budget bounds evaluation, which a term's size doesn't bound;
there would still have to be a step limit, with the same problem.

## 5. Building it, and what it costs

One Opus lane, kernel-side (`crates/core`: `value.rs` `Kept`, `budget.rs`,
`erase.rs`; `crates/elab`: `auto.rs`, `effects.rs`, `congruence.rs`), with
`docs/core.md`'s kept-types bullets rewritten ("A consequence: the steps …
can depend on …" becomes the rule) and a Fable review, since `Kept::fits` is
the kernel's reuse rule. Estimated 1 to 2 hours from past kernel-memo lanes.

1. **Measure first.** A counter of kernel hits on an unfolding made by an
   earlier operation, and the steps those unfoldings took, summed, printed
   by `--timings`. Run on `std/` and a few AoC days (the orchestrator's or
   Overmind's job: it is whole-project). That is A's added cost, measured
   before choosing A over D or C.
2. A and B as above.
3. **The test that holds it.** A CLI test on the probe project: per
   declaration step counts (`--timings=all`'s steps column) equal across a
   cold check, a check after an edit to each namespace, and `--jobs 1/2/3`.
   And extend the rewind test that already checks a sample with the
   elaborator's caches emptied before each declaration
   (`crates/driver/tests/projects/rewind.rs:200`,
   `Options::clear_caches_per_declaration`) to empty `EvalCaches` and the
   kept unfoldings too, and to compare step counts, not only results: any
   site §2 missed shows up there.
4. Afterwards, parallel-checking.md §9.4 item 4 and item 5's "step counts"
   are no longer true: `--jobs N` gives each namespace the verdict of a cold
   check, and `--timings` step totals match.

**What users see.** No new message, no new limit. `--timings` step counts
become stable between runs. A declaration's count drops where it was the
first to ask for a per-definition answer, and rises where it reused an
earlier declaration's kernel forcing: the rise is exactly what that
declaration costs after an edit today, so nothing that passes after an edit
starts failing; something that passes only in a cold check, within one
forcing of 10 billion steps, would fail in a cold check too. None is known.

## 6. Decisions

- **For Matt: D-next, the end state.** "A declaration's step count, so its
  `E-RESOURCE` verdict, depends only on its own source and its
  dependencies' interfaces; a cold check no longer gets cheaper because a
  dependency was checked earlier in the same run." Recommendation: yes. It
  is what `--jobs` (byte-identical to one job) and the cache (replay
  answers as a check would) need, and the user-visible change is limited to
  `--timings` numbers and the never-observed band within one forcing of the
  limit.
- **For Matt, only if §5's measure shows a large cost:** accept D (stable
  for the command line, not inside the language server) instead of A.
- The orchestrator's: A over C, B's fixed limit and modes, the counter and
  the test, sequencing after SW-4719 (the byte-compare) or before it.
