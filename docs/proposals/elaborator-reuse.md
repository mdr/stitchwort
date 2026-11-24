# Could the elaborator reuse work instead of starting fresh? (SW-4745)

Design note only, 24 Nov 2026, Opus paper lane. Nothing here is built. It
follows D3733 (Matt, 24 Nov 2026: "I care more about making best use of
cached work and reusing where possible ... I'd be more interested in seeing
if the elaborator might change to reuse cached results"), so step counts
that depend on what ran before are accepted. Background:
[step-counts-history-free.md](step-counts-history-free.md) (SW-4721), whose
table S1-S9 lists what is remembered and for how long.

Marks: **[measured]** run today with `target/release/stitchwort` (built
17:05, 24 Nov) on copies of `tools/fmt` and `aoc` in the lane's scratch
folder, load about 4; **[estimated]** my reckoning; **[read]** from the code.

## 1. In short

**The problem.** Matt asked whether the elaborator throws away work that a
later declaration, or a later run, then does again, and whether keeping it
would make checks faster.

**What I found.** Very little of the time goes on work done twice.

- **Across declarations and namespaces, the redone work is about 0.05% of
  the steps** [measured]. I checked two proof namespaces twice: once in a
  session that had just checked their dependencies, so everything those
  left in memory was there to reuse, and once with the dependencies loaded
  from the cache, so nothing was. `Fmt.HangProofs` took 7,763,567 steps the
  first way and 7,767,644 the second (+0.05%). `Aoc.Year2024.Day12.Proofs`
  took 14,919,607 and 14,925,817 (+0.04%). Elaboration and kernel times
  were within noise (HangProofs 646/99 ms and 643/105 ms). That difference
  is everything the session-long memos (S1-S3) save across namespaces,
  and so also everything that saving them in the check cache could save
  (§3).
- **Within one declaration, one memo is thrown away more often than it
  needs to be:** the elaborator's kept unfoldings (S5). They are dropped
  before every declaration, and also every time an attempt is undone
  (§2). That is the one place where the elaborator could reuse more. I
  couldn't measure it without a build; §5 says what a lane would count.
- **On a check after an edit, more than half the time is outside the
  edited namespace** [measured]: loading what the cache already holds,
  and parsing. A warm check of `Fmt.HangProofs` after a one-line edit
  takes 2.2 s. The namespace's own declarations take 0.65 s of that.
  Replaying its cached dependencies (14,142 declarations) takes about
  0.45 s, and parsing the project's files 0.25 s. The core and the
  library index take 0.14 s (§4).
- **The repo's release binary overstates that replay by about 2×**
  [measured]. `task build` turns on the `dev` features, which include
  the kernel's `reference` checks, so `reference::validate_marks` runs
  on every group replayed from the cache. It was 244 of the 1,797 ms
  sampled (14%). The shipped binary (the flake's `stitchwort-bin`) doesn't
  run it. So timings agents take with `target/release/stitchwort` make
  warm checks look slower than users see.

**Recommendation.** First, two cheap measurements: a counter for S5 and a
timing of warm checks without the dev features (§5). Make S5 outlive the
epoch (option A) only if the counter shows it is worth it. Put the main
reuse effort into loading less on a warm check (options D and E): that is
where a warm check's time goes, and about half of it is reusable.

## 2. What is remembered today, and why some of it is thrown away

| What | Lives | Why not longer |
|---|---|---|
| The kernel's kept unfoldings of calls in a definition's type (S1, `Kept` at epoch 0, `value.rs:268-361`) | the session | Nothing drops them. They aren't saved in the check cache, so a replayed definition starts with none |
| Per-definition answers: erasure, proof positions, hashes, reliance (S2, `EvalCaches`, `core/src/caches.rs`); result heads, `performs`, congruence lemmas, decision order (S3, `Caches`, `elab/src/state/caches.rs`) | the session (cut on rewind) | Nothing drops them. They aren't saved in the check cache |
| Dot-call tables (`dot_heads`, `dot_failed`) | one declaration | Keyed by syntax nodes, which a later declaration never shares, so keeping them longer would only take memory |
| The elaborator's kept unfoldings (S5) | one *epoch*: until the next undo or the next declaration | See below |
| Memos inside one comparison or read-back (S6) | one comparison | Keyed by what that comparison is doing |

**Why S5 is thrown away** [read]. A call's unfolding is computed once and
kept in a cell on the call (`Unfolding`, `value.rs`). When the elaborator
computes one, it stamps it with the metavariable *epoch*
(`MetaStore::meta_epoch`, `state/metas.rs:96-103`), and a reader may use it
only in the same epoch (`Kept::fits`). The epoch moves forward:

- whenever an attempt is undone and some metavariable solution is taken
  back (`MetaStore::restore`, `metas.rs:262`); every failed try in a
  search, `cases`, a decision procedure or an instance search can do this;
- before every declaration (`clear_metas`, `metas.rs:296`), which forgets
  every metavariable, so the same numbers are used again for new ones.

The reason is correctness. An unfolding may have read a metavariable's
solution. If that solution is undone, or the number later means a
different metavariable, the kept value would be wrong. The epoch rule
can't tell such an unfolding from one that read no metavariable at all, so
it drops every unfolding. Most unfoldings are of the latter kind.
Everything in a definition's type is closed, for example, so forcing a
call there can never read one. Dropping them is safe, just wasteful.

The elaborator also never uses an unfolding the kernel made, nor the
kernel one the elaborator made (the `kernel` mode in `Kept::fits`). That
is not about metavariables: `eta_fields` builds a stuck field of a folded
call differently for the two, and a goal's text would otherwise depend on
whether a dependency was checked or replayed (`value.rs:290-298`). Sharing
across that line would change what goals show, so it is not an option
here.

**What would make keeping S5 unsafe.** Reuse is safe when the unfolding read
no metavariable solution, met no unsolved metavariable it later depends
on, and met no definition that was still pending or opaque in a way that
has since changed (`transparent` is already among the modes; *pending* is
not). The first two can be tracked by noting, while the unfolding is
computed, whether the evaluator asked the store for any solution
(`Metas::solution`). The third by noting whether it met a pending
definition's head. Either flag set: stamp the current epoch, as today.
Neither: stamp 0, valid in every epoch, as the kernel's are.

## 3. Across runs: saving forced work in the check cache

A check cache entry holds a namespace's checked terms and the elaborator's
side tables (`cache/mod.rs`, header comment). It doesn't hold forced
unfoldings or per-definition answers. A replayed definition starts with
none, and the first declaration of the session that needs one pays for it.

**What saving them would save: about 0.05% of the edited namespace's steps**
[measured, §1]. That is exactly the cold-versus-replayed difference above.
HangProofs saw 4,077 extra steps across 58 of its 183 declaration rows;
Day 12 saw 6,210.

**What it would cost** [estimated]. The per-definition answers are small: a
few bits per parameter, and one data type id per definition. That is a few
bytes per definition, under 1% of an entry. Kept unfoldings are values.
They would have to be read back into terms to be written, and read in
again on load. An unfolding can be very large: a `fib 22` call kept
unfolded, or a list built by a computation. So entries could grow without
a bound unless a size cap were added. Both need a format bump and a
decoder, and the encoder would have to agree with the kernel's modes.

**Verdict.** Not worth it. Even the cheap half saves a twentieth of a
percent.

## 4. Where a warm check's time goes

**`Fmt.HangProofs`** (335 declarations, 2,310 lines), with
`STITCHWORT_STD_DIR` set to the repo's std:

| Run | Wall | Own namespace (elab / kernel) |
|---|---|---|
| Cold: std, `Syntax`, `Fmt` and the target, cache written | 13.45 s | 646 / 99 ms |
| After a one-line edit to the target (all else replayed) | 2.21 s | 643 / 105 ms |
| Nothing changed | 0.70 s | (not checked) |

The same edit run under `sample` (1 ms, 1,797 samples on the checking
thread) [measured]:

| Part | Samples | Share | Without the dev-only check |
|---|---|---|---|
| The target's own declarations | ~640 | 36% | 41% |
| Replaying cached project namespaces and library files | ~640 | 36% | 26% |
| … of which `reference::validate_marks` (dev builds only) | 230 | 13% | - |
| Parsing and analysing the project's files | 250 | 14% | 16% |
| Core (elaborated every run) and the library index | 135 | 8% | 9% |
| The binder-sweep warnings (parse the target again) | 56 | 3% | 4% |
| Writing the target's entry | 46 | 3% | 3% |

**`Aoc.Year2024.Day12.Proofs`** (219 declarations) [measured, `--timings`]:
the cold run takes 6.81 s. After a one-line edit, 1.60 s: 0.75 s the
namespace's own, about 0.30 s replay, 0.09 s core, and 0.46 s outside the
units (parsing, core load, printing). With nothing changed, 0.52 s.

Inside the edited namespace's own declarations, the work isn't repeated
in any way a memo would catch. The heaviest are `rowCorners` and
`columnCorners` (2.74 M and 2.69 M steps): mirror-image proofs about
different functions, not the same computation twice. The steps by phase
(`STITCHWORT_STEP_PHASES=1`) for Day 12 are 38% read-back, 7% applying, 4%
unification and 51% other. None of that is work an earlier declaration
already did.

## 5. Options

**A. Kept unfoldings that read no metavariable outlive the epoch**
(elaborator, S5). *Change:* as in §2. While a call is unfolded, the
evaluator notes whether it asked for a metavariable solution or met a
pending definition (a counter in the store, compared at `Frame::Unfolded`).
If neither, the unfolding is stamped epoch 0 and stays valid until the
definition goes. *Saves:* not measured. The SW-4721 probe shows the
mechanism: each declaration using `a: Box (fib 22 == 17711)` re-forces it
in the elaborator, 934,788 steps each time. In real proofs the calls in
goals mostly stop at the first match on a variable, which is cheap
[estimated]. The share is probably small, but it could be larger in
search-heavy declarations, where every undone try drops the goal's
unfoldings. *Risk:* a kept value reused where a fresh one would differ, if
a way of depending on a metavariable or a pending definition is missed.
Then a goal or an elaborated term changes, not just a step count. The
kernel checks every elaborated term, so it can't make a wrong proof pass;
it can make a correct one fail, or change a hash. *Guard:* run the rewind
test (`crates/driver/tests/projects/rewind.rs`) with A on and off, and
compare results and hashes. *How hard:* small in code (`value.rs`
`Unfolding::set`, the `Metas` trait, `MetaStore`), but it is the kernel's
reuse rule, so Opus with a Fable review. About an hour [estimated from
past kernel-memo lanes].

**B. Remember a per-definition answer that ran out** (S2, S3). Today a
`result_head` or erasure computation that runs out of steps isn't
remembered, and the next asker pays again (SW-4721 §4 B). *Saves:*
nothing measurable in these namespaces; it matters only where one does run
out. *Risk:* none to results once it is worked out with fixed limits, as
SW-4721 B describes. Low priority.

**C. Save forced unfoldings and per-definition answers in the check
cache.** Not recommended: §3, about 0.05%.

**D. Load less on a warm check.** Replay only what the target reaches,
not every declaration of every namespace and library file it imports.
Stated theorems (SW-4734) already skip proofs. The next step is to skip
whole declarations the target never names, and to evaluate a cached
type only when it is first read (SW-1200, filed in October at 47-55% of
`check --index` on aoc; `push_def` is now 2% of this sample, so
re-measure it first). *Saves:* up to the replay share, about 26% of a
warm edit check of a tools/fmt proof namespace without the dev check,
and less for an AoC day [estimated from §4]. Most of a namespace's
library files are reached through a few lemmas, so most of it is
reusable. *Risk:* instance search and decision search scan everything
loaded (`library_reach`, parallel-checking.md I1). Loading less changes
what they find. So D needs the same reach rule the cache's key already
assumes, or a namespace's results could differ by what was loaded.
*How hard:* a design note first (Opus), since it touches what a
namespace "sees".

**E. Don't parse files a check doesn't need, or cache the parse.** A
check of one namespace parses and analyses every file of the project:
250 ms of 1.8 s here (14%). On top of that, the binder-sweep warnings
parse the target again (56 ms). *Change:* parse only the files of the
target namespaces and those they import (found from `import` lines, a
cheap scan), or keep each file's syntax tree keyed by its text hash.
Reuse the main parse for the sweep. *Saves:* most of the 14% and the 3%
on tools/fmt [estimated]; the share is larger on a bigger project.
*Risk:* none to results if the namespace set comes out the same. *How
hard:* driver work (`project.rs`, `binder_sweep.rs`), Sonnet. One visible
change to decide first: `check NS` would no longer report a syntax error
in a project file NS doesn't import.

**F. Cache the core** (SW-4623, done as a design note): 0.1 s a run, 8%
here. Already recommended there.

**G. Remember tactic results across declarations.** For example: the same
`omega` goal proved twice. Not recommended. A result depends on the
local context, the instances and the definitions in scope, so a key that
is safe would almost never repeat. The two heavy Day 12 proofs are
mirror images, not repeats.

## 6. What to measure first

One Sonnet lane, about 30 minutes [estimated], with nothing user-visible:

1. **S5's counter.** In `Unfolding::get`, count the misses where a kept
   value was there and failed `fits` *only* on the epoch. Record the steps
   recomputing each one took (the budget's total work, read at the
   `Frame::Unfolded` push and again at `set`). Print both as a `--timings`
   line. Run it on `Fmt.HangProofs`, `Aoc.Year2024.Day12.Proofs` and one
   search-heavy std file (`std/Omega/Omega.sw`). Do A if the recomputed
   steps are over about 5% of a namespace's steps.
2. **Warm checks as shipped.** Time the §4 edit runs with a binary built
   without the dev features (`cargo build --release -p stitchwort-cli`).
   Then D's and E's shares are measured, not estimated. Add a line to
   `docs/testing.md` or the timing docs: `--timings` from `task build`'s
   binary includes the `reference` checks on every replayed group.

## 7. Decisions

- **For Matt: D3734, where the reuse work goes.** "Speed through reuse"
  goes mainly into warm checks loading and parsing less (D, E, with F
  already planned), not into longer-lived elaborator memos. The memos
  save about 0.05% across declarations (measured). The elaborator gets
  only option A, if §6's counter justifies it. Recommendation: yes.
- The orchestrator's: the §6 measuring lane first; A after it, if the
  number says so; B as a backlog ticket; D as an Opus design note; E's
  first step (reuse the main parse for the binder sweep) as a small lane.
