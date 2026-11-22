# Performance log

A paper trail of every optimisation: what was done, why, the reasoning, the
measurements, and what was rejected or dropped, so an attempt that failed
isn't tried again unknowingly (D3444, Matt, 9 Nov 2026). Speed lanes add an
entry as part of the work ("Speed work" in
[workflow.md](../workflow.md#writing-a-brief)); the orchestrator checks it in
review. Newest first. Dropped attempts and accepted regressions are entries
too.

## How things are measured

- **Instructions retired are the primary measure.** They are far more repeatable
  than time, which is noisier (about 0.5% on a quiet machine, more under load) and can move with no change in instructions (see
  SW-2523).
- `task bench:instructions` builds the `bench/compare` programs natively and
  runs each several times (default 5), checks the output, and prints
  min/max instructions and the change against a saved run (`--save`,
  `--against`). The core ten steer the work; the wide set adds Lean's own
  programs (`rbmap`, `rbmap-ck`, `const-fold`), `spectral-norm` and
  `mapops`.
- `task bench:aoc` runs every AoC day natively, checks its answer, counts
  instructions and diffs them against the previous run. Entries quote its
  **geomean** change and the number of days that moved more than 3%.
- Both build non-incrementally into `target/bench`. An incremental release
  build runs native code about 3% slower, so only like-for-like builds
  compare (SW-2474, below).
- **Overmind comparison runs** (native against CPython and Lean, instructions
  and counters) are written up in
  [../reviews/SW-2295-comparative-speed.md](../reviews/SW-2295-comparative-speed.md);
  the headline ratios per run are in
  [../../bench/compare/history.toml](../../bench/compare/history.toml).
- Each entry says whether a figure was **measured** or **estimated**.
  "Instructions" means native instructions retired. Merge-commit hashes are on
  `main`; `keep/...` branches hold work that was not merged.

Earlier work, recorded elsewhere: the first evaluator and Map fixes in
[../evaluator-speed.md](../evaluator-speed.md) and
[../proposals/interpreter-speed.md](../proposals/interpreter-speed.md); the
effect runtime's allocation counters and the plan these entries execute in
[../proposals/effect-runtime-allocation.md](../proposals/effect-runtime-allocation.md);
the 8 Nov wins listed at the end of this file. The design notes' own status is
in [../proposals/README.md](../proposals/README.md).

---

## 22 Nov 2026

### SW-4618: large read-backs kept for reuse within a declaration; `printedSplitParts` 46.6M to 23.9M steps, `printedFinish1` 120.8M to 98.1M

- **Problem.** SW-4608 found reading values back is 37% of a cold
  tools/fmt check's profile; SW-4611 saw the same large terms read back
  many times in one proof.
- **Measured first (throwaway probe, every read-back over 100K nodes:
  value identity, level, mode, metavariable epoch, and a hash of the
  result).** Exact repeats (same value, level, mode and solutions) are a
  minority: `printedSplitParts` 2 of 4 (one 1.03M-node value read back
  three times running), `printedFinish1` 2 of 11, `standsDecl` 0 of 13.
  Most of the rest are the same value read back again **at a deeper
  level** (`standsDecl`: 4 values read back 12 times at levels 10, 14,
  16, 20, 24), which an exact memo can't serve: the term differs in its
  free variables' indices. Each 1.0-1.1M-node read-back took 0.35-0.53 s,
  whether first or repeated (the calls' unfoldings are already kept; the
  cost is visiting the nodes and applying closures).
- **Change.** `value::ReadbackMemo` in `EvalCaches`: a read-back of 10K
  to 4M nodes (not for display, no depth limit) is kept, filed by the
  value's shared parts (held, so addresses aren't reused), level and mode,
  and reused only while the metavariable solutions
  (`Metas::version`: store id, epoch, trail length), the environment
  (`Env::version`, changed by every `&mut` method) and the machine's
  modes (as for a kept unfolding) are unchanged. At most 4M nodes kept,
  oldest let go first; emptied at `clear_metas`. `STITCHWORT_READBACK_MEMO=off`
  turns it off, `=check` re-reads every hit and panics if the terms
  differ. Terms and hashes unchanged.
- **Result (measured, `check NS --no-project-cache --only D --timings`,
  release, load 5-6, memo off then on).** `printedSplitParts` 2,536 →
  1,262 ms, 46,614,335 → 23,869,555 steps; `printedFinish1` 6,574 →
  5,442 ms, 120,833,027 → 98,093,991 steps; `standsDecl` 6,009 → 5,802 ms,
  92,977,622 steps both (no exact repeats). `=check` on
  `printedSplitParts`: no difference.
- **Next.** Reusing a read-back at a deeper level (shift the kept term's
  free indices) would reach `standsDecl`'s 8 repeats (about 2.9 s); not
  done, see the ticket.
- **On main after SW-4619 (measured, merged branch, cold `check
  --no-cache` of all of tools/fmt, nice 19, load 5-22 from other lanes).**
  SW-4619 reshaped the proofs above, so the large repeats are gone.
  `--timings`: off 175.6 s wall, 167.8 s user; on 270.7 s wall, 175.5 s
  user. `--timings=all` (load under 15 at start): off 182.1 s wall,
  171.2 s user, 2,092,873,378 steps over 13,114 declarations; on 195.4 s
  wall, 174.7 s user, 2,080,783,903 steps (-0.58%). 22 declarations took
  fewer steps (12.1M together; most `Fmt.ToldWordProofs.parenTell` 7.11M
  → 5.65M, `Fmt.ElementsKeys.anyCellsKeys` 3.99M → 2.91M), 8 took a few
  more (2,819 together, at most 968; not explained). The top 10 by steps
  are unchanged but for `followsExprKeyword` 28,477,575 → 28,417,277.
  User CPU did not go down (the wall times are dominated by load).
  `STITCHWORT_READBACK_MEMO=check` over the same check: exit 0, no panic.
### SW-4615: std's slow Parse lemmas: lifting their leaves into step lemmas does not pay; no code changed

- **Status:** dropped; measured, nothing merged.
- **Problem.** SW-4608 (win 7) found std's Parse lemmas dominate a cold
  check: `Reads.sw` 2.5 s elaboration (4.4 s in SW-4608's run), the slowest
  `runFromLabelWholeFromOkTree` 14.4M steps, then `runFromOptionalLabelWholeNone`
  10.0M and `runFromLabelWholeFromBack` 9.5M.
- **Profile (measured).** `STITCHWORT_BIG_READBACK=1500 STITCHWORT_STEP_PHASES=1
  check --std Parse/Reads.sw --no-cache --timings`: 10.2 of
  `runFromLabelWholeFromOkTree`'s 14.4M steps are read-back (unify 0.9M,
  apply 0.8M); 165 of the file's 194 read-backs over 1,500 nodes are in it, from
  `substitute_in` (case-branch refinement), `reread_in`, and `rewrite`'s
  `kernel_context`. Cause: after `match reify q`, `h`'s type is `labelWholeFrom`
  unfolded against the concrete step (the whole `handle` expanded, 2.7K nodes), and
  each of the 14 leaves refines it, then `rewrite Effect.translateNoOp _ at h`
  reads it back again. Unlike SW-4611 the terms are small (not 1M nodes); the
  cost is about 1M steps per leaf.
- **Tried (reverted).** Per-effect step lemmas over small values
  (`labelWholeMarkStep`, `…SpanStep`, `…NextEndStep`, `…NextHitStep`,
  `…NextMissStep`, `…LiteralHitStep`, `…LiteralMissStep`), each doing the
  `translateNoOp` rewrite (and the `match c` on `Parse.further`'s comparison,
  and the `s.at.rest` / `stripPrefixBy` equation) in its own small context, with
  the tree lemma passing `if … then … else furthest` to its recursive call.
  They check. Steps: `runFromLabelWholeFromOkTree` 14.4M → 12.8M with only the
  mark and span leaves lifted (about 1.3M saved), but each step lemma costs
  0.36M (mark) to 2.6M (next miss) itself, 10.5M together, so lifting every leaf
  would land near 13.6M, 5% below the 14.4M. The step lemma's own cost is the
  same read-back of the unfolded handler: `rewrite … at h` normalises `h` to find
  `translate`. Doing the rewrites once before the `match c` (instead of inside
  each branch) saved 6% of one lemma. `byComputing h` or plain `h` can't
  replace the rewrite: `translate` over a stuck computation doesn't reduce.
- **Not done: the real fix.** Keep `q` abstract: carry `q () = op ≫ r` as an
  equation instead of refining `q` with `match reify q`, and prove per-effect
  unfolding equations of `labelWholeFrom` once (statements over `q`, `what`,
  `start`, `furthest` only); the tree lemmas then rewrite with small equations
  and `h` never unfolds. It touches every `reify`-based lemma in
  `Reads.sw`/`Runs.sw` (about 13 families), so it wants its own design; or an
  elaborator change so `rewrite … at h` doesn't read back the whole of `h`
  per rewrite (SW-4611's memo of read-backs would reach this too).
- **Ticket:** SW-4615; follows SW-4608 and SW-4611.

### SW-4593: who pays for checking the standard library on import: measured, nothing changed in code

- **Status:** measured; a note, [std-import-cost.md](../proposals/std-import-cost.md).
  No code changed.
- **Method.** `check --no-cache --timings=all` on Parse examples and on every 100th
  example (20 files), declaration steps split into the file's own and the
  library's, and the library's into std `theorem`s and the rest; the examples
  harness run twice by `EXAMPLES=` after a build; `check --cache-dir` warm.
- **Found.** The examples sweeps and `hash_stability` already replay std from the
  test std cache in every tier but all (SW-1761, SW-1765): three Parse examples
  took 14.6 s on the first run after a build and 0.94 s on the second. SW-4587's
  3.58 G is the `examples` benchmark, which checks std per example on purpose;
  in the sample 99.6% of declaration steps were core and library, about 78% of
  the benchmark's 16.5 G (estimated). Theorem bodies are checked on import
  (the file is the unit) and are 31-90% of the library's steps in six files.
  Every session elaborates the core (956,007 steps, about 0.1 s), cache or not.
  A warm `check` of `reads-named-parser` takes 0.48 s against 6.0 s cold.
- **Proposed.** Split the benchmark (std counted once, examples replayed over
  it: about 16.5 G to 3.5 G, estimated); measure the CLI tests that pass
  `--no-cache` before changing them; the core in the cache wants its own note.
  Checking statements only on import is rejected (trust; `--no-cache` is the full
  check).
- **Ticket:** SW-4593; follows SW-4587 and SW-4608.
### SW-4619: SW-4611's reshape on the rest of the slow formatter family; five proofs from 312M steps to 1.9M, and `atomHung` and `unaryHung` 15-55% fewer

- **Problem.** After SW-4611, SW-4608's list still had `printedFinish1`
  (7.3 s), `standsDecl` (6.1 s), `standsRest` (1.8 s), `printedStart1`
  (1.5 s) and `printedSplitParts` (2.3 s), each reading back one 1.0-1.13M-node
  term over and over, and `atomHung` (4.4 s) and `unaryHung` (2.2 s) reading
  back 0.27M and 0.57M.
- **Profile (measured).** `STITCHWORT_BIG_READBACK=200000
  STITCHWORT_STEP_PHASES=1 check NS --no-project-cache --only NS.NAME
  --timings=all`, release build. The big term is always a fact about the
  declaration with its printed leaves or pieces computed (`decl.leaves`,
  `decl.pieces`, `Decl.stands`), which exists as soon as a hypothesis, a `let`
  or a rewrite rule names a concrete `Definition [] header …`. Three shapes
  of step read it back: (a) a `match` (named, or a destructuring `let (a, b)
  := …`) while such a hypothesis or `let` is in scope, which generalises over
  it; (b) a `rewrite` whose rule or goal names the declaration's leaves; (c)
  a `match` on the declaration or its leaves that refines the hypotheses
  `stood`, `starts`, ….
- **Change (proof reshapes, no statement changed).**
  - `printedFinish1` (`Fmt.FileLexProofs`): the document-level part is a
    lemma over an abstract `Doc` (`docFinishes`, with `pairsFollow` and the
    `Marked`/`Finishes` facts as hypotheses), and the facts about the
    declaration are taken by projection (`joins.right.right…`,
    `spelled.right.left`) instead of by destructuring `let`s. Destructuring
    a six-part `declJoins` in a `let` was itself 24M steps: a `let (…) := e`
    is a `match` and generalises like one; a projection doesn't.
  - `printedStart1`: `docStarts` over an abstract document plus
    `plainDefStarts` over the parts; no `match printedLeads … with` in a
    goal that unfolds the declaration's pieces.
  - `standsDecl` (`Fmt.SettleOutputProofs`): `standsDeclOver` takes the
    leaves and the words after the `def` as variables (and `standsText`
    its one text fact); `standsDecl` applies it.
  - `standsRest`: `declStandsParts` (the `def`'s word and `stood`, proved
    with only `within` in scope) and `standsLater` (one declaration), so the
    recursion matches on a variable `decl`, not `Definition [] header …`.
  - `printedSplitParts` (`Fmt.GroupSlots`): `textsOfLeaves` takes the leaves
    as a variable, so the `rewrite` chain doesn't name `decl.leaves`.
  - `atomHung`, `unaryHung`, `signArgHung`: the ∧-valued destructuring
    `let`s (`lineSplit`, `speltHung`, `leadHung`, `startNotClose`) became
    projections. The ∃-valued ones (`hungStep`, `speltStarts`) can't be.
- **Result (measured, steps; load 9-12 so times are rough).**

  | proof | before | after |
  |---|---|---|
  | `printedFinish1` | 6.7 s, 120.8M | 32 ms, 0.54M (+ `docFinishes` 0.12M) |
  | `standsDecl` | 5.8 s, 93.0M | 3 ms, 0.04M (+ `standsDeclOver` 0.19M, `standsText` 0.025M) |
  | `standsRest` | 1.7 s, 28.3M | 3 ms, 0.025M (+ `standsLater` 0.04M, `declStandsParts` 0.013M) |
  | `printedStart1` | 1.3 s, 23.2M | 1 ms, 0.011M (+ `docStarts` 0.05M, `plainDefStarts` 0.1M) |
  | `printedSplitParts` | 2.55 s, 46.6M | 62 ms, 0.75M (+ `textsOfLeaves` 8K) |
  | `atomHung` | 4.4 s, 56.0M | 2.07 s, 25.5M |
  | `unaryHung` | 2.2 s, 30.1M | 1.9 s, 25.5M |
  | `signArgHung` | 0.78 s, 10.1M | 0.68 s, 9.0M |

  The first five go from 312M steps in all to 1.9M (lemmas included). The namespace
  check of each file touched passes (`--no-project-cache`).
- **Not done.** `atomHung` still has 6 read-backs of 0.27M nodes, `unaryHung`
  5 of 0.57M: each is the elimination of an ∃ (`hungStep`'s next state, the
  items `speltStarts` returns) in a `let`, which generalises over the goal.
  No projection form exists for an ∃; a fix would be a continuation-style
  lemma or smaller goals (`AtomReads` unfolds to a large tuple per case).
  `Syntax.ReadBackHungTop.readsBackHungListExample` (10.8 s) is kernel time,
  not read-back, and was left alone.
- **Rule of thumb for the proving guide (not added).** In a proof about a
  concrete declaration, take facts out of tuples with projections, not
  `let (a, b) := …`, and put anything that rewrites about its printed
  leaves in a lemma over the leaves as a variable.

### SW-4611: `standsEachFile`'s three nested matches moved into lemmas; 35.9 s to 16 ms, 474.5M to 0.17M steps (14% of a cold tools/fmt check)

- **Problem.** SW-4608 (win 3) measured six tools/fmt proofs each reading
  back a 1.03-1.13M-node term, 54.5 s together; `standsEachFile` alone was
  32-36 s, 395M of its 475M steps read-back.
- **Profile (measured).** `STITCHWORT_BIG_READBACK=500000
  STITCHWORT_STEP_PHASES=1 check Fmt.SettleOutputProofs --no-project-cache
  --only Fmt.SettleOutputProofs.standsEachFile --timings`: 68 read-backs of
  1.08-1.13M nodes in `standsEachFile`, from five callers (case-branch
  refinement `substitute_in` 22, `matching::blocker` 18, `rewrite`'s
  `kernel_context` 16, `lifted_type` under `check_motive` 12). All came from
  the three `match above: keyword.above` (and the `byComputing` and
  `rewrite` under them) proving `aboveTop`, `blankTop` and `afterTop`
  inside the second declaration-level match: by then the file's hypotheses
  (`stood`, `within`, …) are refined to the first declaration
  `Definition [] header …`, and their types compute to about 1.1M nodes,
  which every nested match, rewrite and refinement reads back again.
- **Change (a proof reshape, option (c)).** The three facts are only about
  `header.keyword`, so they became lemmas over a `Comments`
  (`toppedAboveRead`, `toppedBlankRead`, `toppedAfter`), checked in a small
  context; `standsEachFile` applies them. Its statement is unchanged; its
  proof term (and hash) changes, as does the namespace's.
- **Result (measured, same command, release build).** `standsEachFile`
  35,921 ms, 474,548,405 steps, largest read-back 1,130,507 nodes →
  16 ms, 168,362 steps, 82 nodes; the three lemmas 20 ms and 30K steps
  together. Load 9-12 during both runs, so the times are rough; steps are
  exact. The rest of the family is untouched: `printedFinish1` 7.3 s (11
  big read-backs), `standsDecl` 6.1 s (13), `standsRest` 1.8 s (4),
  `printedStart1` 1.5 s (2); in `standsDecl` they come from the match on
  `(Definition [] header …).leaves` itself (`blocker`, `compile`,
  `generalised_now`), which the proof needs, so no like reshape applies.
- **Not done: the general fix.** Every read-back here is of the same
  hypothesis types, mostly unchanged between calls (not measured); a memo of
  read-backs (by value identity, depth and read-back mode, cleared when a
  metavariable is solved) would share them across all five callers with
  terms unchanged. Not built: it reaches every read-back path, which needs
  its own design and an Opus lane.
### SW-4609: `explain_lifted` skips diagnostics that can't name a `match` helper; about 10% less CPU on a cold tools/fmt check

- **Problem.** SW-4608's profile (docs/reviews/SW-4608-proof-checking-speed.md,
  win 1) put `explain_lifted` at 14% of a cold tools/fmt check: for every
  diagnostic, shown or not, it built and sorted the list of every `match`
  helper lifted so far in the run (`tables.lifted`, which only grows) and
  substring-searched the message, labels and notes for each name.
- **Change.** Every name in `tables.lifted` is `owner.%matchN`, so a
  diagnostic whose text has no `%match` and for which the printer showed no
  helper's call (`printed_matches` empty) is returned straight away, before
  the list is built. Other diagnostics take the old path, so messages are
  unchanged.
- **Result (measured, Speedwell under load 9-11, `check --no-cache`, user CPU
  seconds, one run each).** `Fmt.ElementsProofs` (102 namespaces with its
  dependencies): 158.7 s before, 141.1 s after (-11%); `Fmt.DeclHangProofs`:
  30.2 s before, 27.6 s after (-9%). Wall times were 162 s and 168 s, and 32 s
  and 34 s: too noisy under load to read, hence the CPU figures. Not
  profiled again.
- **Not done.** Diagnostics that do name a helper still walk every helper;
  indexing by name would remove that if it shows up.

### SW-4606: `rewrite`'s completeness check skips the unfolded motive when the motive has lost a variable the left side depends on; Std.Float.Theory 410 MB to 383 MB, 90.0M to 88.5M steps

- **Problem.** SW-4600 left three things: (a) a suspected miss in SW-4469's
  shortcut (a copy of a variable hidden behind a `let`), (b) `ofNatExact`'s
  1.14M-node read-back, named the file's peak, and (c) the completeness
  check's read-back of the unfolded motive in `roundGrid` (806k nodes).
- **Profile (measured).** A backtrace at every read-back over 300k nodes
  (temporary, removed) on `check --std --no-cache Float/Theory.sw`: six,
  `ofIntMonotone` 448k and `add/mul/divRelError` 884k each (the usual
  `match` occurrence test and `blocker`, SW-4600's "left"),
  `ofNatExact` 1.14M (`rewrite_once`'s read-back of the goal), `roundGrid`
  806k (`hidden_copy` under `hypothesis_as_written`). Peak RSS of the file
  cut at a line (`--std-dir`): 258 MB before `ofNatExact`, 345 MB after
  it, 350 MB at line 4000, 405 MB at line 5500 (after `roundGrid`), 410 MB
  whole. So `ofNatExact` is the largest read-back but not the peak.
- **(a) No miss, nothing to fix.** A `let` slot computes to its value,
  never to a variable of its own (docs/proposals/let.md §6.1), a lambda
  closes over the value, and a local definition is lifted with the
  variable as an argument, so the goal read back always shows the copy and
  the search as written replaces it. `examples/accept/rewrite-variable-behind-let.sw`
  closes each case by computing, which a missed copy would fail.
- **(b) Nothing kept.** `ofNatExact`'s `rewrite Float.Theory.ofBitsBits …`
  finds nothing as written, even with calls opened on the path
  (`unfold_path`): the left side `(Float.ofBits (ofIntBits n.toInt)).bits`
  is a projection whose subject is the goal's `Float.ofNat n` opened twice,
  and the walk opens calls under the projection but never tests the
  projection again. The usual search then needs the unfolded goal (37
  occurrences), so no cheap test or reuse of the rule's elaboration can
  skip the read-back with the result unchanged. Making the walk find it
  would change `ofNatExact`'s next goal (to the folded form): a change of
  result, not tried.
- **(c) The change** (crates/elab/src/rewrite/as_written.rs,
  `hidden_copy_in`). Before reading the motive back unfolded, the check
  lists the context variables the left side (read back unfolded) mentions
  and the motive doesn't. If there are any and the motive's unfolding is
  larger than the left side, it compares the left side with itself with
  one such variable renamed to a fresh one (`conv`, at most four tries,
  skipping one the left side's type mentions); if they differ, no copy can
  be hidden and the check answers "none" without the read-back. `roundGrid`'s
  `rewrite n0` (`q * Nat.pow 2 e = 0`) leaves a motive about
  `roundRatio (Int.signed s x')`, which mentions neither `q` nor `e`.
- **Why results stay the same.** A copy is a part of the unfolded motive
  convertible with the left side; computing introduces no variable, so a
  copy can't mention one the motive doesn't. Mentioning isn't depending
  (a proof, an inert argument, a field of an eta record, an argument a stuck
  call's case tree never reads), hence the test by conversion: a copy `c`
  without `v` is unchanged by renaming `v`, so it would be equal to the left
  side and to its renaming, and conversion is an equivalence (docs/core.md,
  G6) preserved by renaming, so the two would be equal. Not tried with an
  unknown or an unlifted `match` in the left side, where the search
  compares by more than conversion. As with SW-4469, a check that would have
  run out reading the motive now answers instead; no case in std or the
  examples run. Hashes unchanged (`task test:hashes ALL=1`), kernel nodes of
  Std.Float.Theory unchanged (257,651).
- **Measured** (release, `check --std --no-cache Float/Theory.sw --std-dir
  crates/elab/src/std`; peak RSS from `/usr/bin/time -l`, two runs each,
  stable to 0.1 MB):

  | | before | after |
  |---|---|---|
  | Std.Float.Theory peak RSS | 410.4 MB | 383.1 MB |
  | the same with `--timings=all` | 408.4 MB | 373.5 MB |
  | Std.Float.Theory steps (sum of the table) | 89,974,592 | 88,489,469 |
  | instructions retired (whole run, `--timings=all`) | 81.0 G | 78.4 G |
  | `roundGrid` steps (largest read-back) | 1,915,842 (805,911) | 748,105 (30,566) |
  | `roundRatioScale` steps | 909,428 | 592,042 |

  No other declaration of the file moved.
- **Rejected (measured).** Running the renaming test whenever the motive's
  unfolding was over 1,000 nodes, without first checking that some variable
  is unmentioned: 7 declarations got slower by 79k steps in all, the capped
  read-back wasted where the motive mentions every variable.
- **Left.** The peak is now `add/mul/divRelError`'s 884k `blocker`
  read-backs and `ofNatExact`'s 1.14M, both needing a design change
  (goal-as-written.md; for `ofNatExact`, a walk that tests a projection
  again after opening its subject).
- **Ticket:** SW-4606; follows SW-4600.

### SW-4600: a generalised `match` and a `rewrite` by a hypothesis stop reading the goal back unfolded where nothing uses it; Std.Float.Theory 565 MB to 409 MB, 110.9M to 90.0M steps

- **Problem.** SW-4594 put float-playlist's 565 MB peak, and 5-9M steps in
  each of about a dozen Std.Float.Theory lemmas, on read-backs of the goal
  or a hypothesis in normal form, where `Float.Model.roundRatio` on a
  variable unfolds to 0.4-1.2M nodes.
- **Profile (measured).** Temporary step counters (`Budget::total_work`)
  between the phases of `generalised_now` and `rewrite_once`, and a
  backtrace printed at every read-back over 400k nodes (both removed), on
  `check --std --no-cache Float/Theory.sw` with the file cut after the
  lemma (`--std-dir`). Twelve such read-backs, in four places:
  - `ofIntMonotone`'s `match lt: Int.less i j`: the usual occurrence test
    reads the goal unfolded (722k steps, 448k nodes) and finds nothing, so
    the arms get the goal as written (`unrefined_goal`). Then the search as
    written unfolds the goal again, though it had no hit in it (725k), and
    `check_motive` reads the motive (the goal as written) back unfolded and
    has the kernel check that 448k-node type (7.65M of the 9.28M steps).
  - `add/mul/divRelError`'s `match Float.Theory.zeroOrPos n`: `blocker`
    reads every hypothesis's type unfolded to look for unknowns, then the
    generalisation reads each again (`sb: (x + c).bits = roundRatio num 1
    (-1074) z`, 884k nodes, twice).
  - `roundGrid`'s `rewrite n0` and `rewrite r`, `zeroMulNonneg`'s `rewrite`:
    the usual path reads the goal unfolded (1.22M nodes, 1.59M steps each)
    before the search as written, which for a rule with no unknowns never
    uses it. SW-4469's fast path skipped it, but only for a hypothesis
    whose replaced side is a variable.
  - `ofNatExact`'s `rewrite Float.Theory.ofBitsBits (…) (…)` (1.14M): the
    same, by a lemma; left (below).
- **Changes** (crates/elab only).
  - `check_motive` reads a motive that is the goal as given (the usual
    test generalised nothing, `Bound::as_given`) back folded, as the
    helper's type holds it (`lift::draft_with`), instead of unfolded.
  - The `match` search as written (`as_written::search`) unfolds the goal
    only if its generalisation had a hit, or check 2 is reached.
  - `blocker` hands what it read back unfolded (`Read`) to the
    generalisation (`generalised_now`, `refined_guard`), which uses it in
    place of reading it again.
  - `rewrite`'s fast path (`hypothesis_as_written`, was
    `variable_as_written`) takes any hypothesis that is an equation; a
    recoverable "too large" error in it (`settles: settle x k 3000 = Some
    y`) now falls back to the usual path, with the run's note of where it
    ran out kept for its message.
- **Why results stay the same.** The folded and unfolded motives are the
  same type by computation, and only the check reads them (the helper's
  type was already the folded one); a goal with no hit has no scrutinee
  variable to survive unfolding, so `found` is the same; the read-backs
  reused are the same reads of the same values with nothing changed in
  between; and a rule with no unknowns makes the search as written ignore
  the unfolded goal, so where it keeps its result the usual path gives
  that result (SW-4469's argument), and otherwise everything is undone and
  the usual path runs. Hashes unchanged (`task test:hashes ALL=1`, 12
  passed); the examples on these paths pass (below).
- **Measured** (release, `check --std --no-cache Float/Theory.sw --std-dir
  crates/elab/src/std --timings=all`, peak RSS from `/usr/bin/time -l`):

  | | before | after |
  |---|---|---|
  | Std.Float.Theory peak RSS | 565.7 MB | 409.4 MB |
  | Std.Float.Theory steps (sum of the table) | 110.9M | 90.0M |
  | Std.Float.Theory elaboration | 7.24 s | 5.65 s |
  | `ofIntMonotone` steps | 9,283,098 | 909,534 |
  | `roundGrid` steps (largest read-back) | 5,129,751 (1.22M) | 1,915,842 (0.81M) |
  | `addRelError` / `mul` / `div` steps | 5.74M / 5.76M / 5.57M | 3.17M / 3.18M / 2.99M |
  | `zeroMulNonneg` steps | 1,365,690 | 81,199 |
  | `ofNatExact` steps | 2,760,537 | 2,760,537 |
  | `examples/accept/float-playlist.sw` peak RSS (`check --no-cache`) | 565.1 MB | 409.0 MB |

  Eight declarations got slower, by 50k steps in all (the fast path's
  as-written attempt where it falls back).
- **Left.** `ofIntMonotone`'s one remaining 448k read-back, and the
  884k in `add/mul/divRelError`, are the usual occurrence test's own read
  of the goal or hypothesis, which checks 1 and 2 of the generalisation as
  written compare against; skipping it is a change to the design
  (docs/proposals/goal-as-written.md), not a cache. `ofNatExact` is now
  the peak (1.14M nodes, a `rewrite` by a lemma).
- **Rejected (measured).** The fast path for any rule with no unknowns once
  elaborated (lemmas too): `ofNatExact`'s search as written doesn't keep
  its result, so the rule was elaborated twice and the search made twice,
  2.76M to 2.85M steps there and `ofNatFinite` 1.42M to 1.49M; only
  `roundGrid` gained (1.92M to 1.79M). Not kept.
- **Ticket:** SW-4600; follows SW-4594.

### SW-4595: SW-4582's put-off redone, except inside a held argument's check after its expected type; AoC 2020 day 16's `runsNotes` 40.3M to 2.4M steps, tools/fmt checks again

- **Problem.** SW-4582 (below) cut `runsNotes` from 40.3M to 2.4M steps
  by not holding a failing nested argument inside an argument checked in
  place that is checked again if it fails (`HolesRetry::Deferred`), and
  SW-4591 exempted a walk's `E-WALK`. Both were reverted: the whole
  tools/fmt check failed at `Syntax.GoodItemProofs.readsAtFraction`
  (E-TYPE-MISMATCH, `byComputing` against `_` at GoodItemProofs.sw:787,
  50 dependents).
- **Cause (measured).** A temporary log of each put-off (removed), and
  keeping one argument's hold at a time by its source range, found the one
  that matters: the `Inr (Both byComputing ...)` given to
  `Parse.readsAtDone after2 True` in the lambda given to the inner
  `readsAtThenMoved`, put off 16 times. The outer `readsAtThenMoved`'s `j`
  can't be found by comparing its type with the theorem's
  (`j (skip 1 ())` against `fractionFrom at` is not a pattern); only the
  outer lambda's in-place trial succeeding fixes it, from the inside out
  (inferred from the error's `_j ()` and the code: the inner call's `j`
  from `readsAtDone`'s `() => True`, the outer's from the inner's
  `() => j u`). In that trial the inner lambda fails in place
  (`readsAtDone`'s spec waits for the inner call's), is held, and is checked
  again after the inner call's expected type; there, `Inr` fails in place
  (its type is `readsAtDone`'s unknown spec applied) and only holding it
  for `readsAtDone`'s expected type lets it pass. SW-4582 put that hold off
  too, since the check was still inside the outer lambda's trial, so the
  trial failed, the outer `j` stayed unknown and the theorem failed.
- **The change** (`check::explicit_arg_failed`, `Decl::holds_put_off`). The
  put-off now follows its own flag, set where an argument's in-place trial
  starts (`holes_retry_as` with `Deferred`) and cleared while a held
  argument is checked after its own application's expected type
  (`check::finish_application`), until a trial inside sets it again.
  Holding is kept in exactly the checks that see more known, which is where
  a hold can make a trial succeed; it is still put off in a first in-place
  check, where in `runsNotes` every hold failed again.
- **Exact?** No, but closer than SW-4582. A trial that succeeded only
  through a nested argument held directly in it (not inside a check after
  an expected type) now fails and is checked after its own expected type
  instead. A small example of the readsAtFraction shape built on std's
  `readsAtThen` checked with and without the change (the expected type
  fixed `j` there), so no example was added; the regression test is
  readsAtFraction in the tools/fmt check.
- **Measured after.** `runsNotes`: 2,413,503 steps (2,414,034 with
  SW-4582; 40,273,232 before); the step_counts ceiling stays 2,900,000,
  1.2x. tools/fmt `check --no-cache`: 149 namespaces, no errors. The four
  example sweeps pass with no snapshot change; `task test:hashes ALL=1`
  passes; AoC 2020 day 16 and its proofs check.
- **Not measured:** `bench:aoc` and the instruction benchmarks (elaboration
  only).
- **Ticket:** SW-4595 (redoes SW-4582 and SW-4591).
### SW-4601: the +4.05 M steps on `rewrite-solution-too-large`'s `Main.big` are SW-4469's variable-hypothesis fast path, a deliberate try that fails here: attributed, nothing changed in code

- **Status:** measured; no code changed.
- **Method.** First-parent bisect of the 155 commits between `99b5d8b6f` and
  `e87365f3f~1`, each built `--release` in a scratch worktree and run with its
  own copy of the example (`check --no-cache --timings=all`, exit 3 each
  time): `b5ffdd704`, `2c04385fc`, `9dc1e60c6`, `1595bbbdb` 12.17 M;
  `5a3c4c4f2`, `ae70f673c` 16.20 M, so the step is `ae70f673c`, the merge of
  SW-4469 (21 Nov, "two-run walks skip four unfolded read-backs"; its parent
  `1595bbbdb` is 12.17 M).
- **Which hunk.** Returning early from its `variable_as_written` (rewrite.rs,
  on `ae70f673c`) gives 12.12 M again, so it is that hunk, not the other
  three. The example's `rewrite same then h` has a variable as the rule's
  side, so the fast path runs `as_written::first` before the usual path; here
  it spends about 4.07 M steps and returns `First::Not` (a debug print showed
  it once, not `Kept`, not `RanOut`), everything is undone, and the usual path
  then fails its unfolded read-back (2 M nodes) and runs the search as
  written again in `unconfirmed`.
- **Verdict: deliberate, the price of the fast path's fall back.** SW-4469's
  message says each skip "falls back to the old path"; a failed try costs
  its steps. It is paid only by a rewrite that the as-written search can't
  keep and that then fails E-RESOURCE, as this example and
  `rewrite-value-too-large` do (message unchanged); the 10 M steps the
  fallback of SW-4237 costs on the same example dwarf it. Not fixed: handing
  the first try's result on to `unconfirmed` would mean carrying a second
  search mode's outcome out of `variable_as_written`, which is not a small
  change for a failing example, and the step count gains nothing a user sees
  (about 0.3 s).
- **Ticket:** SW-4601; closes SW-4594's "Not found".

### SW-4594: the two growths SW-4587 left unexplained (float-playlist's peak, the too-large rewrite examples): both attributed, nothing changed in code

- **Status:** measured; no code changed. Both are costs of work done on
  purpose; one has a cheap local fix, filed as a finding.
- **Method.** `stitchwort check --no-cache FILE` read through a `getrusage`
  probe (user time, peak RSS), and `--timings` for steps and read-back sizes;
  commits bisected by building each in a scratch worktree. For std,
  `check --std --no-cache Float/Theory.sw` with the file cut at declaration
  boundaries (`--std-dir`) found which declaration moves the peak.
- **float-playlist's peak (75 to 428 MB in the bench).** The file's own
  declarations are cheap; the peak is Std.Float.Theory being checked when
  the file uses a lemma from it (a cached library skips that). Bisect on
  peak RSS (`check --no-cache`): 198 MB at `55afa7996`, 438 MB at
  `7872dea99` (SW-638, 17 Nov, "Float.mul, ofInt and ofNat are definitions
  through roundScaled", float laws stage 3), 565 MB now. Cutting the std
  file there put the jump in one declaration, `Float.ofIntMonotone` (+240
  MB, 9.3 M steps, a 448,201-node read-back); the later growth is the
  same kind: `Float.Theory.roundGrid` (1.22 M nodes read back, 5.1 M steps),
  `Float.ofNatExact` (1.14 M), `addRelError`, `mulRelError`, `divRelError`
  (0.88 M each, 5.6 M steps each), `zeroMulNonneg` (0.45 M). Deliberate as
  scope (the Float laws epic puts `Float.ofInt`, `*`, `/`, `round` through
  `Float.Model.roundRatio`, whose unfolding on a variable is a large
  normal form); the size of the unfolded read-back is the cost, and the
  peak is the largest of about a dozen such lemmas, so fixing one lowers
  the steps but not the peak.
  - Measured on `ofIntMonotone` (scratch std, not kept): its
    `match lt: Int.less i j with` abstracts the goal over a scrutinee
    expression and reads the goal back unfolded. Moving the two branches to
    helper lemmas and matching on a Bool variable
    (`ofIntByLess ... (b: Bool) (lt: Int.less i j = b)`, called with
    `byComputing`) takes `ofIntMonotone` from 9.28 M steps to about 20 k in
    all, and the peak of the whole file stays 563 MB. The same lemma stated
    without the `match` (a hypothesis `lt` in the theorem) is cheap, so it
    is the expression-scrutinee guard path, not the statement.
- **rewrite-solution-too-large / rewrite-value-too-large.** `Main.big`:
  2.07 M steps at `fe48f6b51` (20 Nov), 12.15 M at `61f65796e` (SW-4237,
  20 Nov 04:08, "elaborator read-backs of a hypothesis or goal too large
  to write out fall back to the calls as written": the unifier's solution
  of an unknown as a call that steps at once, "rename, second try"), then
  16.20 M from some commit between `99b5d8b6f` (12.17 M, 20 Nov 20:36)
  and `e87365f3f~1` (16.20 M, 21 Nov 19:50), where 261 commits are left
  to bisect; `50848b226` and `e87365f3f` are not it. SW-4091 (19 Nov) is
  not the cause: 0.94 s before it, 0.91 s after. SW-4237 is deliberate:
  an unfolded read-back that overflows 2 M nodes now tries the calls as
  written before giving up, and for this example (whose point is that it
  fails) the second try also overflows, costing 10 M steps (about 0.8 s)
  for an unchanged message. Left alone: it is the price of the fallback,
  paid only by a program that fails E-RESOURCE.
- **The +4.05 M steps between `99b5d8b6f` and `e87365f3f~1`:** found in
  SW-4601 (above): SW-4469's `variable_as_written`, `ae70f673c`.
- **Ticket:** SW-4594; follows SW-4587.

### SW-4592: an indexed family's split no longer compares every variable in the context unless a message shows the arm's goal; `fin-table-deep`'s `Main.code` 55.4M to 5.6M steps

- **Problem.** SW-3325 (`6d960d350`) made `accept/fin-table-deep` go from
  23.1M to 77.8M steps (SW-4587's finding): `enter_family_split` compared
  every variable of the context before and after each split with `same`,
  which quotes both values folded, to record what the split solved.
- **Change.** The split keeps the context's values before and after (cheap
  clones) and the level; the list of solved variables is computed the first
  time `replay` or `unsplit` needs it, that is when an error or hole shows an
  arm's goal, and cached in the split.
- **Why results stay the same.** The same comparison runs on the same
  values, only later; terms and hashes were never touched. A comparison made
  later quotes at the split's own level.
- **Measured** (`check --no-cache --timings=all`, release): `Main.code`
  55,399,703 to 5,626,999 steps, 4.65 s to 0.61 s elaboration.
- **Ticket:** SW-4592; see SW-4587's entry below.

### SW-4582: inside an argument checked again if it fails, a nested argument that fails in place fails it, instead of being held for after its own expected type; AoC 2020 day 16's `runsNotes` 40.3M to 2.4M steps

- **Problem.** SW-4580 left `runsNotes` at 40,273,232 steps, with its
  innermost of nine nested `Parse.runsBind` calls elaborated about 191
  times.
- **Profile (measured).** A temporary counter in `check` and `infer`
  (removed) logged each elaboration of a `runsBind` call with its steps,
  result, error and the chain of argument checks around it (in place, after
  the expected type, recheck, retry). The nine calls of the chain were
  elaborated 1, 2, 3, 6, 12, 24, 48, 96 and 192 times from the outside in:
  each `runsNext` argument is checked in place, fails, is held and checked again after its
  application's expected type, at every level, inside every trial above
  it. Only the path "outermost in place, every other level after its
  expected type" succeeded. Every other trial failed in the same way: at the
  innermost `Parse.runsPure _ ending`, against a goal with an innermost
  `runsBind`'s `j` (its `_`) not yet worked out, which only comparing each
  level's type with its expected type, from the outside in, fixes. The
  innermost call's 192 elaborations cost 31.2M of the 40.3M steps (about
  158k each, mostly its `runsLinesOf` argument). Through the chain the
  steps grow as 2^n in the nesting.
- **Rejected first (measured).** Skipping the in-place check of a nested
  argument inside a trial (holding it at once, as SW-2638 does for lambdas
  in a retried application) broke the standard library:
  `std/Ring/Sound.sw` and `std/Fin/Fin.sw` need an argument checked in
  place inside another's trial. Not kept.
- **The change** (`check::explicit_arg_failed`). Inside an argument checked
  in place that is checked again after its expected type if it fails
  (`HolesRetry::Deferred`, SW-4580's mode for the same arguments), a nested
  argument that fails in place no longer gets held and checked again: the
  trial around it fails, and that argument is checked again with more
  known, as with a `holes_by_arguments` retry. If the argument around
  can't be held after all, it is checked once more with nothing put off
  (`HolesRetry::Always`, SW-4580's fallback), so a call that only succeeds
  through the held check still does when nothing else would check it. The
  in-place trials themselves are kept, so a nested argument that succeeds
  in place inside another's trial (the std cases above) still does.
- **Measured after.** The same calls are elaborated 2, 3, 4, 5, 6, 7, 8, 9
  and 10 times; the outermost now fails in place too and passes after its
  expected type, as every level does. The innermost's ten cost 0.63M steps.
  `runsNotes`: 2,414,034 steps (16.7x fewer); the step_counts ceiling goes
  from 48M to 2.9M. Hashes unchanged (`task
  test:hashes ALL=1`, 12 passed); the standard library, AoC 2020 day 16's
  proofs and tools/fmt's `Fmt.JoinProofs` check.
- **Not exact.** An argument that succeeded in place only because a nested
  argument passed its check after its own expected type, inside the trial,
  is now checked after its expected type instead. That is the same argument
  checked with more known, and none of the hashes or checks above changed,
  but the change is not proved to keep every result. The examples sweep (the
  verifier's) is what would show a changed message or a refusal.
- **Not measured:** `bench:aoc` and the instruction benchmarks (a lane
  doesn't run them; the change is in elaboration only, not in run code).
- **Ticket:** SW-4582. Reverted the same day with SW-4591 (it broke
  tools/fmt's `Syntax.GoodItemProofs.readsAtFraction`); redone as SW-4595
  above.
### SW-4587: where the `examples` bench's growth since 14 Nov comes from (1.96x steps, 4.1x peak): attribution, one accident found

- **Status:** measured, nothing changed in code. The accident below is filed
  as a finding.
- **Method.** `stitchwort-bench examples --no-time --parts FILE` already
  writes per-file steps, visits, allocations and peak bytes. Run on this
  commit (reproduces the baseline: 16,468,521,077 steps, 1,161 MB) and on
  `282325b14` in a scratch worktree (8,412,263,794 steps, 282 MB), then
  joined by file name. The peak is the maximum over files, not a sum.
- **Where the extra 8.06 G steps are.**
  - **New files: 374 files, 5.54 G steps (34%).** 43 of them import
    `Std.Parse` and cost 3.58 G between them (about 83 M each: the walk,
    continuation and `reads-*` families, 75 to 135 M and 135 MB peak each).
    Every file importing Parse checks Parse's lemma library, which has grown
    (`runFromLabelWholeFromOkTree` alone is 14.6 M); the 25 Parse-importing
    files of 14 Nov went from 0.95 G to 1.11 G. The other 331 new files
    cost 1.96 G.
  - **Files already there: 1,619 files, 8.40 G to 10.93 G (1.30x), 2.53 G
    extra.** 659 of them were edited since (sweeps), 996 unchanged ones went
    from 3.67 G to 4.58 G (1.25x, median file 1.07x), so it is not
    content.
    - 489 files carry 2.2 G: 332 files pay +3 to 5 M (median 3.83 M) and 157
      pay +5 to 8 M. A file that uses `rewrite`, `arithmetic`, `algebra`,
      `decreasing` or `cases` loads `Std.Omega`, whose eight types now
      derive `==`, `<` and printing: `Std.Omega.Fact` 1.46 M, `Goal` 0.54 M,
      `ITerm` 0.51 M, `NTerm` 0.38 M, `Cert` 0.38 M, `Step` 0.28 M, `Row`
      0.09 M (about 3.7 M); the ring files add `Std.Ring.ZExpr` 0.47 M and
      `NExpr` 0.30 M and so +8 M. That is D3609 (SW-3369, `2f4c14504`,
      15 Nov: std types derive `==`, `<` and printing), which SW-3710 had
      measured on `import Std`: deliberate. The trivial `reject/rewrite-*`
      files go 2.2 M to 6.0 M (2.77x) for this reason alone. The +5 to 8 M
      group is the same cause plus std growth on `List`/`Nat` imports.
    - 956 files moved less than 1 M either way.
  - **Peak.** The 1,161 MB is one new file, `reject/resource-steps-unfolding.sw`
    (added 14 Nov, SW-2009; a `byComputing` three million calls deep that is
    meant to hit E-RESOURCE): it alone is the maximum, 62 M steps. Without
    it the maximum is `accept/fin-pattern-numbers.sw` (new, 668 MB), then
    `float-playlist` (428 MB; an old file, 282 MB then, now importing the
    larger `Std.Float`). 48 new files peak over 100 MB (13 `large-hypothesis-*`
    and `walk`/`continuation`/`reads` files at 135 to 265 MB), against 9 old
    ones; a file's floor is about 19 MB (the session's stack and library). Total
    allocations 9.37 G to 19.19 G (2.05x), 32% of it from new files.
- **Old files more than 1.5x slower in steps: 214 of 1,619** (1.13 G extra).
  190 are the D3609 cost above (`+3.0 to 4.6 M` or the ring `+8 M`); the
  rest, by extra steps:

  | File | Steps 14 Nov | Steps now | Peak MB | Cause |
  |---|---|---|---|---|
  | `reject/reads-nested-binds-unknown-field` | 102.0 M | 200.7 M (1.97x) | 76 to 99 | Parse's lemma library (`runFromLabelWholeFromOkTree` 14.6 M and others) |
  | `accept/float-playlist` | 34.0 M | 110.9 M (3.26x) | 75 to 428 | `Std.Float` growth (`ofIntMonotone` 9.3 M, `Theory.roundGrid` 5.1 M); the 428 MB is not explained |
  | `accept/fin-table-deep` (file unchanged) | 23.1 M | 77.8 M (3.37x) | 59 to 75 | **accident, below** |
  | `reject/rewrite-solution-too-large`, `reject/rewrite-value-too-large` | 4.3 M, 4.4 M | 22.3 M, 22.2 M (5.1x) | 159 to 253, 236 to 248 | `Main.big` 16.2 M with a 2,000,001-node read-back, plus D3609's 3.8 M; SW-4237's second try (10 M) and SW-4469's failed fast path (4.07 M, SW-4601) |
  | `accept/as-written-unconfirmed` | 16.7 M | 26.9 M (1.61x) | 282 to 296 | the two `at the limit` declarations, 8.4 M and 4.2 M; not bisected |
  | `reject/or-pattern-binds`, `cases-fallback-budget`, `omega-waits`, `cases-budget-int` and the 12 `ring-*` | 0.9 to 3.4 M | 8.5 to 10.2 M | 19 to 40 | D3609 (`Std.Omega`, `Std.Ring`) |

- **The accident: SW-3325 (`6d960d350`, 15 Nov, "Display only: terms and
  hashes are unchanged").** `fin-table-deep` (a 64-row `Fin` table, every
  link a family split) went from 2.4 s to 6.5 s user; bisected by user time
  over 11 builds between `282325b14` and now, first slow commit `6d960d350`.
  Cause: `arm_display::enter_family_split` runs, at every indexed-family
  split, `same(cx, &cx.env[l], &before[l])` for every variable in the
  context, and `same` quotes both values folded; with entries that are
  chains sharing tails, that is most of the file. Measured by emptying
  `solved` in a scratch edit (not kept): `Main.code` 55.4 M steps to 5.6 M (the
  rest of the file is std, about 20 M). The result
  is only needed to print an arm's goal, so it should be computed when an
  error or a hole displays one (keep `before` and the values after the
  split, compare lazily), not on every split of a program that checks.
  Left alone: it moves display code with snapshots under it, which wants
  its own lane and the goal snapshots rerun. Filed as a finding.
- **Conclusion.** The step growth is mostly deliberate: new examples 34%
  (two thirds of those import Parse), D3609's derived instances in std about
  27% of the extra on old files together with std growth, and one accident
  (about 55 M here, more on any large `Fin` or family match). The 4.1x peak
  is one file's size by design plus 48 new files with large state.

### SW-4569: bench baseline re-recorded after eight days of accepted costs

- **Status:** merged (baseline re-recorded on main, 05:12 to 05:25, quiet
  machine, load about 4).
- **Problem.** `baseline::counts_have_not_regressed` failed in the all tier
  (D3712): the baseline was from 14 Nov (`282325b14`) and nothing had re-run
  it since, so every cost from 14 to 22 Nov showed at once.
- **Cause (SW-4569's bisect).** `check-number-table` and `check-number-wide`
  +12.5% steps (10 per number-pattern row) and part of `check-text-literal`'s
  allocations (+15%) are SW-3930 (`526f98b64`, D3680: declared types kept
  glued, a `Refl` body checked unglued), a deliberate design cost its merge
  note reported only as 1.06x on byComputing. `check-closed-*` visits +11.6%
  and peak heap +15.6% grow in steps with the standard library (92 lemmas
  lifted into std by SW-4218, `b78caf004`, among others).
- **Accepted.** Both are the price of changes made on purpose; no accident
  was found, so nothing was changed in code.
- **Measured.** The `examples` sweep is now 1,993 files against 1,625 (1.23x)
  but 16.5 G steps against 8.4 G (1.96x) and 1.16 GB peak against 0.28 GB
  (4.1x): more than the file count explains. Thirteen `large-hypothesis-*`
  examples (19 and 20 Nov) are large by design and are a likely part; not
  yet measured, so filed as SW-4587.
- **Also.** SW-4580 cut AoC 2020 day 16's `runsNotes` from 55.4 M steps
  (358 M uncapped, after SW-4480) to 40.3 M, below its 42 M before SW-4480;
  pinned under 48 M by SW-4581's test.

## 21 Nov 2026

### SW-4536: `byComputing` on a goal with no unknowns compares unglued, as the kernel does; the parser-run examples' elaboration 15-130x fewer steps, a 26-namespace check 19% fewer

Profiling three of the seven slowest declarations of the tools/fmt check
(Overmind, 21 Nov) by probes in a scratch copy of the namespace and an
env-gated step count around `rfl_against_equation`'s unification:

- **Measured:** `readsBackCommentExample` (one `byComputing`: the parser
  run on a lexed line against the tree it gives) cost 95.6M steps, of
  which the elaborator's unification of the two sides was about 90M; the
  kernel checked the same equation in 63-70 ms. Running the lexer and
  parser once costs 0.66M (lexing 0.22M of it). Trying `value::conv`
  before unification changed nothing (91.3M on a copy of the goal): the
  cost is the glued evaluation, which compares calls through their lazily
  kept unfoldings and recomputes the same call many times, not
  unification's own bookkeeping. That experiment, applied to every
  `byComputing`, also ran a dependency check for over 14 minutes before
  it was stopped; not kept.
- **The change:** `same_unglued` (`crates/elab/src/check.rs`) reads both
  sides back folded, fills in solved unknowns, and, if no unknown is left,
  evaluates them unglued and converts them, as the kernel does with
  `Term::Refl`; `true` is `Term::Refl` at once, `false` falls through to
  the unification path as before, so answers, messages and terms are
  unchanged (hashes too: the term is `Term::Refl` either way).
- **Measured after** (`check --no-cache Syntax.ReadBackHungTop
  --timings=all`, 26 namespaces, 5,532 declarations, steps):

  | declaration | before | after |
  |---|---:|---:|
  | `ReadBackLine.readsBackCommentExample` | 95,631,434 | 2,868,867 |
  | `ReadBackHungTop.readsBackHungListExample` | 285,064,200 | 149,944,146 |
  | `ReadBackHungTop.readsBackHungSignExample` | 181,473,032 | 96,885,507 |
  | `ReadBackHungTop.readsBackHungTypeExample` | 5,304,693 | 4,481,259 |
  | `ReadBackLine.commentSpeltExample` | 1,095,691 | 3,964,250 |
  | `ReadBackRuns.runsDefinitionParts` | 165,348,000 | 165,363,193 |
  | all 5,532 | 1,620,932,571 | 1,310,746,986 |

  By namespace: `Syntax.ReadBackHungTop` 473.8M to 253.3M (elab 45.6 s to
  1.0 s; kernel 18 s unchanged), `Syntax.ReadBackLine` 143.6M to 53.7M;
  the others within +0.2%. The wall time of the check fell from 168 s to
  105 s. Accepted regressions: `commentSpeltExample` 1.1M to 4.0M (its
  glued comparison was cheap and the unglued one runs the lexer per
  item) and a few `Std.Doc.Proofs` declarations up to +1%.
- **Left:** the two hung examples' remaining steps are the kernel's (18 s
  for the namespace): every `listAt k` / `signAt k` re-lexes the whole
  source (0.22M steps each), several hundred times over the proof's
  `byComputing` witnesses. `standsEachFile`, `printedFinish1`,
  `atomHung` and `runsDefinitionParts` were not profiled.

### SW-4512: "does this type still hold an unknown?" stops reading back at the first one; walks and hand proofs about parsers 13-20% fewer steps, the walk's 3x gap unchanged

Asked to bring the walks of three slice 1 formatter theorems under 2x
their hand proofs (SW-4495 left them at 1.8-3.3x in steps), this lane
profiled `givesListItemsFrom` (233,170 steps, hand proof 73,311). macOS
`sample` can't pick 18 ms out of a 60 s check, so steps were attributed
instead: an env-gated counter of each part's own steps, over the walk, the
elaborator's application path and the unifier's outermost runs (kept as a
patch, not merged).

- **Measured, by own steps:** unification 98-122k over about 330
  comparisons; `crate::interfaces::unsolved_in` in `lambda_arg` 53k over
  **6** calls; `explicit_arg` 28k; the walk's lemma search 18k;
  `nested_post` 4k; `fix_nested_goal` 3.4k. The nested-bind machinery
  itself is small; the three outer nested binds' then-lemmas cost
  28-48k each as checked against the whole goal.
- **The hotspot:** `unsolved_in` asks whether a type (here a
  continuation's domain, `∀ v => first v → Parse.Gives inv (() => j v)
  holds`) still holds an unknown by reading back its whole normal form
  (up to 100,000 nodes) and then scanning it: as much work as running the
  parser code the relation is about. The answer was yes each time.
- **The change:** `value::normal_form_meets` reads the normal form back
  as before but stops at the first unsolved unknown (or erased
  placeholder) it meets as a value to read back; a value that only
  forces to one is still found in the finished term, and past the cap it
  falls back to the folded read-back as `scanned` does.
  `interfaces::has_unsolved` uses it for the nine callers that only ask
  yes or no (`check.rs`, `rows.rs`, `interfaces.rs`); the three that use
  which unknown it is keep `unsolved_in`, whose first unknown is in the
  finished term's order. The answers are the same: an unknown met is in
  the normal form, and over the cap the folded form, which has every
  unknown the normal form has, says yes too. A run that used to stop
  for size or steps in that read-back can now finish.
- **Tried and dropped:** (1) giving a nested bind's then-lemma the `p`,
  `j` and `first` that `nested_post` already found, as `[name := …]`:
  233k to 215k, a new kind of walk place for 8%, and the terms may
  change; (2) answering from the folded read-back first: no gain, as the
  unknowns sit in `Parse.Gives`'s arguments, which a call may drop, so
  it had to fall back.

Steps (`check --no-cache … --only … --timings=all`, release build, one run
each; ms are under load and only indicative):

| theorem | walk before | walk after | hand before | hand after | walk / hand before | after |
|---|---|---|---|---|---|---|
| `givesListItemsFrom` | 233,170 | 187,303 | 73,311 | 59,576 | 3.18x | 3.14x |
| `givesListItemsFromAny` | 221,603 | 177,507 | 67,734 | 54,499 | 3.27x | 3.26x |
| `givesDataParamStep` | 195,467 | 180,051 | 111,155 | 96,447 | 1.76x | 1.87x |

Term nodes are the same before and after for each theorem and each
namespace (Syntax.ParseWalk 13,508, ParseWalkOutside 1,842,
ParseWalkOthers 25,727), as are the kernel's times. The namespaces'
elaboration, ms (same runs, walks as merged): ParseWalk 245.7 to 220.7,
ParseWalkOutside 46.7 to 46.5, ParseWalkOthers 1,166.9 to 1,035.1.

The target was missed: the hand proofs gain as much as the walks, so the
ratios barely move. What the walk adds on top of a hand proof is mostly
the nested binds' three identity then-lemmas checked against the whole
goal, and the elaboration of the continuation lambdas around them; the
next step is a walk that reassociates a bind whose bound computation
performs an operation (`Effect.bind (Call o k1) k` computes to
`Call o (y => Effect.bind (k1 y) k)`), so it writes the hand proof's
chain, or one that gives the then-lemma's implicits it already knows.

### SW-4498: a chain of `.read`s checked in exponential time; now about cubic in steps, 57 ms for twenty conjuncts

A test fact read by hand to the end of an `&&` chain,
`h.read.right.read.right…` (the term `check --expand-facts` writes for a
`byFacts` there, SW-4488), took 0.76 s for 8 conjuncts, 3.2 s for 10,
13.5 s for 12 and over two minutes for 20. Profiled with macOS `sample`
on 12 and then 40 conjuncts.

- **Cause 1, the exponential.** A dot call checked or inferred goes first
  through its prefix form (SW-129, `dot::prefix_form`), which infers the
  receiver once to find the function, undoes that, and leaves the real
  elaboration to infer it again. A found head is cached by the call
  (`Caches::dot_heads`), so the second inference doesn't search again. A
  missing one (`.read` on a test fact, which no namespace has) was only
  marked failed for the unknowns' state it failed in (`dot_failed`), and
  that state differs each time the outer call visits it, so every `.read`
  inferred its receiver twice: 2^n. A missing member found with no
  unknown in the way is now cached as `None` beside the found heads, as
  stable as they are (the receiver's view met no unknown).
- **Cause 2, most of what was left: errors built to be dropped.** With
  the first fixed, three quarters of the samples were building
  `E-UNKNOWN-FIELD`'s message (`unknown_member`: near misses and other
  namespaces' functions, each a pass over the whole scope) for lookups
  whose error is thrown away: the prefix form's, and the effect check's
  (`effects::may_perform_at` → `dot::target`, which looks up each call of
  the chain up to 8 deep, at every level). Those callers now use
  `find_quietly`, whose missing member's error is bare.

Results are unchanged: the same lookups happen, in the same order, and
only a lookup's failure is remembered longer and described less where no
one reads it. Elaboration steps fell (n = 4: 9,281 to 6,628; n = 10:
1.71M to 89k); terms, kernel time and node counts are the same. The error
a user sees comes from the real lookup, which still builds the full
message (checked with a typo, `.rigth`: "did you mean `right`?").

`Main.longRead` elaboration, ms (`check --timings`, release build;
`h.read.right` repeated n − 1 times):

| n conjuncts | before | after cause 1 | after both |
|---|---|---|---|
| 4 | 30.4 | 23.5 | under 1.5 |
| 6 | 166.9 | | 1.5 |
| 8 | 763.1 | 142.5 | 3.0 |
| 10 | 3,209.5 | 255.3 | 5.9 |
| 12 | 13,529.1 | 409.2 | 11.8 |
| 20 | over 2 min | 1,456.3 | 56.9 |
| 40 | | 7,009.9 | 728.4 |
| 80 | | | 10,681.3 |

`h.right.right…` (a field of a test fact read through its reading, no
`.read` written) wasn't exponential but gains from cause 2: 20 conjuncts,
275.7 to 63.3 ms.

What's left grows about as n^3 in steps (n^2 in nodes: each step's
`Iff.forward` carries the rest of the chain's type, `reading::step_proof`
quoting it each time). The cubic is the prefix form's double visit again:
each level's first visit infers its receiver speculatively and then for
real, and the second, cached, costs the chain below it. Making that linear
means not inferring the receiver twice (keeping the speculative
elaboration, or finding the head without it), a change to SW-129's design
left for a ticket. Regression example:
`examples/accept/facts-long-read-chain.sw` (20 conjuncts, about 60 ms; by the growth above it
would have taken over an hour before, estimated, so the examples sweep's
timeout catches a return).

## 20 Nov 2026

### SW-4469: two-run walks skip four unfolded read-backs

Two-run walks (`Parse.Follows`, `tools/fmt`'s FollowsStatements) checked
2 to 13 times slower than the hand proofs they replace (SW-4421's W4
report). Profiled with temporary step counters (evaluation steps,
`Budget::total_work`, exclusive per phase) around the walk's phases, on
`followsRewriteAfter`: 1.19M steps walked, 61k by hand. Measured:

| Where | Steps |
|---|---|
| Choosing the tail call's lemma: `is_proposition` on each premise (`SelfFollows self selfTwin`, ...), twice | 339k |
| Same place: `has_unknown` on the premises | 102k |
| The walk's `rewrite <- valueFacts`: the goal read back unfolded up front | 213k |
| Same `rewrite`: the hidden-copy check reading the motive back unfolded | 212k |
| Same `rewrite`: `find_ready_dictionaries`' normal-form scan | 215k |
| Unifying lemmas' thunks with the calls | about 28k |

Each is a read-back of a statement about parser code in normal form
(16,388 nodes at the largest), which none of these places needed. Each now
takes a cheap path first and keeps the old code for what that doesn't
settle (crates/elab only, commit 1d182e475):

- **`rewrite` by a hypothesis whose replaced side is a variable**, in a goal
  with no unknowns (`rewrite.rs`, `variable_as_written`): the search as
  written runs without the up-front unfolded read-back of the goal. A rule
  with no unknowns of its own never uses that read-back in the search as
  written (it is only for finding today's instance of an open rule), so
  where that search keeps its result the outcome is the one the usual path
  gives. If it doesn't, everything is undone (snapshot and search budget)
  and the usual path runs from where it started.
- **The hidden-copy check for a variable** (`as_written.rs`,
  `hidden_copy_in`): a definition is closed, so a call's unfolding mentions
  a variable of the goal only through the arguments the call shows, where
  the search already replaced it. A folded motive that doesn't mention the
  variable therefore has no copy unfolded either, and the check answers
  "none" without reading the motive back. If the folded motive still
  mentions it, the full check runs.
- **`find_ready_dictionaries`** (`interfaces.rs`): with no dictionary
  obligation pending, solving finds nothing, and only an equation is ever
  computed again; so for a goal that isn't an equation the result was
  always `None`, and it is now returned without the scan.
- **`cases::is_proposition`**: the sort is inferred from the type read back
  folded first. The kernel has no cumulativity (docs/core.md), so a term
  has one type up to conversion, and by subject reduction its unfolding
  has the same one: the folded and unfolded readings give the same sort.
  Only when the folded term has an unknown (which the kernel can't type),
  or the kernel refuses it, does it read back unfolded as before.
- **The walk's `has_unknown`** (`walk/registry.rs`): unfolding adds no
  unknown, so if the folded, zonked value has none, neither does its normal
  form, and it answers `false` without the scan.

Results, messages and terms unchanged: `hash_stability::*` (12 tests)
passes without re-recording; walk, as-written, rewrite and soundness
examples pass. Measured, `check --no-cache --timings`, one run each
(times noisy, steps exact), elaboration steps and total ms:

| Theorem | Hand | Walked before | Walked after | After ÷ hand, ms |
|---|---|---|---|---|
| followsRewriteAfter | 61k, 5.6 | 1.19M, 71.0 | 109k, 9.6 | 1.6x |
| followsRewriteWith | 143k, 11.4 | 1.05M, 68.3 | 221k, 17.9 | 1.5x |
| followsTargetAfter | 483k, 27.8 | 1.10M, 66.0 | 748k, 45.6 | 1.6x |
| followsRewriteTargetIf | 111k, 9.2 | 721k, 44.6 | 349k, 23.5 | 2.5x |
| followsReverseIf | 113k, 8.1 | 135k, 10.9 | 135k, 10.9 | 1.3x |
| followsHere | 17.5k, 1.4 | 34k, 3.1 | 34k, 3.0 | 2.1x (1.6 ms more) |

Hand proofs' steps unchanged. `followsRewriteAfter`'s `--expand-walk` text,
checked as a hand proof: 710k to 285k steps. Not measured: instructions,
the other 40 FollowsStatements walks, or the whole of `aoc/` (left to the
rolling check).

**What's left.** `followsRewriteTargetIf` (2.5x) and `followsHere` (2.1x,
small in absolute terms) are still over the 1.5x bar, and weren't profiled
after the change. `followsTargetAfter` and `followsRewriteWith` sit near
it.

**Tried and dropped.** A head filter in the walk's lemma fitting (a lemma
whose thunk calls a different function than the call doesn't fit, without
unifying): measured about 0.5k steps saved on `followsRewriteAfter`. Not
kept: it would make fitting accept less than full unification does.

**Not yet done.** The up-front unfolded read-back in `rewrite_once` could be
skipped for any rule with no unknowns, not only a variable hypothesis: the
search as written never uses it for such a rule. That would speed up
hand-written rewrites by lemmas in large goals. It needs care where the
goal is too large to read back, which today goes to the unconfirmed path
first. The hidden-copy shortcut holds only for a variable.

## 17 Nov 2026

### SW-3752: `cases` tries a failing proof a second way (accepted cost)

Not an optimisation: a cost accepted with a feature. A `cases` that fails
now runs a second try (hypotheses first, `arithmetic` before each split,
up to 256 cases) before reporting, so a failing `cases` costs up to that
much more; a proof the first try closes runs exactly as before, keeping
its terms (`hash_stability::prelude` and the `cases` examples' hashes
unchanged). Measured on the rejects: `cases-budget` (512 `Bool` cases)
0.31 s before, 0.36 s with the second try; the second try's new accepts
(`cases-hypotheses-first`, ten character comparisons against a
hypothesis of four) take about 1.2 s. Not measured: instructions, or the
whole of `aoc/` (left to the rolling check).

### SW-3719: derived `==` and `<` laws decide a constructor's fields as nested pairs, once; cubic in fields to about quadratic

- **Status:** kept (Opus), the derivers (`derive.rs`, `derive_ord.rs`) and
  two additions to the core (`Ordering.thenPairEqual`, `Ord.instanceFor`,
  `core/OrdDerived.sw`). Second fix under D3669, from
  [derived-instances-rethink.md](../proposals/derived-instances-rethink.md)
  §3.2. Statements of every derived declaration unchanged; their proof
  terms, and so the hashes of derived declarations and of what uses std's
  derived instances (`Std.Disk`, the `Std.Files` simulators), change
  (D2303). New hidden declarations: `T.%C%unpack`, `T.%C%pack`,
  `T.%sameIff`.
- **Profile** (steps per generated definition, a temporary counter around
  `Elaborator::definition`; 16-field record after the `==` half):
  `%sameIff` 0.20M, `%equal` 0.72M, `%trans` 0.72M, `%flip` 0.11M, the
  record's 256 update lemmas 0.38M. `%equal` read each field's `Equal` out
  of `Ordering.thenEqual`'s conjunction `k` deep and inferred the pairs'
  equality bottom-up; `%trans`'s cost was `Ord.thenTrans` finding the
  field's instance at every level under the hypotheses of the fields
  before (a probe with the instance fixed: 0.16M against 0.72M).
- **Change.** (1) `T.%C%unpack : Pair A0 (Pair A1 …) → T` and `T.%C%pack`
  (kernel terms) for each constructor whose fields are all data; the
  decision of `C a… = C b…` is `Decidable.map` of `Pair.decMk` a field at a
  time, carried back by `Eq.cong` of them (no conjunction, no `J` chain).
  (2) `T.%sameIff : Iff (T.%same r s = True) (r = s)` states each
  constructor's decision once; `%sameSound` and `%sameComplete` are its two
  directions (with two constructors or more, one `J` along `T.%etaAt`
  carries both). (3) `T.%equal` proves the pairs equal by
  `Ordering.thenPairEqual h first (h' => rest)`, `h` first so each level's
  comparisons are known, annotated with the pairs' equation, and carries it
  back with `Eq.cong T.%C%unpack`. (4) `T.%trans`, and `T.%equal` with two
  constructors or more, bind `let %ok := Ord.instanceFor %ak` once per field
  and pass `[ord := %ok]`. Constructors with proof fields keep the old
  shapes. Tried and dropped: the same instance binding for `%flip` (0.11M →
  0.20M on the record) and for `DecEq.decide` in `%sameIff` (no change); a
  `%equal` without the pairs' annotation (2× dearer).
- **Measured** (steps, `STITCHWORT_TIMINGS=decls check --no-cache`, the
  type's row; elaboration ms in brackets, machine load 10 to 38):

  | Probe | Before | After |
  |---|---|---|
  | record of 4 `Nat`s | 252K (16 ms) | 110K (8 ms) |
  | record of 8 | 1.75M (104 ms) | 348K (27 ms) |
  | record of 16 | 16.85M (1,319 ms) | 1.33M (129 ms) |
  | record of 32 | 202.4M (23,339 ms) | 6.79M (773 ms) |
  | 16 constructors × 2 `Nat`s | 2.26M (140 ms) | 1.33M (89 ms) |
  | 16 constructors × 3 `Nat`s | 5.58M (323 ms) | 2.16M (142 ms) |
  | `Std.Omega.Fact` (15 constructors of 2–3 fields) | 4.14M | 1.48M |
  | `Std.Map.Tree` | 1.81M | 0.85M |
  | import programs (`import_cost.rs`): Nat / Int / Text / Map | 19.79M / 26.14M / 17.91M / 43.92M | 14.59M / 20.46M / 12.87M / 35.03M |

  Doubling a record's fields now multiplies the steps by 3.2 to 5.1 (7 to
  12 before). Guarded by `derive_cost::derived_instances_of_wide_constructors_stay_cheap`.
- **Left.** What remains at 16 fields: the record's update lemmas (0.38M,
  `f²` of them; not derived instances), `%trans` 0.29M, `%equal` 0.23M,
  `%sameIff` 0.20M, `%flip` 0.11M. Many constructors of few fields gain
  least (1.7× at 16 × 2): per constructor, the tag and `T.%etaAt` work in
  `%sameIff`, `%equal` and `%trans` (about 25K steps each for `Fact`)
  dominates, not the fields.

### SW-3726: `&&` chains of `Bool`s no longer zonk their tail at every level; a solution's lambdas take their arguments at once

- **Status:** kept (Opus), elaborator (`logic.rs`) and the evaluator's
  forcing of solved unknowns (`value.rs`: `force_solved`, `Frame::Replay`;
  neither runs in the kernel, which has no unknowns). Terms, results and
  messages unchanged: every probe below elaborates to the same node and
  read-back counts. First fix under D3669 (derived instances stay eager;
  their cost is fixed where it arises), from
  [derived-instances-rethink.md](../proposals/derived-instances-rethink.md) §2.3.
- **Profile.** samply (4 kHz) on nine copies of gen4's 32-term
  `(DecEq.decide a b).holds && (…)`: 71% under `as_bool`'s right-operand
  closure in `zonk_changed`, from `Conjunct::outside_binder`. `as_bool`
  takes each level's right operand, the whole rest of the chain, out of
  the branch binder (zonking it) to offer the conjunction to an `if` that
  may use its proof; a chain of `Bool`s re-zonks its tail at every level,
  and `logic::conjunction` throws the result away, since neither side
  is a decided proposition. The zonk's own cost was the second cause: 67%
  in `zonk_solved`'s `eval`, 27% self in `Rc<[Value]>::from_iter_exact`,
  the environment copied to add one variable as each of a solution's
  lambdas is entered; a solution is a function of all the variables in
  scope (65 to 97 here), so each look at an unknown was quadratic in them.
  The projection chain (`And.left (And.right^k q)`) spent 38% in the same
  per-lambda copying, through the unifier's `force_solved`/`force_now`.
- **Change.** (1) The right operand is taken out of its binder only when
  the left or right side is a decided proposition (after the left side's
  kind is known); otherwise the conjunction can't be formed and nothing is
  zonked. (2) Applying a solved unknown's solution (`force_solved`, and the
  machine's `Frame::Replay`) enters a closure's run of nested lambdas with
  all their arguments at once, one environment built (`enter_run`).
- **Measured** (steps; `STITCHWORT_TIMINGS=decls check --no-cache`, the
  sw3725 probes; elaboration ms in brackets, machine load 10 to 26):

  | Probe | Before | After |
  |---|---|---|
  | gen4 `(DecEq.decide a b).holds && …`, 8 / 16 / 32 | 37.4K / 225K / 1.54M (250 ms) | 18.0K / 64.8K / 245K (26 ms) |
  | gen4 `(Nat.decEq a b).holds && …`, 32 | 465K | 42.6K |
  | gen4 `a == b && …`, 32 | 54.1K | 44.0K |
  | `if` of the `DecEq.decide` chain, 32 | 1.66M | 292K |
  | gen2 `congConj` (projection chains), 8 / 16 | 103K / 1.15M | 75.2K / 744K |
  | gen2 `congTrans` (`Eq.trans` of `Eq.cong`s), 8 / 16 | 38.7K / 149K | 32.3K / 121K |
  | one `And.left (And.right^30 q)`, 32 | 896K (136 ms) | 418K (37 ms) |
  | 16-field record with derived instances | 19.27M (1,513 ms) | 16.85M (1,211 ms) |
  | Nat import program, sum over std's declarations | 21.43M (1.88 s wall) | 20.51M (1.81 s) |

- **Left, not this mechanism.** The `DecEq.decide` chain is now as
  quadratic as `a == b` (3.8 times per doubling, from the two variables
  each term adds to the scope) but 5.6 times its steps: `.holds` on a call
  infers the receiver once for dot notation and again as an argument
  (`dot::prefix_form`, 29%), and the instance is found by
  `find_ready_dictionaries` (29%). Projection chains are still about cubic
  (6.5 times per doubling): each level's unification forces the chain of
  unknowns below it (`forced_rules` → `force_now`), so a depth-`k` chain
  re-forces `k` levels `k` times; and naming the tails (`congConjLet`) or
  reshaping the proofs (§3.2 of the note) is still the larger win for the
  derivers. A chain of decided propositions (`a = b && …` as a `Bool`) is
  cubic for another reason: 50% in `solve_ready_instances_keeping` →
  `unsolved_placeholder` under `short_circuit`'s `undo::attempt`
  (448K steps at 32, unchanged). The derived record's main cost is
  elsewhere: `effects::call_performs` 31%, `infer_j` 66% inclusive.

### SW-3709: readsThen chains 3-5x the steps after SW-3561; the first lemma is compared by its arguments first

- **Status:** kept (Opus). Statements, accept/reject results and messages
  unchanged; proof terms of readsThen calls whose first lemma matched in
  place change (hashes: 14 std `Parse` declarations, 2 in the example
  `reads-then-finds-split`), see below.
- **Measured.** `reads_chain_proofs_stay_within_recorded_step_counts`,
  readsTwo's steps: generic 175,035 → 47,741, characters 100,564 → 34,358
  (before SW-3561: 38,452 and 32,406; bounds recorded at the new counts).
  AoC 2020 day 16's four `reads*` proofs: 2.73M → 1.05M steps, 192 → 71 ms
  elaboration (`check --no-cache Aoc.Year2020.Day16.Proofs`).
- **Profile.** Step counts around each phase of `fallback_holding_lambdas`
  in readsTwo: of the outer call's 167K steps (generic), the in-place check
  of the first lemma `Prs.readsSatisfy` against `Prs.Reads ?p ?first` took
  35K and 92K at the two levels (127K, 76%) and failed: the unifier
  compares two calls of one definition with unknowns by unfolding them,
  and the run it unfolds to is stuck on `?p ()`. Then
  `by_arguments_in_place`, the comparison by the calls' arguments, took
  about 200 steps and succeeded. Characters: 66K of 94K.
- **Change.** Under held lambdas (`infer_expecting`'s `hold_lambdas`), an
  argument whose type has unknowns is compared by arguments first
  (`by_arguments_first`), and checked in place only if that doesn't match.
  Where the in-place check fails, the result is the same. Where it
  succeeds (a lemma that is a variable, `readsItem: Parse.ReadsIn inv item
  …`), it also got there by unfolding, and solved `?p` inside the run; by
  arguments it is the lemma's own parser, so those proof terms change.
- **Not the cause.** SW-3715's 6.6 s for `examples/accept/reads-then-finds-split.sw`
  against 0.26 s for a trivial file with its imports: std files load lazily,
  so the trivial file never loads `Parse`; the example's own declarations
  take 45 ms, and the rest is std's `Parse/Reads.sw` (2.7 s, led by
  `runFromLabelWholeFromOkTree`, 1.05 s) and its neighbours, the same
  before and after this change (6.87 s → 6.74 s wall, `check --no-cache`).
- **Left.** readsTwo is still 24% (generic) and 6% (characters) over its
  pre-SW-3561 count: the held call's comparison of its type with the goal
  (6-10K steps a level) unfolds `Reads` too. Not changed: comparing by
  arguments there is the choice SW-3561 exists to avoid (`afterMark`).

### SW-3710: std's derived instances cost every importer +40-60% on a cold load; profiled, fix proposed, nothing changed yet

- **Status:** profiled (Opus); fix waiting for a decision in
  [derived-instances-import-cost.md](../proposals/derived-instances-import-cost.md).
- **Measured.** `check --no-cache` of import_cost's programs, before
  (`8b9c6ace9`) and after (`da665940f`) SW-3369 (D3609): Nat 11.2M → 20.7M
  steps, 1.11 → 1.77 s; Int 17.3M → 27.1M, 1.62 → 2.40 s; Text 10.4M →
  18.9M, 1.06 → 1.66 s; Map 31.7M → 45.0M, 2.76 → 3.90 s (best of three,
  load about 8).
- **Profile.** By instance: derived `Ord` two thirds, `DecEq` one third,
  `Show` and `Finite` negligible. By type: twelve `Std.Omega`/`Std.Ring`
  reflection types are 9.0M of Nat's 9.5M extra (`Omega.Fact` alone 4.2M,
  its `%equal` law 2.3M); `Map.Tree` adds 2.0M for Map. Cost is linear in
  constructors (about 50K steps each for `%sameSound` and `%equal` with two
  `Nat` fields). samply: elaborating the generated source about 80%, the
  kernel 19%; no single hotspot inside elaboration (`infer_j` 37%
  inclusive, instance unification 27%).
- **Tried as a measurement only.** Skipping derivation for `Omega.*` and
  `Ring.*`: Nat 11.6M steps, 1.23 s; Map 35.9M, 3.08 s. Not kept: it
  changes what's derived (an exception to D3609).
- **Proposed.** Derive std types' instances on first use (keeps D3609,
  expected back to the before column).

### SW-3694: check-nested-apps regression (steps +23%, peak heap +38%) from two accidents; both undone

- **Status:** kept (Sonnet). Results, messages and hashes unchanged
  (D3447). Found by Overmind's broad tier at 9ff2833ca; baseline not
  updated.
- **Problem.** `check-nested-apps` (`f (f (… 0))`, 2,000 deep) read 32,081
  steps (baseline 26,081) and 2.6 MB peak heap (1.9 MB); `text-literal-walk`
  heap 4 kB (3 kB). Bisected by building `stitchwort-bench` at a dozen
  commits (steps are deterministic, so one run each).
- **Cause 1, steps: +3 per application.** SW-3561's trigger for holding
  lambdas (fd79bb763, then 0bc8e177f) ran on every application that had no
  `propagation_plan`: `has_implicit_function` forces the callee's type and
  `applies_unknown` quotes the written result type, both counted as
  evaluation steps (+1 a level at fd79bb763: 28,081; +2 more with
  0bc8e177f: 32,081). A call that made no unknown (`f x`, with `f` having
  no implicit parameter) has nothing for either to find.
- **Fix 1.** The trigger first checks that the call made an unknown
  (`metas.len() > metas_from`); only then the two evaluations. Steps are
  26,081 again.
- **Cause 2, peak heap: +0.7 MB.** 72b280851 (SW-3322) added the probe's
  pending context to `undo::Snapshot` as a bare `Option<ProbePending>`
  (several words: a span, a type value, flags, a name list). A deep
  recursion keeps a `Snapshot` live at every level, 2,000 here, so the
  snapshots alone don't explain 0.7 MB on paper (2,000 x a few dozen bytes),
  so the mechanism is not pinned down; the cause is established by the
  measurement below (boxing alone restores 1.9 MB).
- **Fix 2.** `Option<Box<ProbePending>>`: one word in the snapshot, the
  copy made only when a probe has found something.
- **Measured** (`stitchwort-bench check-nested-apps --no-time`, release,
  one run): steps 32,081 -> 26,081; allocations 2,075,500 -> 2,073,500
  (baseline 2,069,502, +0.2%, well inside the threshold); peak heap 2.6 MB -> 1.9 MB. `text-literal-walk`: peak heap
  3 kB again.
- **Not found.** Whether other benchmarks held a similar cost; only the two
  rows Overmind reported were run.

---

## 16 Nov 2026

### SW-3659: today's instance only after a hit as written; `rewrite repeatedly` measured on two std files

- **Status:** kept (Opus), elaborator (`rewrite/as_written.rs`). The std
  conversions are not landed (over 2x, or not shorter):
  dev/patches/SW-3659-std-samples.patch.
- **Change.** For a rule with unknowns, the search as written first found
  today's instance (`todays_instance`, a search of the unfolded goal) and
  then searched as written. Now it searches as written first; only when
  that finds something is today's instance found, with the rule elaborated
  afresh (its unknowns unsolved), and compared as before. Where either
  instance keeps an unknown, or the unfolded goal has one the search as
  written could solve, it is undone and done the old way, so the choice is
  the same. Plain `rewrite` takes the same path. The one difference: a
  search as written that finds nothing no longer spends budget on today's
  instance first, so it can't run out there (`First::RanOut` becomes
  `Not`); both end the same way, since the fallback as written
  (`unconfirmed`) would find nothing either.
- **Measured** (`STITCHWORT_TIMINGS=decls`, sum of elab and kernel, 3 to 4
  interleaved runs, load 4 to 12): toyfmt's Words.sw 556 to 526 ms (-5%);
  todays_instance calls over `Toy.Doc.Proofs` 106 to 48, 118 to 87 ms. The
  nine converted Nat/Bits.sw proofs 89 to 81 ms (-8%). Hashes unchanged
  (`hash_stability::prelude`, `pinned_hashes`, rewrite-repeatedly examples).
- **Ratios against the hand-written proofs, after the change.** Words.sw
  2.42x (0.55 s vs 0.23 s). Nat/Bits.sw, nine proofs (`xorMod`, `xorDiv`,
  `testBitXor` and the `and`, `or` ones; 20 lines shorter, the lemmas'
  arguments dropped): 2.9x on those proofs (87 vs 30 ms), the file 1.4x
  (217 vs 155 ms). Parse/ReadsChars.sw, six proofs whose rules are
  hypotheses (`[split, none, List.appendNil, literal, isTrue]`): 1.1x
  (57 vs 52 ms), but 3 characters longer each. So the cost is in lemmas
  with their arguments left open: `Nat.modAddMul` found by unifying
  `(?a + ?b * ?k) % ?k` with every `%` in the goal, where the explicit
  `Nat.modAddMul x y 2` matched syntactically (orMod 3.2 to 17 ms; a miss
  as written 2 ms with no hit). Hypotheses and closed rules cost little.
- **Dropped.** (1) Not repeating, in the full pass, the try as written that
  just found nothing at the same goal (SW-3654's 22 ms): built, but it
  never fired on Words.sw or Bits.sw, because a rule that reaches the full
  pass was skipped as written by `may_fit` (its key isn't in the goal as
  written) rather than tried. (2) A probe as written before today's
  instance, undone after: instructions over `Toy.Doc.Proofs` +0.1%, since
  the 861 hits paid a second search to spare 58 misses. (3) Skipping
  today's instance for set members (55 ms): changes which instance a set's
  rule rewrites, a design call, not done. (4) `writeLayoutWords`' full
  search (89 ms), found only by the rescue: trying the rescue first would
  change the result wherever the full search finds something.
- **What is left** is the searches themselves: unification of an open
  left side against each candidate (`Search::decide`, unify about 60% of
  it), as SW-3629 found.

### SW-3654: `rewrite repeatedly` rule sets: members only as written, and their checks kept; Words.sw with a set 4.5x to 2.56x, the 1.5x bar still missed

- **Status:** kept (Opus), elaborator (`rewrite/repeatedly.rs`, `cache/rows.rs`).
  The Words.sw conversion is not landed; dev/patches/SW-3602-words-conversion.patch
  is updated to check under the new rule (four calls name their rules).
- **Problem, profiled first.** `STITCHWORT_REWRITE_METRICS` and samply (10 kHz)
  on `check --no-cache Toy.Doc.Proofs`, patch applied. Of 820 ms in rule
  searches, 411 ms was the full search (by computing) of set members that
  didn't fit, `writeLayoutWords` and `writeWords` 290 ms of it: each call
  listing `wordSteps` gets all eleven printer lemmas, and every stall of the
  as-written pass searches each by computing. Besides the searches, each
  call re-ran `check_rule` on every member (unfolding each printer lemma's
  left side): 141 ms over 232 checks.
- **Change.** (1) A set's members are tried only in the as-written pass
  (docs/syntax.md, "Rule sets"): rules listed in the call keep the full
  search, so calls that list rules directly rewrite as before. With the set
  version, 4 calls in `stepWords` then fail (as the brief's stop-early
  experiment found 5); each needed one or two printer lemmas found only by
  computing (`writeLayoutWords`, `newlineWords`), now listed in the call
  instead of the set (the set then rewrote nothing there). A left-open
  error whose set was never found says why. (2) Each set keeps its members'
  checked shapes (per member and direction, filled at first use, not
  cached on disk): a set's members are closed names, checked when the set
  is declared, so the check means the same at every call. Results unchanged.
- **Measured** (`STITCHWORT_TIMINGS=decls`, sum of elab and kernel over
  Words.sw's declarations, 5 runs, load 7 to 12, release build): base
  0.214-0.233 s (median 0.225); set version before 1.07-1.35 s (4.5x); with
  (1) 0.674-0.738 s; with (1) and (2) 0.570-0.585 s (median 0.577, 2.56x),
  the same as SW-3629's per-arm lists. stepWords 437 ms with (1), base 77 ms.
- **What is left** (measured on the converted file, rule searches 340 ms):
  applied as-written rewrites 131 ms (90), failed as-written tries 78 ms
  (60), and the full searches of the rules the four calls name 132 ms
  (`writeLayoutWords` 89 ms). Inside the as-written attempt, today's
  instance (`todays_instance`, an unfolded search for rules with unknowns)
  was 135 ms over the namespace: 40 ms of it for attempts that then found
  nothing as written (computing it after the search would need the search
  run twice when it does find something), and 55 ms for set members. Not
  done, each a few percent: skipping the full pass's repeat of the
  as-written attempt a rule just failed at the same goal (22 ms); skipping
  today's instance for set members (55 ms, which changes which instance a
  set's rule rewrites). Even all three would leave about 2x: the rest is
  the searches themselves, against the base proofs' explicit arguments.

### SW-3629: `rewrite repeatedly` on the toy's Words.sw, profiled; two hotspots cut, the 1.5x bar still missed

- **Status:** kept (Opus), elaborator only (`rewrite.rs`, `rewrite/repeatedly.rs`,
  `check.rs`). The Words.sw conversion (dev/patches/SW-3602-words-conversion.patch)
  is still not landed: 2.46x against a 1.5x bar.
- **Problem, profiled first.** samply at 10 kHz on
  `check --no-cache Toy.Doc.Proofs --only Toy.Doc.Proofs.stepWords`, with the
  patch applied, plus `STITCHWORT_REWRITE_METRICS` and temporary timers. Of
  the time under `rewrite_repeatedly`: comparing candidates with a rule's
  left side (`Search::decide`) 45%, as unify 17%, `has_carrier` (a kernel
  `infer` of each candidate) 12%, `unify_solving_arguments` 11%; in the
  instance-solving second search of `replace_solving_instances`,
  `interfaces::refresh` re-read the whole (large, unfolded) left side for
  every candidate, 60% of that search; and `try_close`'s failing
  `byComputing` built its `E-REFL` message (`refl_error`, read-backs and
  printing) only to throw it away, 8%. In stepWords the as-written pass's
  `todays_instance` (a search of the unfolded goal, for rules with
  unknowns) was 86 ms of 380.
- **Change.** (1) The refreshed left side is kept for the search and used
  for every candidate that solved nothing on the way (the meta store is
  then as it was when the search started); dropped when a candidate
  matches. Same values, so same results; it speeds plain `rewrite` too.
  (2) `try_close` tries `byComputing` with a new `Decl::quiet_refl` set, under
  which a failure is a bare `E-REFL`; the message was never shown.
- **Measured** (`STITCHWORT_TIMINGS=decls`, sum over Words.sw's
  declarations, 3 runs each, load 7 to 36, so read the ratios): before,
  base 0.24 s, converted 0.65-0.68 s (2.8x); after, base 0.223-0.229 s,
  converted 0.555-0.570 s (2.46x). stepWords: base 89 to 74 ms, converted
  400 to 325 ms. `try_close` fell from 616 to 108 samples.
- **Dropped.** A pre-check that skips `todays_instance` when no part of the
  folded goal has the left side's key: same results, but in these proofs
  the goal always holds such a part (`.words` everywhere), so no
  measurable change. L4's key for `may_fit` (the first stuck call after
  computing) wouldn't filter here either: every rule searched in the full
  pass also fits as written. A negative cache of `decide` across searches
  was sized by instrumenting: repeated (rule, candidate) pairs are about
  40 ms of stepWords' 150 ms in `decide`; not built.
- **What is left, and why it isn't a micro-optimisation.** The extra time
  over the base proofs is searches for rules that don't apply: after every
  step each listed rule is tried as written (2 ms each, ~60 per run of
  stepWords), and each written-pass stall runs the full search of every
  printer lemma (25-35 ms each, compared by computing). Two of those
  (`writeWords` in the `FillSep` arm, `writeLayoutWords` in the `Line` arm)
  are found only by `rescue`'s as-printed reading, after both unfolded
  searches fail. Cutting these changes which rewrites run, so it is a
  design call (stage 2's as-written-only question).

## 15 Nov 2026

### SW-3391: `Parse.operators` and `Parse.locatedToEnd`, the toy's hand-written loops moved into std

- **Status:** kept (Sonnet). Std (`Parse/Parse.sw`, `Parse/Tokens.sw`) and
  the toy.
- **Problem.** SW-3383's two speed-ups lived in the toy: precedence
  climbing for operators, and a handler-free loop for lexemes. Every
  grammar written on `Parse` pays what the toy paid before them.
- **Change.** `Parse.operators what levels operand` (levels with an
  associativity; the notes are `chainLeft`'s, tested against a `chainLeft`
  tower on 15 samples, messages included); `Parse.manyToEnd` and
  `Parse.locatedToEnd` for parsers that don't fail part-way. The toy uses
  both.
- **Measured** (native, 933 KB, user seconds, median of 3, load 3 to 5):
  lexing with `Parse.many (() => Parse.located …)` 1.49 s, with
  `Parse.locatedToEnd` 0.97 s (same as the toy's loop). The whole parse
  (lex and parse, print included) 1.84 s with the toy's hand-written
  climbing, 1.97 s with `Parse.operators`: the table scan and a table built
  per expression cost 7%. Format 2.18 s to 2.30 s. Messages unchanged (the
  toy's 82 tests).

### SW-3383: the toy formatter, profiled; its handlers out of the hot paths (3.8 to 2.05 s/MB native)

- **Status:** kept (Opus). Toy code only (`tools/toyfmt`); one runtime
  attempt dropped (below). Scoped to the toy, not the paused speed epics
  (D3465).
- **Problem, profiled first.** `Toy.Timing.main -- format 2600` (933 KB of
  Sprig), native, samply plus the `call-counts` runtime: no hot function;
  the effect runtime and the allocator were three quarters of the time.
  Counted: 5.4 M `Parse` operations, 8.7 M crossings of forwarding
  handlers, about 60 M objects allocated. A probe (1 M operations under
  `Parse.all`) put a `Parse.mark` at about 4,300 instructions and a
  `Parse.optional` round at about 6,300 more [measured]. The toy's grammar
  used nine handlers and about thirty operations per operand (six
  `chainLeft` levels, `many` for negations, `many` of `oneOf` for calls and
  fields), a `many` round and three marks per lexeme, and an `optional` per
  comma.
- **Change.** Precedence climbing and a look at the next token for
  operators, negations, calls, fields, commas and closers, with a handler
  only where something was found (so a dangling operator is still left
  unread); lexemes in a loop of their own, one mark each. Commits on
  `lane/SW-3383`.
- **Why results stay the same.** Every place the old grammar noted an
  expectation, the new one notes the same text at the same offset, in the
  same order; duplicates (six "an operator"s) collapse in the message as
  before. Checked: the toy's 78 tests (goldens, disturbances, exact
  messages), the `toyfmt_formats` end-to-end test, and the old and new
  `toyfmt` on 9,000 mutated sources (three seeds), identical output, exit
  codes and files. No std or compiler change, so no hash moves.
- **Measured** (user seconds, median of 3 at load about 3.5; instructions
  median of 5): lexing 1.15 s / 16.4 G to 0.68 s / 9.3 G; parsing beyond
  lexing 2.08 s / 29.0 G to 0.91 s / 12.2 G; printing unchanged (0.3 s,
  4.4 G); whole format 3.52 s to 1.91 s, 49.8 G to 25.9 G instructions.
  `stitchwort run`: 9.4 s to 5.2 s (one run each, load 25). No benchmark
  run: nothing outside `tools/toyfmt` changed.
- **Dropped:** the runtime's freeing queue (`value::free`'s `pending`) as a
  `SmallVec<[Value; 8]>` instead of a `Vec`, since growing that `Vec` was
  2.8% of the profile: instructions +1%, cycles unchanged. Not kept.
  (Skipping the queue for children that are shared would avoid the
  allocation, but a cell holding the same child twice can then free
  recursively, the overflow SW-2452 fixed.)
- **Left.** Lexing and parsing are still about half `Parse` operations
  (the effect runtime's cost per operation: operations in place, paused,
  D3430) and about a tenth the list of characters (D3597's slices). Details
  in `tools/toyfmt/NOTES.md`, "Speed (SW-3383)".

### SW-3370: derived `==` and `<` linear in the constructor count; 94 constructors from 12.3 s to 0.17 s

- **Status:** kept (Opus). Stage 2 of
  [derived-equality.md](../proposals/derived-equality.md#56-linear-cost-compare-tags-then-rebuild)
  (D3609).
- **Problem, profiled first.** The note's probes (§3), one `check --no-cache`
  each with `STITCHWORT_TIMINGS=1`, timing each derived group: for 47
  constructors `K0 (m: Nat) | K1 | …`, `T.%trans` took 2.4 s of 3.0 s,
  `T.%equal` 0.20 s, `T.%flip` 0.14 s and `DecEq`'s two proofs 0.14 s. Each
  matched both values, with a catch-all for every pair of different
  constructors, so its case tree had n² leaves (n³ for `trans`'s third
  value), each elaborated; `T.%differ` only saved `DecEq` from proving each
  leaf. An enumeration's `T.%equal` and `DecEq` proofs had the same n²
  leaves (0.79 s and 0.53 s of 2.0 s at 94).
- **Change.** With two constructors or more, the derived test and order
  match only the first value, compare the tags first and read the second
  value's fields by projection: `T.%same (C a…) s = Nat.equal c (T.%tag s)
  && …`, `T.%compare r s = if Nat.equal (T.%tag r) (T.%tag s) then
  T.%fields r s else Nat.compare …`. The proofs get the tags' equation from
  new core lemmas (`DecEq.tagsSame`, `Ordering.tagsEqual`, `tagsFlip`,
  `tagsTrans`) and turn the second value into the same constructor by
  `T.%etaAt`, a `J` over `T.%view`, which is built in the kernel from
  projections `T.%C%k%at` that take the tag's equation (their other
  branches refute it). Each law has n equations; `T.%differ` and
  `T.%unfold` are gone, and with them the core's `Ordering.byTagTrans`,
  `andThenTransWhen`, `notBothEqual` and `bothEqual`. One-constructor types
  (records) are unchanged. `if`, not `Ordering.andThen` of the tags'
  comparison, so a run compares fields only when the tags are equal.
- **Why results stay the same.** The order is the same (positions, then
  fields left to right) and so is the test; the instances' laws are the
  same theorems (`Ord.fromCompare` of `compare`, `equal`, `flip`, `trans`;
  `DecEq.sound`, `complete`, the readings), checked by the kernel. The
  derive, ord, deceq, compare, sort, eqeq, nested-data, show and finite
  examples pass, and a new one (`derive-many-constructors.sw`) uses the
  laws on a type with recursive, nested, proof and parameter fields. Every
  derived declaration's hash changed (101 example snapshots); the prelude
  snapshot only gained and lost the lemmas named above.
- **Measured** (release CLI, the type's row of `STITCHWORT_TIMINGS=1`,
  elab + kernel, one run each, load 5-8):

  | Type | before | steps | after | steps |
  |---|---|---|---|---|
  | 24 constructors, `K0 (m: Nat) \| K1 \| …` | 0.78 s | 10.2 M | 0.04 s | 0.48 M |
  | 47 constructors | 3.0 s | 39.4 M | 0.08 s | 0.90 M |
  | 94 constructors | 12.3 s | 158 M | 0.17 s | 1.76 M |
  | 94, an enumeration | 1.78 s | 18.5 M | 0.46 s | 3.0 M |
  | 20, each `(a: Nat) (b: Text) (c: List Node)` | 0.93 s | 13.2 M | 0.43 s | 7.1 M |
  | 94, each as above | 19.7 s | 260 M | 2.65 s | 38.5 M |

  What's left of the enumeration is its derived `Finite` (2.4 M of 3.0 M
  steps), still quadratic; of 94 three-field constructors, the per-
  constructor proofs (about 10 ms each for `equal`) and the `%at`
  projections, n branches each. Small types: `type Dir = | Up | Down |
  Left | Right` 4.9 → 4.1 ms, `| Wall | Open (n: Nat) | Door (key: Char)`
  14.5 → 11.4 ms, a five-constructor token type 32 → 13 ms; but two or
  three constructors that each have three fields, one a nested list, got
  slower, 24 → 41 ms and 37 → 64 ms (the new per-constructor proof costs
  more than the few pairs it saves; break-even near six constructors).
  Running: sorting 60,000 values of a five-constructor type and filtering
  with `==`, 0.79 s before and 0.81 s after (one run each, check included).
- **Guard.** `derived_instances_grow_linearly_with_constructors` (driver
  library tests) checks that 94 constructors take under 2.6 times 47's
  steps, and under 5 M steps for the one-field type.
- **Rejected or not done.** `Ordering.andThen (Nat.compare tags) (fields r
  s)`, as the note wrote it: a run is strict, so it would compare the
  fields of values of different constructors (a value with itself, by the
  default projections, for a recursive field). A `T.%rebuild` with default
  field values, as the note sketched: a field's type needn't be inhabited,
  so the projections that rebuild take the tag's equation instead. The
  enumeration's `Finite` and the small-type regression are left (findings).
  The benchmark and `bench:aoc` were not run in the lane (lane test
  budget); their step counts move with every derived instance.
- **Links.** SW-3370; [derived-equality.md](../proposals/derived-equality.md) §3, §5.6.

### SW-3337: fast text (T1): a text is a piece of a shared buffer; reading by position 20,000 times went from 21 s to nothing measurable

- **Status:** kept (Opus). Stage T1 of
  [file-io-and-text.md](../proposals/file-io-and-text.md#6-staging) (D3587).
- **Problem, from the design's probes and the source.** A text at run time
  was one `Rc<str>`, positions counted in characters, so every read by
  position walked from the start. `Text.get` had no native and ran its
  definition (`text.toList.get i`, building the whole list); `take`, `drop`
  and `uncons` walked and copied the rest; `length` counted. Each loop over
  a text by position was quadratic (the design's table, §1.2).
- **Change.** `Value::Text` holds `crate::text::Text`: an `Rc` of a buffer
  at one fixed width (ASCII bytes, two-byte or four-byte units: PEP 393's
  layout, the design's suggested start) plus a `u32` start and length, in
  characters, so a value is still three words. `get`, `take`, `drop`,
  `slice`, `uncons` and `length` are arithmetic on the two numbers. Every
  buffer is made at its narrowest width; ASCII buffers are borrowed as
  `str` for printing, `contains` and number parsing, and other texts are
  encoded for those (they were O(n) already). New natives: `Text.get`, and
  the new `Text.slice`, `getOr`, `getLt` and `concat`.
- **Why results stay the same.** Positions in the buffer are the positions
  of `Text.toList`, so each native is bounds arithmetic on its definition;
  equality and order compare characters (same-width pieces as slices,
  whose order is scalar order). `Text.repeat` is still charged a step per
  UTF-8 byte. Checked by the three tiers of §4.4: unit tests of every text
  of up to three awkward characters stored three ways (own buffer, piece of
  a two-byte and of a four-byte buffer) at every pair of positions;
  differential cases against the reference evaluator for the same texts
  through every operation, every pair compared and joined across widths,
  and random texts up to 1,600 characters cut by chains of slices (machine
  and native code); and a million characters read four ways on the machine.
  No proof, hash or existing definition changed (the pinned-hash and
  hash-stability tests; the prelude snapshot gained only new names).
- **Measured** (release CLI, one run each, load 4-9; `stitchwort run`
  includes about 0.30 s to check and start; text `"abcdefghij"` repeated,
  or with `→` for "wide"; the probe is the design's, Appendix A):

  | Loop, on a text of n characters | before | after, machine | after, `--native` |
  |---|---|---|---|
  | `text.get i` for every i, n = 20,000 | 21.2 s | 0.30 s | 0.31 s |
  | the same, n = 1,000,000 (ASCII / wide) | (quadratic) | 0.42 / 0.42 s | 0.35 / 0.36 s |
  | `drop i`, `take 5` at every i, n = 100,000 | 4.0 s | 0.31 s | 0.32 s |
  | the same, n = 1,000,000 | | 0.43 s | 0.38 s |
  | `length`, n times, n = 100,000 / 1,000,000 | 0.73 s / | 0.35 s (10^6) | 0.32 s (10^6) |
  | `uncons` until empty, n = 200,000 / 1,000,000 | 1.16 s / | 0.43 s (10^6) | 0.36 s (10^6) |

  Built executables, n = 1,000,000 (no start-up check): `get` 0.06 s
  native, 0.14 s machine; slices 0.06 s and 0.12 s.
- **The copy threshold.** A piece of at most 32 characters of a buffer of
  1,024 or more is copied, at its narrowest width, so a token doesn't keep
  a large source alive and cutting stays O(1) (the copy is bounded).
  Measured cost: 3,000,000 slices of 32 characters (copied) 0.60 s against
  33 (shared) 0.44 s, native: about 50 ns more a slice.
- **Rejected or not done.** UTF-8 with an ASCII flag and a lazily built
  index: less memory but a walk of up to the index's stride per read and
  more trusted code, on exactly the non-ASCII source a formatter reads.
  Four bytes a character always: simplest, four times the memory for ASCII.
  `Text.skipWhile`: not added; a lexer loop on `get` costs about 50-120 ns a
  character on these numbers, so one native call per character is cheap
  enough. In-place `++` is T2; JS natives T3 (`run --js` runs the new
  definitions). The benchmark and `bench:aoc` were not run in the lane
  (lane test budget): the step counts of programs that call `Text.get`
  drop, as `get` is one native step now.
- **Links.** SW-3337; [file-io-and-text.md](../proposals/file-io-and-text.md) §4.

## 14 Nov 2026

### SW-3280: strict marks and the checking builder (parser T1); the lossless tree 7-9% faster, 16 bytes more stack a level

- **Status:** kept (Opus). Stage T1 of
  [parser-end-state.md](../proposals/parser-end-state.md#8-stages)
  (D3600). A correctness change, not speed work: measured because the
  design estimated what it would cost in nesting depth and save in time.
- **Change.** Each parsing function keeps its start as a token index and
  records one mark when it finishes; operators no longer read their left
  operand's start back from the marks, and the `open` stack is gone. The
  tree's builder takes the marks in finishing order and nests them in two
  linear passes, with no sort (lifted from
  [parser-marks-or-nodes.md](../proposals/parser-marks-or-nodes.md#the-builder)),
  refusing marks that don't nest.
- **Why results stay the same.** `dev tree --print` over every tracked
  `.sw` file (2,994) is identical before and after except three files where
  the old tree lost a finished node (two recovered definitions' first arm,
  and attributes with nothing after them); over 11,976 broken copies of
  them, the only other difference is a pipe whose old start was a guess
  for an absent operand. Hashes are computed from the compiler's tree.
- **Measured** (release CLI, `dev tree --time`, `nice -n 15`, load 5-7;
  before is `main` at `8a30cd52c`; std best of 9, twice each, the rest
  best of 5):

  | | before | after |
  |---|---|---|
  | std, the lossless tree alone | 50.8, 50.9 ms | 47.7, 46.4 ms |
  | std, parse and lower | 75.2, 75.8 ms | 72.1, 69.5 ms |
  | std, `aoc/src`, `games`, `examples`: the lossless tree alone | 151.3 ms | 143.0 ms |
  | the same, parse and lower | 222.7 ms | 215.2 ms |

  About 4 ms off std, as SW-3276's prototype predicted (13.6 against about
  39 ns a node for the builder).
- **Stack** (deepest nesting `dev tree` parses, in the parser's 24 MiB, by
  bisection to 8 levels): `(((…)))`, `f (f (…))` and `(1 + (1 + …))`
  19,414 → 19,175 (1,296 → 1,312 bytes a level), lists 16,209 → 16,047,
  lambdas 16,552 → 16,381; an `else if` chain is not limited (past
  40,000) before or after. The design estimated up to 112 bytes a level
  (8%); keeping starts as values cost 16 (1.2%).
- **Not done.** The benchmark (its deep-input rows' allocation counts may
  move: the `open` stack's growth is gone, `logic_chain` still allocates
  two small vectors) is the verifier's to run.
- **Links.** SW-3280; [parser-end-state.md](../proposals/parser-end-state.md),
  [parser-marks-or-nodes.md](../proposals/parser-marks-or-nodes.md).

### SW-3180: stack frames left after SW-3172 (CLI dispatch, inferring applications, renaming)

- **Status:** kept (Opus lane). Robustness on deep input, not speed: the
  same checks, steps and hashes, with less native stack per level.
- **How measured.** Frame sizes from the release binary's arm64 prologues
  (saved registers, `sub sp`, and the probe loop's `sub x9, sp` for
  frames past a page). The deepest point of `check --no-cache
  Aoc.Year2021.Day06.Proofs` from a build with `STITCHWORT_STACK_PROBE`
  and a temporary patch that kept a backtrace at each new deepest
  position; that backtrace times the frame sizes says which frames make
  up the peak. All measured.
- **Changes and frames** (bytes, before → after):
  - The CLI's `run` 21,664 → 592: every command's function had been
    inlined into it. `check`'s own frame is now 10,560. Not a crash risk
    before: `Budget::start` takes the stack floor from where an operation
    starts, with a quarter of the 64 MiB thread in reserve, so frames
    above it never count against the guard.
  - `infer_value` 2,592 → 400 (+ `infer_call` 464), `infer_app_with` 1,168
    → 784, `fallback_inferred` 1,136 → 640: an inferred application's
    level, 4,896 → 2,288. The rarer arms are out of line.
  - `rename_other` 1,328 → 832 (binders through `rename_under`, 224);
    `rename_in` unchanged at 912.
  - `whole_test` returns before allocating its work list unless the
    expression is an `if`, `let`, `match` or brackets.
- **Day 6's peak** (whole thread, CLI frames included): 179,200 →
  171,120 bytes. The elaborator's frames along it: 173.7 → 165.6 KiB.
  The peak is checking with propagation (`check_value`, `Propagation::apply`,
  `apply_args_postponing`, about 0.8 KiB each, 16-19 levels) over eight
  levels of unification; renaming is 6 KiB of it.
- **Nesting thresholds** (`nesting::*`, levels before E-RESOURCE under
  the default guard), release before → after: long_appends 349 → 393,
  nested_functions_and_function_types 367 → 477; unchanged:
  nested_applications 296, nested_parentheses 404, long_sums 844,
  long_blocks 477, long_pattern_blocks 337. Debug: long_appends 23 → 39,
  nested_functions_and_function_types 31 → 67; the others unchanged (40,
  55, 60, 59, 30).
- **Tried and dropped.** `rename_call` out of line: `rename_in` 912 →
  704, but a call's argument then costs 336 more, so the call path, the
  one deep values take, got longer. `unify::run` out of line, to keep
  `run_tasks` out of `unify_shapes`: 1,104 → 1,088, no gain.
- **Not done.** `run_tasks` (848) and `unify_shapes` (1,104) are 22 KiB of
  Day 6's peak over eight levels; their frames hold what the rules by
  shape need, and shrinking them further would mean comparing spines in
  a loop (the ticket's note).
- **Links.** SW-3180, SW-3172, SW-3178, SW-3181.

### SW-3221: List.inRangeReads re-proved; every import of List checks ~840,000 fewer steps

- **Status:** kept (Sonnet investigation, orchestrator's call under D3447).
- **Problem.** stitchwort-bench on 14 Nov showed the seven `check-closed-*`
  rows at 2.09M steps against the 11 Nov baseline's 1.10M (time 99 → 259 ms
  under load). The programs are three lines; changing the list size from
  200,000 to 20 left the steps identical, so the cost was checking std's
  `List` declarations at `import Std (List, Nat)`, not evaluation.
- **Evidence.** Bisect over first-parent commits: 1.23M before the SW-3067
  merge (`c32a7f37c`), 2.07M after. Reverting SW-3067's std files one at a
  time isolated `List.inRangeReads` in `std/List/Toolkit.sw`, proved
  `{ forward = h => omega, backward = b => omega }`: about 860,000 steps.
- **Change.** The proof is `Bool.andReads (from <= x) (x < until)`.
- **Why results stay the same.** Same statement; only the proof term
  changed (the prelude hash snapshot's lines for `inRangeReads`,
  `inRangeReadsFalse` and its `%match1`).
- **Measured.** `check-closed-*`: 2.09M → about 1.25M steps (baseline
  1.10M). The remaining ~14% is std growth between 11 and 13 Nov, not
  chased; the baseline is to be re-recorded after L6 (SW-3213).
- **Follow-up.** SW-3223: a merge-time guard on std's import cost.
- **Links.** SW-3221, SW-3067.
### SW-3213: the parser builds only marks; parsing 1.30x the old parser's time, from 1.57x

- **Status:** done (Opus). Lane L6 of
  [syntax-tree-lowering.md](../proposals/syntax-tree-lowering.md#6-performance):
  step 4, the parser's direct construction of the compiler's tree deleted.
- **Problem.** Since L5 (below) every parse built the compiler's tree twice:
  once by the parser, thrown away, and once by the lowering.
- **Change.** The parser's functions return `Result<()>` (or a small value
  a caller needs, such as a definition's kind), and it records only marks.
  Its decisions that looked at a value just built now look at the marks and
  tokens (an absurd pattern, a block ending in a `let`, a `()` call after a
  name, a membership's operator). Checks on meaning moved to the lowering
  (a parameter named twice, an or-pattern that binds, an absurd arm with a
  condition). Messages that quote a construct's span as the compiler's tree
  has it lower that construct when the message is made
  (`Parser::lowered`). The oracle and `dev tree --lower` are gone.
- **Why results stay the same.** Before deleting anything, the oracle
  compared the two routes over 20,000 fuzz-generated programs (4 seeds):
  215,344 declarations and 48,648 expressions, 0 differences in modules,
  diagnostics or expressions. Then a fingerprint of every result (module,
  diagnostics, lossless tree, and each line parsed as an expression) over
  the repo's 2,983 files and those 20,000 programs, before and after: 15
  differ. 14 differ only in the lossless tree: a declaration whose error is
  now the lowering's is a whole `Def` node, not an `Error` one. One fuzz
  program (an import after a declaration with a meaning error) now also
  reports "imports go at the top of the file", which is true of it. The
  hash and reject snapshots are unchanged.
- **Measured** (release CLI, `dev tree --time 5`, best of 5, `nice -n 15`,
  load average 3-5; two runs agreed within 0.3 ms):

  | | the old parser alone (before L5) | L5, through the lowering | L6, through the lowering | L6, the lossless tree alone |
  |---|---|---|---|---|
  | std, 2.12 MB | 53.2 ms | 83.5 ms (1.57x) | 69.0 ms (1.30x) | 46.4 ms |
  | std, `aoc/src`, `games`, `examples`, 6.88 MB | 161.2 ms | 251.6 ms (1.56x) | 209.9 ms (1.30x) | 142.2 ms |

  The design estimated 1.1-1.3x for the end state. Building the lossless
  tree now costs less than the old parser alone did (46.4 against
  53.2 ms); the lowering is the rest.
- **Bench** (stitchwort-bench on `main` after this merge, against the
  11 Nov baseline). The deep-input rows did not come back down:
  check-nested-parens (12,000 nested brackets) allocations 136 → 220
  (L5: 225), peak heap 2.0 → 5.3 MB (L5: 5.3); check-nested-apps peak heap
  1.2 → 1.9 MB; check-number-huge and check-number-pattern peak heap
  5 → 6 kB, check-text-literal allocations 155 → 178, text-literal-walk
  peak heap +30% of 3 kB. Holding both the lossless tree and the
  compiler's tree is inherent to the design, and on these pathological
  inputs it dominates. Accepted (orchestrator's call: speed work is paused,
  D3465; parse time is within the estimate); the baseline is re-recorded
  (counts only). check-long-sum and check-nested-apps steps fell 23%.
  The check-closed-* rows' +14% steps is std growth (SW-3221's entry).
- **Stack.** Without trees in its frames the parser nests about three
  times as deeply as before in the same stack, deeper than the lowering
  can follow for some shapes (at the parser's deepest, `(.f (.f …))` needed
  1.2 times the stack to lower in release, 1.55 in debug). The parser now
  takes half the stack and the lowering all of it
  (`parser::parser_limit`), so what parses lowers: the release CLI parses
  18,000 nested brackets (12,740 in October), and 2,000 nested `f (`
  check.

### SW-3212: parsing goes through the lowering, 1.57x slower until L6 (accepted regression)

- **Status:** accepted, temporary regression (Opus). Step 3's switch, lane
  L5 of [syntax-tree-lowering.md](../proposals/syntax-tree-lowering.md#6-performance).
- **Problem.** The compiler's tree is now built from the lossless tree by the
  lowering (`crates/syntax/src/lower/`), but until L6 removes the parser's
  direct construction, every public parse function (`parse_module*`,
  `parse_expression*`, `parse_module_and_tree`, `parse_namespace_line`)
  does three jobs: the parser builds the compiler's tree (thrown away) and
  the marks, the tree builder builds the lossless tree (with trivia), and
  the lowering builds the compiler's tree again.
- **Why results stay the same.** The two routes are compared exactly, as
  `Debug` text with spans plus the diagnostics, by `stitchwort dev tree
  --lower` (`lower::oracle`; both removed in L6, SW-3213, below): over all 2,983 `.sw` files in the repo,
  30,713 declarations and 34,376 one-line bodies and types parsed as
  expressions, 0 differences and 0 not lowered. The hash snapshots (`binary(library) &
  test(/hash_stability/)`) are unchanged.
- **Measured** (release CLI, `dev tree --time 5`, best of 5, `nice -n 15`,
  load average 3-4; two runs agreed within 0.1 ms):

  | | the parser alone (before) | with the lossless tree | through the lowering (after) |
  |---|---|---|---|
  | std, 2.12 MB | 54.1 ms | 63.4 ms | 85.0 ms (1.57x) |
  | std, `aoc/src`, `games`, `examples`, 6.88 MB | 163.9 ms | 191.4 ms | 256.3 ms (1.56x) |

  The design estimated 1.3-1.5x; the lowering itself is about 21 ms of
  std's 85. A `check` that loads std parses it once (`library.rs`), so a
  trivial check is about 30 ms slower [estimated from the table].
- **Bench** (on `main` after this merge, against the 11 Nov baseline):
  check-nested-parens allocations 136 → 225 (+65%), peak heap 2.0 →
  5.3 MB; check-nested-apps peak heap 1.2 → 1.9 MB; smaller rises on
  check-number-huge, check-number-pattern, check-text-literal and
  text-literal-walk. (The check-closed-* rows' doubled steps in the same
  run were SW-3067's std proof, not this change: see SW-3221.) For what
  L6 left, see its entry.
- **Not optimised.** Speed work is paused (D3465) and most of the cost goes
  with L6, which deletes the parser's own construction (end state about
  1.1-1.3x, [estimated] in the design). If trivia proves a noticeable part
  then, the compiler's route can build the tree without comments.
- **Stack.** The lowering takes the parser's stack limit and reports its
  `E-RESOURCE` if it runs out. Its frames per level of nesting are 5-43% of
  the parser's in release (measured per shape, `(` to `(.f `), after making
  the application and method-section path out of line and marking
  `function_type` and `effect` `#[inline(never)]`: inlined into
  `node_expr`, they had grown it from 96 to 816 bytes, so nested sections
  ran out before the parser did. The test
  `deep_nesting_lowers_within_the_parsers_stack` lowers each shape's
  deepest parse with a third of the stack to spare.

## 10 Nov 2026

### SW-2609: `ignorable_arguments` profiled in real proofs: not a hotspot (no change)

- **Problem.** SW-2606's profile of a soundness-fuzzer mutant (a bare
  `cases` in place of a proof, 64 contexts with huge hypotheses) found
  `ignorable_arguments` (`crates/elab/src/check.rs`), which reads back the goal
  and every hypothesis type at each `auto` argument, taking most of the CPU.
  The question was whether it costs anything in unmutated proofs.
- **Method** (measured). Release build (non-incremental), `stitchwort check
  --no-cache` of eight AoC proof namespaces picked by how often they use
  `cases` (Day16 `Sound.sw` most), sampled with macOS `sample` at 1 ms;
  inclusive samples of the checking thread, outermost frame only.
- **Result.** `ignorable_arguments` is 0.2% to 1.9% of the checking thread:
  Aoc.Year2021.Day16.Proofs 69 of 7,329 samples (0.9%, 12.2 s wall),
  Aoc.Common.Proofs 67 / 4,161 (1.6%, 5.7 s), Aoc.Year2021.Day05.Proofs
  77 / 4,125 (1.9%, 5.3 s), Aoc.Year2024.Day04.Proofs 7 / 3,372 (0.2%,
  4.3 s), Aoc.Year2024.Day24.Proofs 68 / 5,046 (1.3%), Aoc.Year2024.Day06.Proofs
  67 / 4,708 (1.4%), Aoc.Year2024.Day15.Proofs 84 / 5,441 (1.5%),
  Aoc.Year2021.Day18.Proofs 11 / 1,373 (0.8%). `cases` itself (all of
  `elab::cases`) is under 1% except Day04 (329, 10%). Most of the calls come
  from ordinary implicit `auto` arguments, not from `cases`.
- **Decision.** Not changed: at most about 2% to win, and the mutant case it
  was found in is already stopped by SW-2606's `E-CASES-BUDGET`. If it is
  ever worth doing, the cheap form is to cache the hypotheses' mention marks
  per context, reused while `cx.types` is unchanged (a case split refines
  earlier types, so the key must be the types, not the level), so each
  argument reads back only the goal.
### SW-2607: native compile time of nested `if`s is linear in instructions; no change (dropped)

- **Status:** measured, no code change. Sonnet.
- **Question.** SW-2579 found nested `if`s making the IR's value count grow
  faster than linearly (2.8k values at 1 `if`, 44k at 12, 77k at 20) and
  guessed that every register was carried into every join. Is native
  compile time a cost, and would passing only live registers to joins cut it?
- **Measured** (release CLI, `build --native --verbose`, Mac, the "compiled
  ... in N ms" figure; the programs are SW-2579's `nested_ifs`):

  | nesting | 1 | 4 | 8 | 12 | 16 | 20 | 24 |
  |---|---|---|---|---|---|---|---|
  | native compile, ms | 12.5 | 20.7 | 40.2 | 66.0 | 54.6 | 67.9 | 85.2 |

  Past about 12 levels a body is compiled in parts (SW-2557), so the time
  stops climbing steeply. At depth 20 it is 68 ms, under the 100 ms bar.
- **Real programs.** AoC 2024 day 15: 322 bodies, 477 ms of native
  compile of a 1.18 s `build --native`; day 24: 332 bodies, 465 ms; 2024
  day 21: 246 ms; 2021 day 18: 250 ms. So native compile is a visible share
  of a build, but it is not the nested `if`s. With a temporary timer around
  `define_function`: Cranelift's `define_function` is 89% of it (426 ms of
  477), at about 2 us an instruction in the real days (215,000 instructions)
  and in the depth-12 and depth-20 programs alike. Block parameters are
  27,000 of day 15's 315,000 values (9%); the depth-12 body has 5,766 of
  104,775. The rest of the value count is not live data: Cranelift's SSA
  builder creates a parameter for every variable at every join, then removes
  the redundant ones, leaving the value as an alias in the table. So the
  growth in values is dead entries, not extra work for the compiler:
  time follows instructions and blocks, which grow linearly with nesting.
- **Why no change.** Passing only live registers would remove at most the
  9% of values that are block parameters, and the redundant ones are already
  removed by the builder; no measurable gain on compile time, and it would
  touch every join in the lowering. Dropped. Any compile-time gain in real
  programs lies in the instruction count per body (the largest bodies,
  `lambda #34` of day 15 at 13,000 values and 17 ms, and `Warehouse.move`'s
  match), not in the joins.

### SW-2578: bench baseline re-recorded after 9 Nov's runtime work (four flagged regressions explained, accepted)

- **Problem.** The daily and full tiers flagged `run-machine-calls`
  allocations 247 to 441, `run-machine-loop` allocations 205 to 332 and
  peak heap 4 to 5 kB, `run-machine-aoc-2021-15-part1` peak heap 5.1 to 10.3
  MB, and `check-number-columns` steps 669,003 to 755,301 (+12.9%), while
  gains of up to -77% machine instructions weren't in the baseline. No code
  changed: the baseline was re-recorded (`--update`, release build, 10 Nov;
  `examples` and `extract-js` inputs changed too, 1498 to 1542 files and 56
  to 57).
- **Method** (measured). Bench of the two `run-machine` programs at chosen
  commits, in a scratch worktree, release build, counts only; the same for
  `check-number-columns` and `run-machine-aoc-2021-15`. Counts are
  deterministic, so one run each is exact.
- **`run-machine-calls`/`-loop` allocations: borrow inference (SW-2565 B1,
  `e687be8bf`), a per-run constant.** Calls 276 to 441 (+165), loop 214 to
  332 (+118) at that commit alone; nothing else moved by more than a few
  allocations. The benchmarks' counted region is `run_main_on`, which builds
  the image, and B1's `borrow::apply` (inference over every reachable body,
  a state vector and a pending map per body per pass, then the rewrite and
  check) now runs in it. The cost grows with the number of bodies in the
  image, not with iterations: the programs run 200,000 outer calls and 4
  million tail calls, and a total of 441 or 332 allocations can't scale with
  either.
  The few smaller steps before it are also constants: calls 247 to 255
  (8 Nov, before `3de6c1834`), +19 with SW-2405's sum loops (`96bf4836a`:
  the program's `1 + down n` becomes a loop, so machine instructions fell
  12.6% and peak heap 10 to 6 kB in the same step), +2 with SW-2531's inlining
  (`748dc58a3`). Loop 205 to 212 is also before 9 Nov. Not removed: 100 to
  170 allocations once per run is under 0.001% of a typical run's
  allocations (AoC days: 1 to 10 million) and well under a
  millisecond, and trimming them means restructuring B1's analysis (reusing
  `forward`'s buffers across passes) for no measurable gain. Accepted.
- **`run-machine-loop` peak heap 3.8 to 5.2 kB.** The inference's working
  set (the same constant, at its peak), nothing a run keeps. Accepted.
- **`run-machine-aoc-2021-15-part1` peak heap 5.1 to 10.3 MB: SW-2396
  (`3496aee5f`), intended.** `Graph.distances (index := ...)` keeps the
  costs in arrays: 5.3 to 9.6 MB at that merge, with allocations -44% and
  machine instructions -71% (54.0 M to 22.5 M). The cell cache (SW-2363) was
  the suspect and is not the cause: with `cell_cache::ENABLED` false the
  peak is unchanged at 10.3 MB. Accepted: a dense table is the point of
  the change.
- **`check-number-columns` steps 669,003 to 755,301: SW-2481 (merge
  `11ed0d905`), intended.** Case refinement now rebuilds substituted values
  keeping sharing and charges the steps for the rebuild. The lane's first
  version ran 959,829 steps and 1,575,835 allocations here; its review fixes
  (`e8fbef207`: keep unchanged calls, share spines, charge steps) cut that
  to 755,301 steps and 1,170,115 allocations (allocations +1.0% against the
  old baseline). The rest is the charge, which is the budget doing its job
  (a 256-arm Fin table went 86 s to 12 s, and a 200-arm unknown bound from
  out of memory to 15 s). `check-number-dependent` rose 6.6% in the same
  merge, under the threshold. Accepted.
- **Baseline changes** (new / old): `run-machine-calls` allocations 441 /
  247, peak 7 kB / 10 kB, instructions 26.8 M / 30.2 M; `run-machine-loop`
  allocations 332 / 205, peak 5 kB / 4 kB; `run-machine-set` allocations
  213,575 / 1,719,446 (-87.6%), instructions -12.3%; `aoc-2020-19`
  allocations -47.8%, instructions -20.6%; `aoc-2021-11` allocations
  -67.1%, instructions 173.4 M / 567.2 M (-69.4%); `aoc-2024-09`
  allocations -64.0%, instructions -23.1%; `aoc-2021-15-part1`
  allocations 1.30 M / 4.38 M (-70.3%), instructions 17.8 M / 78.7 M
  (-77.3%), peak 10.3 / 5.1 MB; `check-number-columns` steps as above; the
  new `examples` and `extract-js` fingerprints. Times (`time_ms`) in this
  file were recorded while other lanes were running tests, so they are
  rougher than usual (they are only compared by hand); re-record on a quiet
  machine when timing matters.

### SW-2572: `*` on a long run of `Succ`s around an unknown is linear, not quadratic

- **Cause** (profiled with macOS `sample` on the effect fuzzer's seed
  1794200310, the program shrunk by hand). All the time was in the
  elaborator's obligations loop evaluating `if v % 2 == 0`, inside
  `native::as_nat_with` forcing calls that were already unfolded
  (`force_now`, `Unfolding::get`, `Value::clone`). `(x + k) % 2` is
  `(x + k) - ((x + k) / 2) * 2`; the quotient is `k / 2` `Succ`s around a
  stuck division step, and `*` recurses on its left side one `Succ` at a
  time. At each step `native::run` walked the rest of the chain to see
  whether it was a number before falling back to the case tree: quadratic
  in `k`. The fuzzer's constants are near a million.
- **Change** (`crates/core/src/native.rs`; the evaluators' shared natives, so
  the kernel computes this way too; docs/core.md updated). (1) `Nat.mul`'s
  shortcut for unknowns: `(k + m) * n` for a number `n` is
  `k·n + m * n` in one step, stuck on `m`, which is what `k` steps of the
  definition give. (2) `native::run` forces every number argument's head
  first and stops when one is plainly no number, before walking a `Succ`
  chain in another, so `(k + m) * y` with `y` unknown doesn't walk the chain
  at each of the case tree's steps. Equal values are unchanged; a value
  stuck under `*` keeps its argument unforced, as the case tree does.
- **Measured** (release `stitchwort check --no-cache`, user time, machine
  shared with other lanes). `if (x + 16000) % 2 == 0 …` 10.1 s to 0.46 s;
  `((x + 16000) / 2) * 2` 11.6 s to 0.47 s; `((x + 16000) / 2) * y` 9.2 s
  to 0.56 s; the fuzzer's `let a := if (x + 16000) % 2 == 0 then 4 else 4;
  if a % 2 == 0 …` 16.9 s to 0.70 s. Seed 1794200310's module: over 10 min
  (its slow program alone over 20 s, stopped) to 4.3 s; seeds 1794200346,
  1794201674, 1794200163 and 43: 1.0 to 1.5 s each. The fuzzer's 200
  batches from 1794200000 (three of the slow seeds among them): 51 s, none
  out of resources. What's left grows
  linearly, about 13 µs a unit of `k` (`(x + 500000) % 2` forced fully
  takes 7 s): `Nat.divFuel` builds the quotient one `Succ` a step, as its
  definition does (see "Not done").
- **Not done.** A `Nat.divFuel` shortcut for unknowns (take `d` off `n`
  `q` times at once) would remove the linear part; it would be a new kernel
  shortcut with its own proof obligations, so it's proposed as a follow-up,
  not done here.
### SW-2579: native frame bounds from Cranelift's frame layout (x86-64 frames of 4 KB were put at 2 MB)

- **Status:** on branch `lane/SW-2579`. Opus.
- **Problem.** On Overmind (x86-64), five effect-fuzz batches were refused
  by native code: a lambda of about 20 nested `if`s had a "frame" of
  1.1-2.2 MB, and 2,000,000 frames of that pass the 64 GiB cap. Under
  `run --native` the same bound would not refuse but cut the frame limit
  to 30,000-57,000 frames (`native_frame_limit`).
- **Cause.** Not the frames: the measurement. `frames::frame_bound` read
  the frame from the prologue, and on x86-64 a frame of a page or more
  starts with stack probes, which the reader didn't know, so it took the
  IR fallback (stack slots plus 16 bytes for every SSA value). Nested
  `if`s make many values (each bytecode register is three variables, and
  each join block takes them as parameters: 77,000 values at 20 ifs), so
  the fallback grew with values while the real frame grew by about 160
  bytes an `if`. On aarch64 the reader used the unwind pseudo-instructions
  and was right, so the Mac never saw it.
- **Change.** The bound is Cranelift's own frame layout,
  `MachBufferFinalized::frame_layout().frame_to_fp_offset` plus the saved
  frame pointer and return address, on both architectures; the prologue
  readers are gone. The generated code is unchanged. On aarch64 the bound
  is the same except where a tail call to a wider callee grew the frame:
  the reader counted that growth twice (in `StackAlloc` and in the
  arguments term), so stubs' bounds drop by up to 48 bytes.
- **Measured** (widest body's bound in bytes; x86-64 compiled from the same
  IR by a cross-compiling ISA on the Mac; "before" on aarch64 equals after):

  | program | x86-64 before | x86-64 after | aarch64 |
  |---|---|---|---|
  | 1 nested if | 752 | 752 | 752 |
  | 4 | 944 | 944 | 944 |
  | 8 | 1,136 | 1,136 | 1,152 |
  | 12 | 1,328 | 1,328 | 1,344 |
  | 16 | 2,880 | 2,880 | 2,640 |
  | 20 | 3,520 | 3,520 | 3,136 |
  | 24 (heavier branches, the regression test) | 1,802,480 | 4,672 | 4,112 |
  | 28 (heavier) | 2,376,672 | 5,424 | 5,024 |
  | fuzz seed 1794200320 | 1,331,136 | 4,192 | 3,712 |
  | fuzz seed 1794201291 | 1,731,904 | 4,176 | 3,952 |
  | fuzz seed 1794201473 | 1,187,616 | 4,672 | 4,288 |
  | fuzz seed 1794300165 | 2,198,864 | 4,208 | 3,872 |
  | fuzz seed 1794301295 | 2,092,160 | 6,080 | 4,928 |

  The real frame grows linearly with nesting; past about 40 `if`s a body
  is compiled in parts (SW-2557) and the frame falls to about 1 KB.
  `task native:bench` (macOS, load average 12-18, best of 3, wall):
  set_nat 1.216 s, set_keys 0.310, micro_call 0.242, micro_tail 0.262,
  closures 0.336, effects 0.884; geomean 0.438 s. No earlier entry has
  these numbers to compare with; the code is the same, so no change is
  expected **[estimated]**.
- **Fuzzer.** A native refusal stays a failure, not a skip: generated
  programs' frames are a few KB, far from the 34 KB at which 2,000,000
  frames would pass the cap, so a refusal is a bug in native code, as
  here.

## 9 Nov 2026

### SW-2559: the cell cache's room is exact, so `full` doesn't walk

- **Cause.** `CellCache::full` recounted the held bytes by walking every
  cached block (a pointer chase over up to 64 MB) whenever the room ran
  out, because a take didn't give room back. Overmind (Linux, job 41):
  15% of cycles in binary-trees, 4.4% in rbmap after SW-2511 (LLC load
  misses 0.55 M to 3.8 M).
- **Change.** Native code's cache take adds the block's bytes back to
  `room` (load, add, store on the take's hit path, `n1.rs` `cached_cell`),
  so `room` is exactly `CAP` less the bytes cached. A full cache is then
  just a failed comparison: `full` frees the cell and walks nothing; the
  cut to half the cap is gone.
- **Measured (macOS, instructions, median of 3).** binary-trees +0.34%,
  rbmap +0.25%, rbmap-ck +0.21%, memory-game +0.31%, mapops -0.01%
  (the extra take work; no walk to save on this machine's runs). Wall
  time, best of 10, machine loaded by other lanes (so noisy, +-10%):
  binary-trees 1.37 s to 1.19 s, rbmap 1.54 to 1.35, rbmap-ck 0.86 to 0.82,
  memory-game 1.88 to 1.95, mapops 0.87 to 1.01. The time effect is the
  cache misses, which Overmind's counters should confirm.
- **Rejected.** (b) per-arity counts or a bound: still a walk or more
  state on the free path, for no gain over an exact count. (c) cutting
  lists at a counted point: needs the same walk to find the point, and
  throws away blocks the program will want again. Keeping the recount but
  rarer (cutting deeper) was not tried: the exact count removes the cause.
### SW-2565: borrowed parameters, stage B1 (mapops -6.4%, memory-game -19.3%, AoC geomean -2.3%)

- **Status:** on branch `lane/SW-2565`. Opus. D3441 (build it), D3442 (the machine checks
  borrows), D3443 (step and frame counts unchanged); O6 dropped (orchestrator's call from B0).
- **Problem.** A read-only walk over a structure the program keeps (a `Map` lookup, a list
  summed twice) incremented and decremented every node it passed: the caller's copy of the
  argument, then each field taken from a shared cell.
- **Change.** An inference over each global's bytecode (`crates/rt/src/borrow.rs`) marks the
  parameters a function only reads as borrowed; callers lend them (no count), and a rewrite
  makes each lent value's life explicit (`Peek`, `Lend`, `Forget`, `Own`), checked at compile
  time. Native code copies lent words with no counting; the machine keeps checked, untraced
  clones. Details and rules: docs/proposals/borrow-inference.md §12.
- **Measured** (`task bench:instructions --runs 3` against main at fdde41179, after the review's
  fixes and the rebase onto SW-2559): mapops -6.40%, memory-game -19.31%, expressions -3.10%,
  disk -2.42%, rbmap-ck -2.13%, dijkstra -1.49%, rbmap -0.26%, binary-trees +0.01%; geomean
  -4.59%. `task bench:aoc`: geomean -2.32% over 56 days, 11 days over 3% (2021/17 -11.7%,
  2024/06 -11.3%, 2020/08 -5.0%), none worse (worst 2021/07 -0.05%). Before the rebase, against
  d5bd2f09d: geomean -3.77%, AoC -0.96%, 2021/01 +1.16%. Peak memory unchanged on all eight
  programs (within 0.1 MB, measured before the rebase).
- **Rejected along the way** (measured, one run each; geomean of the eight):
  - The note's rules plus *merge*, without *fresh*: binary-trees +83% (its fresh tree, lent,
    was dropped whole by the runtime instead of freed into the cell cache as walked); +4.49%.
  - Plus *fresh*, with O1-O3 owning as written: expressions +1.30%; -3.52%.
  - O1-O3 owning only when some caller hands over an owned value at its last use: expressions
    +1.27%; -3.58%.
  - Any owned value handed over at its last use owning the parameter: mapops only -1.75% (the
    lookup walk's node, a field of a live tree, counted as handed over); -3.11%.
  - Fields of a fresh value counted as fresh through `Unpack`: rbmap-ck +1.65%, expressions
    +1.42%; -3.18%.
  - Kept: the last but one, except that a copy or a field of a value that stays live doesn't
    count as handed over (*fed*); -3.77% (3 runs, before the rebase).
- **Not done.** B2 (owned copies for O7/O8), B3 (lent reads of owned values), the JS backend.

### SW-2471: native recursion limit 16 million frames (const-fold depth 23 runs)

- **Status:** on branch `lane/SW-2471`. Sonnet. D3450 (Matt, 9 Nov 2026: limits may differ by
  runner).
- **Problem.** The frame limit was a fixed 2,000,000, shared by the machine and native code, so
  `bench/compare/const-fold` stopped with `E-RESOURCE` at depth 21 where Lean's original runs
  depth 23 on a 4 GB stack, and ran at depth 20 in the comparison.
- **Change.** Native code has its own ceiling, `Limits::native_frames` (16,000,000), and a run
  enforces `min(ceiling, (64 GiB cap - rooms) / widest frame - 1)`
  (`native_abi::native_frame_limit`, `Limits::for_native`). The machine keeps 2,000,000. The
  native stack was already mapped lazily, and the limit is a runtime value the frame check
  compares against, so the generated code is unchanged. A program with wide frames is no longer
  refused: it gets the most frames the cap holds. The same program on the same build still fails
  at the same depth.
- **Measured** (release CLI, `run --native`, one run each; time wall, memory peak resident set):

  | const-fold depth | time | peak memory |
  |---|---|---|
  | 21 | 0.86 s | 1.08 GB |
  | 22 | 1.54 s | 2.06 GB |
  | 23 | 2.87 s | 4.00 GB |

  Runaway recursion (`count n = 2 * count (n - 1)` from 20,000,000, 380-byte frames): native
  fails with `E-RESOURCE` at 15,999,999 frames pending after 1.4 s with a 6.1 GB peak; the
  machine fails at 2,000,000 after 0.3 s with 0.58 GB. Instructions are unchanged **[estimated]**
  (the earlier experiment, a patch with the same limit, measured no instruction cost; this
  change did not re-measure instructions).
- **Cost.** A runaway native recursion now uses up to about 8 times the memory before failing
  (6 GB here; a program with wide frames can use more, up to the 64 GiB address space the
  limit allows, and the machine's memory then decides). The roguelike's widest frame is 4,776
  bytes, so its limit is 14.4 million.
- **Rejected.** A byte cap beside the frame limit (the earlier lane's option): not built; the
  frame counter stays exact and deterministic, and SW-2558 adds a flag to lower the ceiling.

### SW-2543: `stitchwort test --native` (tests as native code; 2021 day 15's tests 3.7x faster)

- **Status:** on branch `lane/SW-2543`, behind a flag (`test --native`); the default flips in
  N6 (docs/reviews/SW-2535-native-default-plan.md). Opus.
- **Problem.** `stitchwort test` ran every test on the machine. Native code runs AoC days 2-3x
  faster, but `test` had no native path.
- **Change.** The tests lowered together are compiled once, with each test constant a root
  (`n1::compile_roots`, an entry trampoline per root), and each test's value is computed by
  `NativeExecutor::global` as the machine's `Machine::global` computes it. A test native code
  can't run goes to the machine. Results are cached under native code's own key (not the
  machine's): its recursion limit is deeper (SW-2471), so outcomes at the limit differ.
- **Measured** (release CLI with `dev` features, best of 3 by instructions; `test X
  --verify-cache`, which reruns every test with the check cache warm, less a fully cached `test
  X`; load average 4-10):

  | Tests | Machine: instructions, wall | Native: instructions, wall | Compile (in native) |
  |---|---:|---:|---:|
  | AoC 2021 day 15 (18 tests, real input) | 85.9 G, 5.89 s | 22.3 G, 1.61 s | 259 bodies, 0.43 s |
  | AoC 2024 day 9 (32 tests, real input) | 14.1 G, 1.00 s | 8.4 G, 0.68 s | 321 bodies, 0.48 s |
  | AoC 2020 day 21 (10 tests, real input) | 10.7 G, 0.70 s | 6.6 G, 0.48 s | |
  | `examples/accept/text.sw` (58 small tests) | under 0.01 G, under 0.01 s | 0.44 G, 0.04 s | 69 bodies, 0.035 s |

  So 3.7x on a day whose tests compute a lot, about 1.5x on a typical day, where compiling is
  most of what native code spends, and 30-40 ms more on a file of small tests (the whole
  command: 2.36 G, 0.23 s -> 2.80 G, 0.27 s). Uncached (`--no-cache`, checking included) 2021 day 15 went from
  12.6-13.2 s to 8.0-8.7 s, and 2024 day 9 from 5.6-5.8 s to 5.3-5.5 s.
- **Not done.** No threshold below which small test files stay on the machine (§3.6 of the
  plan): 30-40 ms didn't seem worth a rule. Compile time is now the larger part for a typical
  day (lane J of the plan).
- **Links.** SW-2543, SW-2535.

### SW-2557: native compile time and memory on very large bodies

- **Status:** on `lane/SW-2557`, for review. Opus.
- **Problem.** `run --native` on float_paths' generated program (484 KB, one constant
  `results` that is a 20,161-element list literal) ran over 100 s and reached 17.9 GB before
  it was stopped; the machine runs it in 1.9 s at 260 MB.
- **Profile** (macOS `sample`, measured). At 250 elements: 10 s and 1.9 GB, three quarters of
  it in Cranelift's `seal_all_blocks` (`remove_block_param`), the rest in `define_function`.
  The body's Cranelift IR grew with the square of the list: 60 K, 224 K, 850 K lines at 25, 50,
  100 elements. Cause: `Gen::exit_now_untagged` (`crates/native/src/n1.rs`) writes every
  register that may hold a value to the spill slot at each error exit, and a call has three
  (`count_step`, `push_frame`, `call_result`); a list literal holds every element in its own
  register until the list is built, so each element's call wrote out all the elements before
  it, and each such use of a register variable made the SSA builder thread it through every
  block. The frame grew with the registers too (75 KB at 250 elements, over the 64 GiB stack
  cap at the 2 M frame limit). `maybe_full` would also have needed registers times
  instructions bits (about 0.7 GB at full size).
- **Change.** A body with more than 128 registers or 512 instructions keeps its registers in
  a heap register file laid out as the machine's register vector (`sw_regs_new`); an exit
  hands the whole file to `sw_unwind` and a release drops it whole (`sw_release_down`), the
  registers holding nothing being `Erased`. That alone made the IR linear but Cranelift's
  register allocator still grew faster than the function (5,000 elements: 14.5 s, 2.5 GB),
  so such a body is also compiled in parts of at most 512 instructions, each a function that
  tail-calls the next with the frame's state. Then, within such a body, exits holding nothing
  outside the registers are shared per error (5.2 s to 3.5 s at 5,000 elements) and a write
  skips dropping the old value when no earlier instruction fills the register (`first_fills`;
  IR 230 K to 170 K lines at 500 elements, little time). Part sizes of 128 and 512 measured
  the same (2.74 s, 2.80 s at 5,000 elements); 2,048 took 4.8 s.
- **Measured** (wall time and peak RSS of `run --native --no-cache`, one run each, a shared
  machine; before stopped at 6 GB):

  | program | before | after |
  |---|---|---|
  | float paths, 250 elements | 16.4 s, 1.9 GB, refused (stack over the cap) | 2.4 s, 142 MB (compile 0.40 s) |
  | 2,000 elements | stopped at 6 GB after 7.4 s | 3.4 s, 178 MB (compile 1.2 s) |
  | 20,161 elements (the repro) | stopped at 6 GB after 5.4 s | 13.7 s, 316 MB (compile 11.5 s) |

  Compile time is now linear: about 0.55 ms per element. Of what is left, Cranelift's
  register allocator is about half and its IR verifier about a quarter.
- **Normal programs unchanged.** No body of dijkstra (2021 day 15, 196 bodies) or Rogue (259)
  passes either bound (the largest have 41 registers and 168 instructions), and their machine
  code is byte for byte the same before and after (`STITCHWORT_NATIVE_DUMP`); compile times
  (0.33-0.37 s and 0.45-0.48 s before) were within the machine's noise after.
- **Links.** SW-2557; test `crates/native/tests/it/large.rs` (fails on the old code: 109 s, then
  the frame check).

### SW-2524: skipping the live heap's free at exit (dropped: under 0.3%)

- **Status:** dropped, no code merged. Sonnet.
- **Problem.** About 32-38% of `rbmap-ck`'s cycles are in `value::free` (SW-2523). The suspicion
  was that much of it tears down the heap that is still live when the process ends, which Lean
  doesn't do.
- **Change tried.** A process-wide switch (`leak_live_heap_at_exit`, set by the standalone
  executable's `main` and by `run --native`, never by the tests or the `alloc-trace` and
  `value-census` builds, and overridden by `STITCHWORT_FREE_AT_EXIT`) that `run_on` consults to
  `forget` the runner, and with it the executor's globals, constants, cell cache and tables,
  instead of dropping them. The same binary then runs both ways, so the exit share is the
  difference between the two.
- **Measured** (instructions, 3 runs, native; freeing at exit against skipping it):
  `rbmap-ck` 10.48 G -> 10.45 G (**-0.21%**), `rbmap` -0.08%, `binary-trees` -0.01%, `mapops`
  +0.03% (noise), `const-fold` -0.25%; AoC 2024/05 -0.02%, 2024/10 -0.07%. Wall time and peak
  RSS for `rbmap-ck` (1.82 s, 1.26 GB) and `binary-trees` (1.38 s) were identical to the
  hundredth of a second with the switch on or off. All under the 3% bar.
- **Why it is small** (inferred, not separately measured). What `main` returns is a unit and its locals, including `rbmap-ck`'s
  kept versions, die when `main`'s own native frame ends: those frees run inside the program, so
  they are not teardown and Lean's `main` would do them too. What is left to drop afterwards
  (globals, constants, the cell cache, the closure tables) is small.
- **Therefore** the `value::free` share in `rbmap-ck` is the program's own frees (SW-2523's cold
  child loads), not exit teardown. Skipping it would need a different change: freeing the kept
  versions would have to be dropped from the program's end of `main` itself, which is a trick that
  doesn't generalise (a program's locals dying at `main`'s end is ordinary semantics).
- **Links.** SW-2524, SW-2523; no commits kept beyond this entry.

### SW-2511: a handler's step is one dispatch closure (compiled handler dispatch, stage 1)

- **Status:** on branch `lane/SW-2511`, not yet merged (commits `52da722ff`, the dispatch, on the
  cherry-picked SW-2507 spike `10aa4bf6d`; `200f2d6d9`, the `Unpack` change). Opus.
- **Problem.** Every operation a handler answered went through two partial applications
  (`handlePlus (A.%elim c₁ … cₙ) forward`); applying one copies everything it holds, so each
  operation copied all the clauses and dropped all but one, and a fused state clause was then
  partially applied once more. Profile (SW-2493, `tick`): about a third of an operation's 5.7 K
  instructions, plus 0.47 K more for an eight-operation ability. Each handler start built a
  closure per clause and the two partial applications.
- **Change.** `crates/rt/src/dispatch.rs`: in the runtime's lowering, the step becomes one closure
  of `o, k` (and `jump, s` for a fused state handler) whose body is `handlePlus`'s and `%elim`'s
  case trees with the clauses inlined in the arms; the forward, whatever its variant, is inlined in
  the `R` arm. Named `Owner/dispatchN` in profiles.
  Second commit: an `Unpack` names the fields its arm doesn't use, so native code frees a unique
  cell inline into the cell cache instead of out of line; the dispatch had exposed this (a clause's
  unused argument), and any `match` arm that ignores a field gains from it.
- **Why results stay the same.** The rewrite is β/η on the checked term in `crates/rt` only: kernel
  terms, hashes, the elaborator and JS are untouched; the effect loop does what it did. Machine
  steps (frames entered) fall by two per operation answered (D3440). The `Unpack` change frees
  the same values in the same order. Checked by rt (66), native (70), js (14), the effect/handler
  tests (80, both runtimes' allocation traces agreeing, with rebuilds checked too),
  `every_example_lowers`, the million-element shapes, and the hash tests (14).
- **Measured** (instructions, against `2cce80c5b`; dispatch alone, then both): expressions
  −23.8% / **−25.5%**, scan −29.7% / **−30.4%**, bridge −20.3% / **−21.2%**, disk −11.9% /
  **−13.8%**, matcher −4.1% / **−3.9%**, binary-trees and mapops (no handlers) −0.0% / −0.4%;
  geomean −13.6% / **−14.4%**. `bench:aoc` geomean −10.0% / **−11.0%**, 36 / 38 days moved over
  3%, 22 over 10% (up to −30.6%), none up more than 0.24%. The `Unpack` change alone is −1.2%
  geomean on AoC, between −9.8% and +2.3% per day. §6's estimate was −11.5% / −14.5% on the two
  parsers; the spike's call counts explain the difference (the new apply is the cache's fast path).
- **Not done / rejected.** JS keeps its lowering (D3440's third question; it copies nothing per
  operation). The runtime clause table and an elaborator change were rejected in the note (§2.7).
  Stages 2 (the loop calls the dispatch's code directly) and 3 (a jump as a return) are still open.
- **Links.** SW-2498, SW-2507, SW-2511, SW-2525;
  [../proposals/compiled-handler-dispatch.md](../proposals/compiled-handler-dispatch.md) ("Stage 1b
  results").

### SW-2531: inline a function for its context (a selector's result taken apart at once)

- **Status:** merged 9 Nov 2026 (748dc58a3). Opus.
- **Problem.** SW-2513 target 2 (and SW-2371's "cause 2"): `Map.Tree.balance`
  is `rebuild (shape l r) l key value r`. `shape` (65 IR nodes) and
  `rebuild` (38) were too big for the inliner's 24-node limit, so every
  level of an insert made two calls: `shape` worked out the sizes and
  returned a `Shape` constant, and `rebuild` tested it and worked the sizes
  out again to build the node. The brief's premise, that the old node's cell
  was not reused because the `Bin` is built in another body, no longer holds:
  SW-2391's reuse across calls already passes the token down to
  `rebuild[reuse]`, and an alloc trace of the pattern allocates no more than
  the fused version, before and after this change. What was left was the
  calls and the `Shape` round trip: in the SW-2513 profile (after the record
  fix) `shape` and `rebuild` are 1.7 G + 1.4 G of 12.6 G instructions. A
  hand-fused `insertWith` measured 9.39 G (SW-2513).
- **Change.** `opt.rs`, GHC's "interesting context" discount, in two rules
  with their own caps (`CONTEXT_SIZE` 80 nodes for the function,
  `KNOWN_PUSH_SIZE` 96 for what case of case copies):
  - a non-recursive function whose leaves are all constructors of trivial
    fields (a *selector*, like `shape` or a `compare`) is inlined where its
    result is bound and taken apart at once, if the arms its leaves would
    take come to at most 96 nodes;
  - a non-recursive function whose body is a match on a parameter (like
    `rebuild`) is inlined where that argument's constructor is known, or is
    a call of such a selector, or an inlined one;
  - case of case into leaves that are all constructors is costed by the arm
    each leaf takes (the copy keeps only that arm), not by the whole match
    times the leaves.
  `balance` becomes one 126-node body that tests the sizes once and builds
  the unrotated node itself (and gets a reuse copy, `balance[reuse]`); the
  rotations stay calls. No std source changed.
- **Why results stay the same.** Inlining and case of case are the
  simplifier's existing rules, applied in more places; everything they move
  is pure and total. Kernel terms are untouched (hash tests pass). Checked by
  every `bench:instructions` and `bench:aoc` answer (all ok), rt and native
  lane tiers, `alloc_trace`/`reuse::`, `every_example_lowers`; a new IR test
  (`reuse::balance_builds_its_node_itself`, fails before) and an alloc-trace
  test against a hand-fused tree.
- **Measured.** `bench:instructions --runs 3`: mapops 12.66 -> 9.67 G
  (-23.6%; the hand-fused version is 9.39 G), dijkstra -4.7%, disk -3.6%,
  rbmap -0.2%, binary-trees -0.2%, bridge -0.1%, expressions -0.05%; geomean
  -5.0% over the seven. `bench:aoc`: geomean -1.30% over 55 days, all ok; 9
  days moved more than 3%, all down: 2020/08 -17.5%, 2020/14 -9.9%, 2020/01
  -7.8%, 2021/05 -6.3%, 2020/09 -5.5%, 2024/06 -4.7%, 2021/14 -4.4%, 2021/15
  -4.2%, 2024/05 -4.0%. The largest rise is +0.63% (2025/06, whose IR is
  unchanged: noise).
- **Code size (measured, IR nodes after reuse copies).** +2.09% over the 55
  AoC days and three bench programs (397,316 -> 405,621); most programs
  unchanged, the largest 2021/15 +11.9%, 2024/16 +8.9%, 2024/09 +6.0%,
  mapops +5.3%.
- **Not done.** `balance` itself (126 nodes) is still a call from
  `insertWith`; inlining it there too would take mapops towards the fused
  9.39 G (estimated a further 2-3%) at about 250 more nodes per Map
  instance, and needs a rule of its own (inlining a big function into a body
  that holds a reuse token it would use). Not tried.
- **Links.** SW-2531, SW-2513 target 2, SW-2371 cause 2, SW-2391 (reuse
  across calls).

### SW-2530: borrow inference stage B0, measured (dry run, no behaviour change)

- **Status:** merged pending review (`lane/SW-2530`). Sonnet. Measurement only.
- **Problem.** The note [../proposals/borrow-inference.md](../proposals/borrow-inference.md)
  estimated 3.5-5.5% of mapops and 5-12% of dijkstra from borrowed parameters, from earlier
  profiles; D3441 made building B1 depend on a measurement (gate: 3% on mapops or
  dijkstra, or 1% median on bench:aoc).
- **Change.** A dry-run inference over the bytecode (`crates/rt/src/borrow.rs`) and a machine
  counter behind cargo feature `borrow-counts` that counts the increments and decrements
  borrowing would remove or add (`borrow/shadow.rs`); `dev/borrow-counts` and
  `dev/borrow-counts-report` run and tabulate. Off in every shipped and test build.
- **Why results stay the same.** The counter only observes; answers of all runs matched.
- **Measured** (counts exact, instruction conversion estimated from a native micro-benchmark:
  13.5 per counted inc/dec, 5 per plain; counts validated at 2 increments per lookup level):
  mapops 6.75% (rules as written), 9.1% (O6 dropped); dijkstra 2.5%; disk 2.0/3.2%;
  memory-game 0/13.8%; const-fold 1.7%; binary-trees 1.8%; the rest under 0.6%. bench:aoc
  sample of 27 days: median 0.74% (b1), 0.87% (O6 dropped), 1.51% (with owned copies), max 21-29%.
  No geomean change measured (nothing changed in the compiler).
- **Verdict.** Gate passes on mapops: build B1, with O6 dropped. dijkstra is below 3% alone.
  Rejected finding: O6 as written leaves the specialised `get` walk's tree owned, because the
  optimiser lifts the `match` on `compare` into a function taking the node's value as an owned
  parameter.
- **Links.** SW-2530, SW-2518; note section 11.

### SW-2514: a record update takes a unique record's fields apart first

- **Status:** merged (`44beef6e9`). Opus.
- **Problem.** `{ w | f = g w.f }` on a uniquely held record read the field and
  kept `w` alive while `g` ran, so `w.f` was shared and every in-place reuse
  inside `g` was lost. Profile (SW-2513,
  [../reviews/SW-2513-mapops-profile.md](../reviews/SW-2513-mapops-profile.md)):
  `mapops` (Std.Map, 24.2 G instructions, 2.38 s against Lean's 0.31 s) is 48%
  too slow for this alone; measured by rewriting the program without the
  update. It affects every program that keeps state in records, which is AoC's
  house style.
- **Change.** `opt.rs` `take_apart`: an expression that reads a field of a
  one-constructor variable and uses the variable again gets one `match`
  around it, so a unique record gives up its fields unshared and its cell is
  reused.
- **Why results stay the same.** Only sharing changes: the match binds the same
  fields the projections read, and a shared record takes the same path as
  before. Checked by rt (66), native (70), hash snapshots,
  `every_example_lowers`, the million-element shapes and extraction (80).
- **Measured.** mapops 24.23 -> 12.65 G (-47.8%); bridge -4.5%, disk -1.9%,
  expressions -1.8%. `bench:aoc` geomean -2.59%, 14 days over 3% (up to
  -18.7%), none up more than 0.38%.
- **Not done.** The SW-2513 profile also found a fused balance worth a further
  -25.6% of mapops (measured by hand): filed as SW-2515 (inline balance into
  insertWith/remove so the old node's cell is reused). Read-only walks
  (SW-2516) stopped at design: no library-only fix, since an accessor fails
  the termination check and a nested match folds back into one unpack; the
  answer is borrow inference
  ([../proposals/borrow-inference.md](../proposals/borrow-inference.md), est.
  4-5% of mapops).
- **Links.** SW-2513, SW-2514; [../reviews/SW-2513-mapops-profile.md](../reviews/SW-2513-mapops-profile.md).

### SW-2523: rbmap-ck got 16% slower at unchanged instructions (accepted regression)

- **Status:** accepted regression, investigated, not fixed. The cause is
  SW-2502's side effect below; SW-2502 stays.
- **Evidence.** Overmind job 36: `rbmap-ck` native 1.55 -> 1.80 s (+16.2%)
  between `7d137b9d7` and `11f9f73ca`, instructions identical, `rbmap`
  unchanged. Bisect (job 37): first bad merge `0fdc931a7` (SW-2502). Cycles
  4.68 -> 5.11 G (+9%), IPC 2.27 -> 2.08, LLC misses flat, L1 misses +3%.
  `perf record` (job 38): about 80% of the extra cycles are one load in
  `value::free` (the child cell's count, before freeing it). `free`'s code is
  identical and `sw_static_closure` has no samples, so it is not the shared
  closure path.
- **Reading (orchestrator).** A data-layout effect: closures are no longer
  allocated per call, so the allocator hands out a different block pattern, and
  freeing the kept versions walks colder cells. About 30-38% of
  `rbmap-ck`'s cycles are in `value::free`, much of it the final teardown.
- **Decision.** Accept: SW-2502 is a net win everywhere else. Follow-up
  SW-2524 (skip freeing the live heap at process exit, as Lean does) addresses
  the cause for any program that ends with a big structure; l2 counters not
  yet taken.
- **Lesson (orchestrator's reading).** Instruction counts can hide a time regression when allocation
  patterns change; check the wide set's time on Overmind after allocation
  changes.
- **Links.** SW-2523, SW-2524; job 36 in docs/reviews/SW-2295-comparative-speed.md; the job 37 bisect and job 38 profile are on SW-2523.

### SW-2512 and SW-2481: checking speed (elaborator, not native code)

- **Status:** both merged (`11ed0d905`, `c0a70bcff`). Opus.
- **SW-2481 problem.** Deep `Fin` case chains cost about k^3-k^4 to check:
  `families::enter` substituted through the whole context at each `FSucc` step
  (k=20 0.3 s, 64 about 2 s, 100 about 9 s, 200 over 3 GB with an unknown
  bound).
- **Change.** `check::Rebuild` rebuilds substituted values keeping sharing
  (nodes stay identical), with a memo for spines and budget steps.
- **Why safe.** It touches trusted code (`check.rs` substitute,
  `unify_index::solve`), so an independent Opus review
  ([../reviews/SW-2481-rebuild-review.md](../reviews/SW-2481-rebuild-review.md))
  found no soundness bug and asked for fixes F1 (unchanged parts kept, which
  would otherwise undo SW-1106), F2 (spine memo, else exponential on shared
  spines), F3 (budget steps), F5 (tests, including a memo-off failure
  check); all merged. Values are node-identical, hashes unchanged.
- **Measured.** 256-arm `Fin` table 86 s -> 12 s (known bound), 200 arms with
  an unknown bound out-of-memory -> 15 s (36 s for 256). Ordinary code within
  1%.
- **SW-2512 problem.** A chain of shared lets followed by a `match` was
  exponential, on `main` before SW-2481 too: the equation generator
  (`equations.rs` `find_rhs`/`read_leaf`) substituted lets into a right side of
  about 2^n nodes before its size rule turned it down.
- **Change.** `zeta_size` counts first; `READ_CAP` of 65,536 nodes (and 10x the
  arm) skips before building, with a new skip reason (`docs/syntax.md`).
  Not trusted code.
- **Measured.** 16 lets 1.1-1.8 s -> 0.21 s; 20 and 40 lets (OOM) -> 0.21 and
  0.26 s.
- **Accepted loss.** Rows with a small branch of a huge let body (13-15 lets)
  lose their equation; keeping them needs lets kept through branch steps
  (filed, SW-2520).
- **Dropped: SW-2505.** `check_case` builds the scrutinee's display string for
  every case (about 8% of a deep table's time per a profile). Made lazy on
  `keep/SW-2505-lazy-scrutinee` (`503b8bcb3`): no measurable gain on a 64-arm
  table (0.36 s both), and printing after `enter` could show a solved
  metavariable differently. Dropped for no measured benefit.

### SW-2510: R7 merged; reusing the moved resumption's cell not merged

- **Status:** R7 merged (`6475d6c5d`, commit `bffe9030c`); cell reuse not
  merged.
- **Problem and change.** After SW-2499, forwarding an operation through a
  handler rebuilt a new operation cell each level (R7 in
  [effect-runtime-allocation.md](../proposals/effect-runtime-allocation.md)).
  Rebuilt forwarded operations now reuse the cells of the one they rebuild.
- **Why safe.** Only allocation changes; rt (65), native (70), effect/handler/
  resumption tests (79) pass; allocation traces agree.
- **Measured.** expressions -0.90%, scan -0.32% (estimate was -1.2 to -1.5%
  expressions: under the bar).
- **Not merged.** Reuse of the moved resumption's own cell (R3-style), commit
  `080bdf710` on `keep/SW-2510-cell-reuse`: -0.1 to -0.4%, native-only, and it
  needs a thread-local holding an emptied cell. Complexity for a gain inside
  the noise.

### SW-2502: capture-free lambdas built once

- **Status:** merged (`0fdc931a7`). Stage 1a of
  [../proposals/constant-hoisting.md](../proposals/constant-hoisting.md).
- **Problem.** A lambda with no captures was rebuilt at every use: `optional`
  builds nine per start, at 159 instructions each. Every program pays.
- **Change.** `Instr::StaticClosure`: a capture-free lambda is built on first
  use and shared for the run. The statics table holds a reference, so
  in-place reuse never touches the shared closure.
- **Why safe.** A capture-free closure is a pure value; sharing it changes only
  allocation counts (the orchestrator's call: stage 1a cannot change results,
  effects or step counts, so it did not wait on D3438/D3439). rt (65), native
  (70), hashes (14). JS unchanged.
- **Measured.** expressions -5.25%, scan -4.89%, bridge -5.31%, disk -3.61%
  (estimate expressions -3.5 to -3.9%); `bench:aoc` geomean -2.07%, 17 days
  over 3%, none slower than 0.08%.
- **Cost.** rbmap-ck time +16% at equal instructions (SW-2523 above,
  accepted).
- **Later stages** (1b literal folds, 2 floating pass, 4 unrolling `pick`)
  wait for Matt's D3438/D3439.

### SW-2499: a resumption nothing else holds has its fields moved

- **Status:** merged (`4dd2beaa8`). From SW-2493.
- **Problem.** `sw_resume_begin` copied the fields of a resumption even when
  nothing else held it. SW-2493
  ([../reviews/SW-2493-parse-operation-cost.md](../reviews/SW-2493-parse-operation-cost.md))
  accounts one Parse operation at 12-17 K instructions and 17-24 objects
  (5.7 K floor at depth 0, forwards +1.4-2.1 K each) and ranked this cut.
- **Change.** `Resume::take_unique` moves an unshared eager resumption's fields
  (the cell is left as `DoneK`), in native `sw_resume_begin` and in the
  machine, whose allocation traces must agree. The unsafe read was checked in
  review: fields are inline and the cell is forgotten.
- **Why safe.** Uniqueness is the same test every in-place reuse uses; shared
  resumptions still copy. rt (65), native (70), effects (79).
- **Measured.** expressions -3.36%, scan -2.59%, bridge -1.24%, disk -0.68%
  (estimate -3 to -5% and -2 to -4%).
- **Follow-up.** SW-2509: the value census counted a moved resumption as
  allocated `Fun::Resume` but freed as `Fun::DoneK`; per-kind balance fixed.
- **Not done here.** R7 and cell reuse (SW-2510, above).

### SW-2507: compiled handler dispatch spike (held for Matt)

- **Status:** measurement only, not merged. Prototype on
  `keep/SW-2507-dispatch-spike`; the measurement section is in
  [../proposals/compiled-handler-dispatch.md](../proposals/compiled-handler-dispatch.md).
  Stage 1b (SW-2511) waits for Matt's decision (D3440): shipping lowers step
  counts, which is user-visible.
- **Problem.** SW-2493: reaching a clause through `handlePlus` + `%elim` of 8
  clauses costs 1.85 K of the 5.7 K instruction floor per operation.
- **Spike.** Compile dispatch to a direct jump on SW-2493's scratch loops.
  Go criterion: Tick <= 5,080 instructions per operation and the eight-
  operation ability within 100 of Tick.
- **Measured.** Tick 5,671 -> 3,458; eight-operation ability within 17 of
  Tick; forward levels unchanged; outputs match. On the real programs:
  expressions 235.80 -> 177.99 G (-24.5%), scan 263.47 -> 186.92 G (-29.1%).
- **Open.** The prototype lacks tests, snapshots, profile names, machine/native
  agreement and the extra cell per route (SW-2511). A prior-art review is
  running (SW-2525).

### SW-2495: `pick` notes all its words in one operation

- **Status:** merged (`1486073cb`). Library-only. From SW-2492 target 3
  ([../reviews/SW-2492-expressions-scan-profiles.md](../reviews/SW-2492-expressions-scan-profiles.md)).
- **Problem.** `pick` noted its failure words one operation each.
- **Change.** One `Literals` note with all the words. The new internal
  constructor `Parse.Problem.Literals` is deliberately not user-facing API
  (nothing outside `Parse.sw` matches on `Problem`).
- **Why messages stay identical.** `shown` returns a list; the order was
  checked in review (expected is reversed then concat-mapped). 171 tests
  (hashes, std self-test, parse) and 4 `pick`-using AoC namespaces.
- **Measured.** scan -5.69%, expressions -0.88%, disk and bridge about 0.
  `bench:aoc` geomean -0.27% (2020/04 -4.3%, 2024/03 -5.7%), none slower.
  Estimate was scan -7 to -13.6%, expressions -3 to -6%: under it.

### SW-2494 (dropped) and SW-2497: literal character lists built once

- **Status:** SW-2494 dropped; its general form is SW-2497, a design note
  (`a1ab95d71`) and then SW-2502 above.
- **Problem.** `Parse.text`/`pick`/`literal` run `Text.toList` on a literal per
  try (3.28 M times on scan, 6.02 M on expressions). Hoisting by hand at the
  call site measured scan -5.8%, expressions -3.9%.
- **Tried.** The lane first stopped at 5 min: a library-only fix is
  impossible, since `text`/`pick` are plain calls with no per-parser value to
  hold the list. Option A (a new Parse operation `literalText` that walks the
  `Text` with `uncons`): expressions +0.92%, scan -3.23%; the walk costs about
  2 K per call, about what `toList` did. Net loss, dropped; diff in the
  orchestrator scratchpad.
- **Left.** Option B (native `Text.stripPrefix`) not tried. Option C, a
  compiler that lifts closed constant subterms (SW-2497), is the general fix
  and helps all code; stage 1b of the note.

### SW-2491 and SW-2487: `many` reuses marks and builds no closures per round

- **Status:** merged (`940382185`, `5707dc374`). Library-only.
- **Problem.** SW-2484 (disk and bridge profiles,
  [../reviews/SW-2484-disk-bridge-profiles.md](../reviews/SW-2484-disk-bridge-profiles.md),
  target 5): each round of `many` set a mark, then `optional` set another at
  the same state. SW-2491 swept every Parse combinator for the same kind of
  redundant operation.
- **Change.** SW-2487: `manyFuel` passes its round's mark to `optionalFrom`
  (`optional p = optionalFrom mark() p`, same state). SW-2491: each round's
  closing mark is the next round's opening mark, and a round's `rest`/`end`
  are arguments, not closures.
- **Why safe.** Statements `readsMany`/`runsMany` unchanged; helper lemmas
  replaced (`manyFrom` versions, `runsFromBindAt`); statements checked by the
  orchestrator (D2436). Audit Std.Parse 297/297, std self-test, 130
  parser-using AoC namespaces checked.
- **Measured.** SW-2487: disk 78.46 -> 72.66 G (-7.38%), bridge 102.23 ->
  96.20 G (-5.90%). SW-2491 on top: disk -12.2%, bridge -9.4% (both totals);
  `bench:aoc` geomean -4.12%, 22 days over 3% (up to -21.7%), none slower than
  1.2%.

### SW-2488 (dropped): `replicate k x ++ rest` without the copy

- **Status:** dropped before building (stopped at the bar as briefed).
- **Why.** Profiled after SW-2485: `List.append` is 1.0% of disk (2.1% before
  minOr) and `replicate` 1.3%, and disk's `blocksFrom` proofs rewrite against
  the `replicate ++` shape, so a std function would cost proofs and docs for
  at most 1%. Estimate had been -2 to -3%.
- **Revisit with** a general append-fusion rule, which gets it for free.

### SW-2486: a fused `natToken` operation (held for Matt)

- **Status:** built, not merged (`lane/SW-2486`, `da350645d`, worktree kept).
- **Problem.** SW-2484 target 2: bridge is 83% parsing, and a `token nat` is
  three marks and three spans.
- **Change.** A Parse operation `spacedNat` (one pass: spaces, digits, spaces)
  and public `Parse.natToken`; 22 proof arms (Reads 9, Runs 13), state-level
  theorem `spacedNatBySpans`, 16 hash snapshots; statements unchanged.
- **Measured.** Bridge 102.18 -> 80.56 G (-21.2%); disk +0.56% (the longer
  operation table).
- **Why held.** New user-visible std API, and the gain needs every `token nat`
  call site rewritten to `natToken`, including bridge's own source (2024 day
  7): a benchmark sped up by editing it, the over-fitting Matt warned about.
- **Recommendation.** Keep the operation and make `token nat` itself use it
  (specialise `token` on `nat`) so unchanged code gets the gain, plus
  Reads/Runs lemmas. Rebase on SW-2487/SW-2491 and regenerate snapshots
  (`task snap:hashes`) if it goes ahead.

### SW-814 (dropped): fused Map balance

- **Status:** dropped. Attempt on `keep/SW-814-fused-balance` (`69e17c6b2`).
- **Idea.** A fused `balanceL`/`balanceR` as in Data.Map, estimated about 30%
  fewer instructions per level. Scope: fused balance only; an Int/Nat-keyed
  IntMap not now.
- **Measured.** Statements unchanged. `bench:aoc` geomean -0.17% (best -2.9%),
  dijkstra -0.66%, the rest noise.
- **Why dropped.** Eight new definitions and lemmas for about 0.2%, and shapes
  can differ on unbalanced input. Revisit only with native `Map.Tree`
  `get`/`insertWith` (SW-1825) or a Std.Map benchmark. The `mapops` benchmark
  (SW-2503) now exists, and SW-2513 measured a fused balance at -25.6% of it
  *after* the SW-2514 record fix: that is SW-2515, so the verdict depends on
  the benchmark and should be re-judged there.

### SW-2485: `Map.Tree.minOr`/`maxOr` build the result once

- **Status:** merged (`aee351720`). Library-only. SW-2484 target 1.
- **Problem.** Each level of the walk built `Some (k, v)`; disk's profile
  showed 105.5 M cells.
- **Change.** `minFrom`/`maxFrom` carry key and value as two arguments, with
  `rfl` lemmas `minFromOr`/`maxFromOr`; `minOnto`/`maxOnto` statements
  unchanged.
- **Why safe.** The new function computes the same value (rfl lemmas); hash,
  pinned and prelude-bound tests (14) and the 35 AoC namespaces using min/max
  check clean.
- **Measured.** Disk 95.98 -> 78.19 G (-18.53%; wall 6.42 -> 5.28 s). Cells
  105.5 M -> 53.9 M.
- **Left.** `nearestBelow`/`nearestAbove` have the same pattern on one branch.

### SW-2474: timing builds were not like-for-like (finding, merged)

- **Status:** merged (`ba85fc928`).
- **Problem.** The same commit ran `expressions` in 320.5 G instructions built
  plainly and 310.7 G built in a lane worktree through kache (-3.1%), so lanes'
  numbers and Overmind's could differ for identical source.
- **Cause.** The devShell's `CARGO_PROFILE_RELEASE_INCREMENTAL=true`
  (`flake.nix`) builds `libstitchwort_standalone.a` in 256 codegen units
  without cross-unit inlining; kache strips the flag.
- **Change.** `bench:compare`, `bench:compare:check`, `native:bench` and
  `profile:native` build non-incrementally into `target/bench`. History in
  `history.toml` notes a one-off step of about 3%.
- **Open.** Overmind (job 32) showed no step even with the flag, so why only
  macOS builds differ is unexplained (musl target? linker? kache?).

### SW-2463 and SW-2462: effect-runtime allocation stages 1-3 (R1-R3)

- **Status:** merged (`f4c31a30b`, `37ad36ae5`). Stages of
  [../proposals/effect-runtime-allocation.md](../proposals/effect-runtime-allocation.md)
  (SW-2444: about 14 runtime objects per operation); each kept only if it
  delivered at least 60% of its estimate.
- **R1 (SW-2462).** A resumption is one object, its fields inside the `Fun`, not
  an `Rc<Resume>` plus a wrapper. Measured expressions -1.68%, scan -1.59%,
  matcher -0.36%, bridge -0.75% (5 runs, like-for-like builds); it cleared the
  bar. About 100 instructions saved per object, not the 140 assumed; later
  estimates use 100. `translate` gets `Fun::TranslateK` (two objects). Tests:
  rt 65, native 70, 113 effect/handler/resume.
- **R2 (SW-2463).** The loop reuses the `Bind` node as the pending cell.
  Measured expressions -3.40%, scan -3.20%, bridge -2.87%, matcher -0.69%.
  Pending cells 46.4 M -> 0.5 M.
- **R3.** A skipped forward reuses its `Call` cell: -1.81%, -1.45%, -0.67%,
  -0.39%; skip Calls 29.1 M -> 0. R2 + R3 together: expressions -5.15%, scan
  -4.61%, bridge -3.52%, matcher -1.07%. About 200 instructions saved per
  cell.
- **Why safe.** Only object counts and reuse change; counts of steps, effects
  and results are unchanged (the tickets are labelled "changes no counts").
- **Consequence.** R4 now saves one cell per perform, not two (re-estimate in
  the note, section 4.3). Later stages (R4 onward) are not done.

### SW-2452, SW-2468, SW-2482: freeing a deep value no longer overflows the stack

- **Status:** merged (`68c3a81aa`, `c417f0dc5`, `8674d0437`). Found by the
  elaborator fuzzer (`fuzz:elab`) in compute mode.
- **Problem.** Dropping a very deep `Value` chain recursed (drop glue): case
  531 of seed 0x2451 (a ~10M-deep `Rc<Unfolding>` chain) and case 2415 of seed
  0x246f (a stuck `Spine`), then every other type owning values.
- **Change.** `Drop for Unfolding` and `Spine` go through the iterative
  `free_iteratively` (SW-2452, SW-2468); `DataArgs`, `Shared` (Pi domain,
  NatAdd base, Eq parts) and `Unfolding.base` chains free by ordinary
  recursion down to `NESTING_LIMIT = 128` levels (about 64 KB), then
  iteratively (SW-2482). Six million-deep tests run on a 256 KB thread.
- **Rejected.** The first SW-2482 version always freed iteratively: +1.3-1.6%
  on `check --no-cache`. The depth-counter version is +0.2-0.6% on two files,
  level on one (noise about 0.5%); accepted as the orchestrator's call.
- **Not covered.** `Value::Resumption(Rc<Capture>)`.

### SW-2441: compact values, register dilation experiment (E not built)

- **Status:** experiment done on Overmind, never merged (patch `b28667004` on
  `origin/lane/SW-2441`).
- **Question.** Whether option E of
  [../proposals/compact-values.md](../proposals/compact-values.md) (an 8-byte
  header then two-word values) clears its gate: 1.10x decision-set geomean and
  1.25x on binary-trees. The cost model (SW-2429) predicted 1.088x and 1.21x,
  just under, so the experiment carried a fourth unused word per value
  register to mirror the spill cost.
- **Result.** Mirror reading 1.165x binary-trees, 1.090x decision set: misses
  the gate (clears only with every input at its high value).
- **Decision.** D3435 (Matt, 8 Nov): proceed to C then E only if E clears.
  E is not built; C alone is worth about 1% and waits with E. Related
  measurements: [../reviews/SW-2295-comparative-speed.md](../reviews/SW-2295-comparative-speed.md)
  and the V0-V4 notes in the proposal (E removes 7.0% of native instructions
  on the decision set; the parsers' low IPC is store-buffer and store-
  forwarding stalls, V2).

---

## 8 Nov 2026 and earlier (pointers)

Merged before this log began; figures are from the merge commits and tickets.

- **SW-2443**: freeing a cell with no deep fields skips the worklist
  (`d73ad4e06`): expressions -2.2%, scan -2.1%, octopus -2.3%. The one-slot
  pending variant measured +2.1 to +3.3% and was rejected (as was a
  thread-local and a `SmallVec` in SW-2421's A/B).
- **SW-2440**: native uniqueness tests compare the strong count only
  (`01fa1938c`): binary-trees -1.9%, octopus -1.3%, expressions -0.4%.
- **SW-2433**: one shared `JumpK` per thread (`bcf91079d`): expressions -0.8%,
  scan -1.0%.
- **SW-2398 and SW-2399**: Nat-shaped types, `Fin` as machine numbers and
  `Fin.toNat`/`Fin.ofNatLt` as pinned identities (`8fdfdf30d`, `a3261c779`):
  2025 day 3 -4.0% then -6.0% more, 2021 day 9 -4.3% then -4.1% more; steps
  and results unchanged.
- **Allocation by cause, census and counters** (SW-2422, SW-2425, SW-2461,
  SW-2475, SW-2479) in [../reviews/](../reviews/): the data these entries are
  chosen from.

### SW-2559 confirmed on Overmind (job 44, 9 Nov 2026)

Time on Linux x86-64, median of 5, against 9cc3fa3b8 (before SW-2511):
rbmap -7.0% (SW-2511 alone had been +1.2%), binary-trees -14.5%,
rbmap-ck -13.9%, memory-game -1.3%, mapops -20.6%. `CellCache::full`, 15.3%
of binary-trees' cycles before, is gone from every profile; LLC load misses
fell 54% on binary-trees and from 3.8 M to 0.89 M on rbmap. The 0.3% more
instructions measured on macOS buy this. Data on Overmind, job 44.
