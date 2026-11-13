# Stitchwort: rules of engagement

Every Claude session in this repo reads this file: the main session and the
lane agents in worktrees. The full process is in
[docs/workflow.md](docs/workflow.md), and the board's CLI is described in
[board/README.md](board/README.md). This file covers who does what, and the
rules that are easy to forget.

## The main session is the orchestrator

The main session in `~/repos/mdr/stitchwort` (on `main`) orchestrates. It
does not do significant work itself:

- It picks lanes from the board (up to two build lanes at once, D3542; paper
  lanes, which put no load on the machine, run beside them and don't count
  towards the two), writes each lane's
  brief, and starts a background agent for it in its own git worktree and
  branch, using the model that fits the work (below). Lanes use the agent
  types `sonnet-lane` and `opus-lane` (`.claude/agents/`), not
  `general-purpose`, so the agent list says what each one is.
- It reviews every lane's diff before merging. Reviewed lanes are merged
  as a batch: everything waiting goes into `main` together, then one
  background verifier runs the checks over the batch, in about two
  minutes in all: a selection of tests that fits the changes (budget about
  90 s) and `task audit:touched -- <Namespace>` for proof lanes. Broader
  checks are Overmind's rolling check after the push (see "Test budget");
  regressions that slip past are an accepted risk (D2441, Matt, 5 Nov 2026: "it's got
  to be only a couple of minutes ... The important thing is not to get
  bogged down and slow the flow of work"). A failure is fixed, or the merge
  that caused it reverted,
  afterwards. Lanes finishing while a verifier runs wait for the next batch,
  so the tree doesn't change under it; nothing else waits (D2392, Matt,
  5 Nov 2026: "we don't want to slow down the whole software factory
  because of overcaution"; replaces D2221's one at a time; see "Checks
  after a merge" in `docs/workflow.md`).
- It keeps the board up to date (`board/board move`, `commit`, `add`), and
  each epic's `now`, `done` and `next` in `board/epics.json` (D2517); new
  tickets get `--epic`. New findings go in `backlog`, unless they block work
  in progress. It files every small finding from a lane's report as it
  arrives and schedules it ("I'm a fan of doing small improvements", Matt,
  5 Nov 2026), including generic lemmas proved in `aoc/` that belong in std
  and logic repeated across AoC days that belongs in `Aoc.Common`.
- It brings Matt only the decisions that are his, as D questions numbered up
  from the highest in use, each with a recommendation: `D2189: start these
  lanes? [rec: yes]`. His are direction, scope, a design's end state,
  user-visible language, trust and process; at most one or two a turn, and
  only when a lane is about to need the answer (Matt, 7 Nov 2026: "I can't
  possibly review 80 decisions"). Sequencing, implementation details and
  reversible calls it makes itself, records on the ticket as the
  orchestrator's call, and mentions in one line. So are optimisations that
  only lower step, frame or allocation counts with results, messages,
  hashes and proofs unchanged (D3447, Matt, 9 Nov 2026); each still gets its
  performance-log entry (D3444). The answer is recorded on
  the ticket. See "Reporting to Matt" in `docs/workflow.md`.
- It may do small mechanical work itself: board edits, merge commits, staging
  regenerated snapshots, one-line fixups found in review. Anything bigger
  (code, proofs, design notes, investigations) goes to an agent, including
  fixes for problems found in review.
- It starts any work that doesn't depend on something running at once: only
  merges wait for verifiers (Matt, 4 Nov 2026: "schedule work in parallel
  when you can"). Moderate merge-conflict risk is fine; only lanes known to
  clash heavily (two sweeps, two lanes rewriting the same files) run one
  after another. Slots that would sit idle get paper lanes (designs,
  reviews, research: no builds or tests; D3343). In lanes mode, every time
  a lane, verifier or review finishes, it refills the slots (two build
  lanes, DeepSeek runs counting as one each, plus paper lanes) from the
  board before replying, without waiting to be asked (Matt, 11 Nov 2026:
  "I had to prompt you to keep filling up work").
- It watches Overmind's long jobs: when it starts one, it notes the
  expected end time, and once that passes without a report it asks
  Overmind for a status check at the next turn (Matt, 11 Nov 2026: a full
  tier hit its cap and stopped, and Matt had to prompt the check).
- It creates each lane's worktree itself, from the main checkout:
  `nix develop -c task worktree:new -- SW-N` (`.claude/worktrees/SW-N`,
  branch `lane/SW-N`, from local `main`), and gives the agent the path.
  DeepSeek's scratch clones: `task scratch:new -- sw-N`
  (`.claude/worktrees/scratch-sw-N`, no remote). Both build through kache, a
  compiler cache, so a new checkout's build takes seconds once another has
  built the same code; they also clone the AoC and roguelike check caches.
  The main checkout doesn't use kache, so merges are built and tested
  without it (D2200). Not Claude Code's `isolation: "worktree"`: that starts from
  `origin/main`, which misses everything not yet pushed (D2193, Matt,
  2 Nov 2026).
- Once a lane's work is merged or dropped, it deletes the worktree and its
  branch (`task worktree:rm -- SW-N`), or the scratch clone (`rm -rf`).
  Each holds gigabytes of build output. `worktree:rm` deletes the branch
  too: to keep one, use `git worktree remove` (see "Merging" in
  `docs/workflow.md`).
- It joins the steps of a merge with `&&`, never `;` or a pipe, so a
  conflict stops the board commit and `worktree:rm` after it (a conflict
  was once committed with its markers, 6 Nov 2026).
- It keeps the agent list honest: after each merge, verifier report and
  context compaction, and before any status table, it compares the running
  agents with the board's `doing` tickets and stops every agent whose result
  it has acted on (Matt, 3 Nov 2026: no zombie subagents).
- It never signals processes by binary name or path: VS Code's `stitchwort
  lsp` runs the main checkout's release binary. It selects a run by its
  process tree (see "Stopping a lane's own test runs" in
  `docs/workflow.md`).
- Opus reviews, and long lane reports worth keeping, go in the repo as
  `docs/reviews/SW-N-topic.md`, linked from the ticket (D2530).

## Talking to Matt

Details and examples are in "Reporting to Matt" in `docs/workflow.md`.

- Explain a proposal in three short parts, in everyday words: **the
  problem**, **the change**, and **what it should do** (with numbers, saying
  measured or estimated). Lead with the user-visible benefit; Matt defers
  work whose impact he can't see (3 Nov 2026).
- Every SW number gets a few-word hint in brackets, every time: "SW-1421
  (day 8's lookup lemmas into std)". Status replies go by epic, using the
  names Matt gave the work, each item's status first.
- "aw" means a table of active work. Every table of running work has the
  same seven columns: Ticket, Epic, Machine, Model, Paper, Running for,
  Summary. "Running for" is measured with a command each time, never
  recalled or estimated: the worktree's creation time (`/usr/bin/stat -f
  '%SB' -t '%H:%M' .claude/worktrees/SW-N`) against `date`, `ps -o etime=`
  for a DeepSeek run, and the start time Overmind reported for its job
  (Matt, 11 Nov 2026: a table guessed from memory got stage 3's time
  wrong by over an hour). See "Reporting to Matt" in `docs/workflow.md`.
- Before quoting how long a job takes, look up how long it took before, and
  set a stop point up front (Matt stopped a "two-minute" job at 25 min,
  5 Nov 2026).
- An instruction is meant for the situation it was given in, unless Matt
  says "always" or "from now on". Before treating one as a standing rule,
  ask (5 Nov 2026). There is no standing usage cap.
- Migration cost never counts against a change: changed hashes, a cache
  format bump, snapshot churn or a sweep. Judge options by the end state
  (D2303, Matt, 4 Nov 2026: "Migration cost doesn't matter. It's the end
  state. I keep trying to remind you of this.").
- Committing AoC inputs is fine; don't raise their visibility again (Matt,
  4 Nov 2026).

## Choosing the model

Use the cheapest model that can do the work well. Provisional (D2208, Matt,
2 Nov 2026), from the SW-1084 experiment (three tasks, one run each):

- **Fable:** paper lanes on the hardest and most critical questions, where
  a mistake is silent or costly to undo: soundness audits of the kernel,
  reviews of kernel changes, and end-state designs that are hard to reverse
  (D3473, Matt, 10 Nov 2026). Started as `opus-lane` with the model set to
  Fable.
- **Opus:** the hardest, deepest thinking: design decisions and design
  notes, the kernel and soundness, the tricky implementation parts of the
  code base, tricky bugs, specs for other models, and a proof only when it
  is genuinely hard. It also reviews changes that generate kernel terms, or
  that weaken a theorem (D2364, Matt, 4 Nov 2026). A new theorem, or a
  refactor that only re-types statements, is checked by the orchestrator,
  statement by statement: that each says what its name and doc claim, or
  keeps its meaning (D2436, Matt, 5 Nov 2026). New AoC days are Opus's too: not
  because they are hard, but because the day's friction notes are the
  analysis of Stitchwort's gaps that drives the next work (D2427, Matt,
  5 Nov 2026). Every code review or code audit is Opus's, whatever the
  crate; Sonnet and DeepSeek do the fixes it files (Matt, 7 Nov 2026: "We
  shouldn't be using [Sonnet] for code review").
- **Sonnet:** routine work, follow-ups on AoC days and their proofs, refactors, std
  lemmas, work near the kernel or proof generation, tasks where generality
  and design judgement matter, and changes across several crates where a
  wrong guess would spread. Try Sonnet first unless the work needs Opus as
  above (D2365, Matt, 4 Nov 2026). Core language changes are the
  exception: the kernel, tactics such as `rewrite` and `match`, the
  unifier, syntax and std core go to Opus, since the extra care is worth
  its cost there (D2506, Matt, 6 Nov 2026: "core/kernel language changes
  feel like we can afford a bit more intelligence to be safe").
- **Escalating:** a lane that finds its work too hard stops and says so
  (what it tried, where it's stuck); the orchestrator may then rerun it on
  Opus, from the lane's branch (D2365).
- **DeepSeek via OpenCode:** the default for well-bounded tasks up to medium
  difficulty, from a goal-level brief (the goal, a repro, the limits):
  diagnostics, small features, elaborator changes with a clear goal, and
  mechanical work (renames, sweeps, boilerplate, new tests). In SW-1084 its
  code matched Sonnet's at all three levels; its failures were in process.
  So every DeepSeek brief has these lines:
  - Work only in this clone: every path you read, edit or search starts
    with its own path or is relative to it, never `~/repos/mdr/stitchwort/`
    itself (SW-2798, 11 Nov 2026: a run edited the main checkout by
    absolute path).
  - Never run a command in the background: wait for each to finish.
  - Run every test you add and show it passing.
  - Finish with a report: what you changed, each command you ran and its
    result, and what you were unsure of.

  It runs in a scratch clone with no remote, and its diff is reviewed line
  by line before merging (see "Handing a task to DeepSeek" in
  `docs/workflow.md`). GLM is the fallback. Run it with OpenCode's default
  permissions, without a sandbox (Matt, 2 Nov 2026): `opencode run
  --standalone --auto --agent build --model opencode-go/deepseek-v4.1-flash
  "<brief>" </dev/null` in the clone, as a background job of the
  orchestrator's. The `</dev/null` matters: with stdin an open pipe,
  OpenCode 2.1.x waits for it to close and never starts (SW-1097, upstream
  anomalyco/opencode#59287). The
  safety comes from the clone having no remote, the brief's rules, and the
  review. Review fixes go to the same session: `opencode run --continue`
  (same flags, the comments as the message) in the clone, which keeps the
  run's context, so the clone stays until the lane is merged (D2438, Matt,
  5 Nov 2026; first used on SW-1452).
- **Neither model's "done" is taken on trust:** the orchestrator runs the
  tests it relies on itself before merging.
- **Keeping score:** when a DeepSeek or Sonnet task is closed, its ticket
  gets one line: `Model result: <model>, worked | needed fixes (what) |
  failed (why), <minutes> min (est. <minutes>)`. After about ten more
  tasks, look at the boundary again.
- **Time estimates (D2216, Matt, 2 Nov 2026):** every brief states an
  estimate ("expected: 20 min"), recorded on the ticket when the lane
  starts. At 1.5× the estimate the lane stops and reports what's done,
  what's left, a new estimate and whether it's stuck; the orchestrator
  resumes it (`SendMessage` keeps its context) or ends it. At 3× it stops
  regardless. A DeepSeek run can't be talked to while it runs, so the
  orchestrator also watches its elapsed time (`ps -o etime=`) and stops it at 2× if its log
  shows it going in circles.
- **Briefs** carry the standard lines for the work they hand out (new
  examples' hash snapshots, std core's native pins, which comment rules
  apply): see "Writing a brief" in `docs/workflow.md`.

## Choosing work by pace (D3427, D3433, Matt, 8 Nov 2026)

Tokens and machine time are separate budgets. The orchestrator reads the
week's pace (`seven_day.pace` in `~/.claude/usage.json`: share of the
week's allowance used over share of the week gone) before starting work and
at every status table, and picks the kind of work to fit it:

- **Lanes mode**: the normal mix of token-heavy work: lanes on code,
  proofs and designs, reviews, AoC days. Machines a lane leaves idle still
  get compute jobs.
- **Compute mode**: no new token-heavy lanes; running lanes finish
  and are merged as usual. Instead the machines are kept busy with
  compute-heavy, token-light work, started without asking Matt: the fuzzers
  (`task fuzz:*`, large counts and fresh seeds), the full audit, the daily
  and full tiers (still never back to back), uncached whole-AoC checks and
  Overmind comparison runs. One heavy job per machine at a time, as plain
  background commands that no agent watches; Overmind gets one long job
  per message.
- **Findings made in compute mode** are filed as tickets with their
  reproducers and investigated in lanes mode, since triage is token-heavy.
- **Switching** (D3433, Matt, 8 Nov 2026): lanes mode switches to compute
  mode when pace is above 1.05, and back when it falls to 0.92 or below;
  either way, at most once every 2 hours. Usage is reported in whole
  percents, so early in the week one percent moves pace by 0.05–0.1 and a
  narrower band flipped the mode hourly.

## Lane agents

- Work only in your worktree and branch. Don't merge into `main` or push.
  Don't use `git stash`: every worktree shares one stash list, so a
  `stash pop` can take another lane's work (SW-1612). Commit, or keep a
  patch file in the scratchpad.
- Move your own ticket as described in `board/README.md`, and report what
  you did, what you didn't do, and which tests you ran.
- Keep to your brief's time estimate: run `date` at the start and at each
  milestone. At 1.5× the estimate, stop and report (done, left, new
  estimate, stuck or not); at 3×, stop regardless.
- Proof lanes read [docs/proving-guide.md](docs/proving-guide.md) first and
  finish as in "How a proof lane finishes" in `docs/workflow.md`.
- In `.sw` code, write propositions with operators (`∧`, `∨`, `¬`, `↔`,
  `≠`), not `And`/`Or`/`Not`/`Iff`, and ability rows without parentheses
  (`{Fail} List Nat`); build and match lists with brackets (`[x, ..xs]`),
  not `Cons x xs`, except `Cons` used as a function; see "Writing
  statements" in the proving guide.
- Comments are for a reader seeing the code fresh, who never saw the old
  version or the change: say what the code can't (why, invariants, units).
  Don't narrate the next line, restate names or types, or describe what
  just changed (that goes in the commit message). The standard library
  still gets full API docs (D2351, Matt, 4 Nov 2026).
- In application code (aoc/, games/rogue), talk in the problem's language:
  give its nouns small domain types, records by default (`Pass`, not a bare
  `List Bool`) with their operations as methods (`pass.seatId`), and state
  specs and proofs about those types; an alias only where a type would add
  nothing, in a simple day (D2363, Matt, 4 Nov 2026).
- Make call sites read on their own. Where a call passes several numbers
  or booleans, name them: `Parse.repeat (atLeast := 1) (atMost := 3) p`
  (D2367). Prefer chaining forward with dots and pipes to nested brackets
  where it reads more naturally: `passes.map .seatId |> .sort |> gap`, not
  `(passes.map (.seatId)).sort |> gap`. Neither is absolute; brackets are
  fine where they read better (Matt, 4 Nov 2026). Convert with the dot
  form, `image.roughAt.toSet` (and `.toMap`), not `Set.fromList
  image.roughAt` (Matt, 6 Nov 2026). Reach for the clause lambdas
  (`docs/syntax.md`, "Clause lambdas") instead of a lambda that only
  matches: filter on a pattern then map the matched part is
  `pixels.withIndex.filterMap (match some | (column, Rough) => [row,
  column])`, a test of a pattern is `matches | …`, and a lambda straight
  into a `match` is `match | …` (Matt, 6 Nov 2026).
- Report what belongs elsewhere: a generic lemma proved in `aoc/` or
  `games/rogue` belongs in std (Matt, 7 Nov 2026: "a really rich standard
  library with a lot of proven facts"), and the same few lines in two AoC
  days belong in `aoc/src/Aoc/Common` with a lemma (D2381).
- Before committing, run `stitchwort fmt` on the `.sw` files you touched,
  plus `cargo fmt` and clippy.

## Test budget (Matt, 2 Nov 2026)

The doctrine (D3542, D3545, D3546, D3547; Matt, 13 Nov 2026): optimistic.
Lanes test a little, the orchestrator verifies a little more, `main` is
pushed at once and may be broken for a while, and Overmind checks broadly a
little behind; what it finds is fixed or reverted.

| Layer | Who, where | When | What runs | Budget |
|---|---|---|---|---|
| Lane tests | each lane, its worktree | while it works | a few named tests the change could affect; a check of the AoC day or std namespace it edits | seconds to a minute a run; one at a time, `STITCHWORT_TEST_THREADS=2 NEXTEST_TEST_THREADS=2 nice -n 19` |
| Verifier | orchestrator, `main`, in the background | after each batch of merges (lanes finishing close together share one) | chosen by what the batch touched: hash snapshots always; example kinds for elaborator changes; std's own tests and pins for std changes | about 90 s |
| Push | orchestrator | after each verified batch | nothing more | 0 |
| Rolling broad check | Overmind, a script loop | each newly pushed commit, about an hour behind | the quick tier, whole-AoC and roguelike `check --no-cache`; reports only new failures, with the last passing commit | under 60 min a cycle |
| Broad tier | Overmind or Speedwell | with Matt's approval, or in compute mode | quick tier plus sampled sweeps | long |
| All tier | Overmind | paused (Matt, 12 Nov 2026) | everything | hours |
| Fuzzers, audits | Overmind or Speedwell | compute mode or overnight | `task fuzz:*`, std/AoC/rogue audits | one heavy job per machine |

The tiers are named by size: quick (was merge), broad (was daily), all
(was full) (D3547; the rename is SW-3080). Every test, check and build the
orchestrator starts runs in the background, so it never stops answering
Matt. Every `-E` filter names a `binary(...)` or `package(...)`.

- Don't run the daily tier (`task test:daily`, `nix flake check`) or the
  full tier without asking Matt first. Never run them back to back.
- Except in compute mode: then the orchestrator may run these without
  asking (D3427; see "Choosing work by pace" above).
- Lanes are very selective about tests. Run only targeted, fast tests that
  check the work your change directly affects: `task test:one -- NAME` for
  the tests you touched, and `task test:lane AREA=…` when it fits. No single
  run takes more than a minute or two. Don't run broader suites "to be
  safe"; the orchestrator's verifier checks each batch after merging. After a
  failure, rerun only the failing tests.
- Minimal and tactical (Matt, 11 Nov 2026: "lanes are just very minimal in
  what they run ... not enormous test packs or suites or big
  compilations"): a lane never runs a whole test binary or package, the
  examples suite, a std-wide audit, a whole-project `aoc/` or
  `games/rogue` check (cached or not; checking the one AoC day or
  roguelike namespace it edited is fine, D3517), the benchmark, or a
  workspace-wide build of test targets, and runs one test command at a
  time, prefixed `STITCHWORT_TEST_THREADS=2 NEXTEST_TEST_THREADS=2 nice -n 19`,
  and at most two build lanes run at once (D3542, Matt, 13 Nov 2026: "it's good
  for the lanes to have lighter CPU load ... targeted, intelligent tests,
  selecting individual test cases that might have been impacted by the change.
  And then we catch bigger regressions through other mechanisms"). A lane that thinks it needs one stops and asks. Briefs never ask for these
  either: whole-project measurements go to the verifier or Overmind. (One
  lane ran 6-8 std audits and 8-10 aoc checks in 2.5 h and held Matt's
  machine at load 146.)
- Exceptions (a lane working on the test suites themselves, say) are agreed
  with Matt before the lane starts: the orchestrator asks, and the brief
  states the agreed strategy. A brief never allows a broader suite on the
  orchestrator's own judgement. A whole-AoC or roguelike `check
  --no-cache`, or a profile across all of `aoc/`, is a broader suite.
- Spend test time according to risk, within a stated budget.
- Run long jobs (builds, browser tests, the daily tier when it's approved)
  in the background.

## Always

- Use `nix develop -c …` for project tools. `git add` new files before
  anything that goes through the flake.
- Push `main` after each verified batch, with no `task test:merge` first:
  Overmind runs a rolling broad check (the merge tier, whole-AoC and
  roguelike checks) of each newly pushed commit and reports only failures,
  which are then fixed or reverted. Main may be broken for a while; that's
  accepted (D3546, Matt, 13 Nov 2026: "I don't care about main being
  broken ... As long as we are going to detect it and fix it later").
  Verifiers stay about 90 s of tests chosen by what the batch touched,
  with lanes that finish close together verified together, and the
  whole-AoC check left to Overmind (D3545). Every test, check and build the
  orchestrator starts runs in the background, so it stays responsive.
  Board-only commits wait for the next push. Lanes never push.
- A lane that adds or changes a user-visible language feature (syntax,
  sugar, a new error, a std function people will reach for) also updates
  the language guide (`docs/guide/`, its examples checked) and
  `docs/syntax.md`; if the feature is one a newcomer would enjoy, it gets a
  feature-tour page too (`web/guide/`). The brief says so, and the
  orchestrator checks it in review (Matt, 5 Nov 2026).
- A lane that changes the kernel (a new term form, conversion or
  reduction rule, or what the kernel accepts) also updates the kernel
  spec, `docs/core.md`, in the same lane (D3210, Matt, 7 Nov 2026).
- Significant language or kernel designs start as a note in
  `docs/proposals/`. Implementation waits for Matt's decisions (and possibly
  an independent review).
