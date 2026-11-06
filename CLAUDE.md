# Stitchwort: rules of engagement

Every Claude session in this repo reads this file: the main session and the
lane agents in worktrees. The full process is in
[docs/workflow.md](docs/workflow.md), and the board's CLI is described in
[board/README.md](board/README.md). This file covers who does what, and the
rules that are easy to forget.

## The main session is the orchestrator

The main session in `~/repos/mdr/stitchwort` (on `main`) orchestrates. It
does not do significant work itself:

- It picks lanes from the board (up to three at once), writes each lane's
  brief, and starts a background agent for it in its own git worktree and
  branch, using the model that fits the work (below). Lanes use the agent
  types `sonnet-lane` and `opus-lane` (`.claude/agents/`), not
  `general-purpose`, so the agent list says what each one is.
- It reviews every lane's diff before merging. Reviewed lanes are merged
  as a batch: everything waiting goes into `main` together, then one
  background verifier runs the checks over the batch, in about two
  minutes in all: a selection of tests that fits the changes (budget about
  90 s) and `task audit:touched -- <Namespace>` for proof lanes. The merge
  tier and the full audit wait for the daily and full tiers; regressions
  that slip past are an accepted risk (D2441, Matt, 5 Nov 2026: "it's got
  to be only a couple of minutes ... The important thing is not to get
  bogged down and slow the flow of work"). A failure is fixed, or the merge
  that caused it reverted,
  afterwards. Lanes finishing while a verifier runs wait for the next batch,
  so the tree doesn't change under it; nothing else waits (D2392, Matt,
  5 Nov 2026: "we don't want to slow down the whole software factory
  because of overcaution"; replaces D2221's one at a time; see "Checks
  after a merge" in `docs/workflow.md`).
- It keeps the board up to date (`board/board move`, `commit`, `add`). New
  findings go in `backlog`, unless they block work in progress.
- It brings Matt the decisions that are his as D questions, numbered up from
  the highest in use. After each turn it lists the open ones, each with a
  recommendation: `D2189: start these lanes? [rec: yes]`. The answer is
  recorded on the ticket.
- It may do small mechanical work itself: board edits, merge commits, staging
  regenerated snapshots, one-line fixups found in review. Anything bigger
  (code, proofs, design notes, investigations) goes to an agent, including
  fixes for problems found in review.
- Lanes that touch the same area run one after another, not side by side.
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
  Each holds gigabytes of build output.

## Choosing the model

Use the cheapest model that can do the work well. Provisional (D2208, Matt,
2 Nov 2026), from the SW-1084 experiment (three tasks, one run each):

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
  5 Nov 2026).
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
- Before committing, run `stitchwort fmt` on the `.sw` files you touched,
  plus `cargo fmt` and clippy.

## Test budget (Matt, 2 Nov 2026)

- Don't run the daily tier (`task test:daily`, `nix flake check`) or the
  full tier without asking Matt first. Never run them back to back.
- Lanes are very selective about tests. Run only targeted, fast tests that
  check the work your change directly affects: `task test:one -- NAME` for
  the tests you touched, and `task test:lane AREA=…` when it fits. No single
  run takes more than a minute or two. Don't run broader suites "to be
  safe"; the orchestrator runs the merge tier after merging. After a
  failure, rerun only the failing tests.
- Exceptions (a lane working on the test suites themselves, say) are agreed
  with Matt before the lane starts: the orchestrator asks, and the brief
  states the agreed strategy. A brief never allows a broader suite on the
  orchestrator's own judgement.
- Spend test time according to risk, within a stated budget.
- Run long jobs (builds, browser tests, the daily tier when it's approved)
  in the background.

## Always

- Use `nix develop -c …` for project tools. `git add` new files before
  anything that goes through the flake.
- Push to GitHub only when Matt asks.
- A lane that adds or changes a user-visible language feature (syntax,
  sugar, a new error, a std function people will reach for) also updates
  the language guide (`docs/guide/`, its examples checked) and
  `docs/syntax.md`; if the feature is one a newcomer would enjoy, it gets a
  feature-tour page too (`web/guide/`). The brief says so, and the
  orchestrator checks it in review (Matt, 5 Nov 2026).
- Significant language or kernel designs start as a note in
  `docs/proposals/`. Implementation waits for Matt's decisions (and possibly
  an independent review).
