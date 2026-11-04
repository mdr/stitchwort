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
- It reviews every lane's diff before merging. It merges lanes into `main`
  one at a time. The checks after a merge (a selection of tests that fits the change,
  `task audit`, and `task audit:touched -- <Namespace>` for a proof lane;
  the fixed `task test:merge` too when `core`, `elab` or `driver` change,
  otherwise once per batch and before a push) are run by a background
  verifier agent, so the orchestrator isn't tied up (D2221, D2255; see
  "Checks after a merge" in `docs/workflow.md`). The next merge waits for
  the verifier's pass.
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

- **Opus:** work that needs design or real intelligence: design notes,
  the kernel and soundness, proofs, tricky bugs, and specs for other models.
  It also reviews every change that generates kernel terms or touches
  proofs, whichever model wrote it.
- **Sonnet:** work near the kernel or proof generation, tasks where
  generality and design judgement matter, and changes across several crates
  where a wrong guess would spread.
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
  review.
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
  regardless. A DeepSeek run can't be resumed, so the orchestrator also
  watches its elapsed time (`ps -o etime=`) and stops it at 2× if its log
  shows it going in circles.

## Lane agents

- Work only in your worktree and branch. Don't merge into `main` or push.
- Move your own ticket as described in `board/README.md`, and report what
  you did, what you didn't do, and which tests you ran.
- Keep to your brief's time estimate: run `date` at the start and at each
  milestone. At 1.5× the estimate, stop and report (done, left, new
  estimate, stuck or not); at 3×, stop regardless.
- Proof lanes read [docs/proving-guide.md](docs/proving-guide.md) first and
  finish as in "How a proof lane finishes" in `docs/workflow.md`.
- In `.sw` code, write propositions with operators (`∧`, `∨`, `¬`, `↔`,
  `≠`), not `And`/`Or`/`Not`/`Iff`, and ability rows without parentheses
  (`{Fail} List Nat`); see "Writing statements" in the proving guide.
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
- Significant language or kernel designs start as a note in
  `docs/proposals/`. Implementation waits for Matt's decisions (and possibly
  an independent review).
