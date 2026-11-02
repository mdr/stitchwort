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
  one at a time, then runs `task test:merge` and `task audit` (and
  `task audit:touched -- <Namespace>` for a proof lane).
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
- It creates each lane's worktree itself, from local `main`
  (`git worktree add -b lane/SW-N .claude/worktrees/SW-N main`), and gives
  the agent the path. Not Claude Code's `isolation: "worktree"`: that starts
  from `origin/main`, which misses everything not yet pushed (D2193, Matt,
  2 Nov 2026). DeepSeek's scratch clones are cloned from local `main` too.
- Once a lane's work is merged or dropped, it deletes the worktree and its
  branch (`git worktree remove`, `git branch -D`), or the scratch clone.
  Each holds gigabytes of build output.

## Choosing the model

Use the cheapest model that can do the work well:

- **Opus:** work that needs design or real intelligence: design notes,
  the kernel and soundness, proofs, tricky bugs, and specs for other models.
- **Sonnet:** changes of medium complexity, such as implementation across
  several files, or anywhere a misreading would spread.
- **DeepSeek via OpenCode:** mechanical work from a precise spec written by
  the orchestrator or Opus: renames, sweeps, boilerplate, new tests, small
  features with a clear shape. It runs in a scratch clone with no remote,
  and its diff is reviewed line by line before merging (see "Handing a task
  to DeepSeek" in `docs/workflow.md`). GLM is the fallback. Run it with
  OpenCode's default permissions, without a sandbox (Matt, 2 Nov 2026):
  `opencode run --standalone --auto --agent build --model
  opencode-go/deepseek-v4.1-flash "<spec>"` in the clone, in the background.
  The safety comes from the clone having no remote, the spec's rules, and
  the review.

## Lane agents

- Work only in your worktree and branch. Don't merge into `main` or push.
- Move your own ticket as described in `board/README.md`, and report what
  you did, what you didn't do, and which tests you ran.
- Proof lanes read [docs/proving-guide.md](docs/proving-guide.md) first and
  finish as in "How a proof lane finishes" in `docs/workflow.md`.
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
