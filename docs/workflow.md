# How work gets done

Stitchwort is built by Matt with AI models doing most of the writing. This
note records who does what, so the split stays consistent between sessions
and any model working on the repo can read it. The kanban board in `board/` is the task list (see [board/README.md](../board/README.md)).

## Who does what

| Model | Used for |
|---|---|
| **Claude Opus** | Design notes, analysis, anything touching the kernel or soundness, proofs, tricky bugs, writing specs for other models, and reviewing every diff before it's merged (and, for changes that generate kernel terms or touch proofs, a dedicated review). Also orchestrates: hands out tasks, merges, runs the test tiers. |
| **Claude Sonnet** | Work near the kernel or proof generation, tasks where generality and design judgement matter, changes across several crates where a wrong guess would spread. |
| **DeepSeek V4.1 Flash** (via OpenCode Go) | The default for well-bounded tasks up to medium difficulty, from a goal-level brief: diagnostics, small features, elaborator changes with a clear goal and a repro, and mechanical work (renames, sweeps, boilerplate, new tests). |
| **GLM-5.3-Flash** (via OpenCode Go) | Fallback when DeepSeek is unavailable. |
| Local model (Ollama) | Offline fallback only; about 20 times slower. |

The aim is to spend Opus on the hard reasoning and hand everything else to
cheaper models. The split is provisional (D2208, 2 Nov 2026): it comes from
SW-1084, where DeepSeek and Sonnet got the same goal-level brief for an
easy, a medium and a hard task. DeepSeek's code matched Sonnet's at every
level; its failures were in process (a backgrounded build that ended its
one-shot run, a test it never ran), which three standing lines in its
brief now cover (`CLAUDE.md`, "Choosing the model"). Each closed task's
ticket records how the model did, and the split is looked at again after
about ten more.

## Significant designs

A design that changes the language goes in a note under `docs/proposals/`,
researched against how other languages do it. Matt decides the open
questions, an independent reviewer reads the note, and only then does
implementation start, usually in stages.

## Handing a task to DeepSeek

1. Make a scratch clone with no git remote, so the model can't push:
   `nix develop -c task scratch:new -- sw-N`, from the main checkout
   (`.claude/worktrees/scratch-sw-N`; see "Lane checkouts" below).
2. Run OpenCode there in the background with the brief (the command is in
   `CLAUDE.md`, "Choosing the model"). The brief gives the goal, a repro and
   the limits, and says: no sub-agents, no commits; never run a command in
   the background; run `cargo fmt`, clippy and the relevant targeted tests,
   and every test it adds, showing them passing; leave new snapshots
   (`.snap.new`) and benchmark changes for the reviewer; finish with a
   report of each command and its result.
   The brief also gives a time estimate; the run stops and reports at 1.5×
   it, and the orchestrator watches the elapsed time and stops a run at 2×
   that is going in circles (D2216; `CLAUDE.md`, "Choosing the model").
   Run it with `--print-logs`, so its log shows activity, and with stdin
   from `/dev/null`: given an open pipe as stdin, `opencode run` waits for
   it to close and never starts (SW-1097; upstream anomalyco/opencode#59287,
   open on 2.1.4 and 2.2.x). A run that still logs nothing past its server's
   start within 2 minutes has hung some other way: stop it, start it again,
   and record it on SW-1097 (D2217).
3. Opus reviews the diff line by line and reruns the tests it relies on.
   DeepSeek has introduced real bugs before, and once handed over a test it
   had never run, so its own "tests pass" isn't enough.
4. Commit in the clone with the trailer "Done by OpenCode with DeepSeek V4.1
   Flash (OpenCode Go) from a spec by Claude; reviewed by Claude", check the
   commit author, then fetch and merge into `main`.
5. Regenerate snapshots and the benchmark baseline, stage them, and run the
   merge tier (below). For playground changes also run `task test:browser`.
6. Update the ticket: move it to done and record the commits (`board/board commit N HASH`, `board/board move N done`).
7. Delete the clone (`rm -rf .claude/worktrees/scratch-sw-N`).

Claude's own lanes work the same way, in git worktrees instead of scratch
clones.

## Checks after a merge

(D2221, Matt, 2 Nov 2026; batches since D2392, Matt, 5 Nov 2026.) The
orchestrator merges every reviewed lane that is waiting in one go, then
starts one background verifier over the batch, a Haiku agent, with a short brief: the merge commit,
the exact commands to run on `main` (`task test:selected` with its
filterset, and for a proof lane `task audit:touched --
<Namespace>` from the project's directory, e.g. `aoc/`), and nothing else.
It runs them one after another, never in the background, changes nothing,
and reports pass, or each failing test with the first lines of its output,
plus the wall time and `uptime` before and after. The orchestrator carries
on meanwhile; lanes that finish wait for the next batch, so the tree
doesn't change under the verifier. A failure becomes a fix for an agent,
or the merge that caused it is reverted; bisecting a batch's merges is
cheap, as nothing is pushed until Matt asks. Only one verifier runs at a time, and
none while timing-sensitive work is running.

After each merge the tests run are a selection that fits the change, not a
fixed set (SW-1098; D2255, Matt, 3 Nov 2026). The merge check is tuned for
quick feedback that keeps work flowing; what it misses is caught later by
the fixed merge tier, the daily tier or the full tier.

1. The verifier refreshes the inventory (`nix develop -c task test:inventory
   -- --junit target/nextest/merge/junit.xml`), which lists every test with
   its profiles and last known time. Times come from nextest's JUnit files;
   each run folds in, the latest wins. `task test:selected` folds its own
   JUnit times as it ends, so the next run cannot overwrite them unread.
2. It works out the selection. `nix develop -c task test:affected --
   --dry-run --range OLD..NEW` (OLD the commit before the batch's first
   merge) does it by rule (`dev/test-affected.toml`; docs/testing.md, "The
   affected-test selection"): a filterset, `EXAMPLES`, an estimate and what
   it cut to fit the 90 s budget, always including the fixed core (core,
   syntax, one AoC day). The verifier takes that as the start and adds what
   the diff needs beyond the rules, following [test-selector.md](test-selector.md)
   with the lane's report and the inventory.
3. It runs the selection: `nix develop -c task test:affected -- --range
   OLD..NEW` as it stands, or `SELECTOR_ESTIMATE=N [EXAMPLES=x] nix develop
   -c task test:selected -- '<filterset>'` for an edited one. Both run `task test:features` and
   `cargo fmt --check`, then nextest as `test:merge` does, and logs a line
   to `dev/selector-log.tsv`.

**A batch's whole check takes about two minutes** (D2441, Matt, 5 Nov
2026: "it's got to be only a couple of minutes. We'll pick up other issues
that slip past in the daily or full runs later, and accept regressions as a
risk. The important thing is not to get bogged down and slow the flow of
work."). It runs in the main checkout: the selected tests (budget about
90 s), `task audit:touched` for a proof lane's namespaces, and nothing else.
The fixed merge tier (`task test:merge`) and the full `task audit` don't run
per batch, even when `crates/core`, `crates/elab` or `crates/driver`
changed; they run at the daily and full tiers and before a push, where a
failure that the selections missed is recorded on SW-1098 and the merges
since the last pass are the suspects. The inventory is refreshed only when
a batch adds or renames many tests.

## Lane checkouts

The orchestrator makes every lane's checkout itself, from the main checkout,
and deletes it once the work is merged or dropped (D2193, D2200, Matt,
2 Nov 2026):

| | Make | Delete |
|---|---|---|
| Claude lane | `task worktree:new -- SW-N`: `.claude/worktrees/SW-N`, branch `lane/SW-N` | `task worktree:rm -- SW-N` |
| DeepSeek | `task scratch:new -- sw-N`: `.claude/worktrees/scratch-sw-N`, no remote | `rm -rf` the folder |

- Both start from local `main`, so they have everything committed but not
  yet pushed. Claude Code's own `isolation: "worktree"` isn't used: it
  starts from `origin/main`.
- Both build through **kache**, a compiler cache (in the devShell), set up
  in `.claude/worktrees/.cargo/config.toml`, which the tasks write and cargo
  finds above each checkout. A new checkout's release build takes about 9 s
  once another checkout has built the same code (72 s cold). Build-script
  runs aren't cached, so the driver's build fingerprint is always computed
  afresh. The main checkout doesn't use kache: every merge is built and
  tested without it.
- Both clone the AoC and roguelike check caches (`.stitchwort/`)
  copy-on-write, so a first `stitchwort check` of AoC takes about 3 s, not
  a minute.
- The recipe is in `Taskfile.yml` (`LANE_SETUP`), so it changes in one
  place. Measurements behind it: sccache and a cloned `target/` were tried
  first (66 s and 48 s).

## The test tiers

Tests run in tiers with time budgets ([testing.md](testing.md#tiers)), so
that most of the time the tests being run are fast ones:

- **lane**, under 10 s: a lane runs `task test:lane AREA=…` for the area it
  changed, and `task test:one -- NAME` for the tests it touched (a bare name
  matches test names only; `-E 'binary(name)'` selects a whole test binary),
  while it works.
- **merge**, under 90 s on a 10-core M1 Pro: `task test:merge` on `main` after every merge.
- **daily**, under 5 minutes: `task test:daily`, or `nix flake check`
  (`task test:gate`), at a daily checkpoint: formatting, clippy, every test
  with the corpus sweeps on a sample, the examples and their snapshots, hash
  stability and the benchmark baseline, and `debug-builtins` (the
  `stitchwort-driver` `builtins` test binary, which loads the prelude, built
  and run in the debug profile so overflow checks and `debug_assert!`s are
  exercised; every other check is release).
- **full**: `task test:full`, every test over the whole corpus, only when
  Matt asks.

New files must be `git add`ed first, since the flake only sees tracked
files. Long runs (the daily tier, browser tests, builds) go in the
background.

Before committing, run `stitchwort fmt` on the `.sw` files you touched. The
test `crates/cli/tests/tools/fmt_repo.rs` fails, naming the files, if any tracked
`.sw` file is not formatted. It skips `examples/reject`, `examples/soundness`,
`examples/projects/reject`, `crates/fmt/tests/it/golden` and
`examples/accept/list-literal-layout.sw`, so leave those as written.

Pushing to GitHub happens only when Matt asks.

## Stopping a lane's own test runs

Every worktree builds test binaries with the same names (`target/release/deps/<name>-<hash>`),
and VS Code's `stitchwort lsp` shares the release binary's name. A bare
`pkill <name>` or `killall` therefore also kills the same tests in other
lanes and the verifier in the main checkout (three SIGTERMed runs on the night
of 6 Nov 2026, SW-1774). A lane stops its own processes with
`dev/stop-mine`: it signals only processes whose executable lies under
`<this checkout>/target/` (an absolute-path prefix match) and their
descendants, and prints each one. `dev/stop-mine --dry-run` only lists them;
`dev/stop-mine --tree PID` stops one pid and its children, refusing a pid
whose executable is outside the checkout. A lane never runs `pkill` or
`killall`.

## Lanes and the task list

Work runs in lanes (up to three at once), each in its own git worktree and
branch ("Lane checkouts" above), merged into `main` in batches (with one verifier over each batch).
The main session orchestrates: it chooses lanes, hands each to a background
agent, then reviews, merges and keeps the board up to date. Agents move their
own tickets as described in [board/README.md](../board/README.md).

- Lanes that change performance run the benchmarks before merging
  (`nix develop -c cargo run --release -p stitchwort-bench`) and record an
  intended change with `-- --update`, saying why in the commit. The
  deterministic counts are checked by `nix flake check` (+10% fails).
- A lane that proves theorems is told to read
  [proving-guide.md](proving-guide.md) first: its rules (never weaken a
  statement, prove against a spec in the problem's words, report "not
  proved" honestly), workflow, tools, common errors and performance traps.
  A lane brief that hands out proofs links it.
- A lane that writes or reviews docs or comments follows
  [syntax.md, "What to write"](syntax.md#what-to-write), and its brief
  links it. The standard library is documented in full, and application code
  only where the code can't say it. A brief never asks for higher coverage
  outside std.
- Significant design decisions (soundness, the kernel, language semantics)
  get a design note in `docs/proposals/` first, researched against the
  literature, and wait for the user (and possibly an external reviewer)
  before implementation.
- Questions for Matt in a session get a D number (D1454, D1455, …),
  counting up from the highest in use so each is unique. D numbers are
  handles for the session's open questions, not a permanent record: the
  answer goes on the SW- ticket it concerns. After each turn the
  orchestrator lists the session's unanswered D questions, each followed by
  its recommendation in square brackets (`D1454: start these lanes? [rec:
  yes]`).
- New findings become tickets in `backlog` (label `bug` for known issues),
  not straight into `next`, unless they block what's in progress.
- Design detail lives in `DESIGN.md` and `docs/proposals/`; tickets only
  track what is to do and why. Finished work is in git log;
  [history.md](history.md) keeps what the old `TODO.md` recorded as done.

### How a proof lane finishes

A lane that adds or changes theorems (AoC proofs, the roguelike's, std's)
follows [proving-guide.md](proving-guide.md) while it works (§7 there is
what its report says), and runs `stitchwort audit` on the namespaces it touched before it reports
(SW-912, D2040), from the project folder: `stitchwort audit
Aoc.Year2024.Day06`, `stitchwort audit Rogue.Proofs`, or `stitchwort audit
Std.List` for std ([syntax.md](syntax.md#auditing-theorems-stitchwort-audit)).

- A failure (`✗`: an axiom beyond the allowed ones, an unfinished theorem,
  or a counterexample) is fixed before reporting, or listed under "Not
  proved".
- A warning (`!`: hypotheses no input satisfied) is read. If the
  hypotheses really contradict each other, the theorem proves nothing:
  fix its statement, or say so in the report. If they are only narrow (a
  monster at exactly the given cell), say so in a line.
- The report quotes the summary line (`audited N theorems: …`).

**At merge** (D2043, Matt, 30 October 2026; trimmed by D2441, 5 Nov 2026): a proof lane's touched namespaces are audited with the search (`task audit:touched -- Aoc.Year2024.Day06`) before it is merged. It isn't inside `task test:merge`, whose 90 s budget the search would break.
